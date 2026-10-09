#!/usr/bin/env python3
"""Weighted date budgets, quantile grids and regularization identities for I2."""
from __future__ import annotations

from fractions import Fraction
import json
import math
from typing import Callable


def simpson(fun: Callable[[float], float], lo: float, hi: float, n: int = 4096) -> float:
    if n < 2 or n % 2:
        raise ValueError("Simpson subdivision count must be a positive even integer")
    step = (hi - lo) / n
    total = fun(lo) + fun(hi)
    total += 4 * math.fsum(fun(lo + j * step) for j in range(1, n, 2))
    total += 2 * math.fsum(fun(lo + j * step) for j in range(2, n, 2))
    return step * total / 3


def primitive_q2(r: float, a: float) -> float:
    """Increasing primitive of r^-1 (a^2+r)^-1/4, for a>0."""
    if r <= 0 or a <= 0:
        raise ValueError("The primitive requires r>0 and a>0")
    z = (1 + r / (a * a)) ** 0.25
    return (math.log((z - 1) / (z + 1)) + 2 * math.atan(z)) / math.sqrt(a)


def density(r: float, q: float, a: float) -> float:
    return r ** (-q / 2) * (a * a + r) ** (-0.25)


def primitive(r: float, q: float, a: float) -> float:
    if a == 0:
        beta = q / 2 + 0.25
        return r ** (1 - beta) / (1 - beta)
    if q != 2:
        raise ValueError("This identity check uses an explicit primitive only for q=2 or a=0")
    return primitive_q2(r, a)


def quantile_grid(n: int, q: float, a: float) -> tuple[list[float], float]:
    if n < 2 or q < 2 or not (0 <= a <= 1):
        raise ValueError("Require n>=2, q>=2, and a in [0,1]")
    epsilon = n ** (-1 / (q - 1))
    p0, pe = primitive(1.0, q, a), primitive(epsilon, q, a)
    mass = p0 - pe
    if a == 0:
        beta = q / 2 + 0.25
        grid = [(1 + j / (n - 1) * (epsilon ** (1 - beta) - 1)) ** (-1 / (beta - 1))
                for j in range(n)]
    else:
        grid = [1.0]
        for j in range(1, n - 1):
            target = p0 - j * mass / (n - 1)
            lo, hi = epsilon, 1.0
            for _ in range(72):
                mid = (lo + hi) / 2
                if primitive(mid, q, a) < target:
                    lo = mid
                else:
                    hi = mid
            grid.append((lo + hi) / 2)
        grid.append(epsilon)
    grid[0], grid[-1] = 1.0, epsilon
    return grid, mass


def main() -> dict:
    # The lower-bound argument uses weighted Cauchy with the varying target.
    # A signed y is included to check that positivity of y is not being used.
    weights = [Fraction(1, 7), Fraction(2, 7), Fraction(4, 7)]
    y = [Fraction(-2), Fraction(1, 2), Fraction(3)]
    mu = [Fraction(1, 3), Fraction(5, 4), Fraction(2)]
    w = [Fraction(1), Fraction(7, 5), Fraction(9, 2)]
    energy = sum(x * yy * yy for x, yy in zip(weights, y))
    covariance = sum(x * yy * mm for x, yy, mm in zip(weights, y, mu))
    variance_lower = sum(x * ww * mm * mm for x, ww, mm in zip(weights, w, mu))
    corrected_energy = sum(x * yy * yy / ww for x, yy, ww in zip(weights, y, w))
    cs_gap = corrected_energy * variance_lower - covariance * covariance
    residual = energy - covariance * covariance / variance_lower
    direct_lower = energy - corrected_energy
    assert cs_gap >= 0 and residual >= direct_lower

    # Gaussian integral for E[y_s^2]; fixed inputs, no parameter-rate regression.
    normal_checks = []
    for T, a, s in [(1.0, 0.0, 0.7), (1.0, 0.2, 0.7), (2.0, 0.75, 1.1)]:
        U = T * (1 + a * a)
        exact = 1 / (2 * math.pi * math.sqrt(U * U - s * s))
        numeric = simpson(lambda z: math.exp(-s * z * z / (U - s)) /
                         (2 * math.pi * (U - s)) * math.exp(-z * z / 2) /
                         math.sqrt(2 * math.pi), -10.0, 10.0)
        rel_error = abs(numeric - exact) / exact
        assert rel_error < 2e-10
        # t=U*sin(theta) makes the integral of F identically 1/(2*pi).
        endpoint = math.asin(T / U)
        variance = endpoint / (2 * math.pi)
        assert 0 < variance <= 0.25
        normal_checks.append({"T": T, "a": a, "s": s,
                              "F_relative_error": rel_error, "variance_target": variance})

    # Exact primitive at q=2, checked independently in log-r coordinates.
    primitive_checks = []
    for a, lo, hi in [(0.25, 1/256, 1.0), (1.0, 1/256, 1.0), (0.05, 1/128, 0.7)]:
        exact = primitive_q2(hi, a) - primitive_q2(lo, a)
        numeric = simpson(lambda x: (a*a + math.exp(x)) ** (-0.25), math.log(lo), math.log(hi))
        rel_error = abs(exact - numeric) / exact
        assert rel_error < 2e-10
        primitive_checks.append({"a": a, "lo": lo, "hi": hi, "relative_error": rel_error})

    # Single fixed budget. These are grid identities, not fitted risk rates.
    grid_checks = []
    n = 256
    for q, a in [(2.0, 0.0), (2.0, 0.25), (2.0, 1.0), (4.0, 0.0)]:
        r, mass = quantile_grid(n, q, a)
        step = mass / (n - 1)
        masses = [primitive(r[j], q, a) - primitive(r[j+1], q, a) for j in range(n-1)]
        rel_mass_error = max(abs(x-step) / step for x in masses)
        assert len(r) == n and all(r[j] > r[j+1] for j in range(n-1))
        assert math.isclose(r[-1], n ** (-1/(q-1)), rel_tol=1e-14)
        assert rel_mass_error < 2e-10
        max_relative_cell = max((r[j]-r[j+1])/r[j] for j in range(n-1))
        assert max_relative_cell <= 0.5
        # Verify the monotone-density inequality used by the upper proof.
        max_left_mass_ratio = max((r[j]-r[j+1])*density(r[j], q, a)/step for j in range(n-1))
        assert max_left_mass_ratio <= 1 + 1e-11
        grid_checks.append({"n": n, "q": q, "a": a, "epsilon": r[-1],
                            "lambda": step, "max_relative_cell": max_relative_cell,
                            "max_relative_mass_error": rel_mass_error,
                            "max_left_mass_ratio": max_left_mass_ratio})

    # Exact exponent algebra at representative q values, including nonintegers.
    exponent_checks = []
    for q in [Fraction(2), Fraction(5, 2), Fraction(4), Fraction(7)]:
        beta = q/2 + Fraction(1,4)
        epsilon_exp = -1/(q-1)
        lambda2_over_n_exp = epsilon_exp * 2*(1-beta) - 1
        digital_risk_exp = -1/(2*(q-1))
        assert lambda2_over_n_exp == digital_risk_exp
        exponent_checks.append({"q": str(q), "det_digital_MSE_exponent": str(digital_risk_exp)})

    return {"status": "PASS", "scope": "Deterministic algebra and grid-geometry checks only; no market-risk computation or rate fitting.",
            "weighted_Cauchy": {"gap": str(cs_gap), "projection_residual": str(residual),
                                 "direct_lower": str(direct_lower)},
            "Gaussian_target_moments": normal_checks, "critical_primitive": primitive_checks,
            "fixed_budget_grids": grid_checks, "exponent_algebra": exponent_checks}


if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))
