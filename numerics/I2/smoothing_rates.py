#!/usr/bin/env python3
"""Smoothing exponent identities, Gaussian integrals and sensitivity checks for I2."""
from __future__ import annotations

import json
import math
from fractions import Fraction
from typing import Callable


def simpson(f: Callable[[float], float], a: float, b: float, steps: int) -> float:
    """Composite Simpson quadrature, used only on smooth bounded intervals."""
    if steps <= 0 or steps % 2 or not a < b:
        raise ValueError("Require a < b and a positive even step count")
    h = (b - a) / steps
    odd = math.fsum(f(a + h * j) for j in range(1, steps, 2))
    even = math.fsum(f(a + h * j) for j in range(2, steps, 2))
    return h * (f(a) + f(b) + 4.0 * odd + 2.0 * even) / 3.0


def relative_error(actual: float, expected: float) -> float:
    return abs(actual - expected) / max(abs(expected), 1e-300)


def main() -> None:
    # Exact rational cancellations used in the entropy-smoothing argument.
    exponents = []
    for alpha in (Fraction(11, 20), Fraction(3, 4), Fraction(19, 20)):
        gamma = (2 * alpha - 1) / (2 * alpha)
        assert gamma + 1 / (2 * alpha) == 1
        assert (2 * alpha - 1) / (2 * alpha) == 1 - 1 / (2 * alpha)
        assert gamma / 2 + 1 / (4 * alpha) == Fraction(1, 2)
        assert Fraction(1, 1) - alpha / (2 * alpha) == Fraction(1, 2)
        exponents.append({"alpha": str(alpha), "gamma": str(gamma)})

    # Profile integral: y=b*log(1+x) turns the infinite interval into
    # an exponential integral. Truncation at y=60 is negligible here.
    profiles = []
    for b in (0.1, 0.5, 0.9):
        exact = 1.0 / b + 2.0 / b**2 + 2.0 / b**3
        numeric = simpson(lambda y: math.exp(-y) * (1 + y / b)**2 / b,
                          0.0, 60.0, 24000)
        err = relative_error(numeric, exact)
        assert err < 2e-10, (b, err)
        profiles.append({"b": b, "exact": exact, "quadrature": numeric,
                         "relative_error": err})

    # Independent-stock quadratic-Gaussian identity (8.2).
    gaussian = []
    normalizer = math.sqrt(2.0 * math.pi)
    for q, z in ((0.0, 0.0), (0.08, 0.7), (0.4, -1.2), (1.1, 1.8)):
        mean = math.exp(z*z/(2*(1+q))) / math.sqrt(1+q)
        numeric = simpson(
            lambda x: math.exp(-x*x/2) / normalizer
            * (math.exp(-q*x*x/2 + z*x) / mean)**2,
            -14.0, 14.0, 28000,
        )
        exact = (1+q) / math.sqrt(1+2*q) * math.exp(
            z*z/((1+q)*(1+2*q)))
        err = relative_error(numeric, exact)
        assert err < 1e-11, (q, z, err)
        gaussian.append({"q": q, "z": z, "exact": exact,
                         "quadrature": numeric, "relative_error": err})

    # Integrate the self-consistent sensitivity expression after t=r^alpha.
    # This checks that the extra x in (4.6) is accounted for.
    sensitivity = []
    for alpha, tau, scale in ((0.55, 0.3, 0.8), (0.75, 0.02, 30.0),
                              (0.95, 0.5, 6.0)):
        end = tau**alpha
        exact = -math.expm1(-scale*end)/(alpha*scale)
        numeric = simpson(lambda t: math.exp(-scale*t)/alpha,
                          0.0, end, 12000)
        err = relative_error(numeric, exact)
        assert err < 1e-11, (alpha, tau, scale, err)
        sensitivity.append({"alpha": alpha, "tau": tau, "scale": scale,
                            "relative_error": err})

    report = {
        "scope": "Deterministic identity checks only; no hedging data or rate fits",
        "exact_exponent_checks": exponents,
        "cameron_martin_profile": profiles,
        "quadratic_gaussian_second_moment": gaussian,
        "sensitivity_integration": sensitivity,
        "status": "PASS",
    }
    print(json.dumps(report, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
