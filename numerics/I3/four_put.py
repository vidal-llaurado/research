#!/usr/bin/env python3
"""Shifted-put moments and a rational information-gain certificate for I3."""
from __future__ import annotations

import json
import platform
from fractions import Fraction as F
from typing import Any

import mpmath
import sympy as sp


def equal(actual: sp.Expr, expected: sp.Expr, label: str) -> None:
    if sp.expand(actual - expected) != 0:
        raise AssertionError(f"Exact identity failed: {label}: {sp.simplify(actual - expected)}")


def integral(expr: sp.Expr, *limits: tuple[Any, ...]) -> sp.Expr:
    return sp.expand(sp.integrate(sp.expand(expr), *limits))


def record(value: F) -> dict[str, str | float]:
    return {"exact": str(value), "decimal_for_readability_only": float(value)}


def main() -> None:
    u, v, t, delta, eta = sp.symbols("u v t delta eta", real=True)
    psi = u * (v**2 - sp.Rational(1, 3)) - (u**2 - sp.Rational(1, 3)) * v
    density = 1 - delta * u * v + eta * psi
    equal(integral(density - 1, (u, -1, 1)), 0, "Y marginal matching")
    equal(integral(density - 1, (v, -1, 1)), 0, "X marginal matching")
    equal(psi.xreplace({u: v, v: u}), -psi, "swap antisymmetry")
    for ulo, uhi in [(-1, 0), (0, 1)]:
        for vlo, vhi in [(-1, 0), (0, 1)]:
            equal(integral(psi, (v, vlo, vhi), (u, ulo, uhi)), 0, "quadrant invariance")
    psi2 = integral(psi**2 / 4, (v, -1, 1), (u, -1, 1))
    equal(psi2, sp.Rational(8, 135), "E_Q psi^2")
    covariance = integral(u * v * density / 4, (v, -1, 1), (u, -1, 1))
    equal(covariance, -delta / 9, "covariance")

    # Tuples: payoff, lower-v, upper-v, lower-u, upper-u, J at t=0.
    triangles = [
        (u - t, -1, -u, t, 1, -1),
        (-t - v, -u, -t, t, 1, -1),
        (t + v, -t, -u, -1, t, 1),
        (t - u, -u, 1, -1, t, 1),
    ]
    eh, eh2, score = sp.Integer(0), sp.Integer(0), sp.Integer(0)
    for payoff, vlo, vhi, ulo, uhi, sign in triangles:
        eh += integral(payoff * density / 4, (v, vlo, vhi), (u, ulo, uhi))
        eh2 += integral(payoff**2 * density / 4, (v, vlo, vhi), (u, ulo, uhi))
        score += sign * integral(
            payoff.subs(t, 0) * density / 4,
            (v, sp.sympify(vlo).subs(t, 0), sp.sympify(vhi).subs(t, 0)),
            (u, sp.sympify(ulo).subs(t, 0), sp.sympify(uhi).subs(t, 0)),
        )
    eh, eh2 = sp.expand(eh), sp.expand(eh2)
    expected_eh = (2 * delta + 15 * t**2 + 5) / 30
    expected_eh2 = (
        21 * delta * t**6 - 105 * delta * t**4 + 315 * delta * t**2 + 105 * delta
        + 20 * eta * t**7 - 84 * eta * t**5 + 140 * eta * t**3 - 140 * eta * t
        + 210 * t**4 + 1260 * t**2 + 210
    ) / 2520
    equal(eh, expected_eh, "E H_shift")
    equal(eh2, expected_eh2, "E H_shift^2")
    equal(score, -eta / 36, "signed score")
    j = integral(density / 4, (v, -1, 0), (u, 0, 1)) + integral(
        density / 4, (v, 0, 1), (u, -1, 0)
    )
    equal(j, sp.Rational(1, 2) + delta / 8, "J second moment")
    c = (1 + t)**2 / 4 + (1 - t)**2 / 4 - sp.Rational(1, 3)
    equal(c, sp.Rational(1, 6) + t**2 / 2, "capital")
    q = sp.expand(eh2 - 2 * c * eh + c**2)
    q0 = (20 + 7 * delta) / 360
    equal(q.subs(t, 0), q0, "q0")
    zero_difference = t**2 * (
        sp.Rational(1, 3) - t**2 / 6 + delta * (7 - 5 * t**2 + t**4) / 120
    )
    equal(q.subs(eta, 0) - q0, zero_difference, "zero-score two-put obstruction")
    expected_difference = (
        delta * t**6 / 120 - delta * t**4 / 24 + 7 * delta * t**2 / 120
        + eta * t**7 / 126 - eta * t**5 / 30 + eta * t**3 / 18 - eta * t / 18
        - t**4 / 6 + t**2 / 3
    )
    equal(q - q0, expected_difference, "complete shifted-put risk polynomial")

    # One predetermined rational configuration, not an optimizer or search.
    d, e, n, s = F(1, 16), F(1, 4), 256, F(1, 100)
    eps = s**2 / 2
    h_f, j_f, a_f = F(1, 6) + d / 15, F(1, 2) + d / 8, e / 36
    mu, c0 = d / 15, F(1, 6)
    q0_f = (20 + 7 * d) / 360
    v0 = q0_f - mu**2
    i_low = F(8, 135) / (1 + d)
    posterior_low = n * e**2 * i_low / (1 + (n - 1) * e**2 * i_low)
    assert d + 4 * e / 3 == F(19, 48) < 1
    assert a_f > j_f * s
    phi = 2 * a_f * s - j_f * s**2
    e_minus, e_plus = 2 * s * eps + eps**2, 6 * s * eps
    risk_gain = phi * posterior_low - e_minus - e_plus
    assert risk_gain == F(117427397, 3121200000000) > F(3, 100000)
    v_min = v0 - 2 * h_f * eps - phi - e_minus
    assert v_min == F(45317823, 800000000) > 0
    reserve = c0
    lambda_low, lambda_high = F(2, 25), F(3, 25)
    lambda_required = mu * (c0 + eps) / (reserve * v_min)
    assert lambda_required == F(10003000, 135953469) < lambda_low
    utility_bracket = phi * posterior_low - (v0 / v_min)**2 * (e_minus + e_plus)
    utility_gain = mu**2 * utility_bracket / (2 * lambda_high * v0**2)
    assert utility_gain == F(20662710820734212744, 24464226318304662740190501)
    assert utility_gain > F(8, 10000000)

    output = {
        "status": "all exact assertions passed",
        "execution": {
            "python": platform.python_version(), "sympy": sp.__version__,
            "mpmath": mpmath.__version__,
            "method": "symbolic polynomial integration and exact rational arithmetic",
            "stochastic_draws": 0, "parameter_configurations": 1, "optimization_calls": 0,
        },
        "identities": {
            "marginal_matching": "both exact", "quadrant_invariance": "all four exact",
            "covariance": str(covariance), "E_Q_psi_squared": str(psi2),
            "E_H_shift": str(eh), "E_H_shift_squared": str(eh2),
            "score": str(sp.expand(score)), "j": str(sp.expand(j)),
            "capital": str(sp.expand(c)), "q0": str(q0),
            "q_shift_minus_q0": str(sp.expand(q - q0)),
            "zero_score_risk_difference": str(zero_difference),
        },
        "finite_certificate": {
            "delta": str(d), "eta": str(e), "n": n, "epsilon": str(eps),
            "endpoint_displacement": str(s), "density_positivity_upper_sum": str(d + 4 * e / 3),
            "h": str(h_f), "j": str(j_f), "a": str(a_f), "mu": str(mu),
            "I_lower": str(i_low), "posterior_second_moment_lower": str(posterior_low),
            "Phi_a": str(phi), "E_minus": str(e_minus), "E_plus": str(e_plus),
            "risk_gain_lower": record(risk_gain), "risk_gain_exceeds": "3/100000",
            "v0": str(v0), "v_min": str(v_min), "total_reserve": str(reserve),
            "lambda_interval": [str(lambda_low), str(lambda_high)],
            "lambda_required": record(lambda_required),
            "utility_bracket_lower": record(utility_bracket),
            "uniform_utility_gain_lower": record(utility_gain),
            "utility_gain_exceeds": "8/10000000",
        },
        "limits": [
            "The written proof, not this script, establishes the all-state inequalities.",
            "This is not numerical verification of an infinite-dimensional optimum.",
            "No posterior expectation is numerically approximated.",
            "No market data or fitted parameters are used.",
            "Decimals are informational; all comparisons use exact arithmetic.",
        ],
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
