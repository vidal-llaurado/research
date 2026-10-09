"""Exact uniform-marginal payoff, capital and risk-derivative identities for I3."""
import json

import sympy as sp


def main():
    u, v, delta, eta, t = sp.symbols("u v delta eta t", real=True)
    skew = u * (v**2 - sp.Rational(1, 3)) - (u**2 - sp.Rational(1, 3)) * v
    density = 1 - delta * u * v + eta * skew
    swapped = density.xreplace({u: v, v: u})
    checks = 0

    def equal(actual, expected):
        nonlocal checks
        assert sp.simplify(actual - expected) == 0, (actual, expected)
        checks += 1

    equal(sp.integrate(density, (v, -1, 1)) / 2, 1)
    equal(sp.integrate(density, (u, -1, 1)) / 2, 1)
    equal(swapped, density.subs(eta, -eta))
    covariance = sp.integrate(sp.integrate(u * v * density, (v, -1, 1)),
                              (u, -1, 1)) / 4
    equal(covariance, -delta / 9)
    for lower_u, upper_u in [(-1, 0), (0, 1)]:
        for lower_v, upper_v in [(-1, 0), (0, 1)]:
            equal(sp.integrate(sp.integrate(skew, (v, lower_v, upper_v)),
                               (u, lower_u, upper_u)), 0)

    def moment(h_power, j_power=0):
        # On u>0,v<0, H=min(u,-v), J=-1. The transposed
        # quadrant has J=+1; same-sign quadrants have H=0.
        result = 0
        for payoff, lower, upper in [(u**h_power, -1, -u),
                                      ((-v)**h_power, -u, 0)]:
            integrand = payoff * ((-1)**j_power * density + swapped)
            result += sp.integrate(sp.integrate(integrand, (v, lower, upper)),
                                   (u, 0, 1)) / 4
        return sp.factor(result)

    eh, eh2, score = moment(1), moment(2), moment(1, 1)
    equal(eh, sp.Rational(1, 6) + delta / 15)
    equal(eh2, sp.Rational(1, 12) + delta / 24)
    equal(score, -eta / 36)
    # Uniform-marginal puts have price k^2/4 for 0<=k<=2;
    # basket put at strike 2 has Q price 1/3.
    capital = sp.expand((1 + t)**2 / 4 + (1 - t)**2 / 4 - sp.Rational(1, 3))
    equal(capital, sp.Rational(1, 6) + t**2 / 2)
    equal(sp.diff(capital, t).subs(t, 0), 0)
    equal(sp.diff(capital, t, 2), 1)
    q0 = sp.factor(eh2 - eh / 3 + sp.Rational(1, 36))
    equal(q0, (7 * delta + 20) / 360)
    equal(2 * score, -eta / 18)

    print(json.dumps({
        "status": "passed", "exact_identity_checks": checks,
        "sympy_version": sp.__version__,
        "capital": str(capital), "physical_mean": str(sp.factor(eh - sp.Rational(1, 6))),
        "score": str(score), "risk_derivative": str(2 * score),
        "baseline_second_moment": str(q0), "physical_covariance": str(covariance),
        "scope": "Exact polynomial witness only; no proof of global frontier, error rate, listed-strike feasibility or empirical remuneration."
    }, indent=2))


if __name__ == "__main__":
    main()
