"""Payoff moments, index-projection bounds and exact advantage margins for I3."""
import json

import sympy as sp

R = sp.Rational
x, y, t, delta, eta, k, e = sp.symbols("x y t delta eta k e", real=True)


def equal(actual, expected, label):
    if sp.simplify(actual - expected) != 0:
        raise AssertionError((label, actual, expected))


def positive(value, label):
    if value.is_positive is not True:
        raise AssertionError((label, value))


def swapped(expr):
    return expr.xreplace({x: y, y: x})


def exact_moments():
    low = lambda z: (1 - z) / 2 + (2 - z) / 4
    high = lambda z: (2 - z) / 4
    # All six disjoint payoff regions; shared boundaries have Q measure zero.
    # The two mixed regions are also integrated after swapping both coordinates.
    regions = [
        (low(x) + low(y) - (2 - x - y), 0, 1, 0, 1, False),
        (high(x) + high(y), 1, 2, 1, 2, False),
        (low(x) + high(y) - (2 - x - y), 0, 1, 1, 2 - x, False),
        (low(x) + high(y), 0, 1, 2 - x, 2, False),
        (low(x) + high(y) - (2 - x - y), 0, 1, 1, 2 - x, True),
        (low(x) + high(y), 0, 1, 2 - x, 2, True),
    ]
    u, v = x - 1, y - 1
    skew = u * (v**2 - R(1, 3)) - (u**2 - R(1, 3)) * v
    requested = [("H", 1, 1, R(5, 12)), ("H2", 2, 1, R(7, 32)),
                 ("uvH", 1, u*v, -R(1, 15)), ("uvH2", 2, u*v, -R(43, 720)),
                 ("skewH", 1, skew, 0), ("skewH2", 2, skew, 0)]
    moments, contributions = {}, {}
    for name, power, factor, expected in requested:
        parts = []
        for H, xmin, xmax, ymin, ymax, swap in regions:
            # Transform the complete integrand, then return to the low/high
            # coordinate chart; do not double antisymmetric contributions.
            actual_H = swapped(H) if swap else H
            integrand = factor * actual_H**power
            if swap:
                integrand = swapped(integrand)
            parts.append(sp.integrate(sp.expand(integrand)/4,
                                      (y, ymin, ymax), (x, xmin, xmax)))
        moments[name] = sum(parts)
        equal(moments[name], expected, name)
        contributions[name] = list(map(str, parts))
    mean_payoff = moments["H"] - delta*moments["uvH"] + eta*moments["skewH"]
    second = moments["H2"] - delta*moments["uvH2"] + eta*moments["skewH2"]
    mu = sp.expand(mean_payoff - moments["H"])
    variance = sp.expand(second - mean_payoff**2)
    equal(mu, delta/15, "net mean")
    equal(variance, R(13, 288) + delta/240 - delta**2/225, "physical variance")
    # Verify the existing perturbation preserves both uniform marginals.
    perturbation = -delta*u*v + eta*skew
    equal(sp.integrate(perturbation, (x, 0, 2)), 0, "X marginal perturbation")
    equal(sp.integrate(perturbation, (y, 0, 2)), 0, "Y marginal perturbation")
    return {"moments": {n: str(v) for n, v in moments.items()},
            "region_order": ["LL", "UU", "mixed below", "mixed above",
                             "swapped mixed below", "swapped mixed above"],
            "region_contributions": contributions, "polynomial_integrals": 36,
            "net_mean": str(mu), "variance": str(variance)}


def index_projection():
    # t=X+Y-2; disintegrate the uniform square along both kinds of slices.
    minus = (t**2 - 2*t - 2)/6
    plus = (t**2 + 2*t - 2)/6
    slice_uv = (x - 1) * (1 + t - x)
    equal(sp.integrate(slice_uv, (x, 0, 2+t))/(2+t), minus, "negative t slice")
    equal(sp.integrate(slice_uv, (x, t, 2))/(2-t), plus, "positive t slice")
    values = []
    for power in (0, 1, 2):
        values.append(sp.integrate(minus**power*(2+t)/4, (t, -2, 0))
                      + sp.integrate(plus**power*(2-t)/4, (t, 0, 2)))
    for value, expected in zip(values, (1, 0, R(11, 135))):
        equal(value, expected, "triangular moment")
    for expr, lo, hi in ((minus, -2, 0), (plus, 0, 2)):
        assert sp.reduce_inequalities([t >= lo, t <= hi, expr > 1], t) is sp.false
        assert sp.reduce_inequalities([t >= lo, t <= hi, expr < -R(1, 3)], t) is sp.false
    rbar = R(16, 15)*values[2]
    equal(rbar, R(176, 2025), "likelihood variance bound coefficient")
    return {"m_minus": str(minus), "m_plus": str(plus),
            "normalization": str(values[0]), "EQ_m": str(values[1]),
            "EQ_m2": str(values[2]), "m_range": ["-1/3", "1"],
            "density_lower_bound_for_delta_le_1_16": "15/16",
            "chi_square_upper_bound": str(rbar*delta**2)}, rbar


def protection():
    q = (2-x)**2/4
    factors = [x*(1-x)/4, (x-1)*(2-x)/4]
    for a, lo, hi, factor in ((1-3*x/4, 0, 1, factors[0]),
                              ((2-x)/4, 1, 2, factors[1])):
        equal(a-q, factor, "interpolation domination")
        assert sp.reduce_inequalities([x >= lo, x <= hi, factor < 0], x) is sp.false
    equal((2-x)**2/4 + (2-y)**2/4 - (2-x-y),
          (x**2+y**2)/4, "quadratic hedge below basket strike")
    # On x+y>=2 the short put vanishes. Beyond x=2 the corresponding
    # interpolation and quadratic hedge both vanish; all remaining terms >=0.
    a = lambda z: sp.Max(1-z, 0)/2 + sp.Max(2-z, 0)/4
    vertices = [(i, j) for i in range(3) for j in range(3)]
    values = [a(i)+a(j)-max(2-i-j, 0) for i, j in vertices]
    equal(min(values), 0, "global H minimum")
    equal(max(values), 1, "global H maximum")
    assert all(0 <= value <= 1 for value in values)
    # Lines x=1,2; y=1,2; x+y=2 give only these finite vertices.
    # Every unbounded ray has a coordinate >=2, where H is constant in it.
    return {"interpolation_factors": list(map(str, factors)),
            "vertices": [{"x": i, "y": j, "H": str(value)}
                         for (i, j), value in zip(vertices, values)],
            "global_range": ["0", "1"], "domain": "x,y>=0",
            "unbounded_rays": "H is constant once that coordinate is >=2",
            "exact_loss_reserve": "5/12; with deterministic extra entry cost e: 5/12+e"}


def advantage(rbar):
    variance = R(13, 288)+delta/240-delta**2/225
    vbar = R(523, 11520)
    equal(vbar-variance, (R(1, 16)-delta)/240+delta**2/225, "variance upper bound")
    g = R(1, 15)-k*vbar/2-rbar/(2*k)
    equal(sp.diff(g, k, 2), -rbar/k**3, "concavity on positive k")
    endpoints = [sp.factor(g.subs(k, z)) for z in (R(5, 4), R(7, 4))]
    for actual, expected in zip(endpoints, (R(73129, 20736000), R(61249, 29030400))):
        equal(actual, expected, "endpoint gap")
        positive(actual-R(1, 500), "strict endpoint margin")
    center = sp.factor(g.subs(k, R(3, 2)))
    equal(center, R(22681, 6220800), "center gap")
    positive(center-R(1, 300), "strict center margin")
    # Charging e shifts the mean only. Equality at the declared cost ceiling
    # remains strictly favorable because the proved endpoint bounds are strict.
    shifted = delta*g-e
    equal(shifted.subs(e, delta/500), delta*(g-R(1, 500)), "interval cost ceiling")
    equal(shifted.subs({k: R(3, 2), e: delta/300}),
          delta*(center-R(1, 300)), "center cost ceiling")
    return {"delta_range": "0<delta<=1/16", "lambda": "k*delta",
            "k_interval": ["5/4", "7/4"], "vbar": str(vbar), "rbar": str(rbar),
            "g": str(g), "g_second_derivative": str(sp.diff(g, k, 2)),
            "endpoint_gaps": list(map(str, endpoints)),
            "endpoint_margins_above_1_500": [str(z-R(1, 500)) for z in endpoints],
            "center_gap": str(center), "center_margin_above_1_300": str(center-R(1, 300)),
            "strict_net_gap": "delta*g(k)-e>0 for 0<=e<=delta/500; at k=3/2 for 0<=e<=delta/300",
            "shifted_reserve": "5/12+e", "costs": "Symbolic allowance only; no actual costs calibrated"}


def main():
    moments = exact_moments()
    projection, rbar = index_projection()
    summary = {"status": "passed", "scope": "Exact supporting identities for the retained uniform-law example",
               "law": "Q uniform on [0,2]^2; dP/dQ=1-delta*u*v+eta*(u*(v^2-1/3)-(u^2-1/3)*v)",
               "law_conditions": "delta>0, eta!=0, delta+4*abs(eta)/3<1; advantage also delta<=1/16",
               "moments": moments, "index_projection": projection,
               "protection": protection(), "advantage": advantage(rbar),
               "sympy_version": sp.__version__,
               "limits": "No simulation, optimization, parameter search, market data, fitted law or empirical performance. Exact illustration, not a substitute for the theorem proof."}
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
