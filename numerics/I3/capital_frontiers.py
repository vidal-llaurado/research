#!/usr/bin/env python3
"""Exact obstacle, projection and finite-capital identities for I3."""
from __future__ import annotations

import json
import platform
import sys
from typing import Any

import sympy as s

if s.__version__ != "1.14.0":
    raise RuntimeError(f"Expected SymPy 1.14.0, found {s.__version__}")

u, v, delta, z, a, x = s.symbols("u v delta z a x", real=True)
R = s.Rational
verified: list[str] = []
certificates: dict[str, str] = {}


def check(name: str, expression: Any) -> None:
    """Assert a symbolic expression is identically zero."""
    reduced = s.factor(s.cancel(expression))
    if reduced != 0:
        raise AssertionError(f"{name}: {reduced}")
    verified.append(name)


def positive(name: str, value: Any) -> None:
    value = s.factor(value)
    if value.is_positive is not True:
        raise AssertionError(f"{name} is not certified positive: {value}")
    certificates[name] = str(value)


def integrate_polynomial(expr: Any, bounds: tuple[Any, Any, Any]) -> Any:
    """Integrate a polynomial with exact rational-function coefficients."""
    variable, lower, upper = bounds
    poly = s.Poly(s.cancel(expr), variable)
    primitive = poly.integrate()
    return s.factor(primitive.eval(upper) - primitive.eval(lower))


def moment(poly: Any, weight: Any = 1) -> Any:
    return integrate_polynomial(poly * weight / 2, (u, -1, 1))


# I. The retained law and conditional basket values.
psi = u * (v**2 - R(1, 3)) - (u**2 - R(1, 3)) * v
p = 1 - delta * u * v + z * psi
check("density_uniform_first_marginal", integrate_polynomial(p / 2, (v, -1, 1)) - 1)
check("density_uniform_second_marginal", integrate_polynomial(p / 2, (u, -1, 1)) - 1)
check("density_swap_reverses_sign", p.xreplace({u: v, v: u}) - p.subs(z, -z))
check("psi_L2_Q", integrate_polynomial(integrate_polynomial(psi**2 / 4, (v, -1, 1)), (u, -1, 1)) - R(8, 135))
bz = integrate_polynomial(s.expand((-u-v) * p / 2), (v, -1, -u))
bz_claim = (u-1)**2 * (6*delta*u**2 + 12*delta*u + 9*z*u**3 + 18*z*u**2 + z*u - 4*z + 18) / 72
check("conditional_basket_polynomial", bz - bz_claim)
EB = moment(bz)
check("basket_mean", EB - (R(1, 3) - delta/15))
EB2 = moment(integrate_polynomial(s.expand((-u-v)**2 * p / 2), (v, -1, -u)))
VB = EB2 - EB**2
mu = delta / 15

# II. Exact obstacle solution and its saturation.
g = x/2 + (delta-1)*x**2/4 - delta*x**4/12
g_u = g.subs(x, u)
h = R(1, 6) + delta/15
q0 = (20 + 7*delta)/360
check("conditional_initial_surplus", integrate_polynomial(v * (1+delta*u*v)/2, (v, 0, u)) + integrate_polynomial(u*(1+delta*u*v)/2, (v, u, 1)) - g_u)
check("initial_surplus_mean", integrate_polynomial(g, (x, 0, 1)) - h)
r = g.subs(x, a) - g
eps = 2*integrate_polynomial(r, (x, 0, a))
eps_claim = a**2/2 + (delta-1)*a**3/3 - 2*delta*a**5/15
check("capital_parameter", eps - eps_claim)
check("capital_parameter_derivative", s.diff(eps, a) - 2*a*s.diff(g, x).subs(x, a))
q_a = q0 - 2*h*eps + 2*integrate_polynomial(g.subs(x, a)**2-g**2, (x, 0, a)) - eps**2/2
vstar = (1260 + 135*delta - 289*delta**2)/28350
check("saturated_variance", q_a.subs(a, 1) - mu**2 - vstar)
check("local_cubic_coefficient", s.expand(q_a-q0+2*h*eps).coeff(a, 3) - R(1, 3))

# III. Signed finite-rank projection: verify normal equations independently.
Dz = 135 + 45*delta - 4*z**2
beta = z**2*(19-5*delta)/(7*Dz)
gamma = (7965*delta + 11655 - 548*z**2)/(840*Dz)
f0 = R(1, 4) + delta/6 - u/2 + (1-delta)*u**2/4 + delta*u**4/12
fz = f0 + beta*(u**2-1) + z*((u**5-1)/8 - 13*(u**3-1)/36 + gamma*(u-1))
fm = fz.subs(z, -z)
Fz = fz-moment(fz)
Fm = fm-moment(fm)
A1, A2 = moment(Fz, u), moment(Fz, u**2-R(1, 3))
D1, D2 = moment(Fm, u), moment(Fm, u**2-R(1, 3))
check("projection_moment_A1", A1 - (30*delta*z-315*delta+28*z**2-114*z-945)/(42*Dz))
check("projection_moment_D1", D1 + (30*delta*z+315*delta-28*z**2-114*z+945)/(42*Dz))
check("projection_moment_A2", A2 + (75*delta**2+120*delta-16*z**2-315)/(105*Dz))
check("projection_moment_D2", D2-A2)
check("first_normal_equation", Fz-delta*u*D1+z*(u*D2-(u**2-R(1, 3))*D1) - (bz-EB))
check("second_normal_equation", Fm-delta*u*A1-z*(u*A2-(u**2-R(1, 3))*A1) - (bz.subs(z, -z)-EB))
Lambda = z**2*(R(838, 363825) + 2*(19-5*delta)**2/(2205*Dz))
variance_projected = VB-moment(Fz, bz)-moment(Fm, bz.subs(z, -z))
check("exact_projected_variance", variance_projected - (vstar-Lambda))
check("gain_numerator_decomposition", 4125*delta**2-12495*delta+116130-1676*z**2 - (419*Dz+165*(19-5*delta)**2))
check("normalized_endpoint", fz.subs(u, 1))
central = fz-fm.subs(u, -u)+u
check("central_reflection_constant", s.diff(central, u))
check("central_reflection_constants_cancel", central+central.subs(z, -z))
Cstar = R(1, 3) + delta/5
check("raw_projection_capital", moment(fz)+moment(fm)-R(1, 3) - (Cstar-4*beta/3))
check("strong_convexity_polynomial", s.diff(fz, u, 2) - ((1-delta)/2+delta*u**2+2*beta+z*(R(5, 2)*u**3-R(13, 6)*u)))
check("endpoint_derivative", s.diff(fz, u).subs(u, 1) - (-delta/6+2*beta+z*(gamma-R(11, 24))))

# IV. Solvency-preserving signed deformation and Bernstein positivity.
R2 = integrate_polynomial((x**2-R(1, 3))*r, (x, 0, a))
# Independently integrate psi times H0 on the two opposite-sign subtriangles.
K0_integral = integrate_polynomial((-v)*psi/2, (v, -u, 0)) + integrate_polynomial(u*psi/2, (v, -1, -u))
K0 = -u*(9*u**4-26*u**2+6)/72
check("signed_initial_cross_polynomial", K0_integral-K0)
Kx = K0.subs(u, x)
ell = 2*(integrate_polynomial((x/(2*a))*(Kx+x*R2), (x, 0, a)) + integrate_polynomial(R(1, 2)*(Kx+x*R2), (x, a, 1)))
ell_claim = (10*delta*a**9-65*delta*a**7+21*a**7-15*a**6+140*delta*a**5-98*a**5+63*a**4-105*delta*a**3+105*a**3-105*a**2+105)/3780
check("signed_deformation_cross_coefficient", ell-ell_claim)
Ef2 = integrate_polynomial((x/(2*a))**2, (x, 0, a)) + integrate_polynomial(R(1, 4), (x, a, 1))
EUf = integrate_polynomial(x*x/(2*a), (x, 0, a)) + integrate_polynomial(x/2, (x, a, 1))
check("clipped_direction_second_moment", Ef2-(R(1, 4)-a/6))
check("clipped_direction_first_cross_moment", EUf-(R(1, 4)-a**2/12))
da = R(1, 2)-a/3+2*delta*(R(1, 4)-a**2/12)**2
check("signed_direction_quadratic_coefficient", 2*Ef2+2*delta*EUf**2-da)
bernstein_claim = [R(1,36), R(1,36), R(35,1296), (78-delta)/3024,
                   (93-5*delta)/3780, (1621-205*delta)/68040,
                   (1867-385*delta)/79380, 2*(99-25*delta)/8505,
                   2*(19-5*delta)/1701, (19-5*delta)/945]
poly = s.Poly(ell_claim, a)
for i, target in enumerate(bernstein_claim):
    actual = sum(poly.nth(k)*s.binomial(i,k)/s.binomial(9,k) for k in range(i+1))
    check(f"Bernstein_coefficient_{i}", actual-target)
    # Each listed coefficient is affine and nonincreasing in delta.
    if s.diff(target, delta).is_nonpositive is not True:
        raise AssertionError(f"Unexpected coefficient monotonicity: {target}")
    positive(f"Bernstein_{i}_uniform_lower_bound", target.subs(delta, R(1,16)))

# V. Rational analytic bounds; no parameter grid.
positive("density_lower_bound", 1-R(1,16)-R(1,4)*R(4,3))
positive("beta_bound_slack", R(1,750)-R(1,16)*19/(7*R(539,4)))
positive("gamma_lower_numerator_min", 2205-R(268,16))
positive("gamma_upper_numerator_slack", 2520-R(3240,16))
positive("cubic_extremum_squared_slack", 1-R(13,9)**2*R(13,45))
alpha = R(3,32)+R(1,375)
reserve_upper = R(83,240)+16*alpha**2/7
check("reserve_upper_rational", reserve_upper-R(23126149,63000000))
positive("uniform_reserve_slack", R(3,8)-reserve_upper)
positive("positive_z_endpoint_slope_slack", R(1,3)-2*R(1,4)*19/(7*R(539,4)))
positive("small_z_endpoint_slope_slack_per_delta", R(1,6)-R(3,32)-R(38,15120)*R(1,16))
K_upper = R(838,363825)+2*19**2/(2205*R(539,4))
positive("gain_coefficient_upper_bound_slack", R(1,200)-K_upper)
positive("variance_uniform_lower_bound_slack", R(2,45)-R(1,3200)-R(1,24))
positive("vstar_increasing_derivative_numerator", 135-578*R(1,16))

# VI. Index bound and one finite statistical/economic certificate.
t = s.symbols("t", nonnegative=True)
mt = (t**2+2*t-2)/6
check("index_conditional_covariation_mean", 2*integrate_polynomial(mt*(2-t)/4, (t,0,2)))
check("index_conditional_covariation_square", 2*integrate_polynomial(mt**2*(2-t)/4, (t,0,2))-R(11,135))
check("index_kernel_bound", R(11,135)/(1-R(1,16))-R(176,2025))
vmax = vstar.subs(delta, R(1,16))
check("maximum_saturated_variance", vmax-R(324431,7257600))
index_constant = (1/(225*vmax)-R(176,2025))/4
check("index_gap_coefficient", index_constant-R(2054636,656972775))
positive("index_gap_per_delta_slack", index_constant-R(1,400))

D0, eta, n, lambda_max = R(1,16), R(1,4), 256, R(1,8)
Ilower = R(8,135)/(1+D0)
posterior_lower = n*eta**2*Ilower/(1+(n-1)*eta**2*Ilower)
check("finite_Fisher_lower_bound", Ilower-R(128,2295))
check("finite_posterior_second_moment_lower_bound", posterior_lower-R(2048,4335))
kdelta = (R(838,363825)+2*(19-5*delta)**2/(2205*(135+45*delta))).subs(delta,D0)
risk_lower = s.factor(kdelta*eta**2*posterior_lower)
economic_lower = s.factor((D0/15)**2*risk_lower/(2*lambda_max*vmax**2))
positive("finite_risk_gain_slack_above_1_over_8000", risk_lower-R(1,8000))
positive("finite_pooled_gain_slack_above_1_over_250000", economic_lower-R(1,250000))
positive("finite_index_gap_slack_above_1_over_6400", D0*index_constant-R(1,6400))
positive("finite_preference_feasibility_slack", R(7,64)-24*(D0/15))

report = {
    "status": "PASS",
    "scope": "Exact symbolic identities and rational certificates; not formal proof or market validation.",
    "python": platform.python_version(),
    "sympy": s.__version__,
    "identities_checked": len(verified),
    "identities": verified,
    "strict_positive_rational_certificates": certificates,
    "finite_configuration": {
        "delta": str(D0), "eta": str(eta), "n": n,
        "per_unit_and_total_reserve": "3/8", "lambda_interval": ["7/64", "1/8"],
        "posterior_second_moment_lower_bound": str(posterior_lower),
        "risk_gain_lower_bound": str(risk_lower),
        "pooled_economic_increment_lower_bound": str(economic_lower),
        "complete_index_gap_lower_bound": str(D0*index_constant),
    },
}
json.dump(report, sys.stdout, indent=2, sort_keys=True)
sys.stdout.write("\n")
