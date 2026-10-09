#!/usr/bin/env python3
"""Gaussian hedge weights, deterministic grids and tail-budget identities for I2."""
from __future__ import annotations

import json
import math
from typing import Callable


def simpson(fn: Callable[[float], float], left: float, right: float,
            steps: int = 8000) -> float:
    if steps <= 0 or steps % 2 or not left < right:
        raise ValueError("Simpson requires positive even steps and left < right")
    dx = (right - left) / steps
    odd = math.fsum(fn(left + j * dx) for j in range(1, steps, 2))
    even = math.fsum(fn(left + j * dx) for j in range(2, steps, 2))
    return dx * (fn(left) + fn(right) + 4 * odd + 2 * even) / 3


def gaussian_identity(a: float, variance: float, log_spot: float) -> dict:
    """Integrate the original Black weight rather than the derived ratio."""
    if a <= 0 or variance <= 0:
        raise ValueError("Variances must be positive")
    normal_const = math.sqrt(2 * math.pi)
    def g(z: float) -> float:
        ell = log_spot - a / 2 + math.sqrt(a) * z
        d_plus = ell / math.sqrt(variance) + math.sqrt(variance) / 2
        return (math.exp(math.sqrt(a) * z - a / 2 - d_plus**2 / 2)
                / (2 * normal_const * math.sqrt(variance)))
    def density(z: float) -> float:
        return math.exp(-z * z / 2) / normal_const
    first = simpson(lambda z: g(z) * density(z), -14, 14)
    second = simpson(lambda z: g(z)**2 * density(z), -14, 14)
    observed = second / first**2
    q = a / variance
    z = math.sqrt(a) * (0.5 - (log_spot - a / 2) / variance)
    exact = ((1 + q) / math.sqrt(1 + 2 * q)
             * math.exp(z*z / ((1 + q) * (1 + 2*q))))
    relative_error = abs(observed / exact - 1)
    # Independently check the differentiated Black semigroup.
    total_variance = variance + a
    d_plus = log_spot / math.sqrt(total_variance) + math.sqrt(total_variance)/2
    exact_first = math.exp(-d_plus*d_plus/2)/(2*normal_const*math.sqrt(total_variance))
    semigroup_error = abs(first / exact_first - 1)
    assert relative_error < 2e-10, (a, variance, log_spot, relative_error)
    assert semigroup_error < 2e-10, (a, variance, log_spot, semigroup_error)
    return dict(a=a, variance=variance, log_spot=log_spot,
                integrated_normalized_second_moment=observed,
                exact_normalized_second_moment=exact,
                relative_error=relative_error,
                semigroup_relative_error=semigroup_error)


def grid_check(p: float, n: int, horizon: float) -> dict:
    if p < 0 or n < 2 or horizon <= 0:
        raise ValueError("Require p >= 0, n >= 2, horizon > 0")
    q = 2*p+2
    r = q/2+0.25
    epsilon = horizon*n**(-1/(q-1))
    base = horizon**(1-r)
    spread = epsilon**(1-r)-base
    tau = [(base+j*spread/(n-1))**(-1/(r-1)) for j in range(n)]
    h = [tau[j]-tau[j+1] for j in range(n-1)]
    lam = spread/((n-1)*(r-1))
    assert all(x > 0 for x in h)
    assert math.isclose(tau[0], horizon, rel_tol=1e-13)
    assert math.isclose(tau[-1], epsilon, rel_tol=1e-13)
    assert math.isclose(math.fsum(h)+epsilon, horizon, rel_tol=1e-13)
    ratios = [x/(lam*t**r) for x,t in zip(h,tau[:-1])]
    assert max(ratios) <= 1+1e-11
    discrete = math.fsum(x*t**(-r) for x,t in zip(h,tau[:-1]))
    integral = (epsilon**(1-r)-horizon**(1-r))/(r-1)
    assert discrete <= integral*(1+1e-11)
    # Exact arithmetic digital Riemann error. Not an actual-call risk estimate.
    def digital_energy(t: float) -> float:
        return 1/(2*math.pi*math.sqrt(horizon*horizon-t*t))
    weighted_left_sum = math.fsum(
        x*digital_energy(horizon-t) for x,t in zip(h,tau[:-1]))
    weighted_left_sum += epsilon*digital_energy(horizon-epsilon)
    brownian_remainder = 0.25-weighted_left_sum
    assert 0 <= brownian_remainder <= 0.25
    return dict(p=p,n=n,T=horizon,epsilon=epsilon,
                number_of_cells=len(h)+1,
                max_early_relative_cell=max(x/t for x,t in zip(h,tau[:-1])),
                max_mean_value_bound_ratio=max(ratios),
                integral_comparison_ratio=discrete/integral,
                brownian_remainder= brownian_remainder)


def cauchy_check() -> dict:
    # Arbitrary, fixed nonuniform tail cells; tests algebra, not universal proof.
    weights=[1,2,7,3,11,4,1]
    epsilon,kappa,q=0.07,0.4,4.0
    cells=[epsilon*w/sum(weights) for w in weights]
    lhs=math.fsum(h*h/(epsilon**q+kappa*h) for h in cells)
    rhs=epsilon**2/(len(cells)*epsilon**q+kappa*epsilon)
    assert lhs >= rhs*(1-1e-13)
    return dict(epsilon=epsilon,kappa=kappa,q=q,cell_count=len(cells),
                sum=cells,lhs=lhs,rhs=rhs,ratio=lhs/rhs)


def main() -> None:
    result={
        'scope':'Deterministic identities only; no fitted rates, simulated prices, or optimal-risk estimates.',
        'gaussian_checks':[gaussian_identity(*case) for case in
                           [(0.002,0.06,0.7),(0.03,0.08,-0.4),
                            (0.2,0.3,0.8),(0.004,0.03,-0.55)]],
        'grid_checks':[grid_check(p,1024,T) for p,T in [(0,1),(0.3,1),(1,1),(2,2)]],
        'tail_budget_cauchy':cauchy_check(),
        'status':'PASS'
    }
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__=='__main__':
    main()
