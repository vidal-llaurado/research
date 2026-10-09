"""Dynamic excitation, lag identification and Gaussian score identities for I1."""
from __future__ import annotations

import json
import math
import platform
import sys
from typing import Any

import numpy as np
import scipy
from numpy.polynomial.hermite import hermgauss
from numpy.polynomial.legendre import leggauss
from scipy.linalg import cholesky, expm, logm, solve_continuous_lyapunov

M0 = np.array([[-2.0, 0.5], [0.5, -1.0]])
V0 = np.eye(2)
L0 = np.array([[0.0, 0.6], [0.0, 0.0]])
DELTA, BLOCK_H, KAPPA = 1.0, 0.4, 0.2


def norm(a: np.ndarray) -> float:
    return float(np.linalg.norm(a))


def loading(m: np.ndarray, v: np.ndarray = V0) -> np.ndarray:
    return cholesky(-(m @ v + v @ m.T), lower=True)


def f1(m: np.ndarray) -> np.ndarray:
    eye = np.eye(2)
    ap = np.linalg.solve(m, expm(m * BLOCK_H) - eye) / BLOCK_H
    am = np.linalg.solve(-m, expm(-m * BLOCK_H) - eye) / BLOCK_H
    return ap @ expm(m * DELTA) @ am


def stationary(m: np.ndarray, diffusion_cov: np.ndarray) -> np.ndarray:
    return solve_continuous_lyapunov(m, -diffusion_cov)


def covariance_parts(m: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    a = loading(m)
    tau2 = 1.0 - KAPPA / 2.0
    common = L0 @ L0.T / tau2
    return stationary(m, a @ common @ a.T), stationary(m, a @ (np.eye(2) - common) @ a.T)


def result(name: str, passed: bool, **details: Any) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), **details}


def check_excitation() -> dict[str, Any]:
    a1, a2, gamma = 2.0, 1.0, 0.5
    a = loading(M0)
    h0 = a[:, 0]
    calculated = float(np.linalg.det(np.column_stack((h0, M0 @ h0))))
    formula = 2 * gamma * (a1 * a2 - gamma**2) / a1
    h = a @ L0
    reach = np.column_stack((h, expm(M0) @ h))
    ratio = float(np.linalg.svd(reach, compute_uv=False)[-1]) / norm(h)
    diagonal_m = np.diag([-2.0, -1.0])
    diagonal_h = loading(diagonal_m) @ L0
    diagonal_rank = int(np.linalg.matrix_rank(np.column_stack((diagonal_h, expm(diagonal_m) @ diagonal_h))))
    return result("rank_one_dynamic_excitation", abs(calculated - formula) < 1e-12 and ratio > 0 and diagonal_rank == 1,
                  determinant=calculated, symbolic_value=formula, determinant_tolerance=1e-12,
                  instantaneous_rank=int(np.linalg.matrix_rank(h)), dynamic_rank=int(np.linalg.matrix_rank(reach)),
                  normalized_smallest_singular_value=ratio, diagonal_control_dynamic_rank=diagonal_rank)


def check_factorization() -> dict[str, Any]:
    tau2, r0 = 1 - KAPPA / 2, KAPPA / 2
    gamma = np.eye(2) - L0 @ L0.T / tau2
    # Driver columns: W0, B0, W1. Row order: B then U.
    g = np.block([[L0 / math.sqrt(tau2), cholesky(gamma, lower=True), np.zeros((2, 2))],
                  [math.sqrt(tau2) * np.eye(2), np.zeros((2, 2)), math.sqrt(r0) * np.eye(2)]])
    target = np.block([[np.eye(2), L0], [L0.T, np.eye(2)]])
    brownian_error = norm(g @ g.T - target)
    sc, sr = covariance_parts(M0)
    stationary_error = norm(sc + sr - V0)
    return result("common_driver_factorization", brownian_error < 1e-12 and stationary_error < 1e-12 and np.linalg.eigvalsh(gamma)[0] > 0,
                  brownian_covariance_error=brownian_error, stationary_covariance_error=stationary_error,
                  residual_state_minimum_eigenvalue=float(np.linalg.eigvalsh(gamma)[0]),
                  residual_return_variance=r0, tolerance=1e-12)


def check_conditional_derivative() -> dict[str, Any]:
    direction = np.array([[0.0, 1.0], [0.0, 0.0]])
    derivatives = []
    for step in (1e-4, 5e-5):
        cp, rp = covariance_parts(M0 + step * direction)
        cm, rm = covariance_parts(M0 - step * direction)
        derivatives.append(((cp - cm) / (2 * step), (rp - rm) / (2 * step)))
    dc, dr = derivatives[-1]
    residual_diagonal = norm(np.diag(dr))
    cancellation = norm(dc + dr)
    convergence = norm(dr - derivatives[0][1])
    return result("conditional_covariance_diagonal_derivative", cancellation < 1e-6 and convergence < 1e-6 and residual_diagonal > 1e-5,
                  derivative_residual=dr.tolist(), derivative_common=dc.tolist(),
                  residual_diagonal_norm=residual_diagonal, derivative_cancellation_error=cancellation,
                  step_halving_difference=convergence, cancellation_tolerance=1e-6, nonzero_threshold=1e-5)


def exact_cubic(m: np.ndarray, sigma: np.ndarray, hload: np.ndarray, lag: int, order: int) -> np.ndarray:
    x, w = leggauss(order)
    nodes, weights = BLOCK_H * (x + 1) / 2, w / 2
    times = lag * DELTA + nodes[:, None] - nodes[None, :]
    matrix_exp = expm(times[:, :, None, None] * m[None, None, :, :])
    c = matrix_exp @ sigma
    k = matrix_exp @ hload
    integrand = k * np.exp(2 * c - np.diag(sigma)[None, None, None, :] / 2)
    return np.einsum("a,b,abij->ij", weights, weights, integrand)


def check_cubic() -> dict[str, Any]:
    z, a, first = expm(M0), loading(M0), f1(M0)
    checks = []
    for s in (1e-2, 1e-3, 1e-4):
        h = math.sqrt(s) * a @ L0
        row = {"s": s, "lags": []}
        leading = []
        for lag in (1, 2, 3):
            d18 = exact_cubic(M0, s * V0, h, lag, 18)
            d30 = exact_cubic(M0, s * V0, h, lag, 30)
            lead = np.linalg.matrix_power(z, lag - 1) @ first @ h
            leading.append(lead)
            row["lags"].append({"lag": lag, "quadrature_difference": norm(d30 - d18),
                                "remainder_over_s_H": norm(d30 - lead) / (s * norm(h))})
        x = np.column_stack(leading[:2])
        y = np.column_stack(leading[1:])
        recovered_z = y @ np.linalg.pinv(x)
        row["leading_transition_recovery_error"] = norm(recovered_z - z)
        checks.append(row)
    passed = all(d["quadrature_difference"] < 1e-11 and d["remainder_over_s_H"] < 20 for row in checks for d in row["lags"])
    passed = passed and all(row["leading_transition_recovery_error"] < 1e-12 for row in checks)
    return result("exact_cubic_and_three_lag_recovery", passed, cases=checks,
                  quadrature_tolerance=1e-11, remainder_ratio_bound=20, transition_tolerance=1e-12)


def check_two_lag_ambiguity() -> dict[str, Any]:
    z, h = expm(M0), loading(M0) @ L0
    wmatrix = f1(M0) @ h
    active = wmatrix[:, 1]
    annihilator = np.array([-active[1], active[0]]) / norm(active)
    zp = z + 0.002 * np.outer(np.array([1.0, -0.3]), annihilator)
    mp_complex = logm(zp)
    imag = float(np.max(np.abs(np.imag(mp_complex))))
    mp = np.real(mp_complex)
    hp = np.linalg.solve(f1(mp), wmatrix)
    lp = np.linalg.solve(loading(mp), hp)
    original = [np.linalg.matrix_power(z, lag) @ wmatrix for lag in range(3)]
    perturbed_w = f1(mp) @ hp
    perturbed = [np.linalg.matrix_power(zp, lag) @ perturbed_w for lag in range(3)]
    errors = [norm(x - y) for x, y in zip(original, perturbed)]
    margin = float(np.linalg.eigvalsh(np.eye(2) - lp.T @ lp)[0])
    stable = float(np.max(np.real(np.linalg.eigvals(mp)))) < 0
    passed = errors[0] < 1e-11 and errors[1] < 1e-11 and errors[2] > 1e-7 and imag < 1e-12 and margin > KAPPA and stable and norm(lp) < math.sqrt(1-KAPPA)
    return result("two_lag_leading_ambiguity", passed, lag_differences=errors,
                  imaginary_log_residual=imag, perturbed_brownian_margin=margin,
                  perturbed_leverage_norm=norm(lp), perturbed_drift=mp.tolist(),
                  equality_tolerance=1e-11, third_lag_nonzero_threshold=1e-7,
                  interpretation="Leading response only; not exact price-law equivalence.")


def gaussian_identity(order: int, alpha: float = 0.0) -> tuple[float, float, float, float]:
    """Density and three Gaussian derivative contractions for the frozen toy."""
    base_mean = np.array([-0.4, -0.35])
    mean_derivative = np.array([0.2, -0.1])
    base_covariance = np.array([[0.12, 0.05], [0.05, 0.10]])
    covariance_derivative = np.array([[0.025, -0.012], [-0.012, 0.01]])
    xx, ww = hermgauss(order)
    grid = np.stack(np.meshgrid(xx, xx, indexing="ij"), axis=-1).reshape(-1, 2) * math.sqrt(2)
    weights = np.outer(ww, ww).reshape(-1) / math.pi
    y = grid @ cholesky(base_covariance + alpha * covariance_derivative, lower=True).T + base_mean + alpha * mean_derivative
    ey = np.exp(y)
    emission_m = math.sqrt(0.8) * ey * np.array([0.17, -0.13])
    emission_d = 2 * 0.2 * ey**2 * np.array([0.2, 0.2])
    a = 0.03 + emission_m.sum(axis=1)
    d = emission_d.sum(axis=1) / 2
    z = (0.1 - a) / np.sqrt(d)
    density = np.exp(-z**2 / 2) / np.sqrt(2 * math.pi * d)
    h1, h2 = z, z**2 - 1
    h3, h4 = z**3 - 3*z, z**4 - 6*z**2 + 3
    ka = h1 / np.sqrt(d)
    kd = h2 / (2*d)
    kaa, kad, kdd = h2 / d, h3 / (2*d**1.5), h4 / (4*d**2)
    grad = ka[:, None] * emission_m + kd[:, None] * emission_d
    hessian = (kaa[:, None, None] * emission_m[:, :, None] * emission_m[:, None, :]
               + kad[:, None, None] * (emission_m[:, :, None] * emission_d[:, None, :] + emission_d[:, :, None] * emission_m[:, None, :])
               + kdd[:, None, None] * emission_d[:, :, None] * emission_d[:, None, :])
    for u in range(2):
        hessian[:, u, u] += ka * emission_m[:, u] + kd * 2 * emission_d[:, u]
    state_mean_term = grad @ mean_derivative
    covariance_term = 0.5 * np.einsum("uv,nuv->n", covariance_derivative, hessian)
    diagonal_term = 0.5 * np.einsum("u,nu->n", np.diag(covariance_derivative), np.diagonal(hessian, axis1=1, axis2=2))
    integrate = lambda f: float(np.dot(weights, density * f))
    return float(np.dot(weights, density)), integrate(state_mean_term + covariance_term), integrate(state_mean_term), integrate(diagonal_term)


def check_price_identity() -> dict[str, Any]:
    quadratures = {order: gaussian_identity(order) for order in (32, 48, 64)}
    analytic = quadratures[64][1]
    finite_differences = []
    for step in (1e-4, 5e-5):
        derivative = (gaussian_identity(64, step)[0] - gaussian_identity(64, -step)[0]) / (2*step)
        finite_differences.append({"step": step, "derivative": derivative, "absolute_error": abs(derivative - analytic)})
    agreement = max(abs(quadratures[order][1] - analytic) for order in (32, 48))
    mean_size, diagonal_size = abs(quadratures[64][2]), abs(quadratures[64][3])
    passed = all(row["absolute_error"] < 2e-7 for row in finite_differences) and agreement < 2e-7 and mean_size > 1e-5 and diagonal_size > 1e-5
    return result("finite_gaussian_price_derivative", passed, analytic_derivative=analytic,
                  finite_differences=finite_differences, derivative_quadrature_disagreement=agreement,
                  omitted_state_mean_term=quadratures[64][2], omitted_covariance_diagonal_term=quadratures[64][3],
                  comparison_tolerance=2e-7, nonzero_threshold=1e-5,
                  interpretation="Finite conditional-Gaussian identity, not a simulated full-price experiment.")


def check_hermite_overlap() -> dict[str, Any]:
    x, w = hermgauss(12)
    z, weights = x * math.sqrt(2), w / math.sqrt(math.pi)
    d, caa, cd = 0.7, 0.4, -0.3
    h2 = z**2 - 1
    combined = caa * h2/d + cd * h2/(2*d)
    direct = float(np.dot(weights, combined**2))
    exact = 2 * (caa/d + cd/(2*d))**2
    false_orthogonal = 2 * ((caa/d)**2 + (cd/(2*d))**2)
    return result("hermite_singleton_overlap", abs(direct-exact) < 1e-12 and abs(direct-false_orthogonal) > 1e-5,
                  integrated_combined_norm=direct, grouped_polynomial_norm=exact,
                  incorrect_orthogonality_norm=false_orthogonal, tolerance=1e-12)


def main() -> int:
    functions = (check_excitation, check_factorization, check_conditional_derivative, check_cubic,
                 check_two_lag_ambiguity, check_price_identity, check_hermite_overlap)
    checks = []
    for function in functions:
        try:
            checks.append(function())
        except Exception as exc:  # Preserve a failed case rather than silently aborting.
            checks.append(result(function.__name__, False, error=f"{type(exc).__name__}: {exc}"))
    report = {"environment": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
              "all_passed": all(item["passed"] for item in checks), "check_count": len(checks), "checks": checks,
              "limitations": "Deterministic supporting identities only; no analytic-proof or market-data validation."}
    print(json.dumps(report, indent=2, sort_keys=True, allow_nan=False))
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
