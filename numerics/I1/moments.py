#!/usr/bin/env python3
"""Gaussian moment, leverage and carry identities for I1.

The frozen-Ito check integrates a *finite joint Gaussian vector* analytically,
independently of the continuous cubic/fourth-order integral derivation.
"""
from __future__ import annotations

import itertools
import json
import platform
from typing import Any

import numpy as np
import scipy
from numpy.polynomial.hermite_e import hermegauss
from numpy.polynomial.legendre import leggauss
from scipy.linalg import expm


M = np.array([[-1.2, 0.25], [0.15, -0.85]], dtype=float)
SIGMA = 0.04 * np.array([[1.0, 0.15], [0.15, 1.0]])
OMEGA = -(M @ SIGMA + SIGMA @ M.T)
A = np.linalg.cholesky(OMEGA)
L = np.array([[0.1, -0.15], [0.06, 0.04]])
Q = np.array([[1.0, 0.2], [0.2, 1.0]])
H = A @ L
MU = np.array([-0.2, 0.1])
LAM = np.exp(2 * MU + 2 * np.diag(SIGMA))
HORIZON = 0.3
DELTA = 0.7
EVALS, EVECS = np.linalg.eig(M)
EVECS_INV = np.linalg.inv(EVECS)


def exp_m(times: np.ndarray) -> np.ndarray:
    """Batched exp(M*t), for this fixed real-diagonalizable check matrix."""
    values = np.exp(np.asarray(times)[..., None] * EVALS)
    return np.einsum("ij,...j,jk->...ik", EVECS, values, EVECS_INV)


def exact_integrals(order: int, lag: int = 1, i: int = 0, j: int = 1) -> dict[str, float]:
    nodes, weights = leggauss(order)
    x, w = (nodes + 1) / 2, weights / 2
    t, u = HORIZON * x[:, None], HORIZON * x[None, :]
    tau = lag * DELTA + t - u
    em = exp_m(tau)
    cov, response = em @ SIGMA, em @ H
    weight2 = w[:, None] * w[None, :]
    cubic_norm = np.sum(weight2 * response[..., i, j]
                        * np.exp(2 * cov[..., i, j] - SIGMA[j, j] / 2))
    base = np.sum(weight2 * np.expm1(4 * cov[..., i, j]))
    # v in [0,u], hence the transformed triple integral has an extra factor u.
    z = lag * DELTA + HORIZON * x[:, None, None]
    u3 = HORIZON * x[None, :, None]
    v3 = u3 * x[None, None, :]
    em_zu, em_uv, em_zv = exp_m(z - u3), exp_m(u3 - v3), exp_m(z - v3)
    c_zu, c_uv, c_zv = em_zu @ SIGMA, em_uv @ SIGMA, em_zv @ SIGMA
    k_zu, k_uv, k_zv = em_zu @ H, em_uv @ H, em_zv @ H
    weight3 = w[:, None, None] * w[None, :, None] * w[None, None, :]
    integrand = (k_zu[..., i, j] * (k_uv[..., j, j] + 2 * k_zv[..., i, j])
                 * np.exp(-SIGMA[j, j] + c_uv[..., j, j]
                          + 2 * c_zu[..., i, j] + 2 * c_zv[..., i, j]))
    correction = 4 * np.sum(weight3 * u3 * integrand)
    cubic = 2 * HORIZON**2 * LAM[i] * np.sqrt(LAM[j]) * cubic_norm
    return {"T": float(cubic), "G0": float(base), "J": float(correction),
            "G": float(base + correction)}


def frozen_covariances(cells: int) -> tuple[np.ndarray, ...]:
    """Joint law of left-node states and return-driver cell increments.

    Early block uses asset 2; later block uses asset 1. Covariances between
    Brownian increments and future OU states are integrated exactly.
    """
    step = HORIZON / cells
    times = np.concatenate((np.arange(cells) * step,
                            DELTA + np.arange(cells) * step))
    assets = np.concatenate((np.ones(cells, dtype=int), np.zeros(cells, dtype=int)))
    count = 2 * cells
    cov_y = np.zeros((count, count))
    cov_zy = np.zeros((count, count))
    for p in range(count):
        for q in range(count):
            if times[p] >= times[q]:
                matrix = expm(M * (times[p] - times[q])) @ SIGMA
                cov_y[p, q] = matrix[assets[p], assets[q]]
            else:
                matrix = expm(M * (times[q] - times[p])) @ SIGMA
                cov_y[p, q] = matrix[assets[q], assets[p]]
            left, right, state_t = times[p], times[p] + step, times[q]
            if state_t > left:
                cap = min(right, state_t)
                integral = np.linalg.solve(
                    M, (expm(M * (state_t - left))
                        - expm(M * (state_t - cap))) @ H)
                cov_zy[p, q] = integral[assets[q], assets[p]]
    cov_z = step * np.eye(count)
    joint = np.block([[cov_y, cov_zy.T], [cov_zy, cov_z]])
    if np.linalg.eigvalsh(joint).min() < -1e-11:
        raise AssertionError("Invalid joint Gaussian covariance in frozen-Ito check")
    return MU[assets], cov_y, cov_zy, cov_z


def gaussian_exp_moment(indices: np.ndarray, mean_y: np.ndarray,
                        cov_y: np.ndarray, cov_zy: np.ndarray,
                        cov_z: np.ndarray) -> np.ndarray:
    """E[exp(sum Y_i) product Z_i] via Gaussian exponential tilting + Wick."""
    p = indices.shape[1]
    iy = indices[:, :, None]
    jy = indices[:, None, :]
    prefactor = np.exp(mean_y[indices].sum(axis=1)
                       + 0.5 * cov_y[iy, jy].sum(axis=(1, 2)))
    shifted = cov_zy[iy, jy].sum(axis=2)
    cc = cov_z[iy, jy]
    if p == 3:
        val = (np.prod(shifted, axis=1) + cc[:, 0, 1] * shifted[:, 2]
               + cc[:, 0, 2] * shifted[:, 1] + cc[:, 1, 2] * shifted[:, 0])
    elif p == 4:
        val = np.prod(shifted, axis=1)
        for a, b in itertools.combinations(range(4), 2):
            c, d = [k for k in range(4) if k not in (a, b)]
            val += cc[:, a, b] * shifted[:, c] * shifted[:, d]
        val += (cc[:, 0, 1] * cc[:, 2, 3] + cc[:, 0, 2] * cc[:, 1, 3]
                + cc[:, 0, 3] * cc[:, 1, 2])
    else:
        raise ValueError("Only degree 3 or 4 is needed")
    return prefactor * val


def frozen_moments(cells: int) -> dict[str, float]:
    covs = frozen_covariances(cells)
    early = np.arange(cells)
    future = cells + early
    totals: dict[int, float] = {}
    for degree in (3, 4):
        axes = [future, future, early] + ([early] if degree == 4 else [])
        grid = np.stack(np.meshgrid(*axes, indexing="ij"), axis=-1).reshape(-1, degree)
        total = 0.0
        for start in range(0, len(grid), 8192):
            total += gaussian_exp_moment(grid[start:start + 8192], *covs).sum()
        totals[degree] = float(total)
    norm = HORIZON**2 * LAM[0] * LAM[1]
    return {"T": totals[3], "G": (totals[4] - norm) / norm}


def hermite(x: np.ndarray) -> tuple[np.ndarray, ...]:
    return x, x*x - 1, x*x*x - 3*x, x**4 - 6*x*x + 3


def check_hermite_norm() -> dict[str, float]:
    x, w = hermegauss(12)
    w /= np.sqrt(2 * np.pi)
    z1, z2 = x[:, None], x[None, :]
    h1, h2 = hermite(z1), hermite(z2)
    d1, d2 = 0.7, 1.3
    mm = np.array([0.12, -0.09]); md = np.array([0.07, 0.05]); dd = np.array([0.03, -0.04])
    cross = [0.11, -0.08, 0.06, 0.09]
    poly = (mm[0]*h1[1]/d1 + md[0]*h1[2]/d1**1.5 + dd[0]*h1[3]/(4*d1*d1)
            + mm[1]*h2[1]/d2 + md[1]*h2[2]/d2**1.5 + dd[1]*h2[3]/(4*d2*d2))
    m1, m2 = h1[0]/np.sqrt(d1), h2[0]/np.sqrt(d2)
    s1, s2 = h1[1]/(2*d1), h2[1]/(2*d2)
    poly = poly + 2*(cross[0]*m1*m2 + cross[1]*m1*s2
                     + cross[2]*s1*m2 + cross[3]*s1*s2)
    computed = np.sum(w[:, None]*w[None, :]*poly**2)
    predicted = (2*mm[0]**2/d1**2 + 6*md[0]**2/d1**3 + 1.5*dd[0]**2/d1**4
                 + 2*mm[1]**2/d2**2 + 6*md[1]**2/d2**3 + 1.5*dd[1]**2/d2**4
                 + 4*(cross[0]**2/(d1*d2) + cross[1]**2/(2*d1*d2*d2)
                      + cross[2]**2/(2*d1*d1*d2) + cross[3]**2/(4*d1*d1*d2*d2)))
    return {"quadrature": float(computed), "formula_59": float(predicted),
            "absolute_error": float(abs(computed - predicted))}


def check_random_mean_price_identity() -> dict[str, float]:
    """Finite two-state-node, one-emission identity including H2, H3, H4.

    The revealed Brownian increments are held fixed. Compare covariance
    differentiation of the mixture density with a central finite difference.
    """
    x, w = hermegauss(40); w /= np.sqrt(2*np.pi)
    standard = np.stack(np.meshgrid(x, x, indexing="ij"), axis=-1).reshape(-1, 2)
    weights = (w[:, None]*w[None, :]).ravel()
    a, v, gap = 0.9, 0.045, 0.12
    ell = 0.35; residual = 1-ell**2
    brownian = np.array([0.11, -0.08]); widths = np.array([0.12, 0.18])
    datum, carry_mean = 0.21, 0.015

    def density_and_score(parameter: float) -> tuple[float, float]:
        corr = np.exp(-parameter*gap)
        cov = v*np.array([[1.0, corr], [corr, 1.0]])
        y = -0.1 + standard @ np.linalg.cholesky(cov).T
        ey = np.exp(y)
        means_u = ell*ey*brownian
        vars_u = 2*residual*ey**2*widths
        mean = carry_mean + means_u.sum(axis=1)
        variance = residual*(ey**2*widths).sum(axis=1)
        z = (datum-mean)/np.sqrt(variance)
        _, h2, h3, h4 = hermite(z)
        kernel = np.exp(-z*z/2)/np.sqrt(2*np.pi*variance)
        dr = -gap*corr
        cmm = 2*dr*means_u[:, 0]*means_u[:, 1]
        cmd = dr*(means_u[:, 0]*vars_u[:, 1] + means_u[:, 1]*vars_u[:, 0])
        cdd = 2*dr*vars_u[:, 0]*vars_u[:, 1]
        zscore = cmm*h2/variance + cmd*h3/variance**1.5 + cdd*h4/(4*variance**2)
        return float(weights@kernel), float((v/2)*weights@(kernel*zscore))

    step = 1e-5
    finite_difference = (density_and_score(a+step)[0]-density_and_score(a-step)[0])/(2*step)
    score_formula = density_and_score(a)[1]
    return {"central_difference": finite_difference, "formula_58": score_formula,
            "absolute_error": abs(finite_difference-score_formula)}


def main() -> None:
    low, high = exact_integrals(12), exact_integrals(24)
    quadrature_error = max(abs(low[key]-high[key]) for key in high)
    frozen = []
    for cells in (4, 8, 16, 32):
        result = frozen_moments(cells)
        result.update({"cells_per_block": cells,
                       "T_absolute_error": abs(result["T"]-high["T"]),
                       "G_absolute_error": abs(result["G"]-high["G"])})
        frozen.append(result)
    # Exact deterministic raw-carry correction from (23).
    b = np.array([0.05, -0.04]); noise = np.array([0.015, 0.02])
    mean = b*HORIZON
    qraw = mean**2 + HORIZON*LAM + 2*noise
    raw_t = qraw[0]*mean[1] + high["T"]
    raw_k = qraw[0]*qraw[1] + 2*mean[1]*high["T"] + HORIZON**2*LAM.prod()*high["G"]
    centered_t = raw_t-qraw[0]*mean[1]
    corrected_g = (raw_k-qraw[0]*qraw[1]-2*mean[1]*centered_t)/(HORIZON**2*LAM.prod())
    uncorrected_g = (raw_k-qraw[0]*qraw[1])/(HORIZON**2*LAM.prod())
    # Nuisance-independent two-lag ratio, with two different leverage amplitudes.
    a1 = 0.93
    ratios = []
    for ell, v1, v2, lam1, lam2 in ((-0.27, 0.03, 0.05, 0.8, 1.2),
                                   (0.08, 0.055, 0.025, 1.3, 0.7)):
        f = 2*(np.cosh(a1*HORIZON)-1)/(a1*a1*HORIZON*HORIZON)
        amp = 2*HORIZON**2*lam1*np.sqrt(lam2)*np.exp(-v2/2)*np.sqrt(2*a1*v1)*ell*f
        first, second = amp*np.exp(-a1*DELTA), amp*np.exp(-2*a1*DELTA)
        ratios.append({"ell": ell, "T1": float(first), "T2": float(second),
                       "ratio": float(second/first), "target": float(np.exp(-a1*DELTA))})
    hermite_result = check_hermite_norm()
    price_result = check_random_mean_price_identity()
    checks = {
        "residual_covariance_positive": bool(np.linalg.eigvalsh(Q-L.T@L).min() > 0),
        "quadrature_agrees": quadrature_error < 1e-12,
        "frozen_cubic_converges": all(frozen[k+1]["T_absolute_error"] < frozen[k]["T_absolute_error"] for k in range(3)),
        "frozen_fourth_converges": all(frozen[k+1]["G_absolute_error"] < frozen[k]["G_absolute_error"] for k in range(3)),
        "carry_correction_agrees": abs(corrected_g-high["G"]) < 1e-12,
        "uncorrected_carry_is_nonzero": abs(uncorrected_g-high["G"]) > 1e-6,
        "two_lag_ratio_agrees": all(abs(row["ratio"]-row["target"]) < 1e-13 for row in ratios),
        "hermite_norm_agrees": hermite_result["absolute_error"] < 1e-12,
        "random_mean_price_identity_agrees": price_result["absolute_error"] < 1e-9,
    }
    checks = {key: bool(value) for key, value in checks.items()}
    output: dict[str, Any] = {
        "description": "Deterministic identity checks; not a statistical experiment or proof of minimax rates.",
        "versions": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
        "inputs": {"M": M.tolist(), "Sigma": SIGMA.tolist(), "A": A.tolist(),
                   "L": L.tolist(), "Q": Q.tolist(), "mu": MU.tolist(),
                   "h": HORIZON, "Delta": DELTA},
        "continuous_integrals_order_24": high,
        "order_12_vs_24_max_absolute_difference": quadrature_error,
        "independent_frozen_Ito_Gaussian_moments": frozen,
        "carry": {"corrected_G": float(corrected_g), "uncorrected_G": float(uncorrected_g),
                  "target_G": high["G"]},
        "cross_leverage_two_lag_ratio": ratios,
        "hermite_score_squared_norm": hermite_result,
        "random_mean_covariance_differentiation": price_result,
        "checks": checks,
        "all_passed": all(checks.values()),
    }
    print(json.dumps(output, indent=2, sort_keys=True))
    if not output["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
