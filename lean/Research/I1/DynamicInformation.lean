import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# I1: three-lag reconstruction and the dynamic inverse proof

Deterministic steps in I1's main identification and adaptive-risk argument.
The matrices are the manuscript's normalized cubic responses `D₁,D₂,D₃`
and transition `Z`; the lag residual is exactly `Dₖ₊₁ - Z Dₖ`.
The reconstruction permits nonzero nonlinear residuals. A two-block right
inverse is a concrete row-excitation certificate at the first endpoint only.

The scalar perturbation theorem below proves the two-case absorption step
from separately supplied excitation, transition-action, covariance-profile,
amplitude and compact-diameter bounds. It does NOT establish those analytic
bounds for the paper's integrated stochastic-volatility moments. Gaussian/Itô
moment identities, matrix-log estimates, uniform remainder estimates, mixing,
Hellinger bounds and statistical measurability are outside this file.
-/

namespace Research.I1

open Matrix

section DynamicAlgebra

variable {ι : Type*} [Fintype ι]

/-- The exact nonlinear lag residual in I1, equation (lag-identities). -/
def lagResidual (Z D E : Matrix ι ι ℝ) : Matrix ι ι ℝ := E - Z * D

/-- Differences of exact lag identities, with excitation needed only later. -/
theorem transition_action_identity (Z Z' D D' E E' : Matrix ι ι ℝ) :
    (Z - Z') * D = (E - E') - Z' * (D - D') -
      (lagResidual Z D E - lagResidual Z' D' E') := by
  simp only [lagResidual, sub_mul, mul_sub]
  ext i j
  simp only [Matrix.sub_apply]
  ring

variable [DecidableEq ι]

/-- A row-excitation certificate recovers the transition from all three lags
and their exact residuals. It does not require either single lag to be invertible. -/
theorem three_lag_reconstruction (Z D₁ D₂ D₃ U V : Matrix ι ι ℝ)
    (hspan : D₁ * U + D₂ * V = 1) :
    Z = (D₂ - lagResidual Z D₁ D₂) * U +
      (D₃ - lagResidual Z D₂ D₃) * V := by
  simp only [lagResidual, sub_sub_cancel]
  calc
    Z = Z * (D₁ * U + D₂ * V) := by rw [hspan, mul_one]
    _ = Z * D₁ * U + Z * D₂ * V := by rw [mul_add, mul_assoc, mul_assoc]

/-- Exact error reconstruction against an arbitrary alternative. The right
inverse concerns `D₁,D₂` only; there is no excitation hypothesis on the primed
endpoint. The residual differences retain all nonlinear corrections. -/
theorem transition_error_reconstruction
    (Z Z' D₁ D₂ D₃ D₁' D₂' D₃' U V : Matrix ι ι ℝ)
    (hspan : D₁ * U + D₂ * V = 1) :
    Z - Z' =
      ((D₂ - D₂') - Z' * (D₁ - D₁') -
        (lagResidual Z D₁ D₂ - lagResidual Z' D₁' D₂')) * U +
      ((D₃ - D₃') - Z' * (D₂ - D₂') -
        (lagResidual Z D₂ D₃ - lagResidual Z' D₂' D₃')) * V := by
  rw [← transition_action_identity, ← transition_action_identity]
  calc
    Z - Z' = (Z - Z') * (D₁ * U + D₂ * V) := by rw [hspan, mul_one]
    _ = (Z - Z') * D₁ * U + (Z - Z') * D₂ * V := by
      rw [mul_add, mul_assoc, mul_assoc]

/-- Equal three-lag responses and equal nonlinear residuals identify `Z`.
Equality of residuals is an explicit condition, not inferred from prices. -/
theorem transition_identified_of_equal_responses_and_residuals
    (Z Z' D₁ D₂ D₃ U V : Matrix ι ι ℝ)
    (hspan : D₁ * U + D₂ * V = 1)
    (hres₁ : lagResidual Z D₁ D₂ = lagResidual Z' D₁ D₂)
    (hres₂ : lagResidual Z D₂ D₃ = lagResidual Z' D₂ D₃) : Z = Z' := by
  have h := transition_error_reconstruction Z Z' D₁ D₂ D₃ D₁ D₂ D₃ U V hspan
  simp only [sub_self, mul_zero, hres₁, hres₂,
    zero_mul, add_zero] at h
  exact sub_eq_zero.mp h

/-- In the leading response system, three lags identify `Z` even with a
rank-deficient first response. The alternative loading is not supplied. -/
theorem leading_three_lag_identification
    (Z Z' W W' U V : Matrix ι ι ℝ)
    (hspan : W * U + (Z * W) * V = 1)
    (h₁ : W = W') (h₂ : Z * W = Z' * W')
    (h₃ : Z * (Z * W) = Z' * (Z' * W')) : Z = Z' := by
  subst W'
  apply transition_identified_of_equal_responses_and_residuals
    Z Z' W (Z * W) (Z * (Z * W)) U V hspan
  · simp only [lagResidual, h₂]
  · unfold lagResidual
    rw [h₃, h₂]

end DynamicAlgebra

section RankOneExcitation

/-- A real two-by-two matrix, indexed by `false,true` in row/column order. -/
def matrix₂ (a b c d : ℝ) : Matrix Bool Bool ℝ :=
  fun i j => if i then (if j then d else c) else (if j then b else a)

/-- An explicit right inverse for `[W,ZW]` when `W=diag(1,0)` and `Z₂₁≠0`.
This witnesses the nonvacuous rank-one propagation mechanism in I1's discussion
after Proposition (rank-one), without assuming an invertible loading. -/
theorem rank_one_excitation_certificate (a b c d : ℝ) (hc : c ≠ 0) :
    matrix₂ 1 0 0 0 * matrix₂ 1 (-a / c) 0 0 +
      (matrix₂ a b c d * matrix₂ 1 0 0 0) * matrix₂ 0 (1 / c) 0 0 = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [matrix₂, Matrix.mul_apply, hc]
  ring

/-- Three leading lags identify all entries of a bivariate transition with
rank-one loading, from the explicit nonzero propagated-coordinate condition.
Neither the candidate loading nor candidate excitation is assumed known. -/
theorem rank_one_three_lag_identification (a b c d : ℝ) (hc : c ≠ 0)
    (Z' W' : Matrix Bool Bool ℝ)
    (h₁ : matrix₂ 1 0 0 0 = W')
    (h₂ : matrix₂ a b c d * matrix₂ 1 0 0 0 = Z' * W')
    (h₃ : matrix₂ a b c d * (matrix₂ a b c d * matrix₂ 1 0 0 0) =
      Z' * (Z' * W')) : matrix₂ a b c d = Z' :=
  leading_three_lag_identification _ _ _ _
    (matrix₂ 1 (-a / c) 0 0) (matrix₂ 0 (1 / c) 0 0)
    (rank_one_excitation_certificate a b c d hc) h₁ h₂ h₃

end RankOneExcitation

section SecondMoments

/-- I1's centered second return moment at block length `t`. -/
def centeredSecondMoment (lam ν t : ℝ) : ℝ := t * lam + 2 * ν

/-- The volatility-level inverse in I1, equation (two-lengths). -/
theorem two_lengths_recover_variance_level (lam ν h r : ℝ) (hhr : h ≠ r) :
    (centeredSecondMoment lam ν h - centeredSecondMoment lam ν r) / (h - r) = lam := by
  apply (div_eq_iff (sub_ne_zero.mpr hhr)).2
  unfold centeredSecondMoment
  ring

/-- The level-noise inverse in I1, equation (two-lengths); `ν` is a variance. -/
theorem two_lengths_recover_level_noise (lam ν h r : ℝ) (hhr : h ≠ r) :
    (h * centeredSecondMoment lam ν r - r * centeredSecondMoment lam ν h) /
      (2 * (h - r)) = ν := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hhr))).2
  unfold centeredSecondMoment
  ring

/-- Unknown volatility level and unknown level-noise variance are jointly
identified by the two observed block lengths; positivity is unnecessary. -/
theorem two_lengths_joint_identification (lam lam' ν ν' h r : ℝ)
    (hhr : h ≠ r)
    (hh : centeredSecondMoment lam ν h = centeredSecondMoment lam' ν' h)
    (hr : centeredSecondMoment lam ν r = centeredSecondMoment lam' ν' r) :
    lam = lam' ∧ ν = ν' := by
  constructor
  · rw [← two_lengths_recover_variance_level lam ν h r hhr, hh, hr]
    exact two_lengths_recover_variance_level lam' ν' h r hhr
  · rw [← two_lengths_recover_level_noise lam ν h r hhr, hh, hr]
    exact two_lengths_recover_level_noise lam' ν' h r hhr

end SecondMoments

section DynamicInverse

/-- Scalar endgame of I1's one-endpoint dynamic inverse lemma.

`a = ‖H‖`, `h = max(‖H‖,‖H'‖)`, `s = max(s,s')`, `dm = ‖M-M'‖`,
`ds = ‖Σ-Σ'‖`, and `ε` is the exact feature discrepancy. `action` represents
`‖(Z-Z')[D₁,D₂]‖`; `c` includes the truth-side excitation and the matrix-log
Lipschitz bound. The hypotheses separate the analytically proved intermediate
estimates, and the conclusion follows by a genuine case split and absorption.
No excitation condition is imposed on the alternative endpoint.
-/
theorem dynamic_inverse_from_component_bounds
    (a h s dm ds ε action c A B C K : ℝ)
    (ha : 0 ≤ a) (hdm : 0 ≤ dm)
    (hε : 0 ≤ ε) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hamplitude : h ≤ A * (a + ε))
    (hdiameter : dm ≤ K)
    (hcovariance : ds ≤ B * (ε + s * dm))
    (haction : ε < a → action ≤ C * (ε + a * ds + s * a * dm))
    (hexcitation : ε < a → c * a * dm ≤ action)
    (hsmall : C * (B + 1) * s ≤ c / 2) :
    h * dm ≤
      (2 * A * K + 4 * A * C * (1 + a * B) / c) * ε := by
  have hcoef : 0 ≤ 4 * A * C * (1 + a * B) / c := by positivity
  by_cases hlarge : a ≤ ε
  · have hh' : h ≤ 2 * A * ε := by nlinarith
    have hprod : h * dm ≤ (2 * A * ε) * K :=
      mul_le_mul hh' hdiameter hdm (by positivity)
    nlinarith
  · have hεa : ε < a := lt_of_not_ge hlarge
    have hexc := hexcitation hεa
    have hact := haction hεa
    have hcovmul : C * a * ds ≤ C * a * (B * (ε + s * dm)) :=
      mul_le_mul_of_nonneg_left hcovariance (mul_nonneg hC ha)
    have hsmallmul : C * (B + 1) * s * (a * dm) ≤ c / 2 * (a * dm) :=
      mul_le_mul_of_nonneg_right hsmall (mul_nonneg ha hdm)
    have habsorb : (c / 2) * (a * dm) ≤ C * (1 + a * B) * ε := by
      nlinarith
    have hweighted : a * dm ≤ (2 * C * (1 + a * B) / c) * ε := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      nlinarith [habsorb]
    have hh' : h ≤ 2 * A * a := by nlinarith
    have hprod : h * dm ≤ 2 * A * (a * dm) := by
      nlinarith [mul_le_mul_of_nonneg_right hh' hdm]
    have hbound := mul_le_mul_of_nonneg_left hweighted (show 0 ≤ 2 * A by positivity)
    have heq : 2 * A * ((2 * C * (1 + a * B) / c) * ε) =
        (4 * A * C * (1 + a * B) / c) * ε := by ring
    rw [heq] at hbound
    have hnonneg : 0 ≤ 2 * A * K * ε := by positivity
    nlinarith

/-- Uniform fixed-envelope version of I1 Lemma (dynamic-inverse). The compact
amplitude bound `a ≤ aMax` removes the true physical leverage amplitude from
the comparison constant; only the fixed constants remain. This supplies the
dynamic estimate used by `structural_inverse_from_component_bounds` below. -/
theorem uniform_dynamic_inverse_from_component_bounds
    (a h s dm ds ε action c A B C K aMax : ℝ)
    (ha : 0 ≤ a) (hdm : 0 ≤ dm)
    (hε : 0 ≤ ε) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hcap : a ≤ aMax)
    (hamplitude : h ≤ A * (a + ε))
    (hdiameter : dm ≤ K)
    (hcovariance : ds ≤ B * (ε + s * dm))
    (haction : ε < a → action ≤ C * (ε + a * ds + s * a * dm))
    (hexcitation : ε < a → c * a * dm ≤ action)
    (hsmall : C * (B + 1) * s ≤ c / 2) :
    h * dm ≤
      (2 * A * K + 4 * A * C * (1 + aMax * B) / c) * ε := by
  have hlocal := dynamic_inverse_from_component_bounds
    a h s dm ds ε action c A B C K ha hdm hε hc hA hB hC hK
    hamplitude hdiameter hcovariance haction hexcitation hsmall
  have hcoef := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_right hcap hB) 1)
      (show 0 ≤ 4 * A * C by positivity)) hc.le
  apply le_trans hlocal
  simpa only [add_comm] using
    (mul_le_mul_of_nonneg_right (add_le_add_left hcoef (2 * A * K)) hε)

end DynamicInverse

section FullStructuralInverse

/-- Algebraic closure of I1 Proposition (full-inverse), equation
(structural-inverse). The covariance-pair estimate, loading profile and dynamic
estimate are separate hypotheses; the nonlinear covariance term is absorbed.
All constants in the conclusion depend on the fixed bounds `A,B,D,P,H`, with
no remaining dependence on the actual signal amplitudes `s,h`.
-/
theorem structural_inverse_from_component_bounds
    (s h dm ds dh ε A B D P H : ℝ)
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hdm : 0 ≤ dm) (hds : 0 ≤ ds)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hbounded : h ≤ H)
    (hcov : ds + s * dm ≤ A * ε + B * h ^ 2 * (ds + dm))
    (hdynamic : h * dm ≤ D * ε)
    (hprofile : dh ≤ P * (ε + h * dm + h * ds))
    (hsmall : B * h ^ 2 ≤ 1 / 2) :
    ds + dh + (s + h) * dm ≤
      (2 * (A + B * H * D) + P * (1 + D + 2 * H * (A + B * H * D)) + D) * ε := by
  have hnonneg : 0 ≤ A + B * H * D := by positivity
  have hcross₁ := mul_le_mul_of_nonneg_left hdynamic (show 0 ≤ B * h by positivity)
  have hcross₂ := mul_le_mul_of_nonneg_right hbounded (show 0 ≤ B * D * ε by positivity)
  have habs := mul_le_mul_of_nonneg_right hsmall hds
  have hpair : ds + s * dm ≤ 2 * (A + B * H * D) * ε := by
    nlinarith [mul_nonneg hs hdm]
  have hdsbound : ds ≤ 2 * (A + B * H * D) * ε := by
    nlinarith [mul_nonneg hs hdm]
  have hds₁ := mul_le_mul_of_nonneg_left hdsbound hh
  have hds₂ := mul_le_mul_of_nonneg_right hbounded
    (show 0 ≤ 2 * (A + B * H * D) * ε by positivity)
  have hloading : dh ≤ P * (1 + D + 2 * H * (A + B * H * D)) * ε := by
    have hsum : ε + h * dm + h * ds ≤
        (1 + D + 2 * H * (A + B * H * D)) * ε := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hsum hP
    nlinarith
  nlinarith

/-- At positive covariance, the structural inverse separates all three
structural discrepancies when the observed features agree. This is only the
deterministic separation implication in I1 Theorem (main)(A); it does not
assert that equal observed-price laws supply the analytic inverse hypotheses. -/
theorem positive_scale_structural_separation
    (s h dm ds dh : ℝ) (hs : 0 < s) (hh : 0 ≤ h)
    (hdm : 0 ≤ dm) (hds : 0 ≤ ds) (hdh : 0 ≤ dh)
    (hinverse : ds + dh + (s + h) * dm ≤ 0) :
    dm = 0 ∧ ds = 0 ∧ dh = 0 := by
  have hprod : 0 ≤ (s + h) * dm := mul_nonneg (by positivity) hdm
  have hdmzero : dm = 0 := by
    by_contra hne
    have hpos : 0 < dm := lt_of_le_of_ne hdm (Ne.symm hne)
    have : 0 < (s + h) * dm := mul_pos (by positivity) hpos
    linarith
  constructor
  · exact hdmzero
  constructor <;> nlinarith

end FullStructuralInverse

section InformationWeight

/-- The algebraic comparison used after I1 equation (H-scale): when the
squared physical leverage amplitude is between fixed multiples of `s e²`,
the squared inverse weight `s+h` is comparable to `s²+s e²`, with positive
comparison constants certified in the conclusion. The stochastic
moment bound and expectation step needed for the risk theorem are separate. -/
theorem structural_information_weight_comparison
    (s h e c C : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hcpos : 0 < c) (hc : c ≤ 1) (hC : 1 ≤ C)
    (hlower : c * (s * e ^ 2) ≤ h ^ 2)
    (hupper : h ^ 2 ≤ C * (s * e ^ 2)) :
    0 < c ∧ 0 < 2 * C ∧
    c * (s ^ 2 + s * e ^ 2) ≤ (s + h) ^ 2 ∧
    (s + h) ^ 2 ≤ 2 * C * (s ^ 2 + s * e ^ 2) := by
  refine ⟨hcpos, by linarith, ?_, ?_⟩
  · have hcs := mul_le_mul_of_nonneg_right hc (sq_nonneg s)
    nlinarith [mul_nonneg hs hh]
  · have hCs := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
    nlinarith [sq_nonneg (s - h)]

end InformationWeight

end Research.I1
