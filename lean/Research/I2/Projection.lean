import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# I2: the two-asset projection in a real inner product space

This is the geometric core of Proposition `prop:projection` in I2. The vectors
are actual elements of an arbitrary real inner product space: a stock increment,
a call increment and a target increment. The target is orthogonal to stock.
Orthogonalizing the call gives the exact optimal holdings, residual norm and
excess-loss identity. No probabilistic conclusion is encoded as an axiom.

To apply this result to the manuscript one must separately construct the
conditional L2 gain space, identify its conditional inner products, prove its
positive Gram determinant and show that random optimal holdings are measurable
and admissible. Those stochastic and closure arguments are not formalized here.
-/

noncomputable section

open scoped InnerProductSpace

namespace Research.I2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The stock coefficient in orthogonalization of the call increment. -/
def stockCoefficient (stock call : E) : ℝ :=
  ⟪stock, call⟫_ℝ / ‖stock‖ ^ 2

/-- The part of the call increment orthogonal to the stock increment. -/
def orthogonalCall (stock call : E) : E :=
  call - stockCoefficient stock call • stock

/-- Regression coefficient of a target on the orthogonalized call. -/
def callCoefficient (target orthCall : E) : ℝ :=
  ⟪target, orthCall⟫_ℝ / ‖orthCall‖ ^ 2

theorem orthogonalCall_stock_inner {stock call : E} (hs : stock ≠ 0) :
    ⟪stock, orthogonalCall stock call⟫_ℝ = 0 := by
  have hs2 : ‖stock‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hs)
  simp only [orthogonalCall, stockCoefficient, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [div_mul_cancel₀ _ hs2, sub_self]

/-- Exact loss for two orthogonal tradable increments, before minimization. -/
theorem orthogonal_pair_loss (target stock orthCall : E)
    (hts : ⟪target, stock⟫_ℝ = 0)
    (hsc : ⟪stock, orthCall⟫_ℝ = 0) (u v : ℝ) :
    ‖target - (u • stock + v • orthCall)‖ ^ 2 =
      ‖target‖ ^ 2 - 2 * v * ⟪target, orthCall⟫_ℝ +
        u ^ 2 * ‖stock‖ ^ 2 + v ^ 2 * ‖orthCall‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [inner_add_right, real_inner_smul_right, real_inner_smul_left,
    hts, hsc, norm_smul, Real.norm_eq_abs, mul_zero, add_zero,
    mul_pow, sq_abs]
  ring

/-- The complete square is an identity in the actual vector norm, not a
postulated quadratic objective. -/
theorem orthogonal_pair_excess_loss (target stock orthCall : E)
    (hts : ⟪target, stock⟫_ℝ = 0)
    (hsc : ⟪stock, orthCall⟫_ℝ = 0) (hc : orthCall ≠ 0) (u v : ℝ) :
    ‖target - (u • stock + v • orthCall)‖ ^ 2 =
      (‖target‖ ^ 2 - ⟪target, orthCall⟫_ℝ ^ 2 / ‖orthCall‖ ^ 2) +
        u ^ 2 * ‖stock‖ ^ 2 +
        (v - callCoefficient target orthCall) ^ 2 * ‖orthCall‖ ^ 2 := by
  have hc2 : ‖orthCall‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  rw [orthogonal_pair_loss target stock orthCall hts hsc]
  unfold callCoefficient
  field_simp
  ring

/-- The regression holdings attain the stated residual. -/
theorem orthogonal_pair_attains (target stock orthCall : E)
    (hts : ⟪target, stock⟫_ℝ = 0)
    (hsc : ⟪stock, orthCall⟫_ℝ = 0) (hc : orthCall ≠ 0) :
    ‖target - callCoefficient target orthCall • orthCall‖ ^ 2 =
      ‖target‖ ^ 2 - ⟪target, orthCall⟫_ℝ ^ 2 / ‖orthCall‖ ^ 2 := by
  simpa using orthogonal_pair_excess_loss target stock orthCall hts hsc hc
    0 (callCoefficient target orthCall)

/-- No other finite pair of holdings has smaller squared norm loss. -/
theorem orthogonal_pair_optimal (target stock orthCall : E)
    (hts : ⟪target, stock⟫_ℝ = 0)
    (hsc : ⟪stock, orthCall⟫_ℝ = 0) (hc : orthCall ≠ 0) (u v : ℝ) :
    ‖target - callCoefficient target orthCall • orthCall‖ ^ 2 ≤
      ‖target - (u • stock + v • orthCall)‖ ^ 2 := by
  rw [orthogonal_pair_attains target stock orthCall hts hsc hc,
    orthogonal_pair_excess_loss target stock orthCall hts hsc hc]
  have h₁ := mul_nonneg (sq_nonneg u) (sq_nonneg ‖stock‖)
  have h₂ := mul_nonneg (sq_nonneg (v - callCoefficient target orthCall))
    (sq_nonneg ‖orthCall‖)
  linarith

/-- The fitted gain has at most the target's energy. -/
theorem projected_gain_energy (target stock orthCall : E)
    (hts : ⟪target, stock⟫_ℝ = 0)
    (hsc : ⟪stock, orthCall⟫_ℝ = 0) (hc : orthCall ≠ 0) :
    ‖callCoefficient target orthCall • orthCall‖ ^ 2 ≤ ‖target‖ ^ 2 := by
  have hc2 : ‖orthCall‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have henergy : ‖callCoefficient target orthCall • orthCall‖ ^ 2 =
      ⟪target, orthCall⟫_ℝ ^ 2 / ‖orthCall‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, callCoefficient]
    field_simp
  rw [henergy]
  have h := sq_nonneg ‖target - callCoefficient target orthCall • orthCall‖
  rw [orthogonal_pair_attains target stock orthCall hts hsc hc] at h
  linarith

/-- Nondegeneracy makes the optimal pair unique. -/
theorem orthogonal_pair_optimal_iff (target stock orthCall : E)
    (hts : ⟪target, stock⟫_ℝ = 0)
    (hsc : ⟪stock, orthCall⟫_ℝ = 0) (hs : stock ≠ 0) (hc : orthCall ≠ 0)
    (u v : ℝ) :
    ‖target - (u • stock + v • orthCall)‖ ^ 2 =
      ‖target - callCoefficient target orthCall • orthCall‖ ^ 2 ↔
      u = 0 ∧ v = callCoefficient target orthCall := by
  constructor
  · intro h
    rw [orthogonal_pair_attains target stock orthCall hts hsc hc,
      orthogonal_pair_excess_loss target stock orthCall hts hsc hc] at h
    have h₁ := mul_nonneg (sq_nonneg u) (sq_nonneg ‖stock‖)
    have h₂ := mul_nonneg (sq_nonneg (v - callCoefficient target orthCall))
      (sq_nonneg ‖orthCall‖)
    have hu : u ^ 2 * ‖stock‖ ^ 2 = 0 := by linarith
    have hv : (v - callCoefficient target orthCall) ^ 2 * ‖orthCall‖ ^ 2 = 0 := by
      linarith
    have hs2 : ‖stock‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hs)
    have hc2 : ‖orthCall‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
    constructor
    · exact (sq_eq_zero_iff.mp ((mul_eq_zero.mp hu).resolve_right hs2))
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hv).resolve_right hc2))
  · rintro ⟨rfl, rfl⟩
    simp

/-- Conversion back to the original stock/call holdings is exact. -/
theorem call_book_orthogonal_coordinates (stock call : E) (u v : ℝ) :
    u • stock + v • call =
      (u + stockCoefficient stock call * v) • stock +
        v • orthogonalCall stock call := by
  unfold orthogonalCall
  simp only [add_smul, smul_sub, smul_smul]
  rw [mul_comm (stockCoefficient stock call) v]
  symm
  calc
    (u • stock + (v * stockCoefficient stock call) • stock) +
        (v • call - (v * stockCoefficient stock call) • stock) =
      (u • stock + v • call) +
        ((v * stockCoefficient stock call) • stock -
          (v * stockCoefficient stock call) • stock) := by
            simp only [sub_eq_add_neg]
            ac_rfl
    _ = _ := by simp

/-- The actual two-asset book has the manuscript's exact residual plus two
nonnegative excess-loss terms. The stochastic conditional-L2 identification is
a separate obligation, not a hypothesis asserting this conclusion. -/
theorem call_book_excess_loss (target stock call : E)
    (hts : ⟪target, stock⟫_ℝ = 0) (hs : stock ≠ 0)
    (hc : orthogonalCall stock call ≠ 0) (u v : ℝ) :
    ‖target - (u • stock + v • call)‖ ^ 2 =
      (‖target‖ ^ 2 - ⟪target, orthogonalCall stock call⟫_ℝ ^ 2 /
        ‖orthogonalCall stock call‖ ^ 2) +
      (u + stockCoefficient stock call * v) ^ 2 * ‖stock‖ ^ 2 +
      (v - callCoefficient target (orthogonalCall stock call)) ^ 2 *
        ‖orthogonalCall stock call‖ ^ 2 := by
  rw [call_book_orthogonal_coordinates]
  exact orthogonal_pair_excess_loss target stock (orthogonalCall stock call)
    hts (orthogonalCall_stock_inner hs) hc _ _

/-- In original units the unique optimum is call coefficient c/v and stock
coefficient -beta*c/v; the actual norm loss attains A-c^2/v. -/
theorem call_book_attains (target stock call : E)
    (hts : ⟪target, stock⟫_ℝ = 0) (hs : stock ≠ 0)
    (hc : orthogonalCall stock call ≠ 0) :
    ‖target - ((-(stockCoefficient stock call) *
        callCoefficient target (orthogonalCall stock call)) • stock +
        callCoefficient target (orthogonalCall stock call) • call)‖ ^ 2 =
      ‖target‖ ^ 2 - ⟪target, orthogonalCall stock call⟫_ℝ ^ 2 /
        ‖orthogonalCall stock call‖ ^ 2 := by
  rw [call_book_excess_loss target stock call hts hs hc]
  simp

/-- The manuscript residual A-c^2/v is nonnegative for the actual vectors. -/
theorem call_book_residual_nonneg (target stock call : E)
    (hts : ⟪target, stock⟫_ℝ = 0) (hs : stock ≠ 0)
    (hc : orthogonalCall stock call ≠ 0) :
    0 ≤ ‖target‖ ^ 2 - ⟪target, orthogonalCall stock call⟫_ℝ ^ 2 /
      ‖orthogonalCall stock call‖ ^ 2 := by
  rw [← call_book_attains target stock call hts hs hc]
  exact sq_nonneg _

end Research.I2
