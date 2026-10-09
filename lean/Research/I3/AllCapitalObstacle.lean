import Research.I3.ObstacleProfile
import Research.I3.ObstacleVariational
import Research.I3.Protection

/-!
# I3: the exact all-capital reduced obstacle problem

The optimizer, cap selection and saturation below are proved for the actual
Lebesgue-integral functional on [0,1]. Competitors are arbitrary nonnegative
integrable functions with finite squared integral. This does not assume their
optimality or postulate a scalar risk curve. Identifying this functional with
the risk of every protected additive book under the two-dimensional P₀ model
still requires the full symmetrization and conditional-moment bridge.
-/

open MeasureTheory Set
open Research.I3.ObstacleProfile
open Research.I3.Obstacle

namespace Research.I3.AllCapital

noncomputable def meanLevel (δ : ℝ) : ℝ := 1 / 6 + δ / 15

noncomputable def reducedValue (δ a : ℝ) : ℝ :=
  obstacleObjective unitInterval (g δ) (meanLevel δ) (residual δ a)

/-- The Lagrange multiplier is evaluated from the paper's actual polynomials. -/
theorem multiplier_factorization (δ a : ℝ) :
    g δ a - meanLevel δ - epsilon δ a / 2 =
      (a - 1) ^ 2 * (4 * a ^ 3 * δ + 3 * a ^ 2 * δ - 8 * a * δ +
        10 * a - 4 * δ - 10) / 60 := by
  unfold g meanLevel epsilon
  ring

lemma multiplier_coefficient_bound {δ a : ℝ} (hδ : 0 ≤ δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    4 * a ^ 3 * δ + 3 * a ^ 2 * δ - 8 * a * δ + 10 * a - 4 * δ - 10 ≤ -4 * δ := by
  have ha2 : a ^ 2 ≤ a := by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
  have ha3 : a ^ 3 ≤ a := by
    have hm := mul_le_mul_of_nonneg_left ha2 ha.1
    nlinarith
  have h2 := mul_le_mul_of_nonneg_right ha2 hδ
  have h3 := mul_le_mul_of_nonneg_right ha3 hδ
  have hprod := mul_nonneg ha.1 hδ
  nlinarith [ha.2]

/-- All nonsaturated thresholds have the sign required for cap optimality. -/
theorem multiplier_nonpos {δ a : ℝ} (hδ : 0 ≤ δ) (ha : a ∈ Icc (0 : ℝ) 1) :
    g δ a - meanLevel δ - epsilon δ a / 2 ≤ 0 := by
  rw [multiplier_factorization]
  have hc : 4 * a ^ 3 * δ + 3 * a ^ 2 * δ - 8 * a * δ + 10 * a - 4 * δ - 10 ≤ 0 := by
    have hb := multiplier_coefficient_bound hδ ha
    linarith
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hc) (by norm_num)

/-- The multiplier is strictly negative before the full-support threshold. -/
theorem multiplier_neg {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) (ha1 : a < 1) :
    g δ a - meanLevel δ - epsilon δ a / 2 < 0 := by
  rw [multiplier_factorization]
  have hc : 4 * a ^ 3 * δ + 3 * a ^ 2 * δ - 8 * a * δ + 10 * a - 4 * δ - 10 < 0 := by
    have hb := multiplier_coefficient_bound hδ.le ha
    linarith
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt ha1))) hc)
    (by norm_num)

theorem multiplier_at_saturation (δ : ℝ) : g δ 1 - meanLevel δ - epsilon δ 1 / 2 = 0 := by
  rw [multiplier_factorization]
  norm_num

/-- Feasibility, square integrability and cross integrability are proved for
this continuous threshold, rather than assumed as optimization premises. -/
theorem residual_admissible (δ a : ℝ) : Admissible unitInterval (g δ) (residual δ a) :=
  ⟨Filter.Eventually.of_forall (residual_nonneg δ a), integrable_residual δ a,
    integrable_residual_square δ a, integrable_g_mul_residual δ a⟩

/-- The paper's concrete threshold beats every admissible competitor below
its mean cap. This is a genuine infinite-dimensional integral minimization. -/
theorem concrete_threshold_optimal {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) {r : ℝ → ℝ}
    (hr : Admissible unitInterval (g δ) r)
    (hcap : (∫ s, r s ∂unitInterval) ≤ epsilon δ a / 2) :
    reducedValue δ a ≤ obstacleObjective unitInterval (g δ) (meanLevel δ) r := by
  have hm := integral_residual_unitInterval hδ ha
  apply threshold_optimal_mean_cap hr (residual_admissible δ a) (meanLevel δ)
  · change g δ a - meanLevel δ - (∫ s, residual δ a s ∂unitInterval) ≤ 0
    rw [hm]
    exact multiplier_nonpos hδ.le ha
  · change (∫ s, r s ∂unitInterval) ≤ ∫ s, residual δ a s ∂unitInterval
    rwa [hm]

/-- At saturation the concrete profile is optimal without any upper mean cap. -/
theorem concrete_saturation_optimal {δ : ℝ} (hδ : 0 < δ) {r : ℝ → ℝ}
    (hr : Admissible unitInterval (g δ) r) :
    reducedValue δ 1 ≤ obstacleObjective unitInterval (g δ) (meanLevel δ) r := by
  apply threshold_optimal_saturation hr (residual_admissible δ 1) (meanLevel δ)
  change g δ 1 - meanLevel δ - (∫ s, residual δ 1 s ∂unitInterval) = 0
  rw [integral_residual_unitInterval hδ (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)]
  exact multiplier_at_saturation δ

/-- Cap selection has a unique parameter, is feasible, and attains the
minimum over every admissible residual at every nonnegative excess cap. -/
theorem all_capital_obstacle_optimizer {δ c C₀ : ℝ} (hδ : 0 < δ) (hc : C₀ ≤ c) :
    ∃! a : ℝ, a ∈ Icc (0 : ℝ) 1 ∧
      epsilon δ a = min (c - C₀) (1 / 6 + δ / 5) ∧
      2 * (∫ s, residual δ a s ∂unitInterval) ≤ c - C₀ ∧
      ∀ r : ℝ → ℝ, Admissible unitInterval (g δ) r →
        2 * (∫ s, r s ∂unitInterval) ≤ c - C₀ →
        reducedValue δ a ≤ obstacleObjective unitInterval (g δ) (meanLevel δ) r := by
  obtain ⟨a, ⟨ha, hea⟩, huniq⟩ := capped_cap_inversion hδ hc
  refine ⟨a, ⟨ha, hea, ?_, ?_⟩, ?_⟩
  · rw [integral_residual_unitInterval hδ ha]
    have hh := min_le_left (c - C₀) (1 / 6 + δ / 5)
    linarith
  · intro r hr hcap
    by_cases hlow : c - C₀ ≤ 1 / 6 + δ / 5
    · rw [min_eq_left hlow] at hea
      exact concrete_threshold_optimal hδ ha hr (by linarith)
    · have hae : epsilon δ a = epsilon δ 1 := by
        rw [epsilon_one, hea, min_eq_right (le_of_not_ge hlow)]
      have ha1 : a = 1 := (strictMonoOn_epsilon hδ).injOn ha
        (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hae
      rw [ha1]
      exact concrete_saturation_optimal hδ hr
  · intro b hb
    exact huniq b ⟨hb.1, hb.2.1⟩

/-- Exact evaluation of the integral objective at its threshold optimizer. -/
theorem reducedValue_formula {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    reducedValue δ a = -2 * meanLevel δ * epsilon δ a +
      2 * (a * (g δ a) ^ 2 - gSquarePrimitive δ a) - (epsilon δ a) ^ 2 / 2 := by
  unfold reducedValue obstacleObjective
  rw [integral_g_mul_residual_unitInterval hδ ha,
    integral_residual_unitInterval hδ ha, integral_residual_square_unitInterval hδ ha]
  ring

/-- The same evaluated objective in the integral form used in the manuscript. -/
theorem reducedValue_integral_formula {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    reducedValue δ a = -2 * meanLevel δ * epsilon δ a +
      2 * (∫ s in (0 : ℝ)..a, (g δ a) ^ 2 - (g δ s) ^ 2) -
      (epsilon δ a) ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 a)
    (((continuous_g δ).pow 2).intervalIntegrable 0 a),
    intervalIntegral.integral_const, integral_g_square]
  simp only [sub_zero, smul_eq_mul]
  exact reducedValue_formula hδ ha

/-- A quantitative comparison of two thresholds, inherited from the integral
variational inequality rather than an assumed value-curve derivative. -/
theorem reducedValue_excess_lower_bound {δ a b : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    4 * (g δ b - meanLevel δ - epsilon δ b / 2) *
      (epsilon δ a / 2 - epsilon δ b / 2) ≤ reducedValue δ a - reducedValue δ b := by
  have hp := threshold_multiplier_lower_bound
    (residual_admissible δ a) (residual_admissible δ b) (meanLevel δ)
  change 4 * (g δ b - meanLevel δ - (∫ s, residual δ b s ∂unitInterval)) *
    ((∫ s, residual δ a s ∂unitInterval) - (∫ s, residual δ b s ∂unitInterval)) ≤
      reducedValue δ a - reducedValue δ b at hp
  rwa [integral_residual_unitInterval hδ ha, integral_residual_unitInterval hδ hb] at hp

theorem reducedValue_strict_of_lt_one {δ a b : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) (hb1 : b < 1) : reducedValue δ b < reducedValue δ a := by
  have he := strictMonoOn_epsilon hδ ha hb hab
  have hm := multiplier_neg hδ hb hb1
  have hp := mul_pos_of_neg_of_neg
    (show 4 * (g δ b - meanLevel δ - epsilon δ b / 2) < 0 by linarith)
    (show epsilon δ a / 2 - epsilon δ b / 2 < 0 by linarith)
  have hl := reducedValue_excess_lower_bound hδ ha hb
  linarith

/-- Strict reduction includes the saturation endpoint. -/
theorem reducedValue_strictAntiOn {δ : ℝ} (hδ : 0 < δ) :
    StrictAntiOn (reducedValue δ) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases hb1 : b < 1
  · exact reducedValue_strict_of_lt_one hδ ha hb hab hb1
  · have hb_eq : b = 1 := le_antisymm hb.2 (le_of_not_gt hb1)
    subst b
    have hd : (a + 1) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], by linarith⟩
    have hstrict := reducedValue_strict_of_lt_one hδ ha hd
      (show a < (a + 1) / 2 by linarith) (show (a + 1) / 2 < 1 by linarith)
    have hsat := concrete_saturation_optimal hδ (residual_admissible δ ((a + 1) / 2))
    change reducedValue δ 1 ≤ reducedValue δ ((a + 1) / 2) at hsat
    exact lt_of_le_of_lt hsat hstrict

theorem reducedValue_zero {δ : ℝ} (hδ : 0 < δ) : reducedValue δ 0 = 0 := by
  rw [reducedValue_formula hδ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)]
  simp [epsilon, gSquarePrimitive]

/-- This is the closed expression for the saturated reduced variance. The
identification with actual P₀ variance is a separate model-moment obligation. -/
theorem saturated_variance_expression {δ : ℝ} (hδ : 0 < δ) :
    (20 + 7 * δ) / 360 + reducedValue δ 1 - (δ / 15) ^ 2 =
      (1260 + 135 * δ - 289 * δ ^ 2) / 28350 := by
  rw [reducedValue_formula hδ (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)]
  unfold meanLevel epsilon g gSquarePrimitive
  ring

/-- The paper's global residual uses zero outside the variance coordinate's
support; its optimizer on the unit interval is unchanged. -/
noncomputable def extendedResidual (δ a s : ℝ) : ℝ :=
  if s ∈ Icc (0 : ℝ) 1 then residual δ a s else 0

theorem extendedResidual_measurable (δ a : ℝ) : Measurable (extendedResidual δ a) := by
  exact Measurable.ite measurableSet_Icc (continuous_residual δ a).measurable measurable_const

theorem extendedResidual_nonneg (δ a s : ℝ) : 0 ≤ extendedResidual δ a s := by
  unfold extendedResidual
  split_ifs
  · exact residual_nonneg δ a s
  · exact le_refl 0

theorem extendedResidual_off_support {δ a s : ℝ} (hs : s ∉ Icc (0 : ℝ) 1) :
    extendedResidual δ a s = 0 := if_neg hs

theorem extendedResidual_on_support {δ a s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    extendedResidual δ a s = residual δ a s := if_pos hs

theorem extendedResidual_ae (δ a : ℝ) :
    extendedResidual δ a =ᵐ[ObstacleProfile.unitInterval] residual δ a := by
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
  exact extendedResidual_on_support hs

theorem extendedResidual_integral {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ s, extendedResidual δ a s ∂unitInterval) = epsilon δ a / 2 := by
  rw [integral_congr_ae (extendedResidual_ae δ a)]
  exact integral_residual_unitInterval hδ ha

noncomputable def candidateBook (δ a x y : ℝ) : ℝ :=
  twoPut 2 1 x y + extendedResidual δ a |x - 1| + extendedResidual δ a |y - 1|

/-- The actual zero-extended candidate protects globally, including states
outside the statistical square. -/
theorem candidateBook_protects (δ a x y : ℝ) : basketPut 2 x y ≤ candidateBook δ a x y := by
  have hp := basket_le_twoPut 2 1 x y
  have hx := extendedResidual_nonneg δ a |x - 1|
  have hy := extendedResidual_nonneg δ a |y - 1|
  unfold candidateBook
  linarith

theorem candidateBook_origin {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) : candidateBook δ a 0 0 - basketPut 2 0 0 = 0 := by
  have hz := surplus_at_origin (K := (2 : ℝ)) (k := (1 : ℝ)) (by norm_num) (by norm_num)
  simp only [candidateBook, zero_sub, abs_neg, abs_one]
  rw [extendedResidual_on_support (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num),
    residual_at_one hδ ha]
  simpa only [add_zero, surplus] using hz

/-- Exact global loss for any supplied scalar financing. Pricing that scalar
by Q remains a separate model-integral bridge. -/
theorem candidateBook_exact_floor {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) (c : ℝ) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      -c ≤ candidateBook δ a x y - basketPut 2 x y - c) ∧
    candidateBook δ a 0 0 - basketPut 2 0 0 - c = -c := by
  constructor
  · intro x y _ _
    have hp := candidateBook_protects δ a x y
    linarith
  · rw [candidateBook_origin hδ ha]
    ring

end Research.I3.AllCapital
