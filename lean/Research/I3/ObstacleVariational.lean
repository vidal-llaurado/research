import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! I3's integral obstacle problem. The objective uses Bochner integrals;
competitors are nonnegative, square integrable, and have an integrable
cross term with the fixed state profile. Optimality is derived. -/
open MeasureTheory
namespace Research.I3.Obstacle

noncomputable def obstacleObjective {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) (h : ℝ) (r : Ω → ℝ) : ℝ :=
  4 * (∫ ω, g ω * r ω ∂μ) - 4 * h * (∫ ω, r ω ∂μ) +
    2 * (∫ ω, (r ω) ^ 2 ∂μ) - 2 * (∫ ω, r ω ∂μ) ^ 2

noncomputable def threshold {Ω : Type*} (g : Ω → ℝ) (τ : ℝ) (ω : Ω) : ℝ :=
  max (τ - g ω) 0

structure Admissible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g r : Ω → ℝ) : Prop where
  nonneg : ∀ᵐ ω ∂μ, 0 ≤ r ω
  integrable : Integrable r μ
  square_integrable : Integrable (fun ω => (r ω) ^ 2) μ
  cross_integrable : Integrable (fun ω => g ω * r ω) μ

lemma integrable_product_of_squares {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {r q : Ω → ℝ} (hr : Integrable r μ) (hq : Integrable q μ)
    (hr₂ : Integrable (fun ω => (r ω) ^ 2) μ)
    (hq₂ : Integrable (fun ω => (q ω) ^ 2) μ) :
    Integrable (fun ω => r ω * q ω) μ := by
  apply (hr₂.add hq₂).mono' (hr.aestronglyMeasurable.mul hq.aestronglyMeasurable)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  change |r ω * q ω| ≤ (r ω) ^ 2 + (q ω) ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (r ω - q ω), sq_nonneg (r ω + q ω)]

lemma integrable_difference_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {r q : Ω → ℝ} (hr : Integrable r μ) (hq : Integrable q μ)
    (hr₂ : Integrable (fun ω => (r ω) ^ 2) μ)
    (hq₂ : Integrable (fun ω => (q ω) ^ 2) μ) :
    Integrable (fun ω => (r ω - q ω) ^ 2) μ := by
  have hp := integrable_product_of_squares hr hq hr₂ hq₂
  have hi := (hr₂.sub (hp.const_mul 2)).add hq₂
  convert hi using 1
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma integral_difference_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {r q : Ω → ℝ} (hr : Integrable r μ) (hq : Integrable q μ)
    (hr₂ : Integrable (fun ω => (r ω) ^ 2) μ)
    (hq₂ : Integrable (fun ω => (q ω) ^ 2) μ) :
    (∫ ω, (r ω - q ω) ^ 2 ∂μ) =
      (∫ ω, (r ω) ^ 2 ∂μ) - 2 * (∫ ω, r ω * q ω ∂μ) +
        (∫ ω, (q ω) ^ 2 ∂μ) := by
  have hp := integrable_product_of_squares hr hq hr₂ hq₂
  calc
    _ = ∫ ω, ((r ω) ^ 2 - 2 * (r ω * q ω)) + (q ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = _ := by
      have hadd := integral_add (hr₂.sub (hp.const_mul 2)) hq₂
      have hsub := integral_sub hr₂ (hp.const_mul 2)
      simp only [Pi.sub_apply, integral_const_mul] at hadd hsub
      rw [hadd, hsub]

lemma square_mean_le_integral_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {r : Ω → ℝ}
    (hr : Integrable r μ) (hr₂ : Integrable (fun ω => (r ω) ^ 2) μ) :
    (∫ ω, r ω ∂μ) ^ 2 ≤ ∫ ω, (r ω) ^ 2 ∂μ := by
  let m := ∫ ω, r ω ∂μ
  have hc : Integrable (fun _ : Ω => m) μ := integrable_const m
  have hc₂ : Integrable (fun _ : Ω => m ^ 2) μ := integrable_const _
  have hs := integral_difference_square hr hc hr₂ hc₂
  have hn : 0 ≤ ∫ ω, (r ω - m) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hp : (∫ ω, r ω * m ∂μ) = m * m := by rw [integral_mul_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hs
  rw [hp] at hs
  dsimp [m] at hs hn ⊢
  nlinarith

lemma objective_excess_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g r q : Ω → ℝ} (hr : Admissible μ g r)
    (hq : Admissible μ g q) (h : ℝ) :
    obstacleObjective μ g h r - obstacleObjective μ g h q =
      4 * ((∫ ω, (g ω + q ω) * (r ω - q ω) ∂μ) -
        (h + ∫ ω, q ω ∂μ) * ((∫ ω, r ω ∂μ) - ∫ ω, q ω ∂μ)) +
      2 * ((∫ ω, (r ω - q ω) ^ 2 ∂μ) -
        ((∫ ω, r ω ∂μ) - ∫ ω, q ω ∂μ) ^ 2) := by
  have hp := integrable_product_of_squares hr.integrable hq.integrable
    hr.square_integrable hq.square_integrable
  have he : (∫ ω, (g ω + q ω) * (r ω - q ω) ∂μ) =
      (∫ ω, g ω * r ω ∂μ) - (∫ ω, g ω * q ω ∂μ) +
      (∫ ω, r ω * q ω ∂μ) - (∫ ω, (q ω) ^ 2 ∂μ) := by
    calc
      _ = ∫ ω, ((g ω * r ω - g ω * q ω) + r ω * q ω) - (q ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = _ := by
        have hs := integral_sub ((hr.cross_integrable.sub hq.cross_integrable).add hp) hq.square_integrable
        have ha := integral_add (hr.cross_integrable.sub hq.cross_integrable) hp
        have hg := integral_sub hr.cross_integrable hq.cross_integrable
        simp only [Pi.sub_apply, Pi.add_apply] at hs ha hg
        rw [hs, ha, hg]
  rw [he, integral_difference_square hr.integrable hq.integrable
    hr.square_integrable hq.square_integrable]
  unfold obstacleObjective
  ring

lemma threshold_gradient_inequality (a τ s : ℝ) (hs : 0 ≤ s) :
    τ * (s - max (τ - a) 0) ≤
      (a + max (τ - a) 0) * (s - max (τ - a) 0) := by
  by_cases ha : a ≤ τ
  · rw [max_eq_left (sub_nonneg.mpr ha)]
    nlinarith
  · have hτ : τ ≤ a := le_of_not_ge ha
    rw [max_eq_right (sub_nonpos.mpr hτ)]
    nlinarith

lemma threshold_integral_gradient_inequality {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g r : Ω → ℝ} {τ : ℝ} (hr : Admissible μ g r)
    (hq : Admissible μ g (threshold g τ)) :
    τ * ((∫ ω, r ω ∂μ) - ∫ ω, threshold g τ ω ∂μ) ≤
      ∫ ω, (g ω + threshold g τ ω) * (r ω - threshold g τ ω) ∂μ := by
  have hp := integrable_product_of_squares hr.integrable hq.integrable
    hr.square_integrable hq.square_integrable
  have hi : Integrable (fun ω => (g ω + threshold g τ ω) *
      (r ω - threshold g τ ω)) μ := by
    have hj := ((hr.cross_integrable.sub hq.cross_integrable).add hp).sub hq.square_integrable
    convert hj using 1
    ext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hle : (fun ω => τ * (r ω - threshold g τ ω)) ≤ᵐ[μ]
      (fun ω => (g ω + threshold g τ ω) * (r ω - threshold g τ ω)) := by
    filter_upwards [hr.nonneg] with ω hω
    exact threshold_gradient_inequality (g ω) τ (r ω) hω
  have hm := integral_mono_ae ((hr.integrable.sub hq.integrable).const_mul τ) hi hle
  simp only [Pi.sub_apply, integral_const_mul] at hm
  rw [integral_sub hr.integrable hq.integrable] at hm
  exact hm

/-- The excess dominates the multiplier term and twice the perturbation variance. -/
theorem threshold_excess_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g r : Ω → ℝ} {τ : ℝ} (hr : Admissible μ g r)
    (hq : Admissible μ g (threshold g τ)) (h : ℝ) :
    4 * (τ - h - ∫ ω, threshold g τ ω ∂μ) *
      ((∫ ω, r ω ∂μ) - ∫ ω, threshold g τ ω ∂μ) +
      2 * ((∫ ω, (r ω - threshold g τ ω) ^ 2 ∂μ) -
        ((∫ ω, r ω ∂μ) - ∫ ω, threshold g τ ω ∂μ) ^ 2) ≤
      obstacleObjective μ g h r - obstacleObjective μ g h (threshold g τ) := by
  rw [objective_excess_identity hr hq]
  have hg := threshold_integral_gradient_inequality hr hq
  nlinarith

/-- The multiplier alone bounds the objective excess under a probability law. -/
theorem threshold_multiplier_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g r : Ω → ℝ} {τ : ℝ}
    (hr : Admissible μ g r) (hq : Admissible μ g (threshold g τ)) (h : ℝ) :
    4 * (τ - h - ∫ ω, threshold g τ ω ∂μ) *
      ((∫ ω, r ω ∂μ) - ∫ ω, threshold g τ ω ∂μ) ≤
      obstacleObjective μ g h r - obstacleObjective μ g h (threshold g τ) := by
  have he := threshold_excess_lower_bound hr hq h
  have hv := square_mean_le_integral_square (hr.integrable.sub hq.integrable)
    (integrable_difference_square hr.integrable hq.integrable
      hr.square_integrable hq.square_integrable)
  simp only [Pi.sub_apply] at hv
  rw [integral_sub hr.integrable hq.integrable] at hv
  linarith

/-- A threshold with the prescribed mean minimizes the integral objective. -/
theorem threshold_optimal_fixed_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g r : Ω → ℝ} {τ : ℝ} (hr : Admissible μ g r)
    (hq : Admissible μ g (threshold g τ)) (h : ℝ)
    (hm : (∫ ω, r ω ∂μ) = ∫ ω, threshold g τ ω ∂μ) :
    obstacleObjective μ g h (threshold g τ) ≤ obstacleObjective μ g h r := by
  have he := threshold_excess_lower_bound hr hq h
  rw [hm, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_add] at he
  have hn : 0 ≤ ∫ ω, (r ω - threshold g τ ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  linarith

/-- Equality at the prescribed mean forces almost-everywhere equality. -/
theorem threshold_unique_fixed_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g r : Ω → ℝ} {τ : ℝ} (hr : Admissible μ g r)
    (hq : Admissible μ g (threshold g τ)) (h : ℝ)
    (hm : (∫ ω, r ω ∂μ) = ∫ ω, threshold g τ ω ∂μ)
    (heq : obstacleObjective μ g h r = obstacleObjective μ g h (threshold g τ)) :
    r =ᵐ[μ] threshold g τ := by
  have he := threshold_excess_lower_bound hr hq h
  rw [hm, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_add,
    heq, sub_self] at he
  have hn : 0 ≤ ∫ ω, (r ω - threshold g τ ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hz : (∫ ω, (r ω - threshold g τ ω) ^ 2 ∂μ) = 0 := by linarith
  have hi := integrable_difference_square hr.integrable hq.integrable
    hr.square_integrable hq.square_integrable
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hi).mp hz
  filter_upwards [hae] with ω hω
  have hh : (r ω - threshold g τ ω) ^ 2 = 0 := hω
  nlinarith [sq_nonneg (r ω - threshold g τ ω)]

/-- A nonpositive multiplier gives optimality at the threshold's mean cap. -/
theorem threshold_optimal_mean_cap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g r : Ω → ℝ} {τ : ℝ}
    (hr : Admissible μ g r) (hq : Admissible μ g (threshold g τ)) (h : ℝ)
    (hmult : τ - h - (∫ ω, threshold g τ ω ∂μ) ≤ 0)
    (hm : (∫ ω, r ω ∂μ) ≤ ∫ ω, threshold g τ ω ∂μ) :
    obstacleObjective μ g h (threshold g τ) ≤ obstacleObjective μ g h r := by
  have he := threshold_excess_lower_bound hr hq h
  have hv := square_mean_le_integral_square (hr.integrable.sub hq.integrable)
    (integrable_difference_square hr.integrable hq.integrable
      hr.square_integrable hq.square_integrable)
  simp only [Pi.sub_apply] at hv
  rw [integral_sub hr.integrable hq.integrable] at hv
  have hp := mul_nonneg_of_nonpos_of_nonpos hmult (sub_nonpos.mpr hm)
  nlinarith

/-- Zero multiplier gives global optimality, without a competitor mean cap. -/
theorem threshold_optimal_saturation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g r : Ω → ℝ} {τ : ℝ}
    (hr : Admissible μ g r) (hq : Admissible μ g (threshold g τ)) (h : ℝ)
    (hmult : τ - h - (∫ ω, threshold g τ ω ∂μ) = 0) :
    obstacleObjective μ g h (threshold g τ) ≤ obstacleObjective μ g h r := by
  have he := threshold_excess_lower_bound hr hq h
  rw [hmult, mul_zero, zero_mul, zero_add] at he
  have hv := square_mean_le_integral_square (hr.integrable.sub hq.integrable)
    (integrable_difference_square hr.integrable hq.integrable
      hr.square_integrable hq.square_integrable)
  simp only [Pi.sub_apply] at hv
  rw [integral_sub hr.integrable hq.integrable] at hv
  linarith

end Research.I3.Obstacle
