import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# I3: the concrete obstacle profile and its capital parameter

This file uses the real Lebesgue interval integral. The polynomial profile,
truncated residual, and capital parameter are those in the all-capital
uninformed theorem. No pricing-law or symmetrization identity is assumed here.
-/

open MeasureTheory Set

namespace Research.I3.ObstacleProfile

noncomputable def g (δ s : ℝ) : ℝ := s / 2 + (δ - 1) * s ^ 2 / 4 - δ * s ^ 4 / 12

noncomputable def epsilon (δ a : ℝ) : ℝ :=
  a ^ 2 / 2 + (δ - 1) * a ^ 3 / 3 - 2 * δ * a ^ 5 / 15

noncomputable def residual (δ a s : ℝ) : ℝ := max (g δ a - g δ s) 0

noncomputable def gPrimitive (δ a : ℝ) : ℝ :=
  a ^ 2 / 4 + (δ - 1) * a ^ 3 / 12 - δ * a ^ 5 / 60

noncomputable def gSquarePrimitive (δ a : ℝ) : ℝ :=
  a ^ 3 / 12 + (δ - 1) * a ^ 4 / 16 + (δ - 1) ^ 2 * a ^ 5 / 80
    - δ * a ^ 6 / 72 - (δ - 1) * δ * a ^ 7 / 168 + δ ^ 2 * a ^ 9 / 1296

theorem continuous_g (δ : ℝ) : Continuous (g δ) := by
  unfold g
  fun_prop

theorem continuous_epsilon (δ : ℝ) : Continuous (epsilon δ) := by
  unfold epsilon
  fun_prop

theorem continuous_residual (δ a : ℝ) : Continuous (residual δ a) :=
  ((continuous_const.sub (continuous_g δ)).max continuous_const)

theorem hasDerivAt_g (δ s : ℝ) :
    HasDerivAt (g δ) (1 / 2 + (δ - 1) * s / 2 - δ * s ^ 3 / 3) s := by
  convert (((hasDerivAt_id s).div_const 2).add
    (((hasDerivAt_id s).pow 2).const_mul (δ - 1) |>.div_const 4)).sub
    (((hasDerivAt_id s).pow 4).const_mul δ |>.div_const 12) using 1
  dsimp only [g, id_eq]
  ring

theorem hasDerivAt_epsilon (δ a : ℝ) :
    HasDerivAt (epsilon δ)
      (2 * a * (1 / 2 + (δ - 1) * a / 2 - δ * a ^ 3 / 3)) a := by
  convert ((((hasDerivAt_id a).pow 2).div_const 2).add
    (((hasDerivAt_id a).pow 3).const_mul (δ - 1) |>.div_const 3)).sub
    (((hasDerivAt_id a).pow 5).const_mul (2 * δ) |>.div_const 15) using 1
  dsimp only [epsilon, id_eq]
  ring

theorem g_derivative_pos {δ s : ℝ} (hδ : 0 < δ) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < 1 / 2 + (δ - 1) * s / 2 - δ * s ^ 3 / 3 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2, mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hs3 : s ^ 3 ≤ s := by nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs2)]
  have hmul := mul_le_mul_of_nonneg_left hs3 hδ.le
  by_cases hz : s = 0
  · subst s
    norm_num
  · have hpos : 0 < δ * s := mul_pos hδ (lt_of_le_of_ne hs.1 (Ne.symm hz))
    nlinarith [hs.2]

theorem strictMonoOn_g {δ : ℝ} (hδ : 0 < δ) :
    StrictMonoOn (g δ) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (continuous_g δ).continuousOn
  intro s hs
  rw [(hasDerivAt_g δ s).deriv]
  exact g_derivative_pos hδ (interior_subset hs)

theorem strictMonoOn_epsilon {δ : ℝ} (hδ : 0 < δ) :
    StrictMonoOn (epsilon δ) (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (continuous_epsilon δ).continuousOn
  intro s hs
  have hsi : s ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hs
  rw [(hasDerivAt_epsilon δ s).deriv]
  exact mul_pos (mul_pos (by norm_num) hsi.1)
    (g_derivative_pos hδ ⟨hsi.1.le, hsi.2.le⟩)

theorem epsilon_zero (δ : ℝ) : epsilon δ 0 = 0 := by simp [epsilon]

theorem epsilon_one (δ : ℝ) : epsilon δ 1 = 1 / 6 + δ / 5 := by
  unfold epsilon
  ring

theorem cap_inversion {δ z : ℝ} (hδ : 0 < δ)
    (hz : z ∈ Icc (0 : ℝ) (1 / 6 + δ / 5)) :
    ∃! a, a ∈ Icc (0 : ℝ) 1 ∧ epsilon δ a = z := by
  have hz' : z ∈ Icc (epsilon δ 0) (epsilon δ 1) := by
    simpa only [epsilon_zero, epsilon_one] using hz
  obtain ⟨a, ha, hea⟩ := (continuous_epsilon δ).continuousOn.surjOn_Icc
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hz'
  refine ⟨a, ⟨ha, hea⟩, ?_⟩
  intro b hb
  exact (strictMonoOn_epsilon hδ).injOn hb.1 ha (hb.2.trans hea.symm)

theorem capped_cap_inversion {δ c C₀ : ℝ} (hδ : 0 < δ) (hc : C₀ ≤ c) :
    ∃! a, a ∈ Icc (0 : ℝ) 1 ∧
      epsilon δ a = min (c - C₀) (1 / 6 + δ / 5) := by
  apply cap_inversion hδ
  exact ⟨le_min (sub_nonneg.mpr hc) (by positivity), min_le_right _ _⟩

theorem hasDerivAt_gPrimitive (δ a : ℝ) :
    HasDerivAt (gPrimitive δ) (g δ a) a := by
  convert ((((hasDerivAt_id a).pow 2).div_const 4).add
    (((hasDerivAt_id a).pow 3).const_mul (δ - 1) |>.div_const 12)).sub
    (((hasDerivAt_id a).pow 5).const_mul δ |>.div_const 60) using 1
  dsimp only [gPrimitive, g, id_eq]
  ring

theorem hasDerivAt_gSquarePrimitive (δ a : ℝ) :
    HasDerivAt (gSquarePrimitive δ) ((g δ a) ^ 2) a := by
  convert (((((((hasDerivAt_id a).pow 3).div_const 12).add
    (((hasDerivAt_id a).pow 4).const_mul (δ - 1) |>.div_const 16)).add
    (((hasDerivAt_id a).pow 5).const_mul ((δ - 1) ^ 2) |>.div_const 80)).sub
    (((hasDerivAt_id a).pow 6).const_mul δ |>.div_const 72)).sub
    (((hasDerivAt_id a).pow 7).const_mul ((δ - 1) * δ) |>.div_const 168)).add
    (((hasDerivAt_id a).pow 9).const_mul (δ ^ 2) |>.div_const 1296) using 1
  dsimp only [gSquarePrimitive, g, id_eq]
  ring

theorem integral_g (δ a : ℝ) : ∫ s in (0 : ℝ)..a, g δ s = gPrimitive δ a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_gPrimitive δ s) ((continuous_g δ).intervalIntegrable 0 a)]
  simp [gPrimitive]

theorem integral_g_square (δ a : ℝ) :
    ∫ s in (0 : ℝ)..a, (g δ s) ^ 2 = gSquarePrimitive δ a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_gSquarePrimitive δ s)
    (((continuous_g δ).pow 2).intervalIntegrable 0 a)]
  simp [gSquarePrimitive]

theorem residual_nonneg (δ a s : ℝ) : 0 ≤ residual δ a s := le_max_right _ _

theorem residual_active {δ a s : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) a) :
    residual δ a s = g δ a - g δ s := by
  apply max_eq_left
  exact sub_nonneg.mpr ((strictMonoOn_g hδ).monotoneOn ⟨hs.1, hs.2.trans ha.2⟩ ha hs.2)

theorem residual_inactive {δ a s : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc a (1 : ℝ)) :
    residual δ a s = 0 := by
  apply max_eq_right
  exact sub_nonpos.mpr ((strictMonoOn_g hδ).monotoneOn ha ⟨ha.1.trans hs.1, hs.2⟩ hs.1)

theorem residual_at_one {δ a : ℝ} (hδ : 0 < δ) (ha : a ∈ Icc (0 : ℝ) 1) :
    residual δ a 1 = 0 := residual_inactive hδ ha ⟨ha.2, le_rfl⟩

theorem integral_residual {δ a : ℝ} (hδ : 0 < δ) (ha : a ∈ Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..1, residual δ a s = epsilon δ a / 2 := by
  have hleft : ∫ s in (0 : ℝ)..a, residual δ a s = a * g δ a - gPrimitive δ a := by
    rw [intervalIntegral.integral_congr (g := fun s => g δ a - g δ s)
      (fun s hs => residual_active hδ ha (by simpa only [uIcc_of_le ha.1] using hs))]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 a)
      ((continuous_g δ).intervalIntegrable 0 a), intervalIntegral.integral_const, integral_g]
    simp
  have hright : ∫ s in a..(1 : ℝ), residual δ a s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
      (fun s hs => residual_inactive hδ ha (by simpa only [uIcc_of_le ha.2] using hs))]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_residual δ a).intervalIntegrable 0 a) ((continuous_residual δ a).intervalIntegrable a 1),
    hleft, hright]
  unfold g gPrimitive epsilon
  ring

theorem integral_residual_square {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, (residual δ a s) ^ 2) =
      a * (g δ a) ^ 2 - 2 * g δ a * gPrimitive δ a + gSquarePrimitive δ a := by
  have hd (s : ℝ) :
      HasDerivAt (fun t => t * (g δ a) ^ 2 - 2 * g δ a * gPrimitive δ t +
        gSquarePrimitive δ t) ((g δ a - g δ s) ^ 2) s := by
    convert (((hasDerivAt_id s).mul_const ((g δ a) ^ 2)).sub
      ((hasDerivAt_gPrimitive δ s).const_mul (2 * g δ a))).add
      (hasDerivAt_gSquarePrimitive δ s) using 1
    ring
  have hleft : (∫ s in (0 : ℝ)..a, (residual δ a s) ^ 2) =
      a * (g δ a) ^ 2 - 2 * g δ a * gPrimitive δ a + gSquarePrimitive δ a := by
    rw [intervalIntegral.integral_congr (g := fun s => (g δ a - g δ s) ^ 2)
      (fun s hs => congrArg (fun x : ℝ => x ^ 2)
        (residual_active hδ ha (by simpa only [uIcc_of_le ha.1] using hs)))]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (((continuous_const.sub (continuous_g δ)).pow 2).intervalIntegrable 0 a)]
    simp [gPrimitive, gSquarePrimitive]
  have hright : (∫ s in a..(1 : ℝ), (residual δ a s) ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro s hs
      dsimp only
      rw [residual_inactive hδ ha (by simpa only [uIcc_of_le ha.2] using hs)]
      norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (((continuous_residual δ a).pow 2).intervalIntegrable 0 a)
    (((continuous_residual δ a).pow 2).intervalIntegrable a 1), hleft, hright, add_zero]

theorem integral_g_mul_residual {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, g δ s * residual δ a s) =
      g δ a * gPrimitive δ a - gSquarePrimitive δ a := by
  have hd (s : ℝ) :
      HasDerivAt (fun t => g δ a * gPrimitive δ t - gSquarePrimitive δ t)
        (g δ s * (g δ a - g δ s)) s := by
    convert ((hasDerivAt_gPrimitive δ s).const_mul (g δ a)).sub
      (hasDerivAt_gSquarePrimitive δ s) using 1
    ring
  have hleft : (∫ s in (0 : ℝ)..a, g δ s * residual δ a s) =
      g δ a * gPrimitive δ a - gSquarePrimitive δ a := by
    rw [intervalIntegral.integral_congr (g := fun s => g δ s * (g δ a - g δ s))
      (fun s hs => congrArg (fun x : ℝ => g δ s * x)
        (residual_active hδ ha (by simpa only [uIcc_of_le ha.1] using hs)))]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (((continuous_g δ).mul (continuous_const.sub (continuous_g δ))).intervalIntegrable 0 a)]
    simp [gPrimitive, gSquarePrimitive]
  have hright : (∫ s in a..(1 : ℝ), g δ s * residual δ a s) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro s hs
      dsimp only
      rw [residual_inactive hδ ha (by simpa only [uIcc_of_le ha.2] using hs), mul_zero]
  have hc : Continuous (fun s => g δ s * residual δ a s) :=
    (continuous_g δ).mul (continuous_residual δ a)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a 1),
    hleft, hright, add_zero]

noncomputable def unitInterval : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance unitInterval_isProbabilityMeasure : IsProbabilityMeasure unitInterval where
  measure_univ := by simp [unitInterval, Real.volume_Icc]

theorem integral_unitInterval_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ s, f s ∂unitInterval) = ∫ s in (0 : ℝ)..1, f s := by
  unfold unitInterval
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem integrable_unitInterval_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f unitInterval := hf.continuousOn.integrableOn_Icc

theorem integrable_g (δ : ℝ) : Integrable (g δ) unitInterval :=
  integrable_unitInterval_of_continuous (continuous_g δ)

theorem integrable_residual (δ a : ℝ) : Integrable (residual δ a) unitInterval :=
  integrable_unitInterval_of_continuous (continuous_residual δ a)

theorem integrable_residual_square (δ a : ℝ) :
    Integrable (fun s => (residual δ a s) ^ 2) unitInterval :=
  integrable_unitInterval_of_continuous ((continuous_residual δ a).pow 2)

theorem integrable_g_mul_residual (δ a : ℝ) :
    Integrable (fun s => g δ s * residual δ a s) unitInterval :=
  integrable_unitInterval_of_continuous ((continuous_g δ).mul (continuous_residual δ a))

theorem integral_residual_unitInterval {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ s, residual δ a s ∂unitInterval) = epsilon δ a / 2 := by
  rw [integral_unitInterval_eq_intervalIntegral]
  exact integral_residual hδ ha

theorem integral_residual_square_unitInterval {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ s, (residual δ a s) ^ 2 ∂unitInterval) =
      a * (g δ a) ^ 2 - 2 * g δ a * gPrimitive δ a + gSquarePrimitive δ a := by
  rw [integral_unitInterval_eq_intervalIntegral]
  exact integral_residual_square hδ ha

theorem integral_g_mul_residual_unitInterval {δ a : ℝ} (hδ : 0 < δ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ s, g δ s * residual δ a s ∂unitInterval) =
      g δ a * gPrimitive δ a - gSquarePrimitive δ a := by
  rw [integral_unitInterval_eq_intervalIntegral]
  exact integral_g_mul_residual hδ ha

theorem integral_g_unitInterval (δ : ℝ) :
    (∫ s, g δ s ∂unitInterval) = 1 / 6 + δ / 15 := by
  rw [integral_unitInterval_eq_intervalIntegral, integral_g]
  unfold gPrimitive
  ring

theorem integral_g_square_unitInterval (δ : ℝ) :
    (∫ s, (g δ s) ^ 2 ∂unitInterval) =
      1 / 30 + 149 * δ / 5040 + 83 * δ ^ 2 / 11340 := by
  rw [integral_unitInterval_eq_intervalIntegral, integral_g_square]
  unfold gSquarePrimitive
  ring

end Research.I3.ObstacleProfile
