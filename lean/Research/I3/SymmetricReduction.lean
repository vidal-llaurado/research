import Research.I3.MinimumReserve

/-!
# I3: global payoff symmetrization

The state space for protection remains the entire nonnegative quadrant.
Reflection is implemented on the model square by an explicit globally protected
extension. The four-transform average has a common nonnegative even residual.
The measure-theoretic statements below state their invariance hypotheses
explicitly; the polynomial experiment's density identities are separate.
-/

open MeasureTheory

namespace Research.I3.Symmetry

def residualBook (k : ℝ) (r₁ r₂ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  twoPut 2 k x y + r₁ x + r₂ y

noncomputable def reflectedResidual (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) 2 then r (2 - x) else 0

noncomputable def reflectedBook (k : ℝ) (r₁ r₂ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  residualBook (2 - k) (reflectedResidual r₁) (reflectedResidual r₂) x y

lemma put_reflection (k x : ℝ) :
    put (2 - k) x = put k (2 - x) + (2 - k - x) := by
  unfold put
  by_cases h : 0 ≤ 2 - k - x
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

lemma reflectedResidual_nonnegative {r : ℝ → ℝ}
    (hr : ∀ x : ℝ, 0 ≤ x → 0 ≤ r x) (x : ℝ) :
    0 ≤ reflectedResidual r x := by
  unfold reflectedResidual
  split_ifs with hx
  · exact hr (2 - x) (sub_nonneg.mpr hx.2)
  · exact le_refl 0

theorem residualBook_protects (k : ℝ) {r₁ r₂ : ℝ → ℝ}
    (h₁ : ∀ x : ℝ, 0 ≤ x → 0 ≤ r₁ x)
    (h₂ : ∀ y : ℝ, 0 ≤ y → 0 ≤ r₂ y) :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → basketPut 2 x y ≤ residualBook k r₁ r₂ x y := by
  intro x y hx hy
  have h := basket_le_twoPut 2 k x y
  dsimp [residualBook]
  linarith [h₁ x hx, h₂ y hy]

theorem reflectedBook_protects (k : ℝ) {r₁ r₂ : ℝ → ℝ}
    (h₁ : ∀ x : ℝ, 0 ≤ x → 0 ≤ r₁ x)
    (h₂ : ∀ y : ℝ, 0 ≤ y → 0 ≤ r₂ y) :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → basketPut 2 x y ≤ reflectedBook k r₁ r₂ x y := by
  exact residualBook_protects (2 - k)
    (fun x _ => reflectedResidual_nonnegative h₁ x)
    (fun y _ => reflectedResidual_nonnegative h₂ y)

theorem reflectedBook_on_square (k : ℝ) (r₁ r₂ : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    reflectedBook k r₁ r₂ x y = residualBook k r₁ r₂ (2 - x) (2 - y) + 2 - x - y := by
  simp only [reflectedBook, residualBook, reflectedResidual, if_pos hx, if_pos hy,
    twoPut]
  rw [put_reflection k x]
  have hk : 2 - (2 - k) = k := by ring
  rw [hk]
  have hp := put_reflection (2 - k) y
  rw [hk] at hp
  rw [hp]
  ring

lemma basket_reflection (x y : ℝ) :
    basketPut 2 x y = basketPut 2 (2 - x) (2 - y) + 2 - x - y := by
  unfold basketPut put
  by_cases h : 0 ≤ 2 - (x + y)
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

theorem reflected_surplus_on_square (k : ℝ) (r₁ r₂ : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    reflectedBook k r₁ r₂ x y - basketPut 2 x y =
      residualBook k r₁ r₂ (2 - x) (2 - y) - basketPut 2 (2 - x) (2 - y) := by
  rw [reflectedBook_on_square k r₁ r₂ hx hy, basket_reflection x y]
  ring

noncomputable def fourAverage (k : ℝ) (r₁ r₂ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (residualBook k r₁ r₂ x y + residualBook k r₁ r₂ y x +
    reflectedBook k r₁ r₂ x y + reflectedBook k r₁ r₂ y x) / 4

lemma symmetric_put_gap (k x : ℝ) :
    (put k x + put (2 - k) x) / 2 =
      put 1 x + max (|k - 1| - |x - 1|) 0 / 2 := by
  simp only [put, abs_eq_max_neg, max_def]
  split_ifs <;> linarith

noncomputable def radialResidual (k : ℝ) (r₁ r₂ : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ∈ Set.Icc (0 : ℝ) 1 then
    max (|k - 1| - s) 0 / 2 +
      (r₁ (1 + s) + r₂ (1 + s) + r₁ (1 - s) + r₂ (1 - s)) / 4
  else 0

theorem radialResidual_nonnegative (k : ℝ) {r₁ r₂ : ℝ → ℝ}
    (h₁ : ∀ x : ℝ, 0 ≤ x → 0 ≤ r₁ x)
    (h₂ : ∀ y : ℝ, 0 ≤ y → 0 ≤ r₂ y) (s : ℝ) :
    0 ≤ radialResidual k r₁ r₂ s := by
  unfold radialResidual
  split_ifs with hs
  · have hmax := le_max_right (|k - 1| - s) 0
    have hplus : 0 ≤ 1 + s := by linarith [hs.1]
    have hminus : 0 ≤ 1 - s := by linarith [hs.2]
    linarith [h₁ (1 + s) hplus, h₂ (1 + s) hplus,
      h₁ (1 - s) hminus, h₂ (1 - s) hminus]
  · exact le_refl 0

lemma radialResidual_outside (k : ℝ) (r₁ r₂ : ℝ → ℝ) {s : ℝ}
    (hs : s ∉ Set.Icc (0 : ℝ) 1) : radialResidual k r₁ r₂ s = 0 := by
  simp only [radialResidual, if_neg hs]

lemma absolute_center_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    |x - 1| ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

lemma radialResidual_on_square (k : ℝ) (r₁ r₂ : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    radialResidual k r₁ r₂ |x - 1| = max (|k - 1| - |x - 1|) 0 / 2 +
      (r₁ x + r₂ x + r₁ (2 - x) + r₂ (2 - x)) / 4 := by
  rw [radialResidual, if_pos (absolute_center_mem hx)]
  by_cases h : 0 ≤ x - 1
  · rw [abs_of_nonneg h]
    have heq : 1 + (x - 1) = x := by ring
    have heq' : 1 - (x - 1) = 2 - x := by ring
    rw [heq, heq']
  · rw [abs_of_nonpos (show x - 1 ≤ 0 by linarith)]
    have heq : 1 + -(x - 1) = 2 - x := by ring
    have heq' : 1 - -(x - 1) = x := by ring
    rw [heq, heq']
    ring

noncomputable def radialBook (k : ℝ) (r₁ r₂ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  twoPut 2 1 x y + radialResidual k r₁ r₂ |x - 1| + radialResidual k r₁ r₂ |y - 1|

theorem fourAverage_radial_on_square (k : ℝ) (r₁ r₂ : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    fourAverage k r₁ r₂ x y = radialBook k r₁ r₂ x y := by
  have hp₁ := symmetric_put_gap k x
  have hp₂ := symmetric_put_gap k y
  simp only [fourAverage, reflectedBook, residualBook, reflectedResidual,
    if_pos hx, if_pos hy, twoPut] at *
  simp only [radialBook, twoPut, radialResidual_on_square k r₁ r₂ hx,
    radialResidual_on_square k r₁ r₂ hy]
  have hk : (2 : ℝ) - (2 - k) = k := by ring
  rw [hk]
  norm_num
  linarith

theorem radialBook_protects (k : ℝ) {r₁ r₂ : ℝ → ℝ}
    (h₁ : ∀ x : ℝ, 0 ≤ x → 0 ≤ r₁ x)
    (h₂ : ∀ y : ℝ, 0 ≤ y → 0 ≤ r₂ y) :
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → basketPut 2 x y ≤ radialBook k r₁ r₂ x y := by
  intro x y _ _
  have h := basket_le_twoPut 2 1 x y
  dsimp [radialBook]
  linarith [radialResidual_nonnegative k h₁ h₂ |x - 1|,
    radialResidual_nonnegative k h₁ h₂ |y - 1|]

theorem radialBook_swap (k : ℝ) (r₁ r₂ : ℝ → ℝ) (x y : ℝ) :
    radialBook k r₁ r₂ y x = radialBook k r₁ r₂ x y := by
  unfold radialBook twoPut
  norm_num
  ring

def swapState (z : ℝ × ℝ) : ℝ × ℝ := (z.2, z.1)

def reflectState (z : ℝ × ℝ) : ℝ × ℝ := (2 - z.1, 2 - z.2)

lemma swapState_measurable : Measurable swapState :=
  measurable_snd.prodMk measurable_fst

lemma reflectState_measurable : Measurable reflectState :=
  (measurable_const.sub measurable_fst).prodMk (measurable_const.sub measurable_snd)

noncomputable def orbitAverage (f : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) : ℝ :=
  (f z + f (swapState z) + f (reflectState z) + f (reflectState (swapState z))) / 4

lemma orbitAverage_measurable {f : (ℝ × ℝ) → ℝ} (hf : Measurable f) :
    Measurable (orbitAverage f) :=
  (((hf.add (hf.comp swapState_measurable)).add (hf.comp reflectState_measurable)).add
    (hf.comp (reflectState_measurable.comp swapState_measurable))).div_const 4

lemma preserving_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Measurable f) :
    (∫ ω, f (T ω) ∂μ) = ∫ ω, f ω ∂μ := by
  calc
    (∫ ω, f (T ω) ∂μ) = ∫ ω, f ω ∂Measure.map T μ :=
      (integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ ω, f ω ∂μ := by rw [hT.map_eq]

lemma orbitAverage_integrable (μ : Measure (ℝ × ℝ))
    (hs : MeasurePreserving swapState μ μ) (hr : MeasurePreserving reflectState μ μ)
    {f : (ℝ × ℝ) → ℝ} (hI : Integrable f μ) : Integrable (orbitAverage f) μ := by
  exact (((hI.add (hs.integrable_comp_of_integrable hI)).add
    (hr.integrable_comp_of_integrable hI)).add
    ((hr.comp hs).integrable_comp_of_integrable hI)).div_const 4

theorem orbitAverage_integral (μ : Measure (ℝ × ℝ))
    (hs : MeasurePreserving swapState μ μ) (hr : MeasurePreserving reflectState μ μ)
    {f : (ℝ × ℝ) → ℝ} (hf : Measurable f) (hI : Integrable f μ) :
    (∫ z, orbitAverage f z ∂μ) = ∫ z, f z ∂μ := by
  have hIs := hs.integrable_comp_of_integrable hI
  have hIr := hr.integrable_comp_of_integrable hI
  have hIrs := (hr.comp hs).integrable_comp_of_integrable hI
  have ha₁ := integral_add hI hIs
  have ha₂ := integral_add (hI.add hIs) hIr
  have ha₃ := integral_add ((hI.add hIs).add hIr) hIrs
  simp only [Pi.add_apply, Function.comp_apply] at ha₁ ha₂ ha₃
  unfold orbitAverage
  rw [integral_div, ha₃, ha₂, ha₁,
    preserving_integral μ hs hf, preserving_integral μ hr hf]
  have heq := preserving_integral μ (hr.comp hs) hf
  simp only [Function.comp_apply] at heq
  rw [heq]
  ring

lemma four_mean_square (a b c d : ℝ) :
    ((a + b + c + d) / 4) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

lemma orbitAverage_square_le (f : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) :
    (orbitAverage f z) ^ 2 ≤ orbitAverage (fun w => (f w) ^ 2) z :=
  four_mean_square _ _ _ _

lemma orbitAverage_square_integrable (μ : Measure (ℝ × ℝ))
    (hs : MeasurePreserving swapState μ μ) (hr : MeasurePreserving reflectState μ μ)
    {f : (ℝ × ℝ) → ℝ} (hf : Measurable f)
    (hI : Integrable (fun z => (f z) ^ 2) μ) :
    Integrable (fun z => (orbitAverage f z) ^ 2) μ := by
  apply (orbitAverage_integrable μ hs hr hI).mono'
    ((orbitAverage_measurable hf).pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact orbitAverage_square_le f z

/-- Convex risk reduction is proved for actual Bochner second moments.
The two invariances are assumptions on the measure, not on the desired risk. -/
theorem orbitAverage_second_moment_le (μ : Measure (ℝ × ℝ))
    (hs : MeasurePreserving swapState μ μ) (hr : MeasurePreserving reflectState μ μ)
    {f : (ℝ × ℝ) → ℝ} (hf : Measurable f)
    (hI : Integrable (fun z => (f z) ^ 2) μ) :
    (∫ z, (orbitAverage f z) ^ 2 ∂μ) ≤ ∫ z, (f z) ^ 2 ∂μ := by
  calc
    (∫ z, (orbitAverage f z) ^ 2 ∂μ) ≤ ∫ z, orbitAverage (fun w => (f w) ^ 2) z ∂μ :=
      integral_mono (orbitAverage_square_integrable μ hs hr hf hI)
        (orbitAverage_integrable μ hs hr hI) (orbitAverage_square_le f)
    _ = ∫ z, (f z) ^ 2 ∂μ := orbitAverage_integral μ hs hr (hf.pow_const 2) hI

lemma orbitAverage_sub_const (f : (ℝ × ℝ) → ℝ) (c : ℝ) (z : ℝ × ℝ) :
    orbitAverage (fun w => f w - c) z = orbitAverage f z - c := by
  unfold orbitAverage
  ring

def bookSurplus (A : ℝ → ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  A z.1 z.2 - basketPut 2 z.1 z.2

noncomputable def bookReserve (Q : Measure (ℝ × ℝ)) (A : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z, bookSurplus A z ∂Q

noncomputable def financedRisk (P Q : Measure (ℝ × ℝ)) (A : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z, (bookSurplus A z - bookReserve Q A) ^ 2 ∂P

lemma bookReserve_eq_additiveReserve (Q : Measure (ℝ × ℝ)) (a d : ℝ → ℝ)
    (hA : Integrable (fun z : ℝ × ℝ => a z.1 + d z.2) Q)
    (hB : Integrable (fun z : ℝ × ℝ => basketPut 2 z.1 z.2) Q) :
    bookReserve Q (fun x y => a x + d y) = additiveReserve Q Prod.fst Prod.snd 2 a d := by
  exact integral_sub hA hB

lemma bookSurplus_radial_on_square (k : ℝ) (r₁ r₂ : ℝ → ℝ) {z : ℝ × ℝ}
    (hx : z.1 ∈ Set.Icc (0 : ℝ) 2) (hy : z.2 ∈ Set.Icc (0 : ℝ) 2) :
    bookSurplus (radialBook k r₁ r₂) z =
      orbitAverage (bookSurplus (residualBook k r₁ r₂)) z := by
  have ha := fourAverage_radial_on_square k r₁ r₂ hx hy
  have hb := reflected_surplus_on_square k r₁ r₂ hx hy
  have hc := reflected_surplus_on_square k r₁ r₂ hy hx
  have hswap : basketPut 2 z.2 z.1 = basketPut 2 z.1 z.2 := by
    simp only [basketPut, add_comm]
  have hswap' : basketPut 2 (2 - z.2) (2 - z.1) =
      basketPut 2 (2 - z.1) (2 - z.2) := by simp only [basketPut, add_comm]
  simp only [bookSurplus, orbitAverage, swapState, reflectState, fourAverage,
    hswap, hswap'] at *
  linarith

/-- The square is only the support of the pricing law; the resulting book's
protection continues to hold on the entire nonnegative quadrant. -/
theorem radialBook_reserve_eq (Q : Measure (ℝ × ℝ))
    (hs : MeasurePreserving swapState Q Q) (hr : MeasurePreserving reflectState Q Q)
    (hSquare : ∀ᵐ z ∂Q, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (k : ℝ) (r₁ r₂ : ℝ → ℝ)
    (hm : Measurable (bookSurplus (residualBook k r₁ r₂)))
    (hI : Integrable (bookSurplus (residualBook k r₁ r₂)) Q) :
    bookReserve Q (radialBook k r₁ r₂) = bookReserve Q (residualBook k r₁ r₂) := by
  unfold bookReserve
  calc
    (∫ z, bookSurplus (radialBook k r₁ r₂) z ∂Q) =
        ∫ z, orbitAverage (bookSurplus (residualBook k r₁ r₂)) z ∂Q := by
      apply integral_congr_ae
      filter_upwards [hSquare] with z hz
      exact bookSurplus_radial_on_square k r₁ r₂ hz.1 hz.2
    _ = ∫ z, bookSurplus (residualBook k r₁ r₂) z ∂Q :=
      orbitAverage_integral Q hs hr hm hI

lemma radialBook_surplus_integrable (Q : Measure (ℝ × ℝ))
    (hs : MeasurePreserving swapState Q Q) (hr : MeasurePreserving reflectState Q Q)
    (hSquare : ∀ᵐ z ∂Q, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (k : ℝ) (r₁ r₂ : ℝ → ℝ)
    (hI : Integrable (bookSurplus (residualBook k r₁ r₂)) Q) :
    Integrable (bookSurplus (radialBook k r₁ r₂)) Q := by
  apply (orbitAverage_integrable Q hs hr hI).congr
  filter_upwards [hSquare] with z hz
  exact (bookSurplus_radial_on_square k r₁ r₂ hz.1 hz.2).symm

lemma radialBook_financed_square_integrable (P Q : Measure (ℝ × ℝ))
    (hQs : MeasurePreserving swapState Q Q) (hQr : MeasurePreserving reflectState Q Q)
    (hPs : MeasurePreserving swapState P P) (hPr : MeasurePreserving reflectState P P)
    (hQSquare : ∀ᵐ z ∂Q, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (hPSquare : ∀ᵐ z ∂P, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (k : ℝ) (r₁ r₂ : ℝ → ℝ)
    (hm : Measurable (bookSurplus (residualBook k r₁ r₂)))
    (hQI : Integrable (bookSurplus (residualBook k r₁ r₂)) Q)
    (hPI : Integrable (fun z => (bookSurplus (residualBook k r₁ r₂) z -
      bookReserve Q (residualBook k r₁ r₂)) ^ 2) P) :
    Integrable (fun z => (bookSurplus (radialBook k r₁ r₂) z -
      bookReserve Q (radialBook k r₁ r₂)) ^ 2) P := by
  have hc := radialBook_reserve_eq Q hQs hQr hQSquare k r₁ r₂ hm hQI
  rw [hc]
  apply (orbitAverage_square_integrable P hPs hPr (hm.sub measurable_const) hPI).congr
  filter_upwards [hPSquare] with z hz
  rw [orbitAverage_sub_const, bookSurplus_radial_on_square k r₁ r₂ hz.1 hz.2]

/-- Price preservation and physical-risk contraction for the actual globally
extended radial payoff. Q and P may differ, and both sets of invariance and
support hypotheses remain visible in the statement. -/
theorem radialBook_financedRisk_le (P Q : Measure (ℝ × ℝ))
    (hQs : MeasurePreserving swapState Q Q) (hQr : MeasurePreserving reflectState Q Q)
    (hPs : MeasurePreserving swapState P P) (hPr : MeasurePreserving reflectState P P)
    (hQSquare : ∀ᵐ z ∂Q, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (hPSquare : ∀ᵐ z ∂P, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (k : ℝ) (r₁ r₂ : ℝ → ℝ)
    (hm : Measurable (bookSurplus (residualBook k r₁ r₂)))
    (hQI : Integrable (bookSurplus (residualBook k r₁ r₂)) Q)
    (hPI : Integrable (fun z => (bookSurplus (residualBook k r₁ r₂) z -
      bookReserve Q (residualBook k r₁ r₂)) ^ 2) P) :
    financedRisk P Q (radialBook k r₁ r₂) ≤ financedRisk P Q (residualBook k r₁ r₂) := by
  have hc := radialBook_reserve_eq Q hQs hQr hQSquare k r₁ r₂ hm hQI
  unfold financedRisk
  rw [hc]
  calc
    (∫ z, (bookSurplus (radialBook k r₁ r₂) z -
        bookReserve Q (residualBook k r₁ r₂)) ^ 2 ∂P) =
        ∫ z, (orbitAverage (fun w => bookSurplus (residualBook k r₁ r₂) w -
          bookReserve Q (residualBook k r₁ r₂)) z) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hPSquare] with z hz
      rw [orbitAverage_sub_const, bookSurplus_radial_on_square k r₁ r₂ hz.1 hz.2]
    _ ≤ ∫ z, (bookSurplus (residualBook k r₁ r₂) z -
        bookReserve Q (residualBook k r₁ r₂)) ^ 2 ∂P :=
      orbitAverage_second_moment_le P hPs hPr (hm.sub measurable_const) hPI

lemma put_measurable (k : ℝ) : Measurable (put k) :=
  (measurable_const.sub measurable_id).max measurable_const

lemma residuals_measurable_of_decomposition (k : ℝ) {a d r₁ r₂ : ℝ → ℝ}
    (ha : Measurable a) (hd : Measurable d)
    (hrep : ∀ x y : ℝ, a x + d y = twoPut 2 k x y + r₁ x + r₂ y) :
    Measurable r₁ ∧ Measurable r₂ := by
  have heq₁ : r₁ = fun x => a x + d 0 - (put k x + put (2 - k) 0) - r₂ 0 := by
    funext x
    have h := hrep x 0
    unfold twoPut at h
    linarith
  have heq₂ : r₂ = fun y => a 0 + d y - (put k 0 + put (2 - k) y) - r₁ 0 := by
    funext y
    have h := hrep 0 y
    unfold twoPut at h
    linarith
  constructor
  · rw [heq₁]
    exact ((ha.add measurable_const).sub ((put_measurable k).add measurable_const)).sub
      measurable_const
  · rw [heq₂]
    exact ((measurable_const.add hd).sub (measurable_const.add
      (put_measurable (2 - k)))).sub measurable_const

lemma radialResidual_measurable (k : ℝ) {r₁ r₂ : ℝ → ℝ}
    (h₁ : Measurable r₁) (h₂ : Measurable r₂) :
    Measurable (radialResidual k r₁ r₂) := by
  apply Measurable.ite measurableSet_Icc ?_ measurable_const
  exact (((measurable_const.sub measurable_id).max measurable_const).div_const 2).add
    (((((h₁.comp (measurable_const.add measurable_id)).add
      (h₂.comp (measurable_const.add measurable_id))).add
      (h₁.comp (measurable_const.sub measurable_id))).add
      (h₂.comp (measurable_const.sub measurable_id))).div_const 4)

def radialComponent (r : ℝ → ℝ) (x : ℝ) : ℝ := put 1 x + r |x - 1|

lemma radialComponent_measurable {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable (radialComponent r) :=
  (put_measurable 1).add (hr.comp
    (continuous_abs.measurable.comp (measurable_id.sub measurable_const)))

lemma radialBook_components (k : ℝ) (r₁ r₂ : ℝ → ℝ) :
    (fun x y => radialComponent (radialResidual k r₁ r₂) x +
      radialComponent (radialResidual k r₁ r₂) y) = radialBook k r₁ r₂ := by
  funext x y
  simp only [radialComponent, radialBook, twoPut]
  norm_num
  ring

lemma additiveSurplus_measurable {a d : ℝ → ℝ} (ha : Measurable a) (hd : Measurable d) :
    Measurable (bookSurplus (fun x y => a x + d y)) :=
  ((ha.comp measurable_fst).add (hd.comp measurable_snd)).sub
    ((put_measurable 2).comp (measurable_fst.add measurable_snd))

/-- A full-class competitor is reduced to a finite Borel radial residual,
with the same actual price, no larger actual financed second moment, and
protection on every nonnegative state. The concrete experiment must supply
the explicitly visible measure invariances and support hypotheses. -/
theorem protected_additive_has_radial_improvement (P Q : Measure (ℝ × ℝ))
    (hQs : MeasurePreserving swapState Q Q) (hQr : MeasurePreserving reflectState Q Q)
    (hPs : MeasurePreserving swapState P P) (hPr : MeasurePreserving reflectState P P)
    (hQSquare : ∀ᵐ z ∂Q, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    (hPSquare : ∀ᵐ z ∂P, z.1 ∈ Set.Icc (0 : ℝ) 2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 2)
    {a d : ℝ → ℝ} (ha : Measurable a) (hd : Measurable d)
    (hA : GloballyProtects 2 a d)
    (hQI : Integrable (bookSurplus (fun x y => a x + d y)) Q)
    (hPI : Integrable (fun z => (bookSurplus (fun x y => a x + d y) z -
      bookReserve Q (fun x y => a x + d y)) ^ 2) P) :
    ∃ r : ℝ → ℝ, Measurable r ∧ (∀ s : ℝ, 0 ≤ r s) ∧
      (∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) 1 → r s = 0) ∧
      GloballyProtects 2 (radialComponent r) (radialComponent r) ∧
      Integrable (bookSurplus (fun x y => radialComponent r x + radialComponent r y)) Q ∧
      Integrable (fun z => (bookSurplus (fun x y => radialComponent r x + radialComponent r y) z -
        bookReserve Q (fun x y => radialComponent r x + radialComponent r y)) ^ 2) P ∧
      bookReserve Q (fun x y => radialComponent r x + radialComponent r y) =
        bookReserve Q (fun x y => a x + d y) ∧
      financedRisk P Q (fun x y => radialComponent r x + radialComponent r y) ≤
        financedRisk P Q (fun x y => a x + d y) := by
  obtain ⟨k, r₁, r₂, _, _, h₁, h₂, hrep⟩ :=
    protected_additive_nonnegative_residual (show (0 : ℝ) ≤ 2 by norm_num) hA
  have hbooks : (fun x y => a x + d y) = residualBook k r₁ r₂ := by
    funext x y
    exact hrep x y
  obtain ⟨hm₁, hm₂⟩ := residuals_measurable_of_decomposition k ha hd hrep
  have hm := additiveSurplus_measurable ha hd
  rw [hbooks] at hm hQI hPI ⊢
  refine ⟨radialResidual k r₁ r₂, radialResidual_measurable k hm₁ hm₂,
    radialResidual_nonnegative k h₁ h₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact radialResidual_outside k r₁ r₂ hs
  · intro x y hx hy
    have h := radialBook_protects k h₁ h₂ x y hx hy
    rw [← radialBook_components k r₁ r₂] at h
    exact h
  · rw [radialBook_components]
    exact radialBook_surplus_integrable Q hQs hQr hQSquare k r₁ r₂ hQI
  · rw [radialBook_components]
    exact radialBook_financed_square_integrable P Q hQs hQr hPs hPr hQSquare hPSquare
      k r₁ r₂ hm hQI hPI
  · rw [radialBook_components]
    exact radialBook_reserve_eq Q hQs hQr hQSquare k r₁ r₂ hm hQI
  · rw [radialBook_components]
    exact radialBook_financedRisk_le P Q hQs hQr hPs hPr hQSquare hPSquare
      k r₁ r₂ hm hQI hPI

end Research.I3.Symmetry
