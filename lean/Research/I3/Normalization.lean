import Research.I3.MinimumReserve

/-!
# I3: exact reserve normalization on the full nonnegative quadrant

Formalizes the normalization paragraph following the accounting identities.
The cash adjustment is the actual infimum of all global surplus values; no
minimizing state is assumed. Prices are Bochner expectations under a probability
law. Removing this cash preserves the financed payoff and gives the exact
worst-case terminal loss, with an infimum that may be unattained.
-/

open MeasureTheory

namespace Research.I3

/-- Values on the complete solvency domain, independently of probability support. -/
def quadrantValues (f : ℝ → ℝ → ℝ) : Set ℝ :=
  {v | ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ f x y = v}

noncomputable def quadrantInfimum (f : ℝ → ℝ → ℝ) : ℝ := sInf (quadrantValues f)

/-- The unfinanced surplus of the actual additive payoff. -/
def additiveSurplus (K : ℝ) (a d : ℝ → ℝ) (x y : ℝ) : ℝ :=
  a x + d y - basketPut K x y

/-- Cash removed from a globally protected book. -/
noncomputable def normalizationCash (K : ℝ) (a d : ℝ → ℝ) : ℝ :=
  quadrantInfimum (additiveSurplus K a d)

/-- Cash is subtracted from the first coordinate component only. -/
noncomputable def normalizedFirst (K : ℝ) (a d : ℝ → ℝ) (x : ℝ) : ℝ :=
  a x - normalizationCash K a d

lemma normalizedFirst_measurable {K : ℝ} {a d : ℝ → ℝ} (ha : Measurable a) :
    Measurable (normalizedFirst K a d) := ha.sub measurable_const

lemma normalizedFirst_integrable {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (X : Ω → ℝ) (K : ℝ) (a d : ℝ → ℝ)
    (ha : Integrable (fun ω => a (X ω)) Q) :
    Integrable (fun ω => normalizedFirst K a d (X ω)) Q :=
  ha.sub (integrable_const _)

lemma quadrantValues_nonempty (f : ℝ → ℝ → ℝ) : (quadrantValues f).Nonempty :=
  ⟨f 0 0, 0, 0, le_refl 0, le_refl 0, rfl⟩

lemma quadrantInfimum_le {f : ℝ → ℝ → ℝ} (hf : BddBelow (quadrantValues f))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : quadrantInfimum f ≤ f x y :=
  csInf_le hf ⟨x, y, hx, hy, rfl⟩

lemma le_quadrantInfimum {f : ℝ → ℝ → ℝ} {c : ℝ}
    (hc : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → c ≤ f x y) : c ≤ quadrantInfimum f := by
  apply le_csInf (quadrantValues_nonempty f)
  rintro v ⟨x, y, hx, hy, rfl⟩
  exact hc x y hx hy

lemma quadrantValues_sub_const_bddBelow {f : ℝ → ℝ → ℝ}
    (hf : BddBelow (quadrantValues f)) (c : ℝ) :
    BddBelow (quadrantValues (fun x y => f x y - c)) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨m - c, ?_⟩
  rintro v ⟨x, y, hx, hy, rfl⟩
  exact sub_le_sub_right (hm ⟨x, y, hx, hy, rfl⟩) c

/-- Translation of the genuine global infimum; no minimizing state is required. -/
lemma quadrantInfimum_sub_const {f : ℝ → ℝ → ℝ}
    (hf : BddBelow (quadrantValues f)) (c : ℝ) :
    quadrantInfimum (fun x y => f x y - c) = quadrantInfimum f - c := by
  have hb := quadrantValues_sub_const_bddBelow hf c
  have hlo : quadrantInfimum f - c ≤ quadrantInfimum (fun x y => f x y - c) := by
    apply le_quadrantInfimum
    intro x y hx hy
    exact sub_le_sub_right (quadrantInfimum_le hf hx hy) c
  have hhi : quadrantInfimum (fun x y => f x y - c) + c ≤ quadrantInfimum f := by
    apply le_quadrantInfimum
    intro x y hx hy
    have h := quadrantInfimum_le hb hx hy
    linarith
  exact le_antisymm (by linarith) hlo

lemma additiveSurplus_bddBelow {K : ℝ} {a d : ℝ → ℝ}
    (hA : GloballyProtects K a d) : BddBelow (quadrantValues (additiveSurplus K a d)) := by
  refine ⟨0, ?_⟩
  rintro v ⟨x, y, hx, hy, rfl⟩
  exact sub_nonneg.mpr (hA x y hx hy)

/-- The normalization cash is a finite real, is nonnegative, and does not
exceed any global surplus value. -/
theorem normalizationCash_bounds {K : ℝ} {a d : ℝ → ℝ}
    (hA : GloballyProtects K a d) :
    0 ≤ normalizationCash K a d ∧
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → normalizationCash K a d ≤ additiveSurplus K a d x y := by
  constructor
  · apply le_quadrantInfimum
    intro x y hx hy
    exact sub_nonneg.mpr (hA x y hx hy)
  · intro x y hx hy
    exact quadrantInfimum_le (additiveSurplus_bddBelow hA) hx hy

/-- Removing the actual infimum preserves the floor at every nonnegative state. -/
theorem normalizedFirst_protects {K : ℝ} {a d : ℝ → ℝ}
    (hA : GloballyProtects K a d) : GloballyProtects K (normalizedFirst K a d) d := by
  intro x y hx hy
  have h := (normalizationCash_bounds hA).2 x y hx hy
  unfold normalizedFirst additiveSurplus at *
  linarith

/-- The normalized surplus has infimum zero, without asserting attainment. -/
theorem normalized_surplus_infimum_zero {K : ℝ} {a d : ℝ → ℝ}
    (hA : GloballyProtects K a d) :
    quadrantInfimum (additiveSurplus K (normalizedFirst K a d) d) = 0 := by
  have heq : additiveSurplus K (normalizedFirst K a d) d =
      fun x y => additiveSurplus K a d x y - normalizationCash K a d := by
    funext x y
    unfold additiveSurplus normalizedFirst
    ring
  rw [heq, quadrantInfimum_sub_const (additiveSurplus_bddBelow hA)]
  exact sub_self _

/-- Actual expectation financing changes by exactly the cash withdrawn. -/
theorem normalized_reserve_identity {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : Ω → ℝ) (K : ℝ) (a d : ℝ → ℝ)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    Integrable (fun ω => normalizedFirst K a d (X ω) + d (Y ω)) Q ∧
    additiveReserve Q X Y K (normalizedFirst K a d) d =
      additiveReserve Q X Y K a d - normalizationCash K a d := by
  have heq : (fun ω => normalizedFirst K a d (X ω) + d (Y ω)) =
      fun ω => a (X ω) + d (Y ω) - normalizationCash K a d := by
    funext ω
    unfold normalizedFirst
    ring
  constructor
  · rw [heq]
    exact hInt.sub (integrable_const _)
  · unfold additiveReserve
    rw [heq, integral_sub hInt (integrable_const _)]
    have hc : (∫ _ : Ω, normalizationCash K a d ∂Q) = normalizationCash K a d := by simp
    rw [hc]
    ring

/-- The financed state value is preserved on the entire global domain, including
states not visited by the random coordinates. -/
theorem normalization_preserves_financed_state_value {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : Ω → ℝ) (K : ℝ) (a d : ℝ → ℝ)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) (x y : ℝ) :
    additiveSurplus K (normalizedFirst K a d) d x y -
      additiveReserve Q X Y K (normalizedFirst K a d) d =
    additiveSurplus K a d x y - additiveReserve Q X Y K a d := by
  rw [(normalized_reserve_identity Q X Y K a d hInt).2]
  unfold additiveSurplus normalizedFirst
  ring

/-- Normalization preserves the financed random payoff identically. -/
theorem normalization_preserves_financed_payoff {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : Ω → ℝ) (K : ℝ) (a d : ℝ → ℝ)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) (ω : Ω) :
    additiveFinancedPayoff Q X Y K (normalizedFirst K a d) d ω =
      additiveFinancedPayoff Q X Y K a d ω := by
  exact normalization_preserves_financed_state_value Q X Y K a d hInt (X ω) (Y ω)

/-- The normalized expectation debit is the negative of the original global
financed-payoff infimum; the infimum need not be attained. -/
theorem normalized_reserve_exact_global_loss {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : Ω → ℝ)
    {K : ℝ} {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    quadrantInfimum (fun x y => additiveSurplus K a d x y - additiveReserve Q X Y K a d) =
      -additiveReserve Q X Y K (normalizedFirst K a d) d := by
  rw [quadrantInfimum_sub_const (additiveSurplus_bddBelow hA)]
  have hc := (normalized_reserve_identity Q X Y K a d hInt).2
  change normalizationCash K a d - additiveReserve Q X Y K a d = _
  rw [hc]
  ring

/-- The exact lower bound is expressed as a greatest lower bound of the actual
state-value set, rather than an assumed attained worst state. -/
theorem normalized_reserve_isGLB {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : Ω → ℝ)
    {K : ℝ} {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    IsGLB (quadrantValues (fun x y => additiveSurplus K a d x y - additiveReserve Q X Y K a d))
      (-additiveReserve Q X Y K (normalizedFirst K a d) d) := by
  have hglb := isGLB_csInf
    (quadrantValues_nonempty (fun x y => additiveSurplus K a d x y - additiveReserve Q X Y K a d))
    (quadrantValues_sub_const_bddBelow (additiveSurplus_bddBelow hA) (additiveReserve Q X Y K a d))
  change IsGLB _ (quadrantInfimum _) at hglb
  rw [normalized_reserve_exact_global_loss Q X Y hA hInt] at hglb
  exact hglb

/-- The normalized book itself has the same exact global financed lower bound. -/
theorem normalized_book_isGLB {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : Ω → ℝ)
    {K : ℝ} {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    IsGLB (quadrantValues (fun x y => additiveSurplus K (normalizedFirst K a d) d x y -
      additiveReserve Q X Y K (normalizedFirst K a d) d))
      (-additiveReserve Q X Y K (normalizedFirst K a d) d) := by
  have heq : (fun x y => additiveSurplus K (normalizedFirst K a d) d x y -
      additiveReserve Q X Y K (normalizedFirst K a d) d) =
      fun x y => additiveSurplus K a d x y - additiveReserve Q X Y K a d := by
    funext x y
    exact normalization_preserves_financed_state_value Q X Y K a d hInt x y
  rw [heq]
  exact normalized_reserve_isGLB Q X Y hA hInt

/-- The normalized book's genuine debit remains nonnegative and cannot exceed
the original debit. Thus subtracting the infimum never impairs a reserve cap. -/
theorem normalization_improves_reserve_cap {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K : ℝ} (hK : 0 ≤ K) {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    0 ≤ additiveReserve Q X Y K (normalizedFirst K a d) d ∧
    additiveReserve Q X Y K (normalizedFirst K a d) d ≤ additiveReserve Q X Y K a d := by
  obtain ⟨hNI, hNC⟩ := normalized_reserve_identity Q X Y K a d hInt
  constructor
  · exact additiveReserve_nonnegative Q hX hY hX₀ hY₀ hK (normalizedFirst_protects hA) hNI
  · rw [hNC]
    exact sub_le_self _ (normalizationCash_bounds hA).1

/-- The two-put price minimum lower-bounds the exact global terminal loss of
every protected additive book, including books initially carrying unused cash. -/
theorem minimumReserve_full_terminal_loss {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k₀ : ℝ} (hK : 0 ≤ K)
    (hmin : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k₀ ≤ twoPutReserve Q X Y K k)
    {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    twoPutReserve Q X Y K k₀ ≤
      -quadrantInfimum (fun x y => additiveSurplus K a d x y - additiveReserve Q X Y K a d) := by
  have hN := minimumReserve_full_additive Q hX hY hX₀ hY₀ hK hmin
    (normalizedFirst_protects hA) (normalized_reserve_identity Q X Y K a d hInt).1
  rw [normalized_reserve_exact_global_loss Q X Y hA hInt, neg_neg]
  exact hN

end Research.I3
