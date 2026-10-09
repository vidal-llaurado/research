import Research.I3.Containment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# I3: minimum reserve and rigidity under an actual pricing measure

This file combines whole-class containment with Bochner integration. The price
is the integral of the actual payoff, not an abstract scalar-price proxy.
A minimum of the two-put price curve is assumed, as in the manuscript's local
assumption; its extension to the entire additive class is proved. With a unique
strike minimizer, equality forces the financed payoff to agree almost surely.
-/

open MeasureTheory

namespace Research.I3

/-- Cost of the actual additive payoff against the one fixed basket liability. -/
noncomputable def additiveReserve {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (X Y : Ω → ℝ) (K : ℝ) (a d : ℝ → ℝ) : ℝ :=
  (∫ ω, a (X ω) + d (Y ω) ∂Q) - (∫ ω, basketPut K (X ω) (Y ω) ∂Q)

/-- Cost of the protected two-put book under the same pricing law. -/
noncomputable def twoPutReserve {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (X Y : Ω → ℝ) (K k : ℝ) : ℝ :=
  (∫ ω, twoPut K k (X ω) (Y ω) ∂Q) - (∫ ω, basketPut K (X ω) (Y ω) ∂Q)

/-- Terminal surplus after its actual expectation financing. -/
noncomputable def additiveFinancedPayoff {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (X Y : Ω → ℝ) (K : ℝ) (a d : ℝ → ℝ) (ω : Ω) : ℝ :=
  a (X ω) + d (Y ω) - basketPut K (X ω) (Y ω) - additiveReserve Q X Y K a d

lemma integrable_put_of_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X : Ω → ℝ} (hX : Measurable X)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun ω => put k (X ω)) Q := by
  have hm : Measurable (fun ω => put k (X ω)) :=
    (measurable_const.sub hX).max measurable_const
  apply (integrable_const k).mono' hm.aestronglyMeasurable
  filter_upwards [hX₀] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (put_nonneg k (X ω))]
  exact put_le_strike hk hω

lemma integrable_twoPut {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) :
    Integrable (fun ω => twoPut K k (X ω) (Y ω)) Q :=
  (integrable_put_of_nonnegative Q hX hX₀ hk).add
    (integrable_put_of_nonnegative Q hY hY₀ (sub_nonneg.mpr hkK))

/-- Genuine full-class cost domination, with no assumption about a competitor's
relation to the two-put family. Containment constructs the strike. -/
theorem additiveReserve_dominates_twoPutReserve {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K : ℝ} (hK : 0 ≤ K) {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    ∃ k : ℝ, 0 ≤ k ∧ k ≤ K ∧
      twoPutReserve Q X Y K k ≤ additiveReserve Q X Y K a d := by
  obtain ⟨k, hk, hkK, hdom⟩ := protected_additive_contains_twoPut hK hA
  refine ⟨k, hk, hkK, ?_⟩
  have hle : ∀ᵐ ω ∂Q, twoPut K k (X ω) (Y ω) ≤ a (X ω) + d (Y ω) := by
    filter_upwards [hX₀, hY₀] with ω hx hy
    exact hdom (X ω) (Y ω) hx hy
  have hi := integral_mono_ae (integrable_twoPut Q hX hY hX₀ hY₀ hk hkK) hInt hle
  exact sub_le_sub_right hi _

/-- Every lower bound of the admissible two-put costs also lower-bounds the
whole globally protected additive class. -/
theorem minimumReserve_full_additive {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k₀ : ℝ} (hK : 0 ≤ K)
    (hmin : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k₀ ≤ twoPutReserve Q X Y K k)
    {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    twoPutReserve Q X Y K k₀ ≤ additiveReserve Q X Y K a d := by
  obtain ⟨k, hk, hkK, hcost⟩ :=
    additiveReserve_dominates_twoPutReserve Q hX hY hX₀ hY₀ hK hA hInt
  exact le_trans (hmin k hk hkK) hcost

/-- The minimum is attained by the actual admissible two-put payoff, so the
full-class lower bound is sharp, not merely a lower bound. -/
theorem twoPut_attains_full_class_minimum {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k₀ : ℝ} (hk₀ : 0 ≤ k₀) (hk₀K : k₀ ≤ K)
    (hmin : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k₀ ≤ twoPutReserve Q X Y K k) :
    GloballyProtects K (put k₀) (put (K - k₀)) ∧
    Integrable (fun ω => twoPut K k₀ (X ω) (Y ω)) Q ∧
    ∀ a d : ℝ → ℝ, GloballyProtects K a d →
      Integrable (fun ω => a (X ω) + d (Y ω)) Q →
      twoPutReserve Q X Y K k₀ ≤ additiveReserve Q X Y K a d := by
  refine ⟨?_, integrable_twoPut Q hX hY hX₀ hY₀ hk₀ hk₀K, ?_⟩
  · intro x y _ _
    exact basket_le_twoPut K k₀ x y
  · intro a d hA hInt
    exact minimumReserve_full_additive Q hX hY hX₀ hY₀ (le_trans hk₀ hk₀K) hmin hA hInt

/-- A minimum-cost competitor globally contains the unique minimizing
two-put book; this pointwise fact does not restrict the global state domain. -/
theorem minimumReserve_contains_minimizer {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k₀ : ℝ} (hK : 0 ≤ K)
    (hmin : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k₀ ≤ twoPutReserve Q X Y K k)
    (hunique : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k = twoPutReserve Q X Y K k₀ → k = k₀)
    {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q)
    (hcost : additiveReserve Q X Y K a d = twoPutReserve Q X Y K k₀) :
    0 ≤ k₀ ∧ k₀ ≤ K ∧
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → twoPut K k₀ x y ≤ a x + d y := by
  obtain ⟨k, hk, hkK, hdom⟩ := protected_additive_contains_twoPut hK hA
  have hGI := integrable_twoPut Q hX hY hX₀ hY₀ hk hkK
  have hle : ∀ᵐ ω ∂Q, twoPut K k (X ω) (Y ω) ≤ a (X ω) + d (Y ω) := by
    filter_upwards [hX₀, hY₀] with ω hx hy
    exact hdom (X ω) (Y ω) hx hy
  have hi := integral_mono_ae hGI hInt hle
  have hC : twoPutReserve Q X Y K k ≤ additiveReserve Q X Y K a d :=
    sub_le_sub_right hi _
  have hEq : twoPutReserve Q X Y K k = twoPutReserve Q X Y K k₀ := by
    rw [hcost] at hC
    exact le_antisymm hC (hmin k hk hkK)
  have hkk := hunique k hk hkK hEq
  subst k
  exact ⟨hk, hkK, hdom⟩

/-- Under the manuscript's unique strike minimum assumption, no other
minimum-cost protected additive book has a different Q-almost-sure payoff. -/
theorem minimumReserve_payoff_rigidity {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k₀ : ℝ} (hK : 0 ≤ K)
    (hmin : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k₀ ≤ twoPutReserve Q X Y K k)
    (hunique : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k = twoPutReserve Q X Y K k₀ → k = k₀)
    {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q)
    (hcost : additiveReserve Q X Y K a d = twoPutReserve Q X Y K k₀) :
    ∀ᵐ ω ∂Q, additiveFinancedPayoff Q X Y K a d ω =
      surplus K k₀ (X ω) (Y ω) - twoPutReserve Q X Y K k₀ := by
  obtain ⟨hk₀, hk₀K, hdom⟩ :=
    minimumReserve_contains_minimizer Q hX hY hX₀ hY₀ hK hmin hunique hA hInt hcost
  have hGI := integrable_twoPut Q hX hY hX₀ hY₀ hk₀ hk₀K
  have hle : ∀ᵐ ω ∂Q, twoPut K k₀ (X ω) (Y ω) ≤ a (X ω) + d (Y ω) := by
    filter_upwards [hX₀, hY₀] with ω hx hy
    exact hdom (X ω) (Y ω) hx hy
  have hprices : (∫ ω, twoPut K k₀ (X ω) (Y ω) ∂Q) =
      ∫ ω, a (X ω) + d (Y ω) ∂Q := by
    unfold additiveReserve twoPutReserve at hcost
    linarith
  have hae := (integral_eq_iff_of_ae_le hGI hInt hle).mp hprices
  filter_upwards [hae] with ω hω
  unfold additiveFinancedPayoff surplus
  rw [hcost, ← hω]

/-- Equality of an actual marginal pushforward transfers coordinate integrals. -/
lemma integral_comp_eq_of_map_eq {Ω : Type*} [MeasurableSpace Ω]
    {P Q : Measure Ω} {X : Ω → ℝ} (hX : Measurable X)
    (hmap : Measure.map X P = Measure.map X Q)
    {a : ℝ → ℝ} (ha : Measurable a) :
    (∫ ω, a (X ω) ∂P) = ∫ ω, a (X ω) ∂Q := by
  calc
    (∫ ω, a (X ω) ∂P) = ∫ x, a x ∂Measure.map X P :=
      (integral_map hX.aemeasurable ha.aestronglyMeasurable).symm
    _ = ∫ x, a x ∂Measure.map X Q := by rw [hmap]
    _ = ∫ ω, a (X ω) ∂Q := integral_map hX.aemeasurable ha.aestronglyMeasurable

/-- Coordinate integrability is also transferred by genuine marginal equality. -/
lemma integrable_comp_of_map_eq {Ω : Type*} [MeasurableSpace Ω]
    {P Q : Measure Ω} {X : Ω → ℝ} (hX : Measurable X)
    (hmap : Measure.map X P = Measure.map X Q)
    {a : ℝ → ℝ} (ha : Measurable a)
    (hInt : Integrable (fun ω => a (X ω)) Q) :
    Integrable (fun ω => a (X ω)) P := by
  have hQ : Integrable a (Measure.map X Q) :=
    (integrable_map_measure ha.aestronglyMeasurable hX.aemeasurable).mpr hInt
  have hP : Integrable a (Measure.map X P) := by rw [hmap]; exact hQ
  exact hP.comp_measurable hX

/-- The entire additive payoff has equal P and Q means under matching labeled
marginals. Equality of the joint laws is not assumed. -/
theorem additive_mean_of_matching_marginals {Ω : Type*} [MeasurableSpace Ω]
    {P Q : Measure Ω} {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hmapX : Measure.map X P = Measure.map X Q)
    (hmapY : Measure.map Y P = Measure.map Y Q)
    {a d : ℝ → ℝ} (ha : Measurable a) (hd : Measurable d)
    (haQ : Integrable (fun ω => a (X ω)) Q)
    (hdQ : Integrable (fun ω => d (Y ω)) Q) :
    (∫ ω, a (X ω) + d (Y ω) ∂P) = ∫ ω, a (X ω) + d (Y ω) ∂Q := by
  have haP := integrable_comp_of_map_eq hX hmapX ha haQ
  have hdP := integrable_comp_of_map_eq hY hmapY hd hdQ
  rw [integral_add haP hdP, integral_add haQ hdQ,
    integral_comp_eq_of_map_eq hX hmapX ha,
    integral_comp_eq_of_map_eq hY hmapY hd]

/-- Minimum-reserve rigidity holds under the physical law as well as Q, using
actual equality of labeled marginal measures, even if the joint laws differ. -/
theorem minimumReserve_physical_payoff_rigidity {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXP : ∀ᵐ ω ∂P, 0 ≤ X ω) (hYP : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hXQ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hYQ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    (hmapX : Measure.map X P = Measure.map X Q)
    (hmapY : Measure.map Y P = Measure.map Y Q)
    {K k₀ : ℝ} (hK : 0 ≤ K)
    (hmin : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k₀ ≤ twoPutReserve Q X Y K k)
    (hunique : ∀ k : ℝ, 0 ≤ k → k ≤ K →
      twoPutReserve Q X Y K k = twoPutReserve Q X Y K k₀ → k = k₀)
    {a d : ℝ → ℝ} (ha : Measurable a) (hd : Measurable d)
    (hA : GloballyProtects K a d)
    (haQ : Integrable (fun ω => a (X ω)) Q)
    (hdQ : Integrable (fun ω => d (Y ω)) Q)
    (hcost : additiveReserve Q X Y K a d = twoPutReserve Q X Y K k₀) :
    ∀ᵐ ω ∂P, additiveFinancedPayoff Q X Y K a d ω =
      surplus K k₀ (X ω) (Y ω) - twoPutReserve Q X Y K k₀ := by
  obtain ⟨hk₀, hk₀K, hdom⟩ :=
    minimumReserve_contains_minimizer Q hX hY hXQ hYQ hK hmin hunique hA
      (haQ.add hdQ) hcost
  have haP := integrable_comp_of_map_eq hX hmapX ha haQ
  have hdP := integrable_comp_of_map_eq hY hmapY hd hdQ
  have hmeanA := additive_mean_of_matching_marginals hX hY hmapX hmapY ha hd haQ hdQ
  have hmk (k : ℝ) : Measurable (put k) :=
    (measurable_const.sub measurable_id).max measurable_const
  have hmeanG := additive_mean_of_matching_marginals hX hY hmapX hmapY
    (hmk k₀) (hmk (K - k₀))
    (integrable_put_of_nonnegative Q hX hXQ hk₀)
    (integrable_put_of_nonnegative Q hY hYQ (sub_nonneg.mpr hk₀K))
  have hpricesQ : (∫ ω, twoPut K k₀ (X ω) (Y ω) ∂Q) =
      ∫ ω, a (X ω) + d (Y ω) ∂Q := by
    unfold additiveReserve twoPutReserve at hcost
    linarith
  have hpricesP : (∫ ω, twoPut K k₀ (X ω) (Y ω) ∂P) =
      ∫ ω, a (X ω) + d (Y ω) ∂P := by
    change (∫ ω, put k₀ (X ω) + put (K - k₀) (Y ω) ∂P) = _
    rw [hmeanG]
    exact hpricesQ.trans hmeanA.symm
  have hle : ∀ᵐ ω ∂P, twoPut K k₀ (X ω) (Y ω) ≤ a (X ω) + d (Y ω) := by
    filter_upwards [hXP, hYP] with ω hx hy
    exact hdom (X ω) (Y ω) hx hy
  have hae := (integral_eq_iff_of_ae_le
    (integrable_twoPut P hX hY hXP hYP hk₀ hk₀K) (haP.add hdP) hle).mp hpricesP
  filter_upwards [hae] with ω hω
  change twoPut K k₀ (X ω) (Y ω) = a (X ω) + d (Y ω) at hω
  unfold additiveFinancedPayoff surplus
  rw [hcost, ← hω]

lemma integrable_basketPut {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K : ℝ} (hK : 0 ≤ K) :
    Integrable (fun ω => basketPut K (X ω) (Y ω)) Q := by
  apply integrable_put_of_nonnegative Q (hX.add hY) _ hK
  filter_upwards [hX₀, hY₀] with ω hx hy
  exact add_nonneg hx hy

/-- I3's fixed unit mean is an identity for actual P and Q integrals. The
liability price and financed payoff are also certified integrable. -/
theorem underwriting_mean_fixed_by_basket_laws {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXP : ∀ᵐ ω ∂P, 0 ≤ X ω) (hYP : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hXQ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hYQ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    (hmapX : Measure.map X P = Measure.map X Q)
    (hmapY : Measure.map Y P = Measure.map Y Q)
    {K : ℝ} (hK : 0 ≤ K) {a d : ℝ → ℝ} (ha : Measurable a) (hd : Measurable d)
    (haQ : Integrable (fun ω => a (X ω)) Q)
    (hdQ : Integrable (fun ω => d (Y ω)) Q) :
    Integrable (fun ω => basketPut K (X ω) (Y ω)) Q ∧
    Integrable (additiveFinancedPayoff Q X Y K a d) P ∧
    (∫ ω, additiveFinancedPayoff Q X Y K a d ω ∂P) =
      (∫ ω, basketPut K (X ω) (Y ω) ∂Q) - (∫ ω, basketPut K (X ω) (Y ω) ∂P) := by
  have haP := integrable_comp_of_map_eq hX hmapX ha haQ
  have hdP := integrable_comp_of_map_eq hY hmapY hd hdQ
  have hBP := integrable_basketPut P hX hY hXP hYP hK
  have hBQ := integrable_basketPut Q hX hY hXQ hYQ hK
  have hAP : Integrable (fun ω => a (X ω) + d (Y ω)) P := haP.add hdP
  have hSP : Integrable (fun ω => a (X ω) + d (Y ω) - basketPut K (X ω) (Y ω)) P :=
    hAP.sub hBP
  have hfin : Integrable (additiveFinancedPayoff Q X Y K a d) P :=
    (hAP.sub hBP).sub (integrable_const _)
  refine ⟨hBQ, hfin, ?_⟩
  change (∫ ω, (a (X ω) + d (Y ω) - basketPut K (X ω) (Y ω)) -
    additiveReserve Q X Y K a d ∂P) = _
  rw [integral_sub hSP (integrable_const _), integral_sub hAP hBP]
  have hC : (∫ _ : Ω, additiveReserve Q X Y K a d ∂P) =
      additiveReserve Q X Y K a d := by simp
  rw [hC, additive_mean_of_matching_marginals hX hY hmapX hmapY ha hd haQ hdQ]
  unfold additiveReserve
  ring

/-- The actual financing debit of a globally protected integrable book is
nonnegative under a nonnegative-state pricing law. -/
theorem additiveReserve_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K : ℝ} (hK : 0 ≤ K) {a d : ℝ → ℝ} (hA : GloballyProtects K a d)
    (hInt : Integrable (fun ω => a (X ω) + d (Y ω)) Q) :
    0 ≤ additiveReserve Q X Y K a d := by
  apply sub_nonneg.mpr
  apply integral_mono_ae (integrable_basketPut Q hX hY hX₀ hY₀ hK) hInt
  filter_upwards [hX₀, hY₀] with ω hx hy
  exact hA (X ω) (Y ω) hx hy

/-- The actual two-put expectation debit is nonnegative and is exactly the
maximum terminal loss on the whole nonnegative quadrant. The origin attains
the floor even when it is outside the support of the pricing law. -/
theorem twoPutReserve_exact_global_terminal_floor {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX₀ : ∀ᵐ ω ∂Q, 0 ≤ X ω) (hY₀ : ∀ᵐ ω ∂Q, 0 ≤ Y ω)
    {K k : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) :
    0 ≤ twoPutReserve Q X Y K k ∧
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      -twoPutReserve Q X Y K k ≤ surplus K k x y - twoPutReserve Q X Y K k) ∧
    surplus K k 0 0 - twoPutReserve Q X Y K k = -twoPutReserve Q X Y K k := by
  have hA : GloballyProtects K (put k) (put (K - k)) := by
    intro x y _ _
    exact basket_le_twoPut K k x y
  have hC := additiveReserve_nonnegative Q hX hY hX₀ hY₀ (le_trans hk hkK) hA
    (integrable_twoPut Q hX hY hX₀ hY₀ hk hkK)
  exact ⟨hC, twoPut_exact_terminal_floor hk hkK (twoPutReserve Q X Y K k)⟩

end Research.I3
