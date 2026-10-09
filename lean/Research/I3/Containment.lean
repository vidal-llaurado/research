import Research.I3.Protection
import Mathlib.Data.Real.Archimedean

/-!
# I3: containment of the whole protected additive class

Formalizes the pointwise content of Lemma `lem:containment` of the manuscript.
The components are arbitrary finite real functions on the entire nonnegative
quadrant. No continuity, attainment of an infimum, pricing law, support
restriction, or finite option representation is assumed.
-/

namespace Research.I3

/-- The global basket floor imposed on the full additive class. -/
def GloballyProtects (K : ℝ) (a d : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → basketPut K x y ≤ a x + d y

/-- Infimum over the actual nonnegative state domain. Boundedness is proved
before the corresponding upper-bound property is used. -/
noncomputable def lowerEnvelope (f : ℝ → ℝ) : ℝ := sInf (f '' Set.Ici 0)

lemma nonnegative_image_nonempty (f : ℝ → ℝ) :
    (f '' Set.Ici 0).Nonempty := ⟨f 0, ⟨(0 : ℝ), by simp, rfl⟩⟩

lemma lowerEnvelope_le {f : ℝ → ℝ} (hf : BddBelow (f '' Set.Ici 0))
    {x : ℝ} (hx : 0 ≤ x) : lowerEnvelope f ≤ f x :=
  csInf_le hf ⟨x, hx, rfl⟩

lemma le_lowerEnvelope {f : ℝ → ℝ} {c : ℝ}
    (hc : ∀ x : ℝ, 0 ≤ x → c ≤ f x) : c ≤ lowerEnvelope f := by
  apply le_csInf (nonnegative_image_nonempty f)
  rintro _ ⟨x, hx, rfl⟩
  exact hc x hx

/-- Separated infima without requiring either minimum to be attained. -/
lemma le_add_lowerEnvelope {f g : ℝ → ℝ} {c : ℝ}
    (hc : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → c ≤ f x + g y) :
    c ≤ lowerEnvelope f + lowerEnvelope g := by
  have h : ∀ x : ℝ, 0 ≤ x → c - lowerEnvelope g ≤ f x := by
    intro x hx
    have hg : c - f x ≤ lowerEnvelope g := by
      apply le_lowerEnvelope
      intro y hy
      have hxy := hc x y hx hy
      linarith
    linarith
  have hf := le_lowerEnvelope h
  linarith

lemma component_bddBelow {K : ℝ} {a d : ℝ → ℝ}
    (hA : GloballyProtects K a d) :
    BddBelow (a '' Set.Ici 0) ∧ BddBelow (d '' Set.Ici 0) := by
  constructor
  · refine ⟨-d 0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h := hA x 0 hx (le_refl 0)
    have hB := put_nonneg K (x + 0)
    unfold basketPut at h
    linarith
  · refine ⟨-a 0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h := hA 0 y (le_refl 0) hy
    have hB := put_nonneg K (0 + y)
    unfold basketPut at h
    linarith

lemma put_mono_strike {k l : ℝ} (hkl : k ≤ l) (x : ℝ) : put k x ≤ put l x := by
  unfold put
  exact max_le_max (sub_le_sub_right hkl x) (le_refl 0)

lemma put_strike_increment {z : ℝ} (hz : 0 ≤ z) (k x : ℝ) :
    put (k + z) x ≤ put k x + z := by
  unfold put
  apply max_le
  · have h := le_max_left (k - x) 0
    linarith
  · exact add_nonneg (le_max_right _ _) hz

/-- Every globally protected additive payoff contains a protected two-put
book with admissible strikes, on the complete nonnegative quadrant. -/
theorem protected_additive_contains_twoPut {K : ℝ} (hK : 0 ≤ K)
    {a d : ℝ → ℝ} (hA : GloballyProtects K a d) :
    ∃ k : ℝ, 0 ≤ k ∧ k ≤ K ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → twoPut K k x y ≤ a x + d y := by
  let a₀ := lowerEnvelope a
  let d₀ := lowerEnvelope d
  let M := a₀ + d₀
  let f : ℝ → ℝ := fun x => a x - a₀ + x
  let g : ℝ → ℝ := fun y => d y - d₀ + y
  let c₁ := lowerEnvelope f
  let c₂ := lowerEnvelope g
  obtain ⟨ha, hd⟩ := component_bddBelow hA
  have ha₀ (x : ℝ) (hx : 0 ≤ x) : a₀ ≤ a x := lowerEnvelope_le ha hx
  have hd₀ (y : ℝ) (hy : 0 ≤ y) : d₀ ≤ d y := lowerEnvelope_le hd hy
  have hf (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
    dsimp [f]
    linarith [ha₀ x hx]
  have hg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ g y := by
    dsimp [g]
    linarith [hd₀ y hy]
  have hfb : BddBelow (f '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  have hgb : BddBelow (g '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hg y hy
  have hc₁ : 0 ≤ c₁ := le_lowerEnvelope hf
  have hc₂ : 0 ≤ c₂ := le_lowerEnvelope hg
  have hM : 0 ≤ M := by
    apply le_add_lowerEnvelope
    intro x y hx hy
    exact le_trans (put_nonneg K (x + y)) (hA x y hx hy)
  have hsum : K ≤ M + c₁ + c₂ := by
    have h : K - M ≤ c₁ + c₂ := by
      apply le_add_lowerEnvelope
      intro x y hx hy
      have hfloor := hA x y hx hy
      have hB : K - (x + y) ≤ basketPut K x y := le_max_left _ _
      dsimp [f, g, M]
      linarith
    linarith
  have hput₁ (x : ℝ) (hx : 0 ≤ x) : put c₁ x ≤ a x - a₀ := by
    have hc : c₁ ≤ f x := lowerEnvelope_le hfb hx
    unfold put
    apply max_le
    · dsimp [f] at hc
      linarith
    · linarith [ha₀ x hx]
  have hput₂ (y : ℝ) (hy : 0 ≤ y) : put c₂ y ≤ d y - d₀ := by
    have hc : c₂ ≤ g y := lowerEnvelope_le hgb hy
    unfold put
    apply max_le
    · dsimp [g] at hc
      linarith
    · linarith [hd₀ y hy]
  by_cases hlarge : K ≤ c₁ + c₂
  · let k := min c₁ K
    have hk : 0 ≤ k := le_min hc₁ hK
    have hkK : k ≤ K := min_le_right _ _
    have hkc₁ : k ≤ c₁ := min_le_left _ _
    have hkc₂ : K - k ≤ c₂ := by
      dsimp [k]
      rcases le_total c₁ K with h | h
      · rw [min_eq_left h]
        linarith
      · rw [min_eq_right h]
        simpa using hc₂
    refine ⟨k, hk, hkK, ?_⟩
    intro x y hx hy
    have hp₁ := le_trans (put_mono_strike hkc₁ x) (hput₁ x hx)
    have hp₂ := le_trans (put_mono_strike hkc₂ y) (hput₂ y hy)
    dsimp [twoPut]
    dsimp [M] at hM
    linarith
  · let z := K - c₁ - c₂
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have hzM : z ≤ M := by dsimp [z]; linarith
    have hk : 0 ≤ K - c₂ := by linarith
    have hkK : K - c₂ ≤ K := by linarith
    refine ⟨K - c₂, hk, hkK, ?_⟩
    intro x y hx hy
    have hkz : K - c₂ = c₁ + z := by dsimp [z]; ring
    have hp₁ : put (K - c₂) x ≤ put c₁ x + z := by
      rw [hkz]
      exact put_strike_increment hz c₁ x
    have hp₂ := hput₂ y hy
    have hp₃ := hput₁ x hx
    have hstrike : K - (K - c₂) = c₂ := by ring
    unfold twoPut
    rw [hstrike]
    dsimp [M] at hzM
    linarith

/-- The residual in full-class containment splits into two nonnegative
coordinate functions, without an attained infimum assumption. -/
theorem protected_additive_nonnegative_residual {K : ℝ} (hK : 0 ≤ K)
    {a d : ℝ → ℝ} (hA : GloballyProtects K a d) :
    ∃ (k : ℝ) (r₁ r₂ : ℝ → ℝ),
      0 ≤ k ∧ k ≤ K ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ r₁ x) ∧
      (∀ y : ℝ, 0 ≤ y → 0 ≤ r₂ y) ∧
      ∀ x y : ℝ, a x + d y = twoPut K k x y + r₁ x + r₂ y := by
  obtain ⟨k, hk, hkK, hdom⟩ := protected_additive_contains_twoPut hK hA
  let u : ℝ → ℝ := fun x => a x - put k x
  let v : ℝ → ℝ := fun y => d y - put (K - k) y
  have hsum (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ u x + v y := by
    have h := hdom x y hx hy
    dsimp [u, v]
    unfold twoPut at h
    linarith
  have hub : BddBelow (u '' Set.Ici 0) := by
    refine ⟨-v 0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h := hsum x 0 hx (le_refl 0)
    linarith
  let r₁ : ℝ → ℝ := fun x => u x - lowerEnvelope u
  let r₂ : ℝ → ℝ := fun y => v y + lowerEnvelope u
  refine ⟨k, r₁, r₂, hk, hkK, ?_, ?_, ?_⟩
  · intro x hx
    exact sub_nonneg.mpr (lowerEnvelope_le hub hx)
  · intro y hy
    have h : -v y ≤ lowerEnvelope u := by
      apply le_lowerEnvelope
      intro x hx
      have h := hsum x y hx hy
      linarith
    dsimp [r₂]
    linarith
  · intro x y
    dsimp [r₁, r₂, u, v, twoPut]
    ring

end Research.I3
