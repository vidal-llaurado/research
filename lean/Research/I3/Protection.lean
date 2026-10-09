import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# I3: terminal payoff protection and exact loss-reserve geometry

Supporting algebra for UC1 and the four-put construction in UIC1, dated
2026-10-05. All quantities are real discounted terminal cash amounts.
The state domain is the whole nonnegative quadrant, not only a model support.

This file does not formalize probabilities, put pricing, the whole-additive-class
reduction, the capital-risk frontier, information rates, or optimal learning.
The scalar `c` is supplied financing; no expectation identity is assumed or
proved. A nonnegative payoff with a zero at the origin has exact terminal loss
`c` after financing by `c`. This is not a broker-margin or interim-funding result.
-/

namespace Research.I3

def put (strike spot : ℝ) : ℝ := max (strike - spot) 0

def basketPut (K x y : ℝ) : ℝ := put K (x + y)

def twoPut (K k x y : ℝ) : ℝ := put k x + put (K - k) y

def surplus (K k x y : ℝ) : ℝ := twoPut K k x y - basketPut K x y

def fourPut (K k₁ k₂ p x y : ℝ) : ℝ :=
  p * twoPut K k₁ x y + (1 - p) * twoPut K k₂ x y

theorem put_nonneg (k x : ℝ) : 0 ≤ put k x := le_max_right _ _

theorem put_le_strike {k x : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x) :
    put k x ≤ k := max_le (sub_le_self _ hx) hk

/-- The pointwise two-put superhedge does not require a pricing law. -/
theorem basket_le_twoPut (K k x y : ℝ) :
    basketPut K x y ≤ twoPut K k x y := by
  unfold basketPut twoPut put
  apply max_le
  · calc
      K - (x + y) = (k - x) + (K - k - y) := by ring
      _ ≤ max (k - x) 0 + max (K - k - y) 0 :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem surplus_nonneg (K k x y : ℝ) : 0 ≤ surplus K k x y :=
  sub_nonneg.mpr (basket_le_twoPut K k x y)

/-- UC1's bounded terminal surplus on the entire nonnegative quadrant. -/
theorem surplus_le_strike {K k x y : ℝ}
    (hk : 0 ≤ k) (hkK : k ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    surplus K k x y ≤ K := by
  have h₁ := put_le_strike hk hx
  have h₂ := put_le_strike (sub_nonneg.mpr hkK) hy
  have hB := put_nonneg K (x + y)
  unfold surplus twoPut basketPut
  linarith

/-- The surplus vanishes at a state in the global solvency domain. -/
theorem surplus_at_origin {K k : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) :
    surplus K k 0 0 = 0 := by
  have hK : 0 ≤ K := le_trans hk hkK
  simp only [surplus, twoPut, basketPut, put, add_zero, sub_zero,
    max_eq_left hk, max_eq_left (sub_nonneg.mpr hkK), max_eq_left hK]
  ring

/-- Exact global terminal financed lower bound; no probability law is used. -/
theorem twoPut_exact_terminal_floor {K k : ℝ}
    (hk : 0 ≤ k) (hkK : k ≤ K) (c : ℝ) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → -c ≤ surplus K k x y - c) ∧
    surplus K k 0 0 - c = -c := by
  constructor
  · intro x y _ _
    have h := surplus_nonneg K k x y
    linarith
  · rw [surplus_at_origin hk hkK]
    ring

/-- UIC1's four-put construction preserves the global terminal protection. -/
theorem basket_le_fourPut {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (K k₁ k₂ x y : ℝ) :
    basketPut K x y ≤ fourPut K k₁ k₂ p x y := by
  have h₁ := mul_le_mul_of_nonneg_left (basket_le_twoPut K k₁ x y) hp
  have h₂ := mul_le_mul_of_nonneg_left (basket_le_twoPut K k₂ x y)
    (sub_nonneg.mpr hp1)
  unfold fourPut
  calc
    basketPut K x y = p * basketPut K x y + (1 - p) * basketPut K x y := by ring
    _ ≤ p * twoPut K k₁ x y + (1 - p) * twoPut K k₂ x y := add_le_add h₁ h₂

theorem fourPut_surplus_at_origin {K k₁ k₂ : ℝ}
    (h₁ : 0 ≤ k₁) (h₁K : k₁ ≤ K) (h₂ : 0 ≤ k₂) (h₂K : k₂ ≤ K)
    (p : ℝ) :
    fourPut K k₁ k₂ p 0 0 - basketPut K 0 0 = 0 := by
  have h₁z := surplus_at_origin h₁ h₁K
  have h₂z := surplus_at_origin h₂ h₂K
  unfold surplus at h₁z h₂z
  unfold fourPut
  rw [sub_eq_zero.mp h₁z, sub_eq_zero.mp h₂z]
  ring

/-- Exact floor of every admissible four-put mixture after scalar financing. -/
theorem fourPut_exact_terminal_floor {K k₁ k₂ p : ℝ}
    (h₁ : 0 ≤ k₁) (h₁K : k₁ ≤ K) (h₂ : 0 ≤ k₂) (h₂K : k₂ ≤ K)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (c : ℝ) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      -c ≤ fourPut K k₁ k₂ p x y - basketPut K x y - c) ∧
    fourPut K k₁ k₂ p 0 0 - basketPut K 0 0 - c = -c := by
  constructor
  · intro x y _ _
    have h := basket_le_fourPut hp hp1 K k₁ k₂ x y
    linarith
  · rw [fourPut_surplus_at_origin h₁ h₁K h₂ h₂K p]
    ring

/-- Cash-price algebra only: expectation linearity is outside this file. -/
theorem mixture_financing (p a₁ a₂ b : ℝ) :
    p * a₁ + (1 - p) * a₂ - b = p * (a₁ - b) + (1 - p) * (a₂ - b) := by
  ring

/-- Equal financed endpoint prices give the same financed mixture price. -/
theorem equal_endpoint_financing {a₁ a₂ b c : ℝ}
    (h₁ : a₁ - b = c) (h₂ : a₂ - b = c) (p : ℝ) :
    p * a₁ + (1 - p) * a₂ - b = c := by
  rw [mixture_financing, h₁, h₂]
  ring

end Research.I3
