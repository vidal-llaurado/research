import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# I2: the finite deterministic date budget

The weighted Cauchy--Schwarz step in equations `budget-cs` through
`all-date-lower` is proved for arbitrary finite collections of real cell masses
and strictly positive budget weights. The exact excess-cost identity also
characterizes equality. Specialization to weights `1 + penalty` matches the
manuscript's `1 + d_i / r_i^q`.

The link from a deterministic trading grid to these finite data is not assumed
to be automatic: the stochastic risk comparison, counted refinement, integral
estimates for the power kernel, and quantile construction remain unformalized.
In particular this file does not assert the paper's sharp asymptotic rates.
-/

noncomputable section

open scoped BigOperators

namespace Research.I2

variable {ι : Type*}

/-- The exact finite weighted lower bound, without an assumed optimality
condition on the masses. This is equation `budget-cs`. -/
theorem weighted_date_budget (cells : Finset ι) (mass weight : ι → ℝ)
    (hw : ∀ i ∈ cells, 0 < weight i) :
    (∑ i ∈ cells, mass i) ^ 2 / (∑ i ∈ cells, weight i) ≤
      ∑ i ∈ cells, mass i ^ 2 / weight i :=
  Finset.sq_sum_div_le_sum_sq_div cells mass hw

/-- Exact cost above the optimal weighted allocation, for actual finite sums.
It is a sum of nonnegative squared allocation errors. -/
theorem weighted_date_budget_excess (cells : Finset ι) (mass weight : ι → ℝ)
    (hw : ∀ i ∈ cells, 0 < weight i)
    (hW : (∑ i ∈ cells, weight i) ≠ 0) :
    (∑ i ∈ cells, mass i ^ 2 / weight i) -
        (∑ i ∈ cells, mass i) ^ 2 / (∑ i ∈ cells, weight i) =
      ∑ i ∈ cells,
        (mass i - (∑ j ∈ cells, mass j) * weight i /
          (∑ j ∈ cells, weight j)) ^ 2 / weight i := by
  have hcell (i : ι) (hi : i ∈ cells) :
      (mass i - (∑ j ∈ cells, mass j) * weight i /
          (∑ j ∈ cells, weight j)) ^ 2 / weight i =
        mass i ^ 2 / weight i -
          (2 * (∑ j ∈ cells, mass j) / (∑ j ∈ cells, weight j)) * mass i +
          ((∑ j ∈ cells, mass j) ^ 2 / (∑ j ∈ cells, weight j) ^ 2) *
            weight i := by
    have hiw := (hw i hi).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl hcell]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-- The lower bound is attained exactly by proportional masses. -/
theorem proportional_mass_attains (cells : Finset ι) (weight : ι → ℝ)
    (hw : ∀ i ∈ cells, 0 < weight i)
    (hW : (∑ i ∈ cells, weight i) ≠ 0) (totalMass : ℝ) :
    (∑ i ∈ cells, totalMass * weight i / (∑ j ∈ cells, weight j)) = totalMass ∧
    (∑ i ∈ cells,
        (totalMass * weight i / (∑ j ∈ cells, weight j)) ^ 2 / weight i) =
      totalMass ^ 2 / (∑ j ∈ cells, weight j) := by
  constructor
  · rw [← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ totalMass hW
  · have hcell (i : ι) (hi : i ∈ cells) :
        (totalMass * weight i / (∑ j ∈ cells, weight j)) ^ 2 / weight i =
          (totalMass ^ 2 / (∑ j ∈ cells, weight j) ^ 2) * weight i := by
      have hiw := (hw i hi).ne'
      field_simp
    rw [Finset.sum_congr rfl hcell, ← Finset.mul_sum]
    field_simp

/-- Equality in the weighted date budget holds exactly for proportional
masses. This is an optimization statement about the finite functional only. -/
theorem weighted_date_budget_equality_iff (cells : Finset ι) (mass weight : ι → ℝ)
    (hw : ∀ i ∈ cells, 0 < weight i)
    (hW : (∑ i ∈ cells, weight i) ≠ 0) :
    (∑ i ∈ cells, mass i ^ 2 / weight i) =
        (∑ i ∈ cells, mass i) ^ 2 / (∑ i ∈ cells, weight i) ↔
      ∀ i ∈ cells,
        mass i = (∑ j ∈ cells, mass j) * weight i / (∑ j ∈ cells, weight j) := by
  have hexcess := weighted_date_budget_excess cells mass weight hw hW
  have hnonneg : ∀ i ∈ cells,
      0 ≤ (mass i - (∑ j ∈ cells, mass j) * weight i /
        (∑ j ∈ cells, weight j)) ^ 2 / weight i := by
    intro i hi
    exact div_nonneg (sq_nonneg _) (hw i hi).le
  constructor
  · intro h i hi
    have hsum : (∑ i ∈ cells,
        (mass i - (∑ j ∈ cells, mass j) * weight i /
          (∑ j ∈ cells, weight j)) ^ 2 / weight i) = 0 := by
      rw [h, sub_self] at hexcess
      exact hexcess.symm
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i hi
    have hsquare := (div_eq_zero_iff.mp hzero).resolve_right (hw i hi).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    have hsum : (∑ i ∈ cells,
        (mass i - (∑ j ∈ cells, mass j) * weight i /
          (∑ j ∈ cells, weight j)) ^ 2 / weight i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h i hi, sub_self, zero_pow (by decide), zero_div]
    rw [hsum] at hexcess
    exact sub_eq_zero.mp hexcess

/-- A cap on the total budget and a lower bound on mass give the lower bound
used for every refined grid. Both comparisons are explicit bridge premises. -/
theorem date_budget_from_mass_bound (cells : Finset ι) (mass weight : ι → ℝ)
    (hw : ∀ i ∈ cells, 0 < weight i)
    (hW : 0 < ∑ i ∈ cells, weight i)
    {lowerMass budget : ℝ} (hm : 0 ≤ lowerMass)
    (hMass : lowerMass ≤ ∑ i ∈ cells, mass i)
    (hBudget : (∑ i ∈ cells, weight i) ≤ budget) :
    lowerMass ^ 2 / budget ≤ ∑ i ∈ cells, mass i ^ 2 / weight i := by
  have hbudgetpos : 0 < budget := lt_of_lt_of_le hW hBudget
  have hMassSq : lowerMass ^ 2 ≤ (∑ i ∈ cells, mass i) ^ 2 := by nlinarith
  calc
    lowerMass ^ 2 / budget ≤ (∑ i ∈ cells, mass i) ^ 2 / budget :=
      div_le_div_of_nonneg_right hMassSq hbudgetpos.le
    _ ≤ (∑ i ∈ cells, mass i) ^ 2 / (∑ i ∈ cells, weight i) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hW hBudget
    _ ≤ _ := weighted_date_budget cells mass weight hw

/-- The exact saturated cell-cost form appearing in the band argument. -/
theorem saturated_date_budget (cells : Finset ι) (mass penalty : ι → ℝ)
    (hp : ∀ i ∈ cells, 0 ≤ penalty i) :
    (∑ i ∈ cells, mass i) ^ 2 /
        ((cells.card : ℝ) + ∑ i ∈ cells, penalty i) ≤
      ∑ i ∈ cells, mass i ^ 2 / (1 + penalty i) := by
  have hw : ∀ i ∈ cells, 0 < 1 + penalty i := by
    intro i hi
    linarith [hp i hi]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    using weighted_date_budget cells mass (fun i ↦ 1 + penalty i) hw

/-- Quantitative arbitrary-grid lower reduction. Here `penalty` is d/r^q,
`lowerMass` is the certified lower bound for the allocation integral, and
`budget` bounds N + sum(d/r^q). The stochastic lower constant is explicit. -/
theorem risk_lower_from_date_budget (cells : Finset ι) (mass penalty : ι → ℝ)
    (hne : cells.Nonempty) (hp : ∀ i ∈ cells, 0 ≤ penalty i)
    {lowerMass budget risk factor : ℝ} (hm : 0 ≤ lowerMass)
    (hMass : lowerMass ≤ ∑ i ∈ cells, mass i)
    (hBudget : (cells.card : ℝ) + (∑ i ∈ cells, penalty i) ≤ budget)
    (hf : 0 ≤ factor)
    (hRisk : factor * (∑ i ∈ cells, mass i ^ 2 / (1 + penalty i)) ≤ risk) :
    factor * (lowerMass ^ 2 / budget) ≤ risk := by
  have hw : ∀ i ∈ cells, 0 < 1 + penalty i := by
    intro i hi
    linarith [hp i hi]
  have hW : 0 < ∑ i ∈ cells, (1 + penalty i) :=
    Finset.sum_pos hw hne
  have hBudget' : (∑ i ∈ cells, (1 + penalty i)) ≤ budget := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      using hBudget
  exact le_trans
    (mul_le_mul_of_nonneg_left
      (date_budget_from_mass_bound cells mass (fun i ↦ 1 + penalty i)
        hw hW hm hMass hBudget') hf) hRisk

end Research.I2
