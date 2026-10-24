module
public import BoltmannEntropy.Defs
@[expose] public section

/-!
Gibbs' Inequality for finite probability distributiosn

The goal is to show here that if p and q are prob distributions
on the same finite set and each pᵢ > 0, then
D(q || p) = ∑qᵢ log (qᵢ / pᵢ) ≥ 0 with equality when p = q.


## Main results
* `MaxEnt.sub_le_mul_log_div` : pointwise inequality `q - p ≤ q log (q / p)`.
* `MaxEnt.mul_log_div_eq_sub_iff` : its equality case.
* `MaxEnt.relEntropy_nonneg` : Gibbs' inequality.
* `MaxEnt.relEntropy_eq_zero_iff` : equality case of Gibbs' inequality.
* `MaxEnt.relEntropy_pos` : strict version.
-/

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- Pointwise inequality: `q - p ≤ q log (q / p)` for `p > 0` and `q ≥ 0`. -/
lemma sub_le_mul_log_div {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q - p ≤ q * Real.log (q / p) := by
  sorry

/-- Equality case of the pointwise inequality. -/
lemma mul_log_div_eq_sub_iff {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q * Real.log (q / p) = q - p ↔ q = p := by
  sorry

/-- **Gibbs' inequality.** -/
theorem relEntropy_nonneg {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : IsProbDist q) : 0 ≤ relEntropy q p := by
  sorry

/-- Equality case of Gibbs' inequality. -/
theorem relEntropy_eq_zero_iff {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : IsProbDist q) : relEntropy q p = 0 ↔ q = p := by
  sorry

/-- Strict Gibbs' inequality: different distributions have positive relative entropy. -/
theorem relEntropy_pos {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : IsProbDist q) (hne : q ≠ p) : 0 < relEntropy q p := by
  sorry

end MaxEnt
