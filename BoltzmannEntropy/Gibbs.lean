/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Defs

/-!
# Gibbs' inequality for finite probability distributions

If `p` and `q` are probability distributions on the same finite set and every `pᵢ > 0`, then
`D(q ‖ p) = ∑ qᵢ log (qᵢ / pᵢ) ≥ 0`, with equality exactly when `q = p`.

Both the inequality and its equality case come from the pointwise bound
`q - p ≤ q log (q / p)`, which is `log x ≤ x - 1` at `x = p / q`. Its strict form
`log x < x - 1` for `x ≠ 1` gives the strict pointwise bound directly.

## Main results

* `MaxEnt.sub_le_mul_log_div` : pointwise inequality `q - p ≤ q log (q / p)`.
* `MaxEnt.sub_lt_mul_log_div` : it is strict when `q ≠ p`.
* `MaxEnt.mul_log_div_eq_sub_iff` : its equality case.
* `MaxEnt.relEntropy_nonneg` : Gibbs' inequality.
* `MaxEnt.relEntropy_eq_zero_iff` : equality case of Gibbs' inequality.
* `MaxEnt.relEntropy_pos` : strict version.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- For `q > 0`, `q log (q / p) = -q log (p / q)`, and `q (p / q - 1) = p - q`. Together with
a bound on `log (p / q)` these give the pointwise inequalities below. -/
private lemma mul_log_div_eq {p q : ℝ} (hq : 0 < q) :
    q * Real.log (q / p) = -(q * Real.log (p / q)) ∧ q * (p / q - 1) = p - q := by
  refine ⟨?_, by field_simp⟩
  rw [← inv_div, Real.log_inv, mul_neg]

/-- Pointwise inequality: `q - p ≤ q log (q / p)` for `p > 0` and `q ≥ 0`. -/
lemma sub_le_mul_log_div {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q - p ≤ q * Real.log (q / p) := by
  rcases hq.eq_or_lt with rfl | hq
  · simpa using hp.le
  · obtain ⟨h1, h2⟩ := mul_log_div_eq (p := p) hq
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hp hq)) hq.le
    linarith

/-- Strict pointwise inequality: `q - p < q log (q / p)` when `q ≠ p`. -/
lemma sub_lt_mul_log_div {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hne : q ≠ p) :
    q - p < q * Real.log (q / p) := by
  rcases hq.eq_or_lt with rfl | hq
  · simpa using hp
  · obtain ⟨h1, h2⟩ := mul_log_div_eq (p := p) hq
    have hx : p / q ≠ 1 := fun h => hne ((div_eq_one_iff_eq hq.ne').mp h).symm
    have h := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hp hq) hx) hq
    linarith

/-- Equality case of the pointwise inequality. -/
lemma mul_log_div_eq_sub_iff {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q * Real.log (q / p) = q - p ↔ q = p := by
  constructor
  · intro h
    by_contra hne
    exact (sub_lt_mul_log_div hp hq hne).ne' h
  · rintro rfl
    simp [div_self hp.ne']

/-- **Gibbs' inequality.** -/
theorem relEntropy_nonneg {p q : ι → ℝ} (hp : IsProbDist p) (hp0 : ∀ i, 0 < p i)
    (hq : IsProbDist q) : 0 ≤ relEntropy q p := by
  have h : ∑ i, (q i - p i) ≤ relEntropy q p :=
    Finset.sum_le_sum fun i _ => sub_le_mul_log_div (hp0 i) (hq.nonneg i)
  rw [Finset.sum_sub_distrib, hq.sum_eq_one, hp.sum_eq_one, sub_self] at h
  exact h

/-- Equality case of Gibbs' inequality. -/
theorem relEntropy_eq_zero_iff {p q : ι → ℝ} (hp : IsProbDist p) (hp0 : ∀ i, 0 < p i)
    (hq : IsProbDist q) : relEntropy q p = 0 ↔ q = p := by
  constructor
  · intro h
    -- `D(q ‖ p)` is a sum of the nonnegative gaps in the pointwise inequality
    have hsum : ∑ i, (q i * Real.log (q i / p i) - (q i - p i)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq.sum_eq_one, hp.sum_eq_one]
      simpa [relEntropy] using h
    have hgap := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      sub_nonneg.mpr (sub_le_mul_log_div (hp0 i) (hq.nonneg i))).mp hsum
    funext i
    exact (mul_log_div_eq_sub_iff (hp0 i) (hq.nonneg i)).mp
      (sub_eq_zero.mp (hgap i (Finset.mem_univ i)))
  · rintro rfl
    simp [relEntropy, div_self (hp0 _).ne']

/-- Strict Gibbs' inequality: different distributions have positive relative entropy. -/
theorem relEntropy_pos {p q : ι → ℝ} (hp : IsProbDist p) (hp0 : ∀ i, 0 < p i)
    (hq : IsProbDist q) (hne : q ≠ p) : 0 < relEntropy q p :=
  (relEntropy_nonneg hp hp0 hq).lt_of_ne fun h =>
    hne ((relEntropy_eq_zero_iff hp hp0 hq).mp h.symm)

end MaxEnt
