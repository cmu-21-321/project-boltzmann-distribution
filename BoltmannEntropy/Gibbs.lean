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
  by_cases hq0 : q = 0
  · simp [hq0]
    linarith
  · have hqPos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hqp: 0 < q/p := div_pos hqPos hp
    have hlog : 1 - p/q  ≤ Real.log (q/p) := by
      have h := Real.add_one_le_exp (- (Real.log (q/p)))
      rw [Real.exp_neg, Real.exp_log hqp] at h
      have hdiv : (q/p)⁻¹ = p/q := by field_simp
      rw [hdiv] at h
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog hq
    have hdiv : q * (1 - p/q) = q - p := by field_simp
    rw [hdiv] at hmul
    exact hmul


-- I reproved the pointwise inequality but strict in this proof
-- but it would prob look cleaner if we just had the stirct inequality
-- as the pointwise inequality. Is there ant reason we don't?

/-- Equality case of the pointwise inequality. -/
lemma mul_log_div_eq_sub_iff {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q * Real.log (q / p) = q - p ↔ q = p := by
  constructor
  · intro h
    by_contra hqp
    have hq0 : q ≠ 0 := by
      intro h
      subst q
      simp at h
      linarith
    have hqPos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hqpPos: 0 < q/p := div_pos hqPos hp
    have hlog0 : - (Real.log (q/p)) ≠ 0 := by
      intro h
      rw [neg_eq_zero, Real.log_eq_zero] at h
      rcases h with hqp0 | hqp1 | hqpn1
      · linarith
      · field_simp at hqp1
        exact hqp hqp1
      · linarith
    have hlog : 1 - p/q  < Real.log (q/p) := by
      have h := Real.add_one_lt_exp hlog0
      rw [Real.exp_neg, Real.exp_log hqpPos] at h
      have hdiv : (q/p)⁻¹ = p/q := by field_simp
      rw [hdiv] at h
      linarith
    have hmul := mul_lt_mul_of_pos_left hlog hqPos
    have hdiv : q * (1 - p/q) = q - p := by field_simp
    rw [hdiv] at hmul
    linarith
  · intro h
    rw [h, Real.log_div]
    · ring
    · linarith
    · linarith

/-- **Gibbs' inequality.** -/
theorem relEntropy_nonneg {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : IsProbDist q) : 0 ≤ relEntropy q p := by
  rw [relEntropy]
  have hqPos := hq.nonneg
  have hq1 := hq.sum_eq_one
  have hsum : ∀ i, q i - p i ≤ q i * Real.log (q i / p i) := by
    intro i
    exact sub_le_mul_log_div (hp i) (hqPos i)
  have h : ∑ i, (q i - p i) ≤ ∑ i, q i * Real.log (q i / p i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hsum i
  rw [Finset.sum_sub_distrib, hq1, hp1] at h
  linarith

/-- Equality case of Gibbs' inequality. -/
theorem relEntropy_eq_zero_iff {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : IsProbDist q) : relEntropy q p = 0 ↔ q = p := by
  constructor
  · intro h
    have hqPos := hq.nonneg
    have hq1 := hq.sum_eq_one
    have hsum :
        ∑ i, (q i * Real.log (q i / p i) - (q i - p i)) = 0 := by
      calc
        ∑ i, (q i * Real.log (q i / p i) - (q i - p i))
            = relEntropy q p - ((∑ i, q i) - ∑ i, p i) := by
                simp [relEntropy, Finset.sum_sub_distrib]
        _ = 0 := by
          rw [h, hq1, hp1]
          ring
    have hpoint : ∀ i, q i * Real.log (q i / p i) = q i - p i := by
      intro i
      have hnonneg : ∀ j,
        0 ≤ q j * Real.log (q j / p j) - (q j - p j) := by
        intro j
        exact sub_nonneg.mpr (sub_le_mul_log_div (hp j) (hq.nonneg j))
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (fun j hj => hnonneg j)
        (Finset.mem_univ i)
      rw [hsum] at hsingle
      have hi := hnonneg i
      linarith
    funext i
    exact (mul_log_div_eq_sub_iff (hp i) (hqPos i)).mp (hpoint i)
  · intro h
    rw [h, relEntropy]
    simp

/-- Strict Gibbs' inequality: different distributions have positive relative entropy. -/
theorem relEntropy_pos {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (hq : IsProbDist q) (hne : q ≠ p) : 0 < relEntropy q p := by
    by_contra h
    have h0 : relEntropy q p = 0 :=
      le_antisymm (not_lt.mp h) (relEntropy_nonneg hp hp1 hq)
    exact hne ((relEntropy_eq_zero_iff hp hp1 hq).mp h0)

end MaxEnt
