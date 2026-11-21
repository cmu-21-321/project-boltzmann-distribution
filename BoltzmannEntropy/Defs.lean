/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import Mathlib

/-!
# Definitions

## Main definitions

* `MaxEnt.IsProbDist q` : `q` is a probability distribution on `ι`.
* `MaxEnt.entropy q` : Shannon entropy `S(q) = -∑ qᵢ log qᵢ` (natural log).
* `MaxEnt.meanEnergy E q` : average energy `U(q) = ∑ qᵢ Eᵢ`.
* `MaxEnt.partitionFn E β` : partition function `Z(β) = ∑ⱼ exp (-β Eⱼ)`.
* `MaxEnt.boltzmann E β` : Boltzmann distribution `pᵢ = exp (-β Eᵢ) / Z(β)`.
* `MaxEnt.freeEnergy E β q` : free energy `F(q) = U(q) - S(q) / β`.
* `MaxEnt.relEntropy q p` : relative entropy `D(q ‖ p) = ∑ qᵢ log (qᵢ / pᵢ)`.
* `MaxEnt.groundEnergy E`, `MaxEnt.groundStates E` : the minimum energy and the states that
  attain it.
* `MaxEnt.groundDist E` : the uniform distribution on the ground states.

## Conventions

Lean's real division and logarithm are total, with `x / 0 = 0` and `log 0 = 0`. Two
consequences are worth knowing:

* `freeEnergy E 0 q` is just `meanEnergy E q`, so results about free energy assume `β ≠ 0`.
* `relEntropy q p` only means `D(q ‖ p)` when `pᵢ > 0` wherever `qᵢ > 0`. Results about it
  assume `p` is strictly positive.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- `q` is a probability distribution on the finite set of states `ι`. -/
@[mk_iff]
structure IsProbDist (q : ι → ℝ) : Prop where
  /-- Every probability is nonnegative. -/
  nonneg : ∀ i, 0 ≤ q i
  /-- The probabilities sum to one. -/
  sum_eq_one : ∑ i, q i = 1

/-- Shannon entropy `S(q) = -∑ qᵢ log qᵢ`. -/
def entropy (q : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (q i)

/-- Average energy `U(q) = ∑ qᵢ Eᵢ`. -/
def meanEnergy (E : ι → ℝ) (q : ι → ℝ) : ℝ :=
  ∑ i, q i * E i

/-- Partition function `Z(β) = ∑ⱼ exp (-β Eⱼ)`. -/
def partitionFn (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ j, Real.exp (-β * E j)

/-- Boltzmann distribution `pᵢ = exp (-β Eᵢ) / Z(β)`. -/
def boltzmann (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i) / partitionFn E β

/-- Free energy `F(q) = U(q) - S(q) / β`. -/
def freeEnergy (E : ι → ℝ) (β : ℝ) (q : ι → ℝ) : ℝ :=
  meanEnergy E q - entropy q / β

/-- Relative entropy (Kullback–Leibler divergence) `D(q ‖ p) = ∑ qᵢ log (qᵢ / pᵢ)`. -/
def relEntropy (q p : ι → ℝ) : ℝ :=
  ∑ i, q i * Real.log (q i / p i)

/-! ### Basic facts

`Z > 0`, Boltzmann probabilities are positive and sum to `1`, and the logarithm of a
Boltzmann probability. -/

/-- A probability distribution can only live on a nonempty set of states. -/
theorem IsProbDist.nonempty {q : ι → ℝ} (hq : IsProbDist q) : Nonempty ι := by
  by_contra h
  have := not_nonempty_iff.mp h
  simpa using hq.sum_eq_one

/-- The Boltzmann distribution with the partition function written out as a sum. -/
theorem boltzmann_def (E : ι → ℝ) (β : ℝ) :
    boltzmann E β = fun i => Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j) :=
  rfl

theorem partitionFn_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) : 0 < partitionFn E β := by
  unfold partitionFn
  apply Finset.sum_pos
  · intro i hi
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

theorem boltzmann_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) (i : ι) : 0 < boltzmann E β i := by
  unfold boltzmann
  exact div_pos (Real.exp_pos _) (partitionFn_pos E β)

theorem sum_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ) : ∑ i, boltzmann E β i = 1 := by
  unfold boltzmann
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partitionFn_pos E β))

theorem isProbDist_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    IsProbDist (boltzmann E β) where
  nonneg i := le_of_lt (boltzmann_pos E β i)
  sum_eq_one := sum_boltzmann E β

theorem log_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    Real.log (boltzmann E β i) = -β * E i - Real.log (partitionFn E β) := by
  unfold boltzmann
  rw [Real.log_div]
  · rw [Real.log_exp]
  · exact ne_of_gt (Real.exp_pos _)
  · exact ne_of_gt (partitionFn_pos E β)

/-- Subtracting a constant from every energy does not change the Boltzmann distribution. -/
theorem boltzmann_sub_const (E : ι → ℝ) (β c : ℝ) (i : ι) :
    boltzmann (fun j => E j - c) β i = boltzmann E β i := by
  unfold boltzmann partitionFn
  have hexp (j : ι) : Real.exp (-β * (E j - c)) = Real.exp (β * c) * Real.exp (-β * E j) := by
    rw [← Real.exp_add]
    ring_nf
  simp_rw [hexp, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- Reversing the sign of both the energies and `β` does not change the Boltzmann
distribution. -/
theorem boltzmann_neg_neg (E : ι → ℝ) (β : ℝ) :
    boltzmann (-E) (-β) = boltzmann E β := by
  funext i
  simp [boltzmann, partitionFn]

/-! ### Explicit-sum forms

Entropy and free energy with the `negMulLog` convention unfolded. These are used in
`Main.lean` for the final statement. -/

/-- Entropy with the sum written out: `S(q) = -∑ qᵢ log qᵢ`. -/
theorem entropy_eq_neg_sum (q : ι → ℝ) : entropy q = -∑ i, q i * Real.log (q i) := by
  simp only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

/-- Free energy with the sums written out: `F(q) = ∑ qᵢ Eᵢ + (1/β) ∑ qᵢ log qᵢ`. -/
theorem freeEnergy_eq_sum (E : ι → ℝ) (β : ℝ) (q : ι → ℝ) :
    freeEnergy E β q = ∑ i, q i * E i + (1 / β) * ∑ i, q i * Real.log (q i) := by
  unfold freeEnergy meanEnergy
  rw [entropy_eq_neg_sum]
  ring

/-! ### Ground states -/

section Ground

variable [Nonempty ι]

/-- The minimum energy among all states. -/
def groundEnergy (E : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty E

/-- The set of states attaining the minimum energy. -/
def groundStates (E : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => E i = groundEnergy E)

/-- The uniform distribution on the ground states: `1 / |G|` on a ground state, `0` elsewhere. -/
def groundDist (E : ι → ℝ) (i : ι) : ℝ :=
  if E i = groundEnergy E then 1 / ((groundStates E).card : ℝ) else 0

/-- The ground-state energy is less than or equal to every state energy. -/
theorem groundEnergy_le (E : ι → ℝ) (i : ι) : groundEnergy E ≤ E i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem mem_groundStates (E : ι → ℝ) (i : ι) : i ∈ groundStates E ↔ E i = groundEnergy E := by
  simp [groundStates]

/-- A state is a ground state exactly when no state has lower energy. -/
theorem mem_groundStates_iff_forall_le (E : ι → ℝ) (i : ι) :
    i ∈ groundStates E ↔ ∀ j, E i ≤ E j := by
  rw [mem_groundStates]
  refine ⟨fun h j => h ▸ groundEnergy_le E j, fun h => le_antisymm ?_ (groundEnergy_le E i)⟩
  exact Finset.le_inf' _ _ fun j _ => h j

/-- The set of ground states is nonempty. -/
theorem groundStates_nonempty (E : ι → ℝ) : (groundStates E).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
  exact ⟨i, (mem_groundStates E i).mpr hi.symm⟩

theorem groundStates_card_pos (E : ι → ℝ) : (0 : ℝ) < (groundStates E).card := by
  exact_mod_cast (groundStates_nonempty E).card_pos

/-- Shifting an energy by the ground-state energy gives a nonnegative value: `0 ≤ Eᵢ - E₀`. -/
theorem shiftedEnergy_nonneg (E : ι → ℝ) (i : ι) : 0 ≤ E i - groundEnergy E :=
  sub_nonneg.mpr (groundEnergy_le E i)

/-- A sum of `if i is a ground state then f i else 0` is a sum over the ground states. -/
theorem sum_ite_groundEnergy (E : ι → ℝ) (f : ι → ℝ) :
    ∑ i, (if E i = groundEnergy E then f i else 0) = ∑ i ∈ groundStates E, f i := by
  rw [groundStates, Finset.sum_filter]

theorem isProbDist_groundDist (E : ι → ℝ) : IsProbDist (groundDist E) where
  nonneg i := by
    unfold groundDist
    split_ifs
    · exact (one_div_pos.mpr (groundStates_card_pos E)).le
    · exact le_rfl
  sum_eq_one := by
    unfold groundDist
    rw [sum_ite_groundEnergy, Finset.sum_const, nsmul_eq_mul, mul_one_div,
      div_self (groundStates_card_pos E).ne']

/-- The mean energy of the ground-state distribution is the ground-state energy. -/
theorem meanEnergy_groundDist (E : ι → ℝ) : meanEnergy E (groundDist E) = groundEnergy E := by
  have h : ∀ i, groundDist E i * E i = groundDist E i * groundEnergy E := by
    intro i
    unfold groundDist
    split_ifs with hi
    · rw [hi]
    · simp
  simp only [meanEnergy, h, ← Finset.sum_mul, (isProbDist_groundDist E).sum_eq_one, one_mul]

end Ground

end MaxEnt
