/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Thermodynamics
public import BoltzmannEntropy.Limits

/-!
# The maximum-entropy principle, without a temperature given in advance

`Variational.lean` shows that, for a given `β`, the Boltzmann distribution has the most
entropy among distributions with its own mean energy. Here we go the other way. We are given
only a target mean energy `U`, and show that the maximum-entropy distribution with that mean
energy is a Boltzmann distribution, at a `β` that `U` determines uniquely.

The hypothesis is that `U` lies strictly between the lowest and highest energies. The
equilibrium mean energy `U(β)` is continuous and strictly decreasing in `β`
(`Thermodynamics.lean`). It tends to the highest energy as `β → -∞` and to the lowest as
`β → ∞` (`Limits.lean`). So by the intermediate value theorem it takes the value `U` exactly
once.

`β` is positive when `U` is below the average energy `(1/n) ∑ Eᵢ` and negative when `U` is
above it. That is why the maximum-entropy results in `Variational.lean` are stated for every
real `β`.

At the endpoints `U = min E` or `U = max E` there is no such `β`. The only distribution with
that mean energy is then supported on the lowest (respectively highest) energy states.

## Main results

* `MaxEnt.existsUnique_meanEnergy_boltzmann_eq` : each `U` strictly between the lowest and
  highest energies is the equilibrium mean energy at exactly one `β`.
* `MaxEnt.maxEnt_eq_boltzmann` : the maximum-entropy distribution with mean energy `U` is that
  Boltzmann distribution, and it is the unique maximizer.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace MaxEnt

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Every energy is at most `-groundEnergy (-E)`, the highest energy. -/
lemma le_neg_groundEnergy_neg (E : ι → ℝ) (j : ι) : E j ≤ -groundEnergy (-E) := by
  have := groundEnergy_le (-E) j
  simp only [Pi.neg_apply] at this
  linarith

/-- **Inverting `U(β)`.** If `U` lies strictly between the lowest and highest energies, there is
exactly one `β` at which the Boltzmann distribution has mean energy `U`. -/
theorem existsUnique_meanEnergy_boltzmann_eq (E : ι → ℝ) {U : ℝ}
    (hlo : ∃ i, E i < U) (hhi : ∃ j, U < E j) :
    ∃! β, meanEnergy E (boltzmann E β) = U := by
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  -- far enough out on each side, `U(β)` is on either side of `U`
  obtain ⟨b, hb⟩ := ((tendsto_meanEnergy_boltzmann_atTop E).eventually
    (Iio_mem_nhds ((groundEnergy_le E i).trans_lt hi))).exists
  obtain ⟨a, ha⟩ := ((tendsto_meanEnergy_boltzmann_atBot E).eventually
    (Ioi_mem_nhds (hj.trans_le (le_neg_groundEnergy_neg E j)))).exists
  -- intermediate value theorem
  obtain ⟨β, hβ⟩ := intermediate_value_univ b a (continuous_meanEnergy_boltzmann E)
    ⟨le_of_lt hb, le_of_lt ha⟩
  -- uniqueness: `U(β)` is strictly decreasing, since the energies are not all equal
  have hE : ∃ i j, E i ≠ E j := ⟨i, j, (hi.trans hj).ne⟩
  exact ⟨β, hβ, fun γ hγ => (meanEnergy_boltzmann_strictAnti E hE).injective (hγ.trans hβ.symm)⟩

/-- **Maximum-entropy principle.** Let `U` lie strictly between the lowest and highest energies.
Then there is a `β` such that the Boltzmann distribution at `β` has mean energy `U`, and every
probability distribution `q` with mean energy `U` has at most its entropy, with equality only
for `q = boltzmann E β`. -/
theorem maxEnt_eq_boltzmann (E : ι → ℝ) {U : ℝ} (hlo : ∃ i, E i < U) (hhi : ∃ j, U < E j) :
    ∃ β, meanEnergy E (boltzmann E β) = U ∧
      ∀ q, IsProbDist q → meanEnergy E q = U →
        entropy q ≤ entropy (boltzmann E β) ∧
          (entropy q = entropy (boltzmann E β) → q = boltzmann E β) := by
  obtain ⟨β, hβ, -⟩ := existsUnique_meanEnergy_boltzmann_eq E hlo hhi
  refine ⟨β, hβ, fun q hq hU => ⟨entropy_le_entropy_boltzmann E β hq (hU.trans hβ.symm),
    fun heq => ?_⟩⟩
  by_contra hne
  exact (entropy_lt_entropy_boltzmann E β hq (hU.trans hβ.symm) hne).ne heq

end MaxEnt
