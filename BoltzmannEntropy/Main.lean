/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Variational

/-!
# The principal result

The Gibbs variational principle for `n` states, stated with explicit sums and no auxiliary
definitions: for `β > 0` and any probability distribution `q`,
`∑ qᵢ Eᵢ + (1/β) ∑ qᵢ log qᵢ ≥ -(1/β) log ∑ⱼ exp (-β Eⱼ)`,
with equality exactly for the Boltzmann distribution.

## Main results

* `MaxEnt.gibbs_variational_explicit` : the inequality.
* `MaxEnt.gibbs_variational_explicit_eq_iff` : its equality case.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- `freeEnergy_boltzmann` with the partition function written out as a sum. -/
lemma freeEnergy_boltzmann_eq_explicit [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0) :
    freeEnergy E β (boltzmann E β) = -(1 / β) * Real.log (∑ j, Real.exp (-β * E j)) := by
  rw [freeEnergy_boltzmann E hβ, partitionFn]
  ring

/-- **Principal result.** For energies `E₁, …, Eₙ`, `β > 0` and any probability
distribution `q`, `∑ qᵢ Eᵢ + (1/β) ∑ qᵢ log qᵢ ≥ -(1/β) log Z`. -/
theorem gibbs_variational_explicit {n : ℕ} (E : Fin n → ℝ) {β : ℝ} (hβ : 0 < β)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    -(1 / β) * Real.log (∑ j, Real.exp (-β * E j))
      ≤ ∑ i, q i * E i + (1 / β) * ∑ i, q i * Real.log (q i) := by
  have hq : IsProbDist q := ⟨hq0, hq1⟩
  -- a probability distribution forces `n ≠ 0`
  have := hq.nonempty
  have h := freeEnergy_boltzmann_le E hβ hq
  rwa [freeEnergy_boltzmann_eq_explicit E hβ.ne', freeEnergy_eq_sum E β q] at h

/-- Equality holds exactly for the Boltzmann distribution. -/
theorem gibbs_variational_explicit_eq_iff {n : ℕ} (E : Fin n → ℝ) {β : ℝ} (hβ : 0 < β)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    (∑ i, q i * E i + (1 / β) * ∑ i, q i * Real.log (q i)
        = -(1 / β) * Real.log (∑ j, Real.exp (-β * E j)))
      ↔ q = fun i => Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j) := by
  have hq : IsProbDist q := ⟨hq0, hq1⟩
  have := hq.nonempty
  have h := freeEnergy_eq_freeEnergy_boltzmann_iff E hβ hq
  rwa [freeEnergy_eq_sum E β q, freeEnergy_boltzmann_eq_explicit E hβ.ne',
    boltzmann_def] at h

end MaxEnt
