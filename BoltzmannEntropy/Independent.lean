/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Variational

/-!
# Independent systems

Two systems with state spaces `ι` and `κ` and energies `E`, `E'` combine into a system on
`ι × κ` with energy `E i + E' k`. Thermodynamic quantities behave as expected:

* partition functions multiply, so `log Z` and the equilibrium free energy add;
* the Boltzmann distribution is the product of the two Boltzmann distributions;
* for any product distribution `p ⊗ p'`, mean energy, entropy and free energy add.

## Main results

* `MaxEnt.partitionFn_prod`, `MaxEnt.log_partitionFn_prod` : `Z = Z₁ Z₂`, `log Z` adds.
* `MaxEnt.boltzmann_prod` : Boltzmann probabilities multiply.
* `MaxEnt.isProbDist_prod` : a product of distributions is a distribution.
* `MaxEnt.meanEnergy_prod`, `MaxEnt.entropy_prod`, `MaxEnt.freeEnergy_prod` : additivity for
  product distributions.
* `MaxEnt.entropy_boltzmann_prod`, `MaxEnt.freeEnergy_boltzmann_prod` : additivity at
  equilibrium.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The energy of the combined system: `(i, k) ↦ Eᵢ + E'ₖ`. -/
abbrev sumEnergy (E : ι → ℝ) (E' : κ → ℝ) : ι × κ → ℝ :=
  fun x => E x.1 + E' x.2

/-- The product distribution `(i, k) ↦ pᵢ p'ₖ`. -/
abbrev prodDist (p : ι → ℝ) (p' : κ → ℝ) : ι × κ → ℝ :=
  fun x => p x.1 * p' x.2

/-! ### Partition function and Boltzmann distribution -/

/-- The partition function of two independent systems is the product of their individual
partition functions. -/
lemma partitionFn_prod (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    partitionFn (sumEnergy E E') β = partitionFn E β * partitionFn E' β := by
  unfold partitionFn
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- `log Z` is additive over independent systems. -/
lemma log_partitionFn_prod [Nonempty ι] [Nonempty κ] (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    Real.log (partitionFn (sumEnergy E E') β)
      = Real.log (partitionFn E β) + Real.log (partitionFn E' β) := by
  rw [partitionFn_prod, Real.log_mul (partitionFn_pos E β).ne' (partitionFn_pos E' β).ne']

/-- The Boltzmann distribution of two independent systems is the product of their individual
Boltzmann distributions. -/
lemma boltzmann_prod (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    boltzmann (sumEnergy E E') β = prodDist (boltzmann E β) (boltzmann E' β) := by
  funext x
  simp only [boltzmann, prodDist, sumEnergy]
  rw [partitionFn_prod, div_mul_div_comm, ← Real.exp_add]
  congr 2
  ring

/-! ### Product distributions -/

/-- A product of probability distributions is a probability distribution. -/
lemma isProbDist_prod {p : ι → ℝ} {p' : κ → ℝ} (hp : IsProbDist p) (hp' : IsProbDist p') :
    IsProbDist (prodDist p p') where
  nonneg x := mul_nonneg (hp.nonneg x.1) (hp'.nonneg x.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hp.sum_eq_one, hp'.sum_eq_one, one_mul]

/-- Mean energy is additive for a product distribution. -/
lemma meanEnergy_prod {p : ι → ℝ} {p' : κ → ℝ} (hp : IsProbDist p) (hp' : IsProbDist p')
    (E : ι → ℝ) (E' : κ → ℝ) :
    meanEnergy (sumEnergy E E') (prodDist p p') = meanEnergy E p + meanEnergy E' p' := by
  have h1 : ∀ i, ∑ k, p i * p' k * E i = p i * E i := fun i => by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hp'.sum_eq_one]
    ring
  have h2 : ∀ i, ∑ k, p i * p' k * E' k = p i * meanEnergy E' p' := fun i => by
    rw [meanEnergy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold meanEnergy
  rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib, h1, h2, ← Finset.sum_mul, hp.sum_eq_one, one_mul]
  rfl

/-- Entropy is additive for a product distribution. -/
lemma entropy_prod {p : ι → ℝ} {p' : κ → ℝ} (hp : IsProbDist p) (hp' : IsProbDist p') :
    entropy (prodDist p p') = entropy p + entropy p' := by
  have h1 : ∑ i, ∑ j, p' j * Real.negMulLog (p i) = ∑ i, Real.negMulLog (p i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hp'.sum_eq_one, one_mul]
  have h2 : ∑ i, ∑ j, p i * Real.negMulLog (p' j) = ∑ j, Real.negMulLog (p' j) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
  unfold entropy
  simp_rw [Real.negMulLog_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  rw [h1, h2]

/-- Free energy is additive for a product distribution. -/
lemma freeEnergy_prod {p : ι → ℝ} {p' : κ → ℝ} (hp : IsProbDist p) (hp' : IsProbDist p')
    (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    freeEnergy (sumEnergy E E') β (prodDist p p') = freeEnergy E β p + freeEnergy E' β p' := by
  unfold freeEnergy
  rw [meanEnergy_prod hp hp', entropy_prod hp hp']
  ring

/-! ### At equilibrium -/

/-- The mean energy of the combined Boltzmann distribution is the sum of the individual mean
energies. -/
lemma meanEnergy_boltzmann_prod [Nonempty ι] [Nonempty κ] (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    meanEnergy (sumEnergy E E') (boltzmann (sumEnergy E E') β)
      = meanEnergy E (boltzmann E β) + meanEnergy E' (boltzmann E' β) := by
  rw [boltzmann_prod]
  exact meanEnergy_prod (isProbDist_boltzmann E β) (isProbDist_boltzmann E' β) E E'

/-- The entropy of the combined Boltzmann distribution is the sum of the entropies of the
individual Boltzmann distributions. -/
lemma entropy_boltzmann_prod [Nonempty ι] [Nonempty κ] (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    entropy (boltzmann (sumEnergy E E') β)
      = entropy (boltzmann E β) + entropy (boltzmann E' β) := by
  rw [boltzmann_prod]
  exact entropy_prod (isProbDist_boltzmann E β) (isProbDist_boltzmann E' β)

/-- The equilibrium free energy of the combined system is the sum of the individual
equilibrium free energies. -/
lemma freeEnergy_boltzmann_prod [Nonempty ι] [Nonempty κ] (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    freeEnergy (sumEnergy E E') β (boltzmann (sumEnergy E E') β)
      = freeEnergy E β (boltzmann E β) + freeEnergy E' β (boltzmann E' β) := by
  rw [boltzmann_prod]
  exact freeEnergy_prod (isProbDist_boltzmann E β) (isProbDist_boltzmann E' β) E E' β

end MaxEnt
