/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Variational
public import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

/-!
# Bridge to Physlib's canonical ensemble

The `MaxEnt` development works with a bare energy function `E : ι → ℝ` and a real inverse
temperature `β`. Physlib packages the same data as a `CanonicalEnsemble ι` together with a
`Temperature`, whose inverse temperature is `T.β = 1 / (k_B T)`.

For a finite ensemble (`[𝓒.IsFinite]`: counting measure, no continuous degrees of freedom) the
two descriptions agree. This file proves that they agree and restates the main results of this
project in Physlib's language.

Physlib only describes the equilibrium distribution, while the variational principle ranges over
*every* probability distribution `q`. So `q`, its mean energy and its entropy still use the
`MaxEnt` definitions.

## Dictionary

* `mathematicalPartitionFunction_eq_partitionFn`, `partitionFunction_eq_partitionFn` :
  `Z = MaxEnt.partitionFn 𝓒.energy T.β`.
* `probability_eq_boltzmann` : `𝓒.probability T = MaxEnt.boltzmann 𝓒.energy T.β`.
* `meanEnergy_eq_maxEnt_meanEnergy` : the equilibrium mean energies agree.
* `shannonEntropy_eq_kB_mul_entropy` : `S = k_B · MaxEnt.entropy`.
* `helmholtzFreeEnergy_eq_freeEnergy_boltzmann` : `F = MaxEnt.freeEnergy` at equilibrium.

## Main results in Physlib terms

* `helmholtzFreeEnergy_le` : Gibbs variational principle, `F ≤ U(q) - k_B T S(q)`.
* `helmholtzFreeEnergy_eq_iff` : equality holds only for the Boltzmann distribution.
* `kB_mul_entropy_le_shannonEntropy` : maximum entropy at fixed mean energy.
* `shannonEntropy_le_kB_mul_log_card` : `S ≤ k_B log |ι|`.
-/

@[expose] public section

noncomputable section

namespace CanonicalEnsemble

open Constants Temperature

variable {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (𝓒 : CanonicalEnsemble ι)

/-! ### Dictionary -/

/-- For a finite ensemble the partition function is the `MaxEnt` one at `β = T.β`. -/
theorem mathematicalPartitionFunction_eq_partitionFn [𝓒.IsFinite] (T : Temperature) :
    𝓒.mathematicalPartitionFunction T = MaxEnt.partitionFn 𝓒.energy (T.β : ℝ) := by
  rw [mathematicalPartitionFunction_of_fintype]
  rfl

theorem partitionFunction_eq_partitionFn [𝓒.IsFinite] (T : Temperature) :
    𝓒.partitionFunction T = MaxEnt.partitionFn 𝓒.energy (T.β : ℝ) := by
  rw [partitionFunction_of_fintype]
  rfl

theorem probability_eq_boltzmann [𝓒.IsFinite] (T : Temperature) (i : ι) :
    𝓒.probability T i = MaxEnt.boltzmann 𝓒.energy (T.β : ℝ) i := by
  rw [probability, mathematicalPartitionFunction_eq_partitionFn]
  rfl

theorem probability_eq_boltzmann_fun [𝓒.IsFinite] (T : Temperature) :
    𝓒.probability T = MaxEnt.boltzmann 𝓒.energy (T.β : ℝ) :=
  funext (𝓒.probability_eq_boltzmann T)

theorem isProbDist_probability [𝓒.IsFinite] [Nonempty ι] (T : Temperature) :
    MaxEnt.IsProbDist (𝓒.probability T) := by
  rw [probability_eq_boltzmann_fun]
  exact MaxEnt.isProbDist_boltzmann _ _

theorem meanEnergy_eq_maxEnt_meanEnergy [𝓒.IsFinite] (T : Temperature) :
    𝓒.meanEnergy T = MaxEnt.meanEnergy 𝓒.energy (𝓒.probability T) := by
  rw [meanEnergy_of_fintype, MaxEnt.meanEnergy]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [MeasurableSingletonClass ι] in
/-- Physlib's Shannon entropy carries a factor of `k_B`; `MaxEnt.entropy` is dimensionless. -/
theorem shannonEntropy_eq_kB_mul_entropy (T : Temperature) :
    𝓒.shannonEntropy T = kB * MaxEnt.entropy (𝓒.probability T) := by
  rw [shannonEntropy, MaxEnt.entropy_eq_neg_sum]
  ring

omit [MeasurableSingletonClass ι] in
/-- Since `1 / β = k_B T` (and Lean's `x / 0 = 0` makes this hold even at `T = 0`), the `MaxEnt`
free energy of any distribution is `U(q) - k_B T S(q)`. -/
theorem freeEnergy_eq_meanEnergy_sub (T : Temperature) (q : ι → ℝ) :
    MaxEnt.freeEnergy 𝓒.energy (T.β : ℝ) q
      = MaxEnt.meanEnergy 𝓒.energy q - kB * T.val * MaxEnt.entropy q := by
  rw [MaxEnt.freeEnergy, β_toReal, div_div_eq_mul_div, div_one]
  unfold Temperature.toReal
  ring

theorem helmholtzFreeEnergy_eq_freeEnergy_boltzmann [𝓒.IsFinite] [Nonempty ι]
    (T : Temperature) (hT : 0 < T.val) :
    𝓒.helmholtzFreeEnergy T
      = MaxEnt.freeEnergy 𝓒.energy (T.β : ℝ) (MaxEnt.boltzmann 𝓒.energy (T.β : ℝ)) := by
  rw [MaxEnt.freeEnergy_boltzmann _ (beta_pos T hT).ne', helmholtzFreeEnergy,
    partitionFunction_eq_partitionFn, β_toReal, div_div_eq_mul_div, div_one]
  unfold Temperature.toReal
  ring

/-! ### Main results in Physlib terms -/

/-- **Gibbs variational principle.** At positive temperature, no probability distribution `q`
has a lower free energy `U(q) - k_B T S(q)` than the equilibrium value `F = -k_B T log Z`. -/
theorem helmholtzFreeEnergy_le [𝓒.IsFinite] [Nonempty ι] (T : Temperature) (hT : 0 < T.val)
    {q : ι → ℝ} (hq : MaxEnt.IsProbDist q) :
    𝓒.helmholtzFreeEnergy T
      ≤ MaxEnt.meanEnergy 𝓒.energy q - kB * T.val * MaxEnt.entropy q := by
  rw [𝓒.helmholtzFreeEnergy_eq_freeEnergy_boltzmann T hT, ← 𝓒.freeEnergy_eq_meanEnergy_sub T q]
  exact MaxEnt.freeEnergy_boltzmann_le _ (beta_pos T hT) hq

/-- The equilibrium distribution `𝓒.probability T` is the only minimiser of free energy. -/
theorem helmholtzFreeEnergy_eq_iff [𝓒.IsFinite] [Nonempty ι] (T : Temperature)
    (hT : 0 < T.val) {q : ι → ℝ} (hq : MaxEnt.IsProbDist q) :
    MaxEnt.meanEnergy 𝓒.energy q - kB * T.val * MaxEnt.entropy q = 𝓒.helmholtzFreeEnergy T
      ↔ q = 𝓒.probability T := by
  rw [𝓒.helmholtzFreeEnergy_eq_freeEnergy_boltzmann T hT, ← 𝓒.freeEnergy_eq_meanEnergy_sub T q,
    probability_eq_boltzmann_fun]
  exact MaxEnt.freeEnergy_eq_freeEnergy_boltzmann_iff _ (beta_pos T hT) hq

/-- **Maximum entropy.** Among distributions with the same mean energy as the canonical
ensemble at temperature `T`, none has more entropy. -/
theorem kB_mul_entropy_le_shannonEntropy [𝓒.IsFinite] [Nonempty ι] (T : Temperature)
    {q : ι → ℝ} (hq : MaxEnt.IsProbDist q)
    (hU : MaxEnt.meanEnergy 𝓒.energy q = 𝓒.meanEnergy T) :
    kB * MaxEnt.entropy q ≤ 𝓒.shannonEntropy T := by
  rw [shannonEntropy_eq_kB_mul_entropy, probability_eq_boltzmann_fun]
  rw [meanEnergy_eq_maxEnt_meanEnergy, probability_eq_boltzmann_fun] at hU
  exact mul_le_mul_of_nonneg_left (MaxEnt.entropy_le_entropy_boltzmann _ _ hq hU)
    kB_nonneg

/-- The entropy of a finite canonical ensemble is at most `k_B log |ι|`. -/
theorem shannonEntropy_le_kB_mul_log_card [𝓒.IsFinite] [Nonempty ι] (T : Temperature) :
    𝓒.shannonEntropy T ≤ kB * Real.log (Fintype.card ι : ℝ) := by
  rw [shannonEntropy_eq_kB_mul_entropy]
  exact mul_le_mul_of_nonneg_left (MaxEnt.entropy_le_log_card (𝓒.isProbDist_probability T))
    kB_nonneg

end CanonicalEnsemble
