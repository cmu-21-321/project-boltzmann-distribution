/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Variational

/-!
# Thermodynamic identities

How the equilibrium quantities change with the inverse temperature `β`. Write
`U(β) = meanEnergy E (boltzmann E β)` for the equilibrium mean energy and
`Var(β) = ∑ pᵢ (Eᵢ - U)²` for the energy variance. Then

* `d(log Z)/dβ = -U`,
* `dU/dβ = -Var ≤ 0`, so the mean energy decreases as `β` grows (as temperature falls), and
  strictly so unless all energies are equal,
* `dS/dβ = -β Var`, so for `β > 0` the entropy decreases as `β` grows,
* with `T = 1/β` (and `k_B = 1`), the heat capacity `C = dU/dT = β² Var` is nonnegative.

The identity `S = β U + log Z` (`MaxEnt.entropy_boltzmann`) is in `Variational.lean`.

## Main results

* `MaxEnt.hasDerivAt_log_partitionFn` : `d(log Z)/dβ = -U`.
* `MaxEnt.hasDerivAt_boltzmann` : `dpᵢ/dβ = pᵢ (U - Eᵢ)`.
* `MaxEnt.hasDerivAt_meanEnergy_boltzmann` : `dU/dβ = -Var`.
* `MaxEnt.meanEnergy_boltzmann_antitone`, `MaxEnt.meanEnergy_boltzmann_strictAnti` :
  the mean energy is decreasing in `β`.
* `MaxEnt.hasDerivAt_entropy_boltzmann` : `dS/dβ = -β Var`.
* `MaxEnt.entropy_boltzmann_antitoneOn` : entropy is decreasing in `β` for `β ≥ 0`.
* `MaxEnt.hasDerivAt_meanEnergy_temperature`, `MaxEnt.heatCapacity_nonneg` : `dU/dT = C ≥ 0`.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The energy variance at equilibrium: `Var(β) = ∑ pᵢ (Eᵢ - U)²`. -/
def energyVariance (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, boltzmann E β i * (E i - meanEnergy E (boltzmann E β)) ^ 2

/-- The heat capacity at equilibrium, in units where `k_B = 1`: `C(β) = β² Var(β)`. -/
def heatCapacity (E : ι → ℝ) (β : ℝ) : ℝ :=
  β ^ 2 * energyVariance E β

/-! ### Energy variance -/

theorem energyVariance_nonneg (E : ι → ℝ) (β : ℝ) : 0 ≤ energyVariance E β :=
  Finset.sum_nonneg fun i _ => mul_nonneg (boltzmann_pos E β i).le (sq_nonneg _)

/-- `Var = ⟨E²⟩ - U²`. -/
theorem energyVariance_eq (E : ι → ℝ) (β : ℝ) :
    energyVariance E β
      = ∑ i, boltzmann E β i * E i ^ 2 - meanEnergy E (boltzmann E β) ^ 2 := by
  unfold energyVariance
  set U := meanEnergy E (boltzmann E β) with hU
  have h : ∀ i, boltzmann E β i * (E i - U) ^ 2
      = boltzmann E β i * E i ^ 2 - 2 * U * (boltzmann E β i * E i) + U ^ 2 * boltzmann E β i :=
    fun i => by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_boltzmann]
  rw [hU, meanEnergy]
  ring

/-- The variance is positive unless all energies are equal. -/
theorem energyVariance_pos (E : ι → ℝ) (β : ℝ) (hE : ∃ i j, E i ≠ E j) :
    0 < energyVariance E β := by
  refine (energyVariance_nonneg E β).lt_of_ne fun h => ?_
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_nonneg (boltzmann_pos E β i).le (sq_nonneg _)).mp h.symm
  have hconst : ∀ i, E i = meanEnergy E (boltzmann E β) := fun i => by
    have := hzero i (Finset.mem_univ i)
    rw [mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at this
    exact this.resolve_left (boltzmann_pos E β i).ne'
  obtain ⟨i, j, hij⟩ := hE
  exact hij ((hconst i).trans (hconst j).symm)

theorem heatCapacity_nonneg (E : ι → ℝ) (β : ℝ) : 0 ≤ heatCapacity E β :=
  mul_nonneg (sq_nonneg β) (energyVariance_nonneg E β)

/-! ### Derivatives in `β` -/

omit [Fintype ι] [Nonempty ι] in
lemma hasDerivAt_exp_neg_mul (a β : ℝ) :
    HasDerivAt (fun β => Real.exp (-β * a)) (-a * Real.exp (-β * a)) β := by
  convert ((hasDerivAt_neg' β).mul_const a).exp using 1
  ring

/-- `∑ⱼ Eⱼ exp (-β Eⱼ) = Z U`. -/
lemma sum_mul_exp_eq (E : ι → ℝ) (β : ℝ) :
    ∑ j, E j * Real.exp (-β * E j) = partitionFn E β * meanEnergy E (boltzmann E β) := by
  have hZ := (partitionFn_pos E β).ne'
  rw [meanEnergy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [boltzmann]
  field_simp

omit [Nonempty ι] in
lemma hasDerivAt_partitionFn (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun β => partitionFn E β) (-∑ j, E j * Real.exp (-β * E j)) β := by
  rw [← Finset.sum_neg_distrib]
  simp_rw [← neg_mul]
  exact HasDerivAt.fun_sum fun j _ => hasDerivAt_exp_neg_mul (E j) β

/-- `d(log Z)/dβ = -U`. -/
theorem hasDerivAt_log_partitionFn (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun β => Real.log (partitionFn E β)) (-meanEnergy E (boltzmann E β)) β := by
  have hZ := (partitionFn_pos E β).ne'
  convert (hasDerivAt_partitionFn E β).log hZ using 1
  rw [sum_mul_exp_eq]
  field_simp

/-- `dpᵢ/dβ = pᵢ (U - Eᵢ)`. -/
theorem hasDerivAt_boltzmann (E : ι → ℝ) (β : ℝ) (i : ι) :
    HasDerivAt (fun β => boltzmann E β i)
      (boltzmann E β i * (meanEnergy E (boltzmann E β) - E i)) β := by
  have hZ := (partitionFn_pos E β).ne'
  have h := (hasDerivAt_exp_neg_mul (E i) β).div (hasDerivAt_partitionFn E β) hZ
  change HasDerivAt (fun β => Real.exp (-β * E i) / partitionFn E β) _ β
  convert h using 1
  rw [sum_mul_exp_eq]
  set U := meanEnergy E (boltzmann E β)
  rw [boltzmann]
  field_simp
  ring

/-- `dU/dβ = -Var`. -/
theorem hasDerivAt_meanEnergy_boltzmann (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun β => meanEnergy E (boltzmann E β)) (-energyVariance E β) β := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_boltzmann E β i).mul_const (E i)
  refine h.congr_deriv ?_
  rw [energyVariance_eq]
  set U := meanEnergy E (boltzmann E β) with hU
  have hterm : ∀ i, boltzmann E β i * (U - E i) * E i
      = U * (boltzmann E β i * E i) - boltzmann E β i * E i ^ 2 := fun i => by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hU, meanEnergy]
  ring

/-- The mean energy decreases as `β` increases. -/
theorem meanEnergy_boltzmann_antitone (E : ι → ℝ) :
    Antitone (fun β => meanEnergy E (boltzmann E β)) :=
  antitone_of_deriv_nonpos (fun β => (hasDerivAt_meanEnergy_boltzmann E β).differentiableAt)
    fun β => by
      rw [(hasDerivAt_meanEnergy_boltzmann E β).deriv]
      linarith [energyVariance_nonneg E β]

/-- Unless all energies are equal, the mean energy strictly decreases as `β` increases. -/
theorem meanEnergy_boltzmann_strictAnti (E : ι → ℝ) (hE : ∃ i j, E i ≠ E j) :
    StrictAnti (fun β => meanEnergy E (boltzmann E β)) :=
  strictAnti_of_deriv_neg fun β => by
    rw [(hasDerivAt_meanEnergy_boltzmann E β).deriv]
    linarith [energyVariance_pos E β hE]

/-- `dS/dβ = -β Var`. -/
theorem hasDerivAt_entropy_boltzmann (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun β => entropy (boltzmann E β)) (-β * energyVariance E β) β := by
  have h := ((hasDerivAt_id' β).mul (hasDerivAt_meanEnergy_boltzmann E β)).add
    (hasDerivAt_log_partitionFn E β)
  rw [show (fun β => entropy (boltzmann E β)) = fun β =>
      β * meanEnergy E (boltzmann E β) + Real.log (partitionFn E β) from
    funext (entropy_boltzmann E)]
  convert h using 1
  ring

/-- At positive temperature, the entropy decreases as `β` increases, that is, it increases
with temperature. -/
theorem entropy_boltzmann_antitoneOn (E : ι → ℝ) :
    AntitoneOn (fun β => entropy (boltzmann E β)) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun β _ => (hasDerivAt_entropy_boltzmann E β).continuousAt.continuousWithinAt)
    (fun β _ => (hasDerivAt_entropy_boltzmann E β).differentiableAt.differentiableWithinAt)
    fun β hβ => ?_
  rw [interior_Ici] at hβ
  rw [(hasDerivAt_entropy_boltzmann E β).deriv]
  nlinarith [energyVariance_nonneg E β, Set.mem_Ioi.mp hβ]

/-! ### Temperature -/

/-- With `T = 1/β`, the heat capacity is the temperature derivative of the mean energy:
`dU/dT = β² Var`. -/
theorem hasDerivAt_meanEnergy_temperature (E : ι → ℝ) {T : ℝ} (hT : T ≠ 0) :
    HasDerivAt (fun T => meanEnergy E (boltzmann E T⁻¹)) (heatCapacity E T⁻¹) T := by
  refine ((hasDerivAt_meanEnergy_boltzmann E T⁻¹).comp T (hasDerivAt_inv hT)).congr_deriv ?_
  rw [heatCapacity, inv_pow]
  ring

end MaxEnt
