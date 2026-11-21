/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Gibbs

/-!
# The Gibbs variational principle and maximum entropy

The key identity is `β U(q) - S(q) + log Z = D(q ‖ p)`, where `p` is the Boltzmann
distribution. It holds for every real `β`. Dividing by `β ≠ 0` gives
`β F(q) + log Z = D(q ‖ p)`.

With Gibbs' inequality it shows that `p` is the unique minimizer of free energy when `β > 0`.
It also shows, for every `β`, that `p` is the unique maximum-entropy distribution with its
average energy.

## Main results

* `MaxEnt.mul_meanEnergy_sub_entropy_add_log_partitionFn` : the key identity.
* `MaxEnt.mul_freeEnergy_add_log_partitionFn` : the key identity in terms of free energy.
* `MaxEnt.entropy_boltzmann` : `S(p) = β U(p) + log Z`.
* `MaxEnt.freeEnergy_boltzmann` : `F(p) = -(log Z) / β`.
* `MaxEnt.freeEnergy_boltzmann_le` : the Boltzmann distribution minimizes free energy.
* `MaxEnt.freeEnergy_eq_freeEnergy_boltzmann_iff` : it is the only minimizer.
* `MaxEnt.entropy_le_entropy_boltzmann` : maximum entropy at fixed average energy.
* `MaxEnt.entropy_lt_entropy_boltzmann` : strict version.
* `MaxEnt.entropy_le_log_card` : no distribution beats the uniform one.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- Key identity: `β U(q) - S(q) + log Z = D(q ‖ p)`, valid for every real `β`. -/
lemma mul_meanEnergy_sub_entropy_add_log_partitionFn [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    {q : ι → ℝ} (hq : IsProbDist q) :
    β * meanEnergy E q - entropy q + Real.log (partitionFn E β)
      = relEntropy q (boltzmann E β) := by
  have hZ : Real.log (partitionFn E β) = ∑ i, q i * Real.log (partitionFn E β) := by
    rw [← Finset.sum_mul, hq.sum_eq_one, one_mul]
  rw [hZ]
  unfold meanEnergy entropy relEntropy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i = 0
  · simp [h]
  · rw [Real.log_div h (boltzmann_pos E β i).ne', log_boltzmann]
    simp only [Real.negMulLog]
    ring

/-- Key identity in terms of free energy: `β F(q) + log Z = D(q ‖ p)` for `β ≠ 0`. -/
lemma mul_freeEnergy_add_log_partitionFn [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0)
    {q : ι → ℝ} (hq : IsProbDist q) :
    β * freeEnergy E β q + Real.log (partitionFn E β) = relEntropy q (boltzmann E β) := by
  rw [← mul_meanEnergy_sub_entropy_add_log_partitionFn E β hq]
  unfold freeEnergy
  field_simp

/-- The Boltzmann distribution has zero relative entropy to itself. -/
lemma relEntropy_boltzmann_self [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    relEntropy (boltzmann E β) (boltzmann E β) = 0 :=
  (relEntropy_eq_zero_iff (isProbDist_boltzmann E β) (boltzmann_pos E β)
    (isProbDist_boltzmann E β)).mpr rfl

/-- The entropy of the Boltzmann distribution is `S(p) = β U(p) + log Z`. -/
lemma entropy_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    entropy (boltzmann E β)
      = β * meanEnergy E (boltzmann E β) + Real.log (partitionFn E β) := by
  have h := mul_meanEnergy_sub_entropy_add_log_partitionFn E β (isProbDist_boltzmann E β)
  rw [relEntropy_boltzmann_self] at h
  linarith

/-- The free energy of the Boltzmann distribution is `-(log Z) / β`. -/
lemma freeEnergy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0) :
    freeEnergy E β (boltzmann E β) = -Real.log (partitionFn E β) / β := by
  have h := mul_freeEnergy_add_log_partitionFn E hβ (isProbDist_boltzmann E β)
  rw [relEntropy_boltzmann_self] at h
  rw [eq_div_iff hβ]
  linarith

/-- **Main theorem (Gibbs variational principle):**
the Boltzmann distribution minimizes free energy. -/
theorem freeEnergy_boltzmann_le [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q) :
    freeEnergy E β (boltzmann E β) ≤ freeEnergy E β q := by
  have h1 := mul_freeEnergy_add_log_partitionFn E hβ.ne' hq
  have h2 := relEntropy_nonneg (isProbDist_boltzmann E β) (boltzmann_pos E β) hq
  rw [freeEnergy_boltzmann E hβ.ne', div_le_iff₀ hβ]
  linarith

/-- The Boltzmann distribution is the only minimizer of free energy. -/
theorem freeEnergy_eq_freeEnergy_boltzmann_iff [Nonempty ι] (E : ι → ℝ) {β : ℝ}
    (hβ : 0 < β) {q : ι → ℝ} (hq : IsProbDist q) :
    freeEnergy E β q = freeEnergy E β (boltzmann E β) ↔ q = boltzmann E β := by
  constructor
  · intro h
    apply (relEntropy_eq_zero_iff (isProbDist_boltzmann E β) (boltzmann_pos E β) hq).mp
    rw [← mul_freeEnergy_add_log_partitionFn E hβ.ne' hq, h,
      mul_freeEnergy_add_log_partitionFn E hβ.ne' (isProbDist_boltzmann E β),
      relEntropy_boltzmann_self]
  · rintro rfl
    rfl

/-- **Maximum entropy:** among distributions with the same average energy as the
Boltzmann distribution, none has more entropy. This holds for every real `β`. -/
theorem entropy_le_entropy_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    {q : ι → ℝ} (hq : IsProbDist q)
    (hU : meanEnergy E q = meanEnergy E (boltzmann E β)) :
    entropy q ≤ entropy (boltzmann E β) := by
  have h1 := mul_meanEnergy_sub_entropy_add_log_partitionFn E β hq
  have h2 := relEntropy_nonneg (isProbDist_boltzmann E β) (boltzmann_pos E β) hq
  rw [entropy_boltzmann, ← hU]
  linarith

/-- Strict maximum entropy: any other such distribution has strictly less entropy. -/
theorem entropy_lt_entropy_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    {q : ι → ℝ} (hq : IsProbDist q)
    (hU : meanEnergy E q = meanEnergy E (boltzmann E β)) (hne : q ≠ boltzmann E β) :
    entropy q < entropy (boltzmann E β) := by
  have h1 := mul_meanEnergy_sub_entropy_add_log_partitionFn E β hq
  have h2 := relEntropy_pos (isProbDist_boltzmann E β) (boltzmann_pos E β) hq hne
  rw [entropy_boltzmann, ← hU]
  linarith

/-- No distribution has more entropy than the uniform one. -/
theorem entropy_le_log_card [Nonempty ι] {q : ι → ℝ} (hq : IsProbDist q) :
    entropy q ≤ Real.log (Fintype.card ι : ℝ) := by
  have hZ : partitionFn (fun _ : ι => (0 : ℝ)) 0 = Fintype.card ι := by
    simp [partitionFn]
  have h := entropy_le_entropy_boltzmann (fun _ : ι => (0 : ℝ)) 0 hq (by simp [meanEnergy])
  rwa [entropy_boltzmann, hZ, zero_mul, zero_add] at h

end MaxEnt
