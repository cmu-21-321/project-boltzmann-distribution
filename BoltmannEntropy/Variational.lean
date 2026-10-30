module
public import BoltmannEntropy.Gibbs
@[expose] public section

/-!
# The Gibbs variational principle and maximum entropy

The key identity is `β F(q) + log Z = D(q ‖ p)`, where `p` is the Boltzmann distribution.
With Gibbs' inequality it shows that `p` is the unique minimizer of free energy, and
therefore the unique maximum-entropy distribution with its average energy.

## Main results

* `MaxEnt.mul_freeEnergy_add_log_partitionFn` : the key identity.
* `MaxEnt.freeEnergy_boltzmann` : `F(p) = -(log Z) / β`.
* `MaxEnt.freeEnergy_boltzmann_le` : the Boltzmann distribution minimizes free energy.
* `MaxEnt.freeEnergy_eq_freeEnergy_boltzmann_iff` : it is the only minimizer.
* `MaxEnt.entropy_le_entropy_boltzmann` : maximum entropy at fixed average energy.
* `MaxEnt.entropy_lt_entropy_boltzmann` : strict version.
* `MaxEnt.entropy_le_log_card` : no distribution beats the uniform one.
-/

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- Key idenity: `β F(q) + log Z = D(q || p)`-/

lemma mul_freeEnergy_add_log_partitionFn [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0)
  {q : ι → ℝ} (hq : IsProbDist q) :
  β * freeEnergy E β q + Real.log (partitionFn E β) = relEntropy q (boltzmann E β) := by
  have hF : β * freeEnergy E β q = β * meanEnergy E q - entropy q := by
    unfold freeEnergy
    field_simp
  have hZ : Real.log (partitionFn E β) = ∑ i, q i * Real.log (partitionFn E β) := by
    rw [← Finset.sum_mul, hq.sum_eq_one, one_mul]
  rw [hF, hZ]
  unfold meanEnergy entropy relEntropy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i = 0
  · simp [h]
  · rw [Real.log_div h (boltzmann_pos E β i).ne', log_boltzmann]
    simp only [Real.negMulLog]
    ring


/-- The free energy of the Boltzmann distribution is `-(log Z) / β`. -/
lemma freeEnergy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0) :
    freeEnergy E β (boltzmann E β) = -Real.log (partitionFn E β) / β := by
  have h := mul_freeEnergy_add_log_partitionFn E hβ (isProbDist_boltzmann E β)
  rw [(relEntropy_eq_zero_iff (boltzmann_pos E β) (sum_boltzmann E β)
    (isProbDist_boltzmann E β)).mpr rfl] at h
  rw [eq_div_iff hβ]
  linarith

/-- **Main theorem (Gibbs variational principle):**
the Boltzmann distribution minimizes free energy. -/
theorem freeEnergy_boltzmann_le [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q) :
    freeEnergy E β (boltzmann E β) ≤ freeEnergy E β q := by
  have h1 := mul_freeEnergy_add_log_partitionFn E hβ.ne' hq
  have h2 := relEntropy_nonneg (boltzmann_pos E β) (sum_boltzmann E β) hq
  rw [freeEnergy_boltzmann E hβ.ne', div_le_iff₀ hβ]
  linarith

/-- The Boltzmann distribution is the only minimizer of free energy. -/
theorem freeEnergy_eq_freeEnergy_boltzmann_iff [Nonempty ι] (E : ι → ℝ) {β : ℝ}
    (hβ : 0 < β) {q : ι → ℝ} (hq : IsProbDist q) :
    freeEnergy E β q = freeEnergy E β (boltzmann E β) ↔ q = boltzmann E β := by
  constructor
  · intro h
    apply (relEntropy_eq_zero_iff (boltzmann_pos E β) (sum_boltzmann E β) hq).mp
    rw [← mul_freeEnergy_add_log_partitionFn E hβ.ne' hq, h,
      mul_freeEnergy_add_log_partitionFn E hβ.ne' (isProbDist_boltzmann E β)]
    exact (relEntropy_eq_zero_iff (boltzmann_pos E β) (sum_boltzmann E β)
      (isProbDist_boltzmann E β)).mpr rfl
  · rintro rfl
    rfl

/-- **Maximum entropy:** among distributions with the same average energy as the
Boltzmann distribution, none has more entropy. -/
theorem entropy_le_entropy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q)
    (hU : meanEnergy E q = meanEnergy E (boltzmann E β)) :
    entropy q ≤ entropy (boltzmann E β) := by
  have h := freeEnergy_boltzmann_le E hβ hq
  unfold freeEnergy at h
  have h' : entropy q / β ≤ entropy (boltzmann E β) / β := by linarith
  exact (div_le_div_iff_of_pos_right hβ).mp h'

/-- Strict maximum entropy: any other such distribution has strictly less entropy. -/
theorem entropy_lt_entropy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q)
    (hU : meanEnergy E q = meanEnergy E (boltzmann E β)) (hne : q ≠ boltzmann E β) :
    entropy q < entropy (boltzmann E β) := by
  apply lt_of_le_of_ne (entropy_le_entropy_boltzmann E hβ hq hU)
  intro h
  apply hne
  apply (freeEnergy_eq_freeEnergy_boltzmann_iff E hβ hq).mp
  unfold freeEnergy
  rw [hU, h]

/-- No distribution has more entropy than the uniform one. -/
theorem entropy_le_log_card [Nonempty ι] {q : ι → ℝ} (hq : IsProbDist q) :
    entropy q ≤ Real.log (Fintype.card ι : ℝ) := by
  have hZ : partitionFn (fun _ : ι => (0 : ℝ)) 1 = Fintype.card ι := by
    simp [partitionFn]
  have hU : meanEnergy (fun _ : ι => (0 : ℝ)) q = 0 := by
    simp [meanEnergy]
  have h := freeEnergy_boltzmann_le (fun _ : ι => (0 : ℝ)) one_pos hq
  rw [freeEnergy_boltzmann (fun _ : ι => (0 : ℝ)) one_ne_zero, hZ] at h
  unfold freeEnergy at h
  rw [hU] at h
  linarith

end MaxEnt
