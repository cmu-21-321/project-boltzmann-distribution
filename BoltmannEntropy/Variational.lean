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
  sorry

/-- The free energy of the Boltzmann distribution is `-(log Z) / β`. -/
lemma freeEnergy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0) :
    freeEnergy E β (boltzmann E β) = -Real.log (partitionFn E β) / β := by
  sorry

/-- **Main theorem (Gibbs variational principle):**
the Boltzmann distribution minimizes free energy. -/
theorem freeEnergy_boltzmann_le [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q) :
    freeEnergy E β (boltzmann E β) ≤ freeEnergy E β q := by
  sorry

/-- The Boltzmann distribution is the only minimizer of free energy. -/
theorem freeEnergy_eq_freeEnergy_boltzmann_iff [Nonempty ι] (E : ι → ℝ) {β : ℝ}
    (hβ : 0 < β) {q : ι → ℝ} (hq : IsProbDist q) :
    freeEnergy E β q = freeEnergy E β (boltzmann E β) ↔ q = boltzmann E β := by
  sorry

/-- **Maximum entropy:** among distributions with the same average energy as the
Boltzmann distribution, none has more entropy. -/
theorem entropy_le_entropy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q)
    (hU : meanEnergy E q = meanEnergy E (boltzmann E β)) :
    entropy q ≤ entropy (boltzmann E β) := by
  sorry

/-- Strict maximum entropy: any other such distribution has strictly less entropy. -/
theorem entropy_lt_entropy_boltzmann [Nonempty ι] (E : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    {q : ι → ℝ} (hq : IsProbDist q)
    (hU : meanEnergy E q = meanEnergy E (boltzmann E β)) (hne : q ≠ boltzmann E β) :
    entropy q < entropy (boltzmann E β) := by
  sorry

/-- No distribution has more entropy than the uniform one. -/
theorem entropy_le_log_card [Nonempty ι] {q : ι → ℝ} (hq : IsProbDist q) :
    entropy q ≤ Real.log (Fintype.card ι : ℝ) := by
  sorry

end MaxEnt
