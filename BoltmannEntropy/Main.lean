module
public import BoltmannEntropy.Variational
/-!
# The principal result
-/

@[expose] public section

noncomputable section

namespace MaxEnt

/-- **Principal result.** For energies `E₁, …, Eₙ`, `β > 0` and any probability
distribution `q`, `∑ qᵢ Eᵢ + (1/β) ∑ qᵢ log qᵢ ≥ -(1/β) log Z`. -/
theorem declared_result {n : ℕ} (E : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    -(1 / β) * Real.log (∑ j, Real.exp (-β * E j))
      ≤ ∑ i, q i * E i + (1 / β) * ∑ i, q i * Real.log (q i) := by
  have hq : IsProbDist q := ⟨hq0, hq1⟩
  -- a probability distribution forces `n ≠ 0`
  have := hq.nonempty
  -- `freeEnergy_boltzmann` with `Z` written out
  have hp : freeEnergy E β (boltzmann E β)
      = -(1 / β) * Real.log (∑ j, Real.exp (-β * E j)) := by
    rw [freeEnergy_boltzmann E hβ.ne']
    unfold partitionFn
    ring
  have h := freeEnergy_boltzmann_le E hβ hq
  rw [hp, freeEnergy_eq_sum E β q] at h
  exact h

/-- Equality holds exactly for the Boltzmann distribution. -/
theorem declared_result_eq_iff {n : ℕ} (E : Fin n → ℝ) {β : ℝ} (hβ : 0 < β)
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    (∑ i, q i * E i + (1 / β) * ∑ i, q i * Real.log (q i)
        = -(1 / β) * Real.log (∑ j, Real.exp (-β * E j)))
      ↔ q = fun i => Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j) := by
  have hq : IsProbDist q := ⟨hq0, hq1⟩
  have := hq.nonempty
  have hp : freeEnergy E β (boltzmann E β)
      = -(1 / β) * Real.log (∑ j, Real.exp (-β * E j)) := by
    rw [freeEnergy_boltzmann E hβ.ne']
    unfold partitionFn
    ring
  have h := freeEnergy_eq_freeEnergy_boltzmann_iff E hβ hq
  rw [freeEnergy_eq_sum E β q, hp] at h
  -- `boltzmann E β` is by definition the explicit function on the right
  exact h

end MaxEnt
