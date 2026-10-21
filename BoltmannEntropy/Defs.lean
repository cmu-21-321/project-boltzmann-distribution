module
public import Mathlib
/-!
## Main definitions

* `MaxEnt.IsProbDist q` : `q` is a probability distribution on `ι`.
* `MaxEnt.entropy q` : Shannon entropy `S(q) = -∑ qᵢ log qᵢ` (natural log).
* `MaxEnt.meanEnergy E q` : average energy `U(q) = ∑ qᵢ Eᵢ`.
* `MaxEnt.partitionFn E β` : partition function `Z(β) = ∑ⱼ exp (-β Eⱼ)`.
* `MaxEnt.boltzmann E β` : Boltzmann distribution `pᵢ = exp (-β Eᵢ) / Z(β)`.
* `MaxEnt.freeEnergy E β q` : free energy `F(q) = U(q) - S(q) / β`.
* `MaxEnt.relEntropy q p` : relative entropy `D(q ‖ p) = ∑ qᵢ log (qᵢ / pᵢ)`.

-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- `q` is a probability distribution on the finite set of states `ι`. -/
def IsProbDist (q : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1

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

/-! ### Basic Proofs needed elsewhere
Z > 0
Boltzmann probabilities are positive and sum to 1
log of a Boltzmann probability -/

theorem IsProbDist.nonneg {q : ι → ℝ} (hq : IsProbDist q) (i : ι) : 0 ≤ q i := by
  rcases hq with ⟨a, b⟩
  apply a

theorem IsProbDist.sum_eq_one {q : ι → ℝ} (hq : IsProbDist q) : ∑ i, q i = 1 := by
  rcases hq with ⟨a, b⟩
  apply b

/-- A probability distribution can only live on a nonempty set of states. -/
theorem IsProbDist.nonempty {q : ι → ℝ} (hq : IsProbDist q) : Nonempty ι := by
  by_contra h
  have hempty : IsEmpty ι := not_nonempty_iff.mp h
  have hsum : ∑ i, q i = 0 := by
    simp
  rcases hq with ⟨a, b⟩
  rw [hsum] at b
  exact zero_ne_one b

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
    IsProbDist (boltzmann E β) := by
  unfold IsProbDist
  constructor
  · intro i
    exact le_of_lt (boltzmann_pos E β i)
  · exact sum_boltzmann E β

theorem log_boltzmann [Nonempty ι] (E : ι → ℝ) (β : ℝ) (i : ι) :
    Real.log (boltzmann E β i) = -β * E i - Real.log (partitionFn E β) := by
  unfold boltzmann
  rw [Real.log_div]
  · rw [Real.log_exp]
  · exact ne_of_gt (Real.exp_pos _)
  · exact ne_of_gt (partitionFn_pos E β)

end MaxEnt
