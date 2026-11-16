module
public import BoltmannEntropy.Defs
/-!
# Temperature limits

* High temperature (`β → 0`): the Boltzmann distribution becomes uniform.
* Low temperature (`β → ∞`): the Boltzmann distribution concentrates uniformly
  on the ground states.

## Main results

* `MaxEnt.boltzmann_zero` : at `β = 0` every state has probability `1/n`.
* `MaxEnt.continuous_boltzmann` : each Boltzmann probability is continuous in `β`.
* `MaxEnt.tendsto_boltzmann_zero` : the high-temperature limit.
* `MaxEnt.tendsto_boltzmann_atTop` : the low-temperature limit; ground states
  get probability `1/|G|`, all other states get `0`.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace MaxEnt

variable {ι : Type*} [Fintype ι]

/-- At `β = 0` the Boltzmann distribution is uniform. -/
lemma boltzmann_zero [Nonempty ι] (E : ι → ℝ) (i : ι) :
    boltzmann E 0 i = 1 / (Fintype.card ι : ℝ) := by
  simp [boltzmann, partitionFn]

/-- Each Boltzmann probability depends continuously on `β`. -/
lemma continuous_boltzmann [Nonempty ι] (E : ι → ℝ) (i : ι) :
    Continuous (fun β => boltzmann E β i) := by
  unfold boltzmann
  refine Continuous.div (by fun_prop) ?_ (fun β => (partitionFn_pos E β).ne')
  unfold partitionFn
  fun_prop

/-- **High-temperature limit:** as `β → 0`, every state has probability `1/n`. -/
theorem tendsto_boltzmann_zero [Nonempty ι] (E : ι → ℝ) (i : ι) :
    Tendsto (fun β => boltzmann E β i) (𝓝 0) (𝓝 (1 / (Fintype.card ι : ℝ))) := by
  rw [← boltzmann_zero E i]
  exact (continuous_boltzmann E i).tendsto 0

/-- The minimum energy among all states. -/
def groundEnergy [Nonempty ι] (E : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty E

/-- The set of states attaining the minimum energy. -/
def groundStates [Nonempty ι] (E : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => E i = groundEnergy E)

/-- The ground-state energy is less than or equal to every state energy. -/
lemma groundEnergy_le [Nonempty ι] (E : ι → ℝ) (i : ι) :
    groundEnergy E ≤ E i := by
  unfold groundEnergy
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The set of ground states is nonempty. -/
lemma groundStates_nonempty [Nonempty ι] (E : ι → ℝ) :
    (groundStates E).Nonempty := by
  classical
  unfold groundStates groundEnergy
  obtain ⟨i, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
  refine ⟨i, Finset.mem_filter.mpr ?_⟩
  constructor
  · exact hi.left
  · exact hi.right.symm

/-- Subtracting a constant from every energy does not change
the Boltzmann distribution. -/
lemma boltzmann_sub_const [Nonempty ι] (E : ι → ℝ) (β c : ℝ) (i : ι) :
    boltzmann (fun j => E j - c) β i = boltzmann E β i := by
  unfold boltzmann partitionFn
  have hexp (j : ι) :
      Real.exp (-β * (E j - c)) =
        Real.exp (β * c) * Real.exp (-β * E j) := by
    rw [show -β * (E j - c) = β * c + (-β * E j) by ring]
    rw [Real.exp_add]
  simp_rw [hexp]
  have hsum :
      (∑ x, Real.exp (β * c) * Real.exp (-β * E x)) =
        Real.exp (β * c) * ∑ x, Real.exp (-β * E x) := by
          rw [Finset.mul_sum]
  rw [hsum]
  field_simp

/-- An exponential term converges to zero for positive energy
and remains one for zero energy. -/
lemma tendsto_exp_neg_mul_atTop (a : ℝ) (ha : 0 ≤ a) :
    Tendsto
      (fun β : ℝ => Real.exp (-β * a))
      Filter.atTop
      (nhds (if a = 0 then 1 else 0)) := by
  by_cases h : a = 0
  · simp [h]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    have hneg : -a < 0 := by linarith
    have harg : Tendsto (fun β : ℝ => -β * a)
      Filter.atTop Filter.atBot := by
      have hfun : (fun β : ℝ => -β * a) = (fun β => -a * β) := by
        funext β
        ring
      rw [hfun]
      exact tendsto_id.const_mul_atTop_of_neg hneg
    have hlim : Tendsto (fun β : ℝ => Real.exp (-β * a))
        Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp harg
    simpa [h] using hlim

/-- Shifting an energy by the ground-state energy gives a nonnegative value:
`0 ≤ Eᵢ - E₀`. -/
lemma shiftedEnergy_nonneg [Nonempty ι]
    (E : ι → ℝ) (i : ι) :
    0 ≤ E i - groundEnergy E := by
  exact sub_nonneg.mpr (groundEnergy_le E i)

/-- As `β → ∞`, the shifted Boltzmann weight `exp (-β (Eᵢ - E₀))` tends to `1`
if `i` is a ground state and to `0` otherwise. -/
lemma tendsto_exp_shifted_energy [Nonempty ι]
    (E : ι → ℝ) (i : ι)
    [Decidable (i ∈ groundStates E)] :
    Tendsto
      (fun β : ℝ =>
        Real.exp (-β * (E i - groundEnergy E)))
      Filter.atTop
      (nhds (if i ∈ groundStates E then (1 : ℝ) else 0)) := by
  have h := tendsto_exp_neg_mul_atTop
    (E i - groundEnergy E)
    (shiftedEnergy_nonneg E i)
  simpa [groundStates, sub_eq_zero] using h

/-- As `β → ∞`, the shifted partition function `∑ⱼ exp (-β (Eⱼ - E₀))` tends to
the number of ground states `|G|`. -/
lemma tendsto_shifted_partitionFn [Nonempty ι]
    (E : ι → ℝ) :
    Tendsto
      (fun β : ℝ =>
        ∑ i, Real.exp (-β * (E i - groundEnergy E)))
      Filter.atTop
      (nhds ((groundStates E).card : ℝ)) := by
  classical
  have hterm (i : ι) :=
    tendsto_exp_shifted_energy E i
  have hsum :
      Tendsto
        (fun β : ℝ =>
          ∑ i, Real.exp (-β * (E i - groundEnergy E)))
        Filter.atTop
        (nhds (∑ i, if i ∈ groundStates E then (1 : ℝ) else 0)) := by
    apply tendsto_finsetSum
    intro i hi
    exact hterm i
  convert hsum using 1
  simp [groundStates]

/-- **Low-temperature limit:** as β tends to infinity, the Boltzmann
distribution converges to the uniform distribution over ground states.

Ground states have limiting probability 1 / |G|, while all other
states have limiting probability 0. -/
theorem tendsto_boltzmann_atTop [Nonempty ι]
    (E : ι → ℝ) (i : ι)
    [Decidable (i ∈ groundStates E)] :
    Tendsto
      (fun β : ℝ => boltzmann E β i)
      Filter.atTop
      (nhds (if i ∈ groundStates E
        then 1 / ((groundStates E).card : ℝ)
        else 0)) := by
  have hnum := tendsto_exp_shifted_energy E i
  have hden := tendsto_shifted_partitionFn E
  have hcard : (groundStates E).card ≠ 0 :=
    Nat.ne_of_gt (Finset.card_pos.mpr (groundStates_nonempty E))
  have hquot := hnum.div hden (by exact_mod_cast hcard)
  have hrewrite (β : ℝ) :
      boltzmann E β i =
        (Real.exp (-β * (E i - groundEnergy E))) /
          (∑ j, Real.exp (-β * (E j - groundEnergy E))) := by
    rw [← boltzmann_sub_const E β (groundEnergy E) i]
    unfold boltzmann partitionFn
    rfl
  have hfinal :
      (if i ∈ groundStates E then (1 : ℝ) else 0) /
          (groundStates E).card =
        if i ∈ groundStates E
          then 1 / ((groundStates E).card : ℝ)
          else 0 := by
    split_ifs <;> simp
  have hfunc :
      (fun β : ℝ =>
        Real.exp (-β * (E i - groundEnergy E)) /
          (∑ j, Real.exp (-β * (E j - groundEnergy E)))) =
      (fun β => boltzmann E β i) := by
    funext β
    exact (hrewrite β).symm
  rw [hfinal] at hquot
  rw [← hfunc]
  exact hquot

end MaxEnt
