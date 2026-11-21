/-
Copyright (c) 2026 Yuktha Vemula, Cassandra Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuktha Vemula, Cassandra Yang
-/
module

public import BoltzmannEntropy.Defs

/-!
# Temperature limits

* High temperature (`β → 0`): the Boltzmann distribution becomes uniform.
* Low temperature (`β → ∞`): the Boltzmann distribution concentrates uniformly on the
  ground states.
* Negative temperature (`β → -∞`): the Boltzmann distribution concentrates uniformly on the
  highest-energy states, which are the ground states of `-E`.

The corresponding limits of the entropy and the mean energy follow by continuity.

## Main results

* `MaxEnt.boltzmann_zero` : at `β = 0` every state has probability `1/n`.
* `MaxEnt.continuous_boltzmann` : each Boltzmann probability is continuous in `β`.
* `MaxEnt.tendsto_boltzmann_zero` : the high-temperature limit.
* `MaxEnt.tendsto_boltzmann_atTop` : the low-temperature limit, `groundDist E`.
* `MaxEnt.tendsto_boltzmann_atBot` : the `β → -∞` limit, `groundDist (-E)`.
* `MaxEnt.tendsto_entropy_boltzmann_zero` : entropy tends to `log n` as `β → 0`.
* `MaxEnt.tendsto_entropy_boltzmann_atTop` : entropy tends to `log |G|` as `β → ∞`.
* `MaxEnt.tendsto_meanEnergy_boltzmann_atTop` : mean energy tends to the ground-state energy.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace MaxEnt

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### High temperature -/

omit [Nonempty ι] in
/-- At `β = 0` the Boltzmann distribution is uniform. -/
lemma boltzmann_zero (E : ι → ℝ) (i : ι) :
    boltzmann E 0 i = 1 / (Fintype.card ι : ℝ) := by
  simp [boltzmann, partitionFn]

/-- Each Boltzmann probability depends continuously on `β`. -/
lemma continuous_boltzmann (E : ι → ℝ) (i : ι) :
    Continuous (fun β => boltzmann E β i) := by
  unfold boltzmann
  refine Continuous.div (by fun_prop) ?_ (fun β => (partitionFn_pos E β).ne')
  unfold partitionFn
  fun_prop

/-- **High-temperature limit:** as `β → 0`, every state has probability `1/n`. -/
theorem tendsto_boltzmann_zero (E : ι → ℝ) (i : ι) :
    Tendsto (fun β => boltzmann E β i) (𝓝 0) (𝓝 (1 / (Fintype.card ι : ℝ))) := by
  rw [← boltzmann_zero E i]
  exact (continuous_boltzmann E i).tendsto 0

/-! ### Low temperature -/

omit [Fintype ι] [Nonempty ι] in
/-- An exponential term converges to zero for positive energy and remains one for zero
energy. -/
lemma tendsto_exp_neg_mul_atTop (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun β : ℝ => Real.exp (-β * a)) atTop (𝓝 (if a = 0 then 1 else 0)) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  · have harg : Tendsto (fun β : ℝ => -β * a) atTop atBot := by
      simpa [neg_mul, mul_comm] using tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha)
    rw [show (if a = 0 then (1 : ℝ) else 0) = 0 by simp [ha.ne']]
    exact Real.tendsto_exp_atBot.comp harg

/-- As `β → ∞`, the shifted Boltzmann weight `exp (-β (Eᵢ - E₀))` tends to `1` if `i` is a
ground state and to `0` otherwise. -/
lemma tendsto_exp_shifted_energy (E : ι → ℝ) (i : ι) :
    Tendsto (fun β : ℝ => Real.exp (-β * (E i - groundEnergy E))) atTop
      (𝓝 (if E i = groundEnergy E then 1 else 0)) := by
  simpa [sub_eq_zero] using tendsto_exp_neg_mul_atTop _ (shiftedEnergy_nonneg E i)

/-- As `β → ∞`, the shifted partition function `∑ⱼ exp (-β (Eⱼ - E₀))` tends to the number of
ground states `|G|`. -/
lemma tendsto_shifted_partitionFn (E : ι → ℝ) :
    Tendsto (fun β : ℝ => ∑ i, Real.exp (-β * (E i - groundEnergy E))) atTop
      (𝓝 ((groundStates E).card : ℝ)) := by
  have hsum := tendsto_finsetSum Finset.univ fun i _ => tendsto_exp_shifted_energy E i
  rwa [sum_ite_groundEnergy, Finset.sum_const, nsmul_one] at hsum

/-- **Low-temperature limit:** as `β → ∞`, the Boltzmann distribution converges to the
uniform distribution on the ground states. Ground states have limiting probability `1 / |G|`,
and all other states have limiting probability `0`. -/
theorem tendsto_boltzmann_atTop (E : ι → ℝ) (i : ι) :
    Tendsto (fun β : ℝ => boltzmann E β i) atTop (𝓝 (groundDist E i)) := by
  have hquot := (tendsto_exp_shifted_energy E i).div (tendsto_shifted_partitionFn E)
    (groundStates_card_pos E).ne'
  have hlim : (if E i = groundEnergy E then (1 : ℝ) else 0) / (groundStates E).card
      = groundDist E i := by
    unfold groundDist
    split_ifs <;> simp
  rw [hlim] at hquot
  -- the shifted ratio is the Boltzmann distribution of `E - E₀`, which is that of `E`
  exact hquot.congr fun β => boltzmann_sub_const E β (groundEnergy E) i

/-! ### Negative temperature -/

/-- The ground states of `-E` are the states of highest energy. -/
theorem mem_groundStates_neg_iff (E : ι → ℝ) (i : ι) :
    i ∈ groundStates (-E) ↔ ∀ j, E j ≤ E i := by
  simp [mem_groundStates_iff_forall_le]

/-- **Negative-temperature limit:** as `β → -∞`, the Boltzmann distribution converges to the
uniform distribution on the highest-energy states. -/
theorem tendsto_boltzmann_atBot (E : ι → ℝ) (i : ι) :
    Tendsto (fun β : ℝ => boltzmann E β i) atBot (𝓝 (groundDist (-E) i)) := by
  have h := (tendsto_boltzmann_atTop (-E) i).comp tendsto_neg_atBot_atTop
  refine h.congr fun β => ?_
  simp [boltzmann_neg_neg]

/-! ### Entropy limits -/

lemma continuous_entropy_boltzmann (E : ι → ℝ) :
    Continuous (fun β => entropy (boltzmann E β)) :=
  continuous_finsetSum _ fun i _ =>
    Real.continuous_negMulLog.comp (continuous_boltzmann E i)

/-- The entropy of the uniform distribution on the ground states is `log |G|`. -/
lemma entropy_groundDist (E : ι → ℝ) :
    entropy (groundDist E) = Real.log ((groundStates E).card : ℝ) := by
  have hc := (groundStates_card_pos E).ne'
  unfold entropy groundDist
  simp_rw [apply_ite Real.negMulLog, Real.negMulLog_zero]
  rw [sum_ite_groundEnergy, Finset.sum_const, nsmul_eq_mul]
  simp only [Real.negMulLog, one_div, Real.log_inv]
  field_simp

/-- At high temperature, the entropy of the Boltzmann distribution tends to the logarithm of
the number of states. -/
theorem tendsto_entropy_boltzmann_zero (E : ι → ℝ) :
    Tendsto (fun β : ℝ => entropy (boltzmann E β)) (𝓝 0)
      (𝓝 (Real.log (Fintype.card ι : ℝ))) := by
  have h0 : entropy (boltzmann E 0) = Real.log (Fintype.card ι : ℝ) := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    unfold entropy
    simp_rw [boltzmann_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Real.negMulLog, one_div, Real.log_inv]
    field_simp
  rw [← h0]
  exact (continuous_entropy_boltzmann E).tendsto 0

/-- At low temperature, the entropy of the Boltzmann distribution tends to the logarithm of
the number of ground states. -/
theorem tendsto_entropy_boltzmann_atTop (E : ι → ℝ) :
    Tendsto (fun β : ℝ => entropy (boltzmann E β)) atTop
      (𝓝 (Real.log ((groundStates E).card : ℝ))) := by
  rw [← entropy_groundDist]
  exact tendsto_finsetSum _ fun i _ =>
    (Real.continuous_negMulLog.tendsto _).comp (tendsto_boltzmann_atTop E i)

/-- As `β → -∞`, the entropy of the Boltzmann distribution tends to the logarithm of the number
of highest-energy states. -/
theorem tendsto_entropy_boltzmann_atBot (E : ι → ℝ) :
    Tendsto (fun β : ℝ => entropy (boltzmann E β)) atBot
      (𝓝 (Real.log ((groundStates (-E)).card : ℝ))) := by
  rw [← entropy_groundDist]
  exact tendsto_finsetSum _ fun i _ =>
    (Real.continuous_negMulLog.tendsto _).comp (tendsto_boltzmann_atBot E i)

/-! ### Mean-energy limits -/

lemma continuous_meanEnergy_boltzmann (E : ι → ℝ) :
    Continuous (fun β => meanEnergy E (boltzmann E β)) :=
  continuous_finsetSum _ fun i _ => (continuous_boltzmann E i).mul continuous_const

/-- At low temperature, the mean energy tends to the ground-state energy. -/
theorem tendsto_meanEnergy_boltzmann_atTop (E : ι → ℝ) :
    Tendsto (fun β : ℝ => meanEnergy E (boltzmann E β)) atTop (𝓝 (groundEnergy E)) := by
  rw [← meanEnergy_groundDist]
  exact tendsto_finsetSum _ fun i _ => (tendsto_boltzmann_atTop E i).mul_const (E i)

/-- As `β → -∞`, the mean energy tends to the highest energy, `-groundEnergy (-E)`. -/
theorem tendsto_meanEnergy_boltzmann_atBot (E : ι → ℝ) :
    Tendsto (fun β : ℝ => meanEnergy E (boltzmann E β)) atBot (𝓝 (-groundEnergy (-E))) := by
  have h : meanEnergy E (groundDist (-E)) = -groundEnergy (-E) := by
    rw [← meanEnergy_groundDist (-E)]
    simp [meanEnergy]
  rw [← h]
  exact tendsto_finsetSum _ fun i _ => (tendsto_boltzmann_atBot E i).mul_const (E i)

end MaxEnt
