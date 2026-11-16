module
public import BoltmannEntropy.Defs
public import BoltmannEntropy.Variational
public import BoltmannEntropy.Limits
/-!
# Stretch goals: independent systems and entropy limits

Combining two independent systems gives a product partition function,
a product Boltzmann distribution, and additive entropy.

We also establish the limiting entropy of the Boltzmann distribution
at high and low temperatures.

## Main results

* `MaxEnt.partitionFn_prod` : partition functions multiply.
* `MaxEnt.boltzmann_prod` : Boltzmann probabilities multiply.
* `MaxEnt.entropy_boltzmann_prod` : entropies add.
* `MaxEnt.tendsto_entropy_boltzmann_zero` : entropy tends to log n as β → 0.
* `MaxEnt.tendsto_entropy_boltzmann_atTop` : entropy tends to log |G| as β → ∞.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The partition function of two independent systems is the product
of their individual partition functions. -/
lemma partitionFn_prod (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    partitionFn (fun x : ι × κ => E x.1 + E' x.2) β =
      partitionFn E β * partitionFn E' β := by
  unfold partitionFn
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- The Boltzmann distribution of two independent systems is the
product of their individual Boltzmann distributions. -/
lemma boltzmann_prod (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ)
    (i : ι) (k : κ) :
    boltzmann (fun x : ι × κ => E x.1 + E' x.2) β (i, k) =
      boltzmann E β i * boltzmann E' β k := by
  unfold boltzmann
  rw [partitionFn_prod, div_mul_div_comm, ← Real.exp_add]
  congr 2
  ring

/-- Entropy is additive for a product distribution. -/
lemma entropy_prod_mul {p : ι → ℝ} {p' : κ → ℝ}
    (hp : ∑ i, p i = 1) (hp' : ∑ j, p' j = 1) :
    entropy (fun x : ι × κ => p x.1 * p' x.2) = entropy p + entropy p' := by
  have h1 : ∑ i, ∑ j, p' j * Real.negMulLog (p i) = ∑ i, Real.negMulLog (p i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hp', one_mul]
  have h2 : ∑ i, ∑ j, p i * Real.negMulLog (p' j) = ∑ j, Real.negMulLog (p' j) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hp, one_mul]
  unfold entropy
  simp_rw [Real.negMulLog_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  rw [h1, h2]

/-- The entropy of the combined Boltzmann distribution is the sum
of the entropies of the individual Boltzmann distributions. -/
lemma entropy_boltzmann_prod [Nonempty ι] [Nonempty κ]
    (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    entropy (boltzmann (fun x : ι × κ => E x.1 + E' x.2) β) =
      entropy (boltzmann E β) + entropy (boltzmann E' β) := by
  have h : boltzmann (fun y : ι × κ => E y.1 + E' y.2) β =
      fun x : ι × κ => boltzmann E β x.1 * boltzmann E' β x.2 := by
    funext x
    exact boltzmann_prod E E' β x.1 x.2
  rw [h]
  exact entropy_prod_mul (sum_boltzmann E β) (sum_boltzmann E' β)

/-- At high temperature, the entropy of the Boltzmann distribution
tends to the logarithm of the number of states. -/
theorem tendsto_entropy_boltzmann_zero [Nonempty ι]
    (E : ι → ℝ) :
    Filter.Tendsto
      (fun β : ℝ => entropy (boltzmann E β))
      (nhds 0)
      (nhds (Real.log (Fintype.card ι : ℝ))) := by
  have hcont : Continuous (fun β => entropy (boltzmann E β)) := by
    unfold entropy
    exact continuous_finsetSum _ fun i _ =>
      Real.continuous_negMulLog.comp (continuous_boltzmann E i)
  have h0 : entropy (boltzmann E 0) = Real.log (Fintype.card ι : ℝ) := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold entropy
    simp_rw [boltzmann_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Real.negMulLog, one_div, Real.log_inv]
    field_simp
  rw [← h0]
  exact hcont.tendsto 0

/-- At low temperature, the entropy of the Boltzmann distribution
tends to the logarithm of the number of ground states. -/
theorem tendsto_entropy_boltzmann_atTop [Nonempty ι]
    (E : ι → ℝ) :
    Filter.Tendsto
      (fun β : ℝ => entropy (boltzmann E β))
      Filter.atTop
      (nhds (Real.log (groundStates E).card : ℝ)) := by
  classical
  have hterm (i : ι) :
      Filter.Tendsto (fun β : ℝ => Real.negMulLog (boltzmann E β i)) Filter.atTop
        (nhds (Real.negMulLog (if i ∈ groundStates E
          then 1 / ((groundStates E).card : ℝ) else 0))) :=
    (Real.continuous_negMulLog.tendsto _).comp (tendsto_boltzmann_atTop E i)
  have hsum : Filter.Tendsto (fun β : ℝ => entropy (boltzmann E β)) Filter.atTop
      (nhds (∑ i, Real.negMulLog (if i ∈ groundStates E
        then 1 / ((groundStates E).card : ℝ) else 0))) := by
    unfold entropy
    exact tendsto_finsetSum _ fun i _ => hterm i
  have hc : ((groundStates E).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (groundStates_nonempty E)).ne'
  have hpt (i : ι) :
      Real.negMulLog (if i ∈ groundStates E
        then 1 / ((groundStates E).card : ℝ) else 0) =
      if i ∈ groundStates E
        then Real.negMulLog (1 / ((groundStates E).card : ℝ)) else 0 := by
    split_ifs <;> simp
  have hval : (∑ i, Real.negMulLog (if i ∈ groundStates E
        then 1 / ((groundStates E).card : ℝ) else 0)) =
      Real.log ((groundStates E).card : ℝ) := by
    simp_rw [hpt]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    simp only [Real.negMulLog, one_div, Real.log_inv]
    field_simp
  rw [← hval]
  exact hsum

end MaxEnt
