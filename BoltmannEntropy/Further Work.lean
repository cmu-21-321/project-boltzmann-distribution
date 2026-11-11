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
  sorry

/-- The Boltzmann distribution of two independent systems is the
product of their individual Boltzmann distributions. -/
lemma boltzmann_prod (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ)
    (i : ι) (k : κ) :
    boltzmann (fun x : ι × κ => E x.1 + E' x.2) β (i, k) =
      boltzmann E β i * boltzmann E' β k := by
  sorry

/-- The entropy of the combined Boltzmann distribution is the sum
of the entropies of the individual Boltzmann distributions. -/
lemma entropy_boltzmann_prod [Nonempty ι] [Nonempty κ]
    (E : ι → ℝ) (E' : κ → ℝ) (β : ℝ) :
    entropy (boltzmann (fun x : ι × κ => E x.1 + E' x.2) β) =
      entropy (boltzmann E β) + entropy (boltzmann E' β) := by
  sorry

/-- At high temperature, the entropy of the Boltzmann distribution
tends to the logarithm of the number of states. -/
theorem tendsto_entropy_boltzmann_zero [Nonempty ι]
    (E : ι → ℝ) :
    Filter.Tendsto
      (fun β : ℝ => entropy (boltzmann E β))
      (nhds 0)
      (nhds (Real.log (Fintype.card ι : ℝ))) := by
  sorry

/-- At low temperature, the entropy of the Boltzmann distribution
tends to the logarithm of the number of ground states. -/
theorem tendsto_entropy_boltzmann_atTop [Nonempty ι]
    (E : ι → ℝ) :
    Filter.Tendsto
      (fun β : ℝ => entropy (boltzmann E β))
      Filter.atTop
      (nhds (Real.log (groundStates E).card : ℝ)) := by
  sorry

end MaxEnt
