module
public import BoltmannEntropy.Defs
/-!
# Temperature limits

* High temperature (`β → 0`): the Boltzmann distribution becomes uniform.
* Low temperature (`β → ∞`): to be added later, together with ground states.

## Main results

* `MaxEnt.boltzmann_zero` : at `β = 0` every state has probability `1/n`.
* `MaxEnt.continuous_boltzmann` : each Boltzmann probability is continuous in `β`.
* `MaxEnt.tendsto_boltzmann_zero` : the high-temperature limit.
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

end MaxEnt
