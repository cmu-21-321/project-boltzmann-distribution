module

public import BoltmannEntropy.Defs

/-!
# Sanity checks

Small concrete cases we can work out by hand. If one of these is hard to prove, a
definition is probably set up badly.
-/

@[expose] public section

noncomputable section

namespace MaxEnt

/-- With all energies equal, every state is equally likely. -/
example (β : ℝ) (i : Fin 3) : boltzmann (fun _ : Fin 3 => (5 : ℝ)) β i = 1 / 3 := by
  simp only [boltzmann, partitionFn, Fin.sum_univ_three]
  rw [div_eq_iff]
  · ring
  · positivity

/-- Two states with energies `0` and `1` at `β = log 2`: `Z = 1 + 1/2 = 3/2`,
so the probabilities are `2/3` and `1/3`. -/
example : boltzmann (![0, 1] : Fin 2 → ℝ) (Real.log 2) 0 = 2 / 3 := by
  norm_num [boltzmann, partitionFn, Fin.sum_univ_two, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

example : boltzmann (![0, 1] : Fin 2 → ℝ) (Real.log 2) 1 = 1 / 3 := by
  norm_num [boltzmann, partitionFn, Fin.sum_univ_two, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The convention `0 log 0 = 0` is automatic. -/
example : Real.negMulLog 0 = 0 := by
  simp [Real.negMulLog]

end MaxEnt
