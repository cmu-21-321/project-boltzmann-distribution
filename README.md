# BoltzmannEntropy

A Lean 4 formalization of the maximum-entropy / Gibbs variational characterization of the
Boltzmann distribution on a finite set of states, connected to the canonical ensemble in
[Physlib](https://github.com/leanprover-community/physlib).

## Contents

| File | What it contains |
|---|---|
| `BoltzmannEntropy/Defs.lean` | Entropy, mean energy, partition function, Boltzmann distribution, free energy, relative entropy, ground states |
| `BoltzmannEntropy/Gibbs.lean` | Gibbs' inequality: relative entropy is nonnegative, and zero only for equal distributions |
| `BoltzmannEntropy/Variational.lean` | The Boltzmann distribution uniquely minimizes free energy (`β > 0`) and maximizes entropy at fixed mean energy (any `β`) |
| `BoltzmannEntropy/Main.lean` | The headline result, stated with explicit sums |
| `BoltzmannEntropy/Limits.lean` | `β → 0`, `β → ∞` and `β → -∞` limits of the distribution, its entropy and its mean energy |
| `BoltzmannEntropy/Thermodynamics.lean` | `d(log Z)/dβ = -U`, `dU/dβ = -Var`, `dS/dβ = -β Var`, heat capacity, monotonicity in `β` |
| `BoltzmannEntropy/MaxEntConverse.lean` | Given only a mean energy `U`, the maximum-entropy distribution is Boltzmann at a unique `β` |
| `BoltzmannEntropy/Independent.lean` | Independent systems: `Z` multiplies; mean energy, entropy and free energy add |
| `BoltzmannEntropy/Physlib.lean` | Bridge to Physlib's `CanonicalEnsemble`, and the main results restated in its language |
| `BoltzmannEntropy/Examples.lean` | Sanity checks |

The core development (`MaxEnt` namespace) uses a bare energy function `E : ι → ℝ` and a real
inverse temperature `β`. `Physlib.lean` shows that for a finite canonical ensemble
(`[𝓒.IsFinite]`) these agree with Physlib's `partitionFunction`, `probability`, `meanEnergy`,
`shannonEntropy` and `helmholtzFreeEnergy` at `β = 1 / (k_B T)`.

## Main results

All results are fully proved, with no `sorry`. Throughout, `p_β(i) = exp(-β Eᵢ) / Z(β)` is the
Boltzmann distribution and `Z(β) = ∑ⱼ exp(-β Eⱼ)`.

**Gibbs variational principle** (`Main.lean`, `Variational.lean`). For `β > 0` and every
probability distribution `q` on `n` states,

```
∑ qᵢ Eᵢ + (1/β) ∑ qᵢ log qᵢ  ≥  -(1/β) log Z(β),
```

with equality exactly when `q = p_β`. In Lean these are `MaxEnt.gibbs_variational_explicit` and
`MaxEnt.gibbs_variational_explicit_eq_iff`. The underlying statements are
`freeEnergy_boltzmann_le` and `freeEnergy_eq_freeEnergy_boltzmann_iff`.

**Maximum entropy** (`Variational.lean`, `MaxEntConverse.lean`).
- `entropy_le_entropy_boltzmann` / `entropy_lt_entropy_boltzmann`: for any real `β`, among
  distributions with the same mean energy as `p_β`, `p_β` has the strictly largest entropy.
- `maxEnt_eq_boltzmann`: given only a target mean energy `U` strictly between the lowest and
  highest energies, there is a `β` such that `p_β` has mean energy `U` and is the unique
  maximum-entropy distribution with that mean energy. That `β` is unique
  (`existsUnique_meanEnergy_boltzmann_eq`).
- `entropy_le_log_card`: no distribution has more entropy than the uniform one.

**Gibbs' inequality** (`Gibbs.lean`). `relEntropy_nonneg`, `relEntropy_eq_zero_iff`: relative
entropy is nonnegative and vanishes only for equal distributions.

**Limits** (`Limits.lean`).
- `β → 0`: `p_β` tends to the uniform distribution and its entropy to `log n`.
- `β → ∞`: `p_β` tends to the uniform distribution on the ground states
  (`tendsto_boltzmann_atTop`). Entropy tends to `log |G|` and mean energy to the ground energy.
- `β → -∞` (negative temperature): `p_β` tends to the uniform distribution on the
  highest-energy states (`tendsto_boltzmann_atBot`).

**Thermodynamic identities** (`Thermodynamics.lean`).
- `hasDerivAt_log_partitionFn`: `d(log Z)/dβ = -U`.
- `hasDerivAt_meanEnergy_boltzmann`: `dU/dβ = -Var(E)`.
- `hasDerivAt_entropy_boltzmann`: `dS/dβ = -β Var(E)`.
- `heatCapacity_nonneg`, `meanEnergy_boltzmann_strictAnti`: heat capacity is nonnegative and
  `U` is strictly decreasing in `β` unless all energies are equal.

**Independent systems** (`Independent.lean`). For a composite system with energy
`E(i, j) = Eᵢ + E'ⱼ`, `Z` multiplies, `p_β` factors, and mean energy, entropy and free energy
add (`partitionFn_prod`, `boltzmann_prod`, `entropy_boltzmann_prod`, …).

**Physlib bridge** (`Physlib.lean`). `helmholtzFreeEnergy_le` and `helmholtzFreeEnergy_eq_iff`
restate the variational principle for a finite Physlib `CanonicalEnsemble`.
`kB_mul_entropy_le_shannonEntropy` restates the maximum-entropy principle there.

## Building

Install Lean via [elan](https://github.com/leanprover/elan). The Lean version comes from
`lean-toolchain`. Then run:

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

Physlib modules are compiled locally on the first build. Only the ones this project imports are
built.

## Updating dependencies

Physlib pins its own Mathlib version, so this project follows Physlib's release tags rather than
Mathlib's. To update, set `rev` under `[[require]]` in `lakefile.toml` to a new Physlib tag, set
`lean-toolchain` to Physlib's toolchain for that tag, then run:

```bash
lake update
lake exe cache get
lake build
```

The **Update Dependencies** GitHub workflow (`.github/workflows/update.yml`) tracks Mathlib
releases, not Physlib releases. Prefer updating by hand.
