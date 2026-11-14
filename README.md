# BoltmannEntropy

A Lean 4 formalization of the maximum-entropy / Gibbs variational characterization of the
Boltzmann distribution on a finite set of states, connected to the canonical ensemble in
[Physlib](https://github.com/leanprover-community/physlib).

## Contents

| File | What it contains |
|---|---|
| `BoltmannEntropy/Defs.lean` | Entropy, mean energy, partition function, Boltzmann distribution, free energy, relative entropy |
| `BoltmannEntropy/Gibbs.lean` | Gibbs' inequality: relative entropy is nonnegative, and zero only for equal distributions |
| `BoltmannEntropy/Variational.lean` | The Boltzmann distribution uniquely minimizes free energy and maximizes entropy at fixed mean energy |
| `BoltmannEntropy/Main.lean` | The headline result, stated with explicit sums |
| `BoltmannEntropy/Limits.lean` | High- and low-temperature limits of the Boltzmann distribution |
| `BoltmannEntropy/FurtherWork.lean` | Independent systems and entropy limits (in progress) |
| `BoltmannEntropy/Physlib.lean` | Bridge to Physlib's `CanonicalEnsemble`, and the main results restated in its language |
| `BoltmannEntropy/Examples.lean` | Sanity checks |

The core development (`MaxEnt` namespace) uses a bare energy function `E : ι → ℝ` and a real
inverse temperature `β`. `Physlib.lean` shows that for a finite canonical ensemble
(`[𝓒.IsFinite]`) these agree with Physlib's `partitionFunction`, `probability`, `meanEnergy`,
`shannonEntropy` and `helmholtzFreeEnergy` at `β = 1 / (k_B T)`.

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
