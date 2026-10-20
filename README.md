# CausalPhys

A Lean 4 library for **causal ordering of equation systems** in physics, chemistry and economics, building on Herbert Simon's idea that an equation system becomes causal once each equation is assigned to the variable it determines.

Given an equation system and a choice of exogenous variables, the library

- computes which equation determines which variable (a perfect matching) and the strongly connected blocks, and proves that the blocks do not depend on the matching chosen (Dulmage–Mendelsohn);
- turns the result into a structural causal model where `do(x := c)` replaces one mechanism;
- proves conditions under which cyclic blocks have exactly one solution;
- derives conditional independences through a decidable d-separation check, connected to [PearlDoCalculus](https://github.com/Johaan70/PearlDoCalculus).

Worked examples include the ideal gas law under different lab setups, chemical equilibrium and Le Chatelier, metal–ligand complexation, electrical circuits, supply–demand markets with taxes and the Lucas critique, the cobweb model, and counterfactuals.

## Functional analysis along the way

Proving that cyclic blocks have solutions led to a sequence of results, several of which are not in Mathlib as far as we know:

| Result | Module |
|---|---|
| Banach and Zarantonello (strongly monotone Lipschitz operators) | `Existence`, `BrowderMinty` |
| Gale–Nikaido (P-matrix Jacobians give injectivity) | `GaleNikaido` |
| Brouwer's fixed point theorem via Sperner's lemma | `Brouwer` |
| Minty–Browder in finite dimensions, Hilbert spaces and reflexive Banach spaces | `MintyBrowder`, `MintyBrowderHilbert`, `MintyBrowderBanach` |
| Minty–Browder with hemicontinuity only (via KKM) | `MintyBrowderHemi` |
| (ℓᵖ)* ≅ ℓ^q and reflexivity of ℓᵖ and of finite-dimensional spaces | `LpReflexive` |
| Goldstine and Milman–Pettis | `Reflexivity` |
| Clarkson's inequality and reflexivity of Lᵖ(μ), 1 < p < ∞, arbitrary measures | `LpMeasure` |
| Causal models with infinitely many variables on ℓ² | `InfiniteSCM` |

## Status

- 29 modules in `CausalPhys/`, about 8,800 lines.
- No `sorry`. `#print axioms` on the main theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
- **How it was made:** the code was developed together with Claude (Anthropic), an AI assistant, under the direction of the repository owner. It compiles, but it has not yet been reviewed by anyone else. Feedback is very welcome.

## Building

Requires Lean `v4.36.0-rc1` and Mathlib at commit `807d383`, both pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get   # if the Mathlib cache is available for this commit
lake build
```

The build prints warnings that Mathlib modules are "designed for use with the module system"; these are harmless for this toolchain.

## Contents

- `CausalPhys/` — the library (see `CausalPhys.lean` for the module list)
- `PearlDoCalculus/` — a copy of PearlDoCalculus ported to this toolchain; the changes are in `docs/pearldocalculus-lean-4.36-port.patch`
- `docs/kausal-lab.html` — an interactive teaching page (Norwegian) on causal ordering for secondary school

## Known limitations

- The duality (Lᵖ)* ≅ L^q is proved for sequence spaces ℓᵖ but not for general measures (only the isometric embedding Lᵖ → (L^q)* that reflexivity needs).
- Uniqueness for infinite models holds among square-summable solutions only.
- Mechanisms have finitely many parents, so aggregates over infinitely many variables are not expressible.
- Some examples (such as the nonlinear lattice) are equilibrium equations in Simon's sense rather than acyclic causal assignments.
