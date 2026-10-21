# CausalPhys

A Lean 4 library for **causal ordering of equation systems** in physics, chemistry and economics, building on Herbert Simon's idea that an equation system becomes causal once each equation is assigned to the variable it determines.

Given an equation system and a choice of exogenous variables, the library

- computes which equation determines which variable (a perfect matching) and the strongly connected blocks, and proves that the blocks do not depend on the matching chosen (Dulmage–Mendelsohn);
- turns the result into a structural causal model where `do(x := c)` replaces one mechanism;
- proves conditions under which cyclic blocks have exactly one solution;
- derives conditional independences through a decidable d-separation check, connected to [PearlDoCalculus](https://github.com/Johaan70/PearlDoCalculus).

Worked examples include the ideal gas law under different lab setups, chemical equilibrium and Le Chatelier, metal–ligand complexation, electrical circuits, supply–demand markets with taxes and the Lucas critique, the cobweb model, and counterfactuals.

## The language

A model is written the way it is written on a blackboard (`CausalPhys/Lang/Examples/Gas.lean`):

```lean
causal_model Gas where
  variables p vol n T
  domain 0 < p ∧ 0 < vol
  law gas : p * vol = n * R * T
    solve p := n * R * T / vol
    solve vol := n * R * T / p
  witness p := 1, vol := 1, n := 1, T := 1 / R by have := R_pos.ne'; witness_check
  setup locked fixes vol n T      -- locked piston, heat bath, closed vessel
  setup weighted fixes p n T      -- weighted piston, heat bath, closed vessel

#causal_order Gas.locked
-- gas determines p, reading [n, T, vol]
-- acyclic: every intervention has exactly one outcome
```

What the user writes is only domain content: variables, laws, the domain where they make sense, how each law can be solved, a witness (one concrete state that lies in the domain and satisfies every law), and which variables a lab holds fixed. The witness is checked, so a domain that contradicts the laws is rejected. Everything else is field-independent machinery:

- `causal_model` (`Lang/Syntax.lean`) collects what each formula reads from the formula itself, and proves with `law_solve` that each formula solves its law on the domain (a proof can be given after `by` when the algebra needs more, such as a positive parameter).
- `Lang/Core.lean` computes the Simon order of each setup (`struct_decide`, checked by the kernel, also for models with symbolic parameters) and proves general theorems for every model: inside the domain, solutions of the causal model are the solutions of the laws (`solves_iff`), setups cannot be told apart by data (`obs_equiv`), do(x := c) is equation surgery (`do_iff`), and an acyclic setup gives exactly one outcome for every intervention (`do_existsUnique`). An outcome is a solution of the solved formulas; when it lies in the domain, `laws_existsUnique` turns it into a statement about the laws themselves. The tactic `laws_unique` does this in one step (structure or linear criterion, then `in_domain`, which shows that the outcome lies in the domain); for example `Gas.locked_laws`: with positive n, T and V the gas law has exactly one solution in the domain. For a cyclic block, uniqueness is the domain-specific part and is plugged in through `unique_of_laws`.
- `Lang/Tactic.lean` has `read_solution h`, which turns a solution, before or after an intervention, into one equation per variable, and `#causal_order`.
- Cyclic blocks are handled by a toolbox. `Lang/Linear.lean` proves once for every model that affine formulas with det(I − C) ≠ 0 give exactly one outcome (`linear_existsUnique`). `Lang/Blockwise.lean` does the same block by block, in causal order (`block_existsUnique`): each formula only has to be affine in the variables of its own block, its coefficients may depend nonlinearly on lower blocks, and each block needs its own det(I − C_b) ≠ 0. The tactic `block_linear` computes the blocks, proves affinity, reduces each determinant to the block's own k×k determinant, substitutes the laws of lower blocks, and leaves only the conditions it cannot show. The tactic `linear_block` applies it: it enumerates the computed matching, checks that every formula is affine, computes the determinant, and tries to show it is nonzero; if it cannot, the determinant condition is left as the domain-specific goal. `#causal_check S` reports which case a setup is in: acyclic, cyclic and linear in each block (with the conditions still to show), singular, or not covered because some formula is nonlinear in its own block (then a domain argument such as monotonicity, Gale–Nikaido or Minty–Browder goes in through `unique_of_laws`).

Interventions inside a cyclic block are written `S.intervene e x`: switch off law `e`, and the lab now holds `x` fixed. Lean recomputes the causal order, and every tool above applies to the new setup. When `e` is the law that determines `x` in the computed reading, this is exactly Pearl's do(x := c) (`intervene_iff_doI`); otherwise it is a different intervention, and the difference matters. In the closed market, holding the price fixed by do(P) switches off demand (buyers absorb what is supplied), whereas a price ceiling switches off market clearing and leaves excess demand (b + e)·(P* − P̄) (`Market.ceiling_excess_demand`). In the closed flask, do([L]) leaves a linear block whose free metal is the buffer's closed form (`Complexation.fixL_metal`).

For the closed market, `linear_block` leaves 1 + e/b ≠ 0, which is the economics; for the ligand buffer it leaves 1 + K₁L + K₁K₂L² ≠ 0, the familiar denominator of complexation chemistry; for the current divider it finishes on its own.

`docs/test-suite.md` lists twelve textbook models (five physics, four chemistry, three economics) with the answers expected from the subject. In `CausalPhys/Lang/Tests` the expected answers are theorems and the computed causal orders are pinned with `#guard_msgs`, so the build fails if the language starts computing something else; negative tests pin the errors for wrong models.

Mistakes are caught with plain messages: a formula that does not solve its law on the domain, a missing witness or a domain that contradicts the laws, an unknown variable, a setup that fixes too many variables, or a false claim about the causal order.

The examples are special cases, each a model plus two setups that give opposite answers to the same question:

| Example | Field | Setups | Same intervention, different answers |
|---|---|---|---|
| `Gas` | physics | locked vs weighted piston | heating raises p, or raises V |
| `Circuit` | physics | voltage vs current source | a larger resistor runs cooler, or hotter |
| `Complexation` | chemistry | closed flask vs ligand buffer | one cyclic block of four laws, or the ligand balance determines the ligand delivered; Le Chatelier as do(m₀) |
| `Market` | economics | closed vs small open economy | a tax raises the price by e/(b+e)·Δ, or leaves it and raises imports by e·Δ |
| `Divider` | physics | current vs voltage source | a linear cyclic block (solved by `linear_block`), or acyclic; the current divider rule |

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

- 42 modules in `CausalPhys/`, about 11,000 lines.
- No `sorry`. `#print axioms` on the main theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
- **How it was made:** the code was developed together with Claude (Anthropic), an AI assistant, under the direction of the repository owner. It compiles, but it has not yet been reviewed by anyone else. Feedback is very welcome.

## Checks

Every push runs `.github/workflows/ci.yml`: a full build and then `scripts/ci.sh`, which fails on

1. any build error;
2. any `sorry`;
3. any warning in `CausalPhys/` (the vendored `PearlDoCalculus/` copy is exempt);
4. any declaration of the project that depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound` (`scripts/AxiomCheck.lean`, which also catches `sorry` and `native_decide`);
5. any change in the errors the language gives for wrong models (`CausalPhys/Lang/Tests/Rejects.lean`, which is not part of the library because Lean keeps the failed declarations).

Run the same checks locally with `lake build 2>&1 | tee build.log && scripts/ci.sh build.log`.

An independent review of the language (by a separate AI agent that had not seen the work) is summarised in `docs/review.md`, with what was changed in response.

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

- The witness shows that the domain and the laws are consistent at one state, not that the domain contains every meaningful solution; a domain that is too narrow still narrows what the formula check covers. `in_domain` handles acyclic setups and domain conditions on exogenous variables; for cyclic blocks the domain condition may need a hand proof.
- A block whose formulas are nonlinear in the block's own variables (such as the closed complexation flask) is not covered by the automatic criteria; uniqueness there needs a domain argument.
- In formulas, every identifier that names a variable is read as that variable, also inside `fun y => …`.
- The surface language uses `variables`, `domain`, `law`, `solve`, `witness`, `setup` and `fixes` as keywords in files that import it, and values are real numbers.
- The duality (Lᵖ)* ≅ L^q is proved for sequence spaces ℓᵖ but not for general measures (only the isometric embedding Lᵖ → (L^q)* that reflexivity needs).
- Uniqueness for infinite models holds among square-summable solutions only.
- Mechanisms have finitely many parents, so aggregates over infinitely many variables are not expressible.
- Some examples (such as the nonlinear lattice) are equilibrium equations in Simon's sense rather than acyclic causal assignments.
