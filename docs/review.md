# Independent review (21 October 2026)

The language under `CausalPhys/Lang` was reviewed by a separate AI agent that had not seen the work, with the instruction to look for soundness holes, statements that do not mean what their documentation says, wrong verdicts from `#causal_check`, and robustness problems. It ran every claim it made as Lean code against the built project.

## Soundness: no problems found

- No `sorry`, `native_decide`, `implemented_by`, `unsafe` or extra axioms. Main theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- `kernel_decide` evaluates the statement in the kernel before it assigns a proof, so a false structural claim is refused even where no later kernel check happens (for example inside `#causal_check`).
- `law_solve`, `read_solution` and `linear_block` build real proofs, so they cannot introduce false hypotheses.

## Findings and what was done

| Finding | Severity | Change |
|---|---|---|
| "Exactly one outcome" is about the causal model (the solved formulas). Outside the domain an outcome need not satisfy the laws (e.g. do(V := 0) in the gas law, R₁ = 0 in the current divider), and no message said so. | misleading claim | Messages now say "outcome of the causal model". New theorems `Setup.sat_of_solves` and `Setup.laws_existsUnique` carry a unique outcome that lies in the domain over to the laws; used in `Divider.currentSource_laws` and `Market.closed_laws`. Core header and README explain the distinction. |
| Nothing checks that the domain is consistent with the laws; a contradictory or too small domain makes the formula check empty. | misleading claim | Every model must now give a `witness`, a concrete state in the domain that satisfies every law, checked by Lean (theorem `consistent`). A contradictory domain is rejected (pinned in `Tests/Rejects.lean`). `in_domain` and `laws_unique` turn uniqueness of the causal model into uniqueness for the laws. A domain that is consistent but too narrow is still possible and documented. |
| `#causal_check` called a setup "nonlinear" whenever the linear criterion failed, also when the cyclic block itself is linear (a nonlinear formula elsewhere, or coefficients from an upstream block). | wrong verdict (safe direction) | Fixed: the criterion now works block by block (`Blockwise.lean`, `block_linear`), so both situations are covered; the two review examples are tests in `Tests/Blockwise.lean` (as physics models). `#causal_check` only reports "not covered" when a formula is nonlinear in its own block. |
| Macro: implicit parameters failed with an obscure error; a parameter with the same name as a variable was silently shadowed; identifiers bound inside formulas are rewritten. | robustness | Implicit parameters and name clashes now give plain errors (pinned in `Tests/Rejects.lean`); the rewriting of bound identifiers is documented. |
| `kernel_decide` docstring understated the check; pinned outputs contained hygienic names (`u✝`); `blocks_independent` was listed without its hypothesis; acyclic answer tests mostly read back the user's own formulas. | cosmetic / test quality | Docstring and header corrected; `#causal_check` now names the variable `u`; `docs/test-suite.md` says what the acyclic tests do and do not show. |

## Not confirmed

- The kernel evaluation used by `kernel_decide` and `#causal_order` has no heartbeat limit, so a very large model could hang instead of timing out.
