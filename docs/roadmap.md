# Roadmap

The plan, ordered by what it gives: first make the core right, then make it useful in the classroom, then test it against the outside world. Each step has a goal, the work, and a criterion for when it is done. Status is updated as steps finish.

## 1. Tidy and tighten — done

**Goal:** a smaller and more robust base.

- The functional analysis the language does not use (Minty–Browder in Hilbert and Banach spaces, KKM, reflexivity of ℓᵖ and Lᵖ, infinite causal models) is a separate library, `CausalPhysAnalysis`. Finite-dimensional Brouwer, Minty–Browder and Gale–Nikaido stay in `CausalPhys`: the secant criterion uses the P-matrix lemmas, and step 3 may use Brouwer.
- `#causal_check` gives the same answer for a setup written in place (`{ exo := … }`) as for a named one. Such a setup now gets an auxiliary name, so the tactics no longer unfold the structure literal (they used to run out of time). Pinned in `Examples/Complexation`.
- Each criterion in `#causal_check` runs with a fixed time budget and reports a timeout instead of failing.
- CI prints the time of each build step and each check.

**Done when:** `Lang/` depends only on what it needs, the checks after the build take under five minutes, and a setup written in place gets the same answer as a named one.

## 2. Let Lean find the formulas

**Problem:** the causal order depends on which `solve` lines the user writes. The gas law could not make T the effect until the formula was added by hand.

- When a law is linear in a variable, `causal_model` derives the formula for it and proves it with `law_solve`. This covers almost all textbook laws (pV = nRT, U = RI, mass balances).
- The domain conditions this needs (what is divided by must not be zero) are proposed, or the model is refused with a clear message.
- User formulas remain possible for laws that are not linear in the variable.

**Done when:** the examples work without `solve` lines where the law is linear in the variable, and the teaching page shows more valid setups.

## 3. Existence, not only uniqueness, in nonlinear blocks

**Problem:** the secant criterion gives at most one solution; complexation and titration need exactly one.

- An automatic existence criterion for blocks whose domain is a box: monotonicity along one variable (as in the complexation proof), Brouwer where needed.
- The titration case: let a block be decided by the laws directly, not through the formulas the matching chose (`unique_of_laws`, automated).
- A new `#causal_check` answer: exactly one outcome in the domain.

**Done when:** the closed flask and the weak acid under titration get "exactly one outcome" automatically.

## 4. Numbers, not only directions

- `#causal_eval S with T := 450, …` computes the outcome exactly (rationals) for acyclic setups and linear blocks, with a proof that the numbers solve the laws.
- The teaching page gets sliders whose values were computed by Lean. This closes the gap the teacher section states openly: the numbers in the circuit are computed on the page, not proved.

**Done when:** every number in the first three experiments on the page is exported from Lean and checked in CI.

## 5. Try it in a classroom

- Use the page in one class (physics or science) and note where students go wrong.
- Three or four task sets with answers, linked to the LK20 competence aims, and a short teacher's guide.
- Adjust the models and the text after what you see.

**Done when:** the page has been used in at least one lesson with students, with notes on what worked and what did not.

## 6. Larger and more realistic models

- Three models with 10–20 variables: acid–base with water autoprotolysis, IS–LM, a circuit with several branches.
- Measure where the language stops (kernel time, size of determinants) and document the limits.

**Done when:** three larger models are in the test suite and the limits are in the README.

## 7. Test it against the outside world

- A short note (6–8 pages): what the language does and does not do, and how it relates to existing work on Simon's causal ordering (among others Blom and Mooij); the literature needs a proper check before writing.
- Give the note and the code to one person in formal methods or causal inference and ask for errors, not praise.
- arXiv when the note holds.

## Left out on purpose

- Units with scale (litre versus cubic metre): little gain for the effort.
- Noise and estimation from data: a different project; the bridge to PearlDoCalculus is enough for now.
- More functional analysis without a concrete example that needs it.

## Order

Steps 1, 2, 4 and 5 each take a few sessions and give a language that is better and actually used. Step 3 is the hardest mathematically and can run in parallel. Steps 6 and 7 come last.
