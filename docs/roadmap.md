# Roadmap

The plan, ordered by what it gives: first make the core right, then make it useful in the classroom, then test it against the outside world. Each step has a goal, the work, and a criterion for when it is done. Status is updated as steps finish.

## 1. Tidy and tighten — done

**Goal:** a smaller and more robust base.

- The functional analysis the language does not use (Minty–Browder in Hilbert and Banach spaces, KKM, reflexivity of ℓᵖ and Lᵖ, infinite causal models) is a separate library, `CausalPhysAnalysis`. Finite-dimensional Brouwer, Minty–Browder and Gale–Nikaido stay in `CausalPhys`: the secant criterion uses the P-matrix lemmas, and step 3 may use Brouwer.
- `#causal_check` gives the same answer for a setup written in place (`{ exo := … }`) as for a named one. Such a setup now gets an auxiliary name, so the tactics no longer unfold the structure literal (they used to run out of time). Pinned in `Examples/Complexation`.
- Each criterion in `#causal_check` runs with a fixed time budget and reports a timeout instead of failing.
- CI prints the time of each build step and each check.

**Done when:** `Lang/` depends only on what it needs, the checks after the build take under five minutes, and a setup written in place gets the same answer as a named one.

## 2. Let Lean find the formulas — done

**Problem:** the causal order depended on which `solve` lines the user wrote. The gas law could not make T the effect until the formula was added by hand.

- For every variable a law is affine in, `causal_model` derives the formula from the law (`deriveFormula`: split each side into the part proportional to the variable and the rest, then x = (lB − rB)/(rA − lA), simplified) and keeps it if `law_solve` proves that it solves the law on the domain. A formula that needs more than the domain gives is left out, not refused: MV = PY is not solved for M without `0 < V` (pinned in `Tests/Rejects.lean`).
- `law_solve` now uses the facts stored in parameter structures (`c.hK1 : 0 < c.K1`), and a new clause `facts R_pos` makes facts about constants available to every formula proof and to the witness.
- `#causal_solvable M` shows what each law can be solved for.
- Formulas written by hand (`solve x := …`) remain, must be proved, and come first. They are needed for laws that are not affine in the variable.
- No example or test model writes a formula any more. The models on the teaching page went from 29 to 50 valid lab setups (complexation 4 → 15, market 4 → 9, circuit 3 → 6, weak acid 6 → 7, Keynes 2 → 3); the gas law already had all four formulas by hand.

**What changed in the pinned outputs:** only the order in which a law lists what it reads, and in the two-wall model which law determines which variable inside the cyclic block (pinned only to detect changes). One theorem (`Keynes.target_G`) needed a `ring` because the derived formula is written Y − (C + I) instead of Y − C − I.

**Left for later:** the derivation does not divide by a factor the domain keeps positive only through a fact it cannot see; such a formula is simply not derived (a hand-written formula with a proof still works). Of the 45 setups with a cyclic block on the page, 18 are not decided by either criterion: formulas such as M = ML/(K₁L) are neither affine nor multi-affine. That is step 3.

## 3. Existence, not only uniqueness, in nonlinear blocks — done (with limits)

**Problem:** the secant criterion gave at most one outcome; the closed flask and titration need exactly one. And the criterion read each law through the formula the matching chose.

What was built:

- **Existence** (`block_exists`, `Lang/Exist.lean`): the other variables are computed from a small set of core variables by their formulas; for each core variable F(x) = x − (its formula); the box is 0 ≤ x ≤ (the formula at x = 0), which for a mass balance is the total. The Poincaré–Miranda theorem (`PoincareMiranda.lean`, proved from the Brouwer theorem already in the library) gives a zero when F < 0 on the lower faces and F ≥ 0 on the upper ones. The tactic tries every matching of laws to variables and every small core, proves the face inequalities, the domain and the laws (`Model.mechOf_sound`), and skips candidates whose formulas divide by a core variable.
- **Uniqueness from the laws** (`law_secant_unique`, `Setup.laws_secant_unique`): the secant P-matrix argument on residuals ±(lhs − rhs) of the laws, so it no longer depends on the formulas the matching chose. Also `secant_unique_any`, which reads the setup through another matching (`Model.restrict`, `Setup.solves_iff_restrict`).
- `positivity_hyps`: positivity that uses hypotheses 0 < t, 0 ≤ t from the context.
- `#causal_check` now says "exactly one outcome in the domain whenever every fixed value is positive" when both halves succeed.

Results:

- Closed flask: exactly one equilibrium for positive m₀, l₀, fully automatic (`Complexation.closed_existsUnique`).
- Weak acid under titration: exactly one equilibrium before the equivalence point, Na⁺ < C (`WeakAcid.titration_existsUnique`), and none at or after it (`WeakAcid.titration_none`), because the model leaves out water. This needed the domain to say that all concentrations are positive, which it should have said from the start.
- Of the 45 setups with a cyclic block on the teaching page, 14 are still undecided (17 before). Most of those are genuinely not unique: fixing [ML] in the complexation model leaves a quadratic in [L] with two positive roots for some values. The heated resistor with R and P fixed is unique physically (U > 0 picks the positive root), but the criterion fails because it asks for a P-matrix on the whole domain, where the current may be negative.

**Limits:** existence is only attempted automatically under "every fixed value positive"; conditions like Na⁺ < C must be given as hypotheses. `block_exists` does not handle a model with a law switched off (an intervention). The checks on the page take about five minutes.

## 4. Numbers, not only directions — done (with one gap)

- `#causal_eval S with T := 300, … using R` computes the outcome exactly (rationals) for acyclic setups and linear blocks, and proves that the state lies in the domain, satisfies every law, solves the causal model with these fixed values and is the only outcome (`Lang/Eval.lean`). The numbers are found without being trusted: block by block in causal order, a cyclic block by probing its affine formulas and solving the linear system over ℚ; the proof then checks them with `norm_num`, and uniqueness comes from `Setup.unique` or `block_linear` with the determinant evaluated at the given values.
- It reports instead of guessing: a value for a variable the lab does not hold fixed, a nonlinear block (the closed flask), or a formula that does not give a rational number (an exponential). Pinned in `Examples/Gas`, `Examples/Divider` and `Tests/Rejects.lean`.
- The builder on the teaching page shows Lean's numbers for every named setup with linear blocks: four values of one fixed variable each, 56 evaluations, regenerated and compared in CI.
- Found along the way: the rank the matching certificate carries does not give the order of the blocks (in the weak-acid buffer all three laws had the same rank), so both `#causal_eval` and the page now order blocks by what they read. The rank is no longer exported.

**Gap:** the three hand-built experiments at the top of the page still compute their numbers in the browser. The gas and circuit numbers could be replaced by Lean's; the equilibrium A + B ⇌ C is the root of a quadratic and is rarely rational, so exact numbers need a different method (an interval that provably contains the root).

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
