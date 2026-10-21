# Test suite

Every model below is a textbook special case. For each lab setup the expected answer was written down from the subject matter, and Lean has to reproduce it:

- the computed causal order (which law determines which variable, and the cyclic blocks) and the uniqueness check are pinned with `#guard_msgs`, so the build fails if the language ever computes something else;
- the expected physical, chemical or economic answer is a theorem.

Negative tests (`Tests/Rejects.lean`) pin the errors the language must give for wrong models.

## Physics

| Model | Setups | Expected structure | Expected answer | Theorems |
|---|---|---|---|---|
| Ideal gas, pV = nRT (`Examples/Gas`) | locked piston; weighted piston | acyclic; the law determines p, or V | heating raises p with V fixed, or V with p fixed; same do(T), different volumes | `locked_heat`, `weighted_heat`, `different_answers` |
| Resistor heated by a current (`Examples/Circuit`) | voltage source; current source | acyclic in both | a larger resistor runs cooler with a voltage source, hotter with a current source | `voltage_larger_R_cooler`, `current_larger_R_hotter` |
| Current divider (`Examples/Divider`) | current source; voltage source | one linear cyclic block; acyclic | exactly one state; I₁ = R₂/(R₁+R₂)·I | `currentSource_existsUnique`, `divider_rule` |
| Heat through two walls (`Tests/Physics`) | both baths fixed | one linear cyclic block {Q, Tm} | exactly one steady state; Q = (T₁−T₂)/(R₁+R₂) | `baths_existsUnique`, `series` |
| Battery with internal resistance (`Tests/Physics`) | ε, r, R fixed | acyclic: loop law → I, load → U | U = εR/(R+r) rises with the load resistance | `terminal_voltage`, `larger_load_higher_voltage` |

## Chemistry

| Model | Setups | Expected structure | Expected answer | Theorems |
|---|---|---|---|---|
| Stepwise complexation (`Examples/Complexation`) | closed flask; ligand buffer | one nonlinear block of four laws, multi-affine, uniqueness proved automatically by the secant P-matrix criterion; with a buffer a linear block of three, and the ligand balance determines l₀ | exactly one equilibrium; Le Chatelier: more metal, less free ligand; buffer determinant 1 + K₁L + K₁K₂L² | `closed_atMostOne` (automatic), `closed_unique_by_monotonicity`, `le_chatelier`, `buffered_existsUnique` |
| Weak acid (`Tests/Chemistry`) | titration (base added); buffer (pH fixed) | one nonlinear block; a linear block {acid, mass}, and the charge balance determines Na⁺ | Henderson–Hasselbalch: [A⁻] = C·Ka/([H⁺]+Ka) | `buffer_existsUnique`, `dissociated` |
| Beer–Lambert after dilution (`Tests/Chemistry`) | prepared sample; flow cell | acyclic: n,V → c → A; or c,V → n | doubling V halves A; in the flow cell A stays and n doubles | `prepared_dilute`, `flowCell_dilute` |
| Arrhenius (`Tests/Chemistry`) | A, Eₐ, T, [X] fixed | acyclic | a higher temperature gives a higher rate | `hotter_faster` |

## Economics

| Model | Setups | Expected structure | Expected answer | Theorems |
|---|---|---|---|---|
| Market with tax (`Examples/Market`) | closed economy; small open economy | one linear block {P, Q_d, Q_s}; acyclic, clearing determines imports | exactly one equilibrium (needs 1 + e/b ≠ 0); tax raises the price by e/(b+e)·Δ, or leaves it and raises imports by e·Δ | `closed_existsUnique`, `closed_tax`, `open_tax` |
| Keynesian cross (`Tests/Economics`) | short run; policy target | one linear block {Y, C} (needs 1 − c₁ ≠ 0); acyclic, income identity determines G | multiplier 1/(1 − c₁); the G needed for a target income | `shortRun_existsUnique`, `multiplier`, `target_G` |
| Quantity theory, MV = PY (`Tests/Economics`) | flexible prices; fixed prices | acyclic; the law determines P, or Y | doubling M doubles P, or doubles Y | `classical_money`, `fixedPrice_money` |

## Blockwise criterion (`Tests/Blockwise`)

| Model | Setup | Expected | Theorems |
|---|---|---|---|
| Current divider with the power in one resistor | current source | linear block {U, I₁, I₂} with a nonlinear law (P₁ = R₁I₁²) downstream; exactly one state | `DividerPower.existsUnique` (proved by `block_linear` alone) |
| Current divider with a heated resistor | heater and current source | upstream laws T = Tₐ + kP_h and R₁ = R₀(1 + αT) give the divider an endogenous coefficient; exactly one state when the heated resistance is positive | `HeatedDivider.existsUnique` |

## Interventions inside cyclic blocks

| Model | Intervention | Expected | Theorems |
|---|---|---|---|
| Market, closed economy | price held fixed, switching off market clearing (price ceiling) | demand and supply still hold; acyclic; excess demand (b + e)·(P* − P̄) | `ceiling_existsUnique`, `ceiling_excess_demand` |
| Market, closed economy | price held fixed, switching off demand (Pearl's do(P), since demand determines P in the computed reading) | buyers absorb supply plus imports; no excess demand | `demand_reading_is_do`, `do_reading_no_excess` |
| Complexation, closed flask | free ligand held fixed, switching off the ligand balance (Pearl's do(L)) | the remaining block {k1, k2, metal} is linear; free metal m₀/(1 + K₁L + K₁K₂L²), as with a buffer | `fixL_is_do`, `fixL_existsUnique`, `fixL_metal` |

## What the language must reject (`Tests/Rejects.lean`)

- a formula that does not solve its law;
- a solver for a variable that does not exist;
- a formula for x that mentions x;
- a setup that fixes so much that the laws cannot be matched to the remaining variables;
- a false claim about the causal order;
- a singular linear block must be reported as singular, not as unique;
- a nonlinear block must not be treated as linear;
- parameters must be explicit and must not share a name with a variable;
- a model without a witness, and a model whose domain contradicts its laws;
- units that do not match: the gas law without R, a solving formula with the wrong unit, an Arrhenius exponent that is not dimensionless, a constant or variable without a unit;
- an intervention on a variable the lab already holds fixed (a law is left with nothing to determine).

## What the tests do and do not show

For acyclic setups, most answer theorems read the outcome off the solved formulas with `read_solution`; they check the formulas the user wrote and the causal order, not that the formulas were derived from the laws (that is what `law_solve` checks, on the domain). For cyclic setups the answers are derived from the laws through `solves_iff`. `Gas.locked_laws`, `Battery.circuit_laws`, `Divider.currentSource_laws` and `Market.closed_laws` state uniqueness for the laws themselves inside the domain. Every model carries a checked witness (`consistent`) and declares units, so every law and formula in the suite is dimensionally consistent.

## How the expected answers were chosen

The answers are standard textbook results and were written before the Lean proofs. The pinned outputs of `#causal_order` and `#causal_check` were then compared with them by hand. Where the textbook only says that some variables are determined jointly (a cyclic block), the exact pairing of laws and variables inside the block is whatever the matching algorithm chose, and is pinned only to detect changes.
