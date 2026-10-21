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
| Stepwise complexation (`Examples/Complexation`) | closed flask; ligand buffer | one nonlinear block of four laws; with a buffer a linear block of three, and the ligand balance determines l₀ | exactly one equilibrium; Le Chatelier: more metal, less free ligand; buffer determinant 1 + K₁L + K₁K₂L² | `closed_unique`, `le_chatelier`, `buffered_existsUnique` |
| Weak acid (`Tests/Chemistry`) | titration (base added); buffer (pH fixed) | one nonlinear block; a linear block {acid, mass}, and the charge balance determines Na⁺ | Henderson–Hasselbalch: [A⁻] = C·Ka/([H⁺]+Ka) | `buffer_existsUnique`, `dissociated` |
| Beer–Lambert after dilution (`Tests/Chemistry`) | prepared sample; flow cell | acyclic: n,V → c → A; or c,V → n | doubling V halves A; in the flow cell A stays and n doubles | `prepared_dilute`, `flowCell_dilute` |
| Arrhenius (`Tests/Chemistry`) | A, Eₐ, T, [X] fixed | acyclic | a higher temperature gives a higher rate | `hotter_faster` |

## Economics

| Model | Setups | Expected structure | Expected answer | Theorems |
|---|---|---|---|---|
| Market with tax (`Examples/Market`) | closed economy; small open economy | one linear block {P, Q_d, Q_s}; acyclic, clearing determines imports | exactly one equilibrium (needs 1 + e/b ≠ 0); tax raises the price by e/(b+e)·Δ, or leaves it and raises imports by e·Δ | `closed_existsUnique`, `closed_tax`, `open_tax` |
| Keynesian cross (`Tests/Economics`) | short run; policy target | one linear block {Y, C} (needs 1 − c₁ ≠ 0); acyclic, income identity determines G | multiplier 1/(1 − c₁); the G needed for a target income | `shortRun_existsUnique`, `multiplier`, `target_G` |
| Quantity theory, MV = PY (`Tests/Economics`) | flexible prices; fixed prices | acyclic; the law determines P, or Y | doubling M doubles P, or doubles Y | `classical_money`, `fixedPrice_money` |

## What the language must reject (`Tests/Rejects.lean`)

- a formula that does not solve its law;
- a solver for a variable that does not exist;
- a formula for x that mentions x;
- a setup that fixes so much that the laws cannot be matched to the remaining variables;
- a false claim about the causal order;
- a singular linear block must be reported as singular, not as unique;
- a nonlinear block must not be treated as linear.

## How the expected answers were chosen

The answers are standard textbook results and were written before the Lean proofs. The pinned outputs of `#causal_order` and `#causal_check` were then compared with them by hand. Where the textbook only says that some variables are determined jointly (a cyclic block), the exact pairing of laws and variables inside the block is whatever the matching algorithm chose, and is pinned only to detect changes.
