#!/usr/bin/env bash
# Checks run by CI after `lake build`. Exit code 0 only if everything passes.
set -uo pipefail
fail=0
log=${1:-build.log}

echo "== 1. build errors"
if grep -E "^error|error:" "$log" | grep -v "module system" ; then fail=1; fi

echo "== 2. sorry"
if grep -n "declaration uses .sorry." "$log"; then fail=1; fi

echo "== 3. warnings in CausalPhys (PearlDoCalculus is a vendored copy and exempt)"
if grep -E "^warning: CausalPhys/" "$log" | grep -v "module system"; then fail=1; fi

echo "== 4. axioms"
out=$(lake env lean scripts/AxiomCheck.lean 2>&1 | grep -v "module system")
echo "$out"
echo "$out" | grep -q "axiom check passed" || fail=1

echo "== 5. negative tests (errors the language must give)"
out=$(lake env lean CausalPhys/Lang/Tests/Rejects.lean 2>&1 | grep -v "module system")
if [ -n "$out" ]; then echo "$out"; fail=1; else echo "all pinned errors match"; fi

echo "== 6. teaching page agrees with Lean (docs/kausal-lab.html)"
python3 scripts/build_lab.py --check || fail=1

if [ $fail -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "CHECKS FAILED"; fi
exit $fail
