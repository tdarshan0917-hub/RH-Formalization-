#!/bin/zsh
echo "===== 1. how does the Y chain set B.Cshared? (assignments in the builder chain) ====="
grep -rn -B3 -A6 "Cshared :=" RHFormalization/CanonicalPrimePowerSharpCutoffChosenLength*.lean RHFormalization/AppendixDOperator*.lean RHFormalization/DOperatorExport.lean 2>/dev/null | head -40
echo "===== 2. any Y-side Cshared_eq theorem ====="
grep -rn "Cshared_eq\|Cshared =" RHFormalization/*.lean | grep -e "theorem" -e "lemma" | head -10
echo "===== 3. what kernel/package does the mass-envelope S induce ====="
grep -rn -B2 -A8 "def.*canonicalPackage\|CanonicalPrimePowerPackage :=\|toCanonicalPrimePowerPackage" RHFormalization/CanonicalPrimePowerPackage.lean RHFormalization/CanonicalPrimePowerSharpCutoffChosenLength*.lean 2>/dev/null | head -30
echo "===== 4. HasGenuinePole actual definition (structure or def, name variant) ====="
grep -rn -B2 -A8 "HasGenuinePole" RHFormalization/HSidePoleWitness.lean RHFormalization/Basic.lean RHFormalization/AnalyticWrappers.lean 2>/dev/null | head -20
echo "===== 5. WindowFR (one level up) signature: what the NoSpeed builder delegates to ====="
sed -n '1,30p' RHFormalization/CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFR.lean
