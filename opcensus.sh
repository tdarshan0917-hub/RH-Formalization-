#!/bin/zsh
echo "===== 1. DFiniteStage (the base object) ====="
grep -rn -B3 -A14 "structure DFiniteStage where\|structure DFiniteStage " RHFormalization/*.lean | head -22
echo "===== 2. DFiniteStageOperatorLegality ====="
grep -rn -B3 -A16 "structure DFiniteStageOperatorLegality" RHFormalization/*.lean | head -24
echo "===== 3. DFiniteTraceConstructionAPI + DFiniteTraceFunctionData ====="
grep -rn -A10 "structure DFiniteTraceConstructionAPI" RHFormalization/*.lean | head -14
grep -rn -A10 "structure DFiniteTraceFunctionData" RHFormalization/*.lean | head -14
echo "===== 4. Duhamel split API ====="
grep -rn -A12 "structure DFiniteStageSplitFromDuhamelAPI" RHFormalization/*.lean | head -16
echo "===== 5. the finite prime-power formula (Theorem B shape) ====="
grep -rn -A16 "structure DFiniteStageCanonicalPrimePowerFormula" RHFormalization/*.lean | head -22
echo "===== 6. existing builders/witnesses for the operator layer ====="
grep -rn "DFiniteStagePackageFromOperatorLayer\|DFiniteStageOperatorLegality" RHFormalization/*.lean | grep -e "def build" -e "def default" -e "theorem.*witness" | head -12
echo "===== 7. one-prime / Theorem B scaffolding anywhere ====="
grep -rln -i "oneprime\|one_prime\|theoremB\|theorem_b\|singlePrime\|log 2\|log2" RHFormalization/*.lean | head -12
echo "===== 8. S sub-structures: ChosenSpeedData + CanonicalKernelC ====="
grep -rn -A12 "structure DCanonicalWindowSharpCutoffConcreteChosenSpeedData" RHFormalization/*.lean | head -16
grep -rn -B2 -A8 "def CanonicalKernelC\|abbrev CanonicalKernelC\|structure CanonicalKernelC" RHFormalization/*.lean | head -14
