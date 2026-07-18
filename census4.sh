#!/bin/zsh
echo "===== 1. X-with-chosen-Cshared builder: full signature ====="
sed -n '1,60p' RHFormalization/HMeromorphicWithNormalFormChosenCshared.lean
echo "===== 2. Y.B Cshared: DBcanLimitData fields ====="
grep -rn -A22 "structure DBcanLimitData" RHFormalization/*.lean | head -28
echo "===== 3. shared-package match evidence structures ====="
grep -rn -A12 "structure DMatchesSharedCanonicalPackage" RHFormalization/*.lean | head -16
echo "----"
grep -rn -A12 "structure HMatchesSharedCanonicalPackage" RHFormalization/*.lean | head -16
echo "===== 4. threshold choice structure ====="
grep -rn -B2 -A10 "structure InterfaceThresholdChoiceAPI" RHFormalization/*.lean | head -16
echo "===== 5. any endpoint already combining shared-Cshared Y and X ====="
grep -rn "ChosenCshared\|SharedCanonicalPackage" RHFormalization/*.lean | grep -e "theorem\|def main\|def RH" | head -10
