#!/bin/zsh
tar --exclude='.lake' -czf ~/Downloads/RHFormalization_CLEAN_8659_zero_native_witness.tar.gz .
echo "===== FULL DFiniteStage STRUCTURE =====" > zside_ground_truth.txt
sed -n '1,260p' RHFormalization/DOperatorExport.lean >> zside_ground_truth.txt
echo "===== PrimePowerPair core defs =====" >> zside_ground_truth.txt
grep -n -B2 -A10 -e "def IsPrimePowerPair" -e "def weightC" -e "def natValue" -e "def center" -e "def weightReal" RHFormalization/CanonicalPrimePowerPackage.lean >> zside_ground_truth.txt
echo "===== finite active-set helper signature =====" >> zside_ground_truth.txt
grep -n -B2 -A12 "valid_primePower_natValue_lt_finite" RHFormalization/CanonicalPrimePowerHeatKernelGaussianCoreSummability.lean >> zside_ground_truth.txt
echo "===== the axiom statement to be replaced =====" >> zside_ground_truth.txt
sed -n '20,45p' RHFormalization/AppendixDStageExistenceAssumption.lean >> zside_ground_truth.txt
echo "===== Mathlib minFac/factorization lemma names =====" >> zside_ground_truth.txt
grep -rn -e "minFac_prime" -e "minFac_dvd" -e "Prime.factorization" -e "factorization_minFac" .lake/packages/mathlib/Mathlib/Data/Nat/ --include='*.lean' | grep theorem | head -15 >> zside_ground_truth.txt
wc -l zside_ground_truth.txt
