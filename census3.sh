#!/bin/zsh
echo "===== 1. E narrowest builders: signatures ====="
sed -n '30,70p' RHFormalization/AppendixESharedPackageFunctionalCompatibility.lean
echo "----"
sed -n '80,110p' RHFormalization/AppendixESharedPackageObligations.lean
echo "===== 2. what does buildInterfaceBridgeNonnegativeAPI consume ====="
sed -n '90,125p' RHFormalization/InterfaceNonnegative.lean
echo "===== 3. Y input S: MassEnvelopeData fields ====="
grep -rn -A20 "structure CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData" RHFormalization/*.lean | head -26
echo "===== 4. Y input F: DFHLimitData fields ====="
grep -rn -A15 "structure DFHLimitData" RHFormalization/*.lean | head -20
echo "===== 5. Y input R: DMasterResidualData fields ====="
grep -rn -A15 "structure DMasterResidualData" RHFormalization/*.lean | head -20
echo "===== 6. Y input: DFiniteStagePackageFromOperatorLayer fields ====="
grep -rn -A20 "structure DFiniteStagePackageFromOperatorLayer" RHFormalization/*.lean | head -26
