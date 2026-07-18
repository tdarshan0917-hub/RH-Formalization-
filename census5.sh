#!/bin/zsh
echo "===== 1. ZeroWitness: the central definition ====="
grep -rn -B4 -A14 "structure ZeroWitness" RHFormalization/*.lean | head -24
echo "===== 2. ZeroMultiplicityData ====="
grep -rn -A12 "structure ZeroMultiplicityData" RHFormalization/*.lean | head -16
echo "===== 3. ZeroExhaustion ====="
grep -rn -A12 "structure ZeroExhaustion" RHFormalization/*.lean | head -16
echo "===== 4. HasGenuinePole ====="
grep -rn -B2 -A10 "def HasGenuinePole" RHFormalization/*.lean | head -16
echo "===== 5. where ZeroWitness enters the final spine (how RH consumes it) ====="
grep -rn "ZeroWitness" RHFormalization/MainTheorem.lean RHFormalization/RigidityBridge.lean RHFormalization/FinalSpineFromRealZeroFree.lean 2>/dev/null | head -12
echo "===== 6. HArchPackage + CanonicalPrimePowerPackage (the concrete objects) ====="
grep -rn -A10 "structure HArchPackage" RHFormalization/*.lean | head -14
grep -rn -A12 "structure CanonicalPrimePowerPackage " RHFormalization/*.lean | head -16
echo "===== 7. ZeroPoleLocalUniformConvergenceAPI + ZpoleMeromorphicFromSeriesAPI ====="
grep -rn -A10 "structure ZeroPoleLocalUniformConvergenceAPI" RHFormalization/*.lean | head -14
grep -rn -A10 "structure ZpoleMeromorphicFromSeriesAPI" RHFormalization/*.lean | head -14
