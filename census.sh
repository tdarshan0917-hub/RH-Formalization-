#!/bin/zsh
echo "===== 1. Y: DDetailedConstructionWithOperatorLegality (full structure) ====="
grep -rn -A40 "structure DDetailedConstructionWithOperatorLegality" RHFormalization/*.lean | head -50
echo "===== 2. Y's parent: OperatorResolventBridge ====="
grep -rn -A20 "structure OperatorResolventBridge" RHFormalization/*.lean | head -28
echo "===== 3. X: HMeromorphicWithNormalFormPoles (full structure) ====="
grep -rn -A40 "structure HMeromorphicWithNormalFormPoles" RHFormalization/*.lean | head -50
echo "===== 4. X's parent: LegacyZeroPolePackageAPI ====="
grep -rn -A20 "structure LegacyZeroPolePackageAPI" RHFormalization/*.lean | head -28
echo "===== 5. E: InterfaceBridgeNonnegativeAPI (full structure) ====="
grep -rn -A30 "structure InterfaceBridgeNonnegativeAPI" RHFormalization/*.lean | head -40
echo "===== 6. existing partial witnesses / builders for Y X E ====="
grep -rn "DDetailedConstruction\|HMeromorphicWithNormalFormPoles\|InterfaceBridgeNonnegativeAPI" RHFormalization/*.lean | grep -e "def \|theorem \|:= {" | grep -v "structure" | head -20
