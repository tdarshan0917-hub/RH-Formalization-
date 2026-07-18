#!/bin/zsh
echo "===== 1. narrowest Y builder: WindowFRNoSpeed (full file head) ====="
sed -n '1,40p' RHFormalization/CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed.lean
echo "===== 2. payload structure: ChosenLengthDLimitPayload ====="
grep -rn -B2 -A18 "structure ChosenLengthDLimitPayload" RHFormalization/*.lean | head -28
echo "===== 3. E core: InterfaceBridgeAPI fields ====="
grep -rn -A25 "structure InterfaceBridgeAPI" RHFormalization/*.lean | head -32
echo "===== 4. X core: HMeromorphicPackageLayerV2 fields ====="
grep -rn -A25 "structure HMeromorphicPackageLayerV2" RHFormalization/*.lean | head -32
echo "===== 5. X core: HSideGroupedPoleNormalFormData fields ====="
grep -rn -A20 "structure HSideGroupedPoleNormalFormData" RHFormalization/*.lean | head -26
echo "===== 6. existing E builders ====="
grep -rn "InterfaceBridge" RHFormalization/*.lean | grep -e "def build" -e "def default" | head -10
echo "===== 7. existing X builders ====="
grep -rn "HMeromorphicPackageLayerV2\|HSideGroupedPoleNormalForm\|HMeromorphicWithNormalFormPoles" RHFormalization/*.lean | grep -e "def build" -e "def default" | head -10
