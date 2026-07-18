#!/bin/zsh
tar --exclude='.lake' -czf ~/Downloads/RHFormalization_FINAL_SPINE_8667.tar.gz .
OUT=api_triage.txt
echo "===== A. OperatorResolventBridge =====" > $OUT
grep -rn -B2 -A40 "structure OperatorResolventBridge" RHFormalization/ --include='*.lean' | head -60 >> $OUT
echo "===== B. ZeroPolePackageAPI =====" >> $OUT
grep -rn -B2 -A40 "structure ZeroPolePackageAPI" RHFormalization/ --include='*.lean' | head -60 >> $OUT
echo "===== C. InterfaceBridgeAPI =====" >> $OUT
grep -rn -B2 -A40 "structure InterfaceBridgeAPI" RHFormalization/ --include='*.lean' | head -60 >> $OUT
echo "===== D. PoleWitnessAPI =====" >> $OUT
grep -rn -B2 -A40 "structure PoleWitnessAPI" RHFormalization/ --include='*.lean' | head -60 >> $OUT
echo "===== E. RigidityNoPoleAPI =====" >> $OUT
grep -rn -B2 -A40 "structure RigidityNoPoleAPI" RHFormalization/ --include='*.lean' | head -60 >> $OUT
echo "===== F. existing builders/defaults for any of the five =====" >> $OUT
grep -rn -e "def default.*OperatorResolventBridge\|def default.*ZeroPolePackage\|def default.*InterfaceBridge\|def default.*PoleWitness\|def default.*RigidityNoPole\|: OperatorResolventBridge :=\|: ZeroPolePackageAPI :=\|: PoleWitnessAPI :=" RHFormalization/ --include='*.lean' | head -20 >> $OUT
wc -l $OUT && cat $OUT
