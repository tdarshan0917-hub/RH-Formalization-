#!/bin/zsh
OUT=cai_ground_truth.txt
echo "===== 1. ConnectedOmegaAPI + Omega definition =====" > $OUT
grep -rn -B3 -A12 "structure ConnectedOmegaAPI" RHFormalization/ --include='*.lean' | head -25 >> $OUT
grep -rn -B2 -A6 -e "def Omega" -e "def Ω" -e "notation.*Ω" RHFormalization/Basic.lean RHFormalization/OmegaTopology.lean 2>/dev/null | head -25 >> $OUT
echo "===== 2. MeromorphicAlgebraAPI =====" >> $OUT
grep -rn -B3 -A20 "structure MeromorphicAlgebraAPI" RHFormalization/ --include='*.lean' | head -35 >> $OUT
echo "===== 3. MeromorphicIdentityPrincipleAPI =====" >> $OUT
grep -rn -B3 -A20 "structure MeromorphicIdentityPrincipleAPI" RHFormalization/ --include='*.lean' | head -35 >> $OUT
echo "===== 4. repo defs of MeromorphicOnC / HolomorphicOnC =====" >> $OUT
grep -rn -B2 -A6 -e "MeromorphicOnC" -e "HolomorphicOnC" RHFormalization/ --include='*.lean' | grep -A6 -B2 "def \|abbrev " | head -30 >> $OUT
echo "===== 5. Mathlib battery =====" >> $OUT
cat > CAIBattery.lean <<'EOF'
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
#check @MeromorphicOn.add
#check @MeromorphicOn.sub
#check @MeromorphicOn.eqOn_of_preconnected_of_eqOn
#check @AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check @Convex.isPreconnected
#check @IsPreconnected.isConnected
EOF
lake env lean CAIBattery.lean 2>&1 >> $OUT
wc -l $OUT && cat $OUT
