#!/bin/zsh
OUT=final_frontier_map.txt
echo "===== 1. HasGenuinePole / MeromorphicOnC / HolomorphicOnC (loose) =====" > $OUT
grep -rn -B2 -A8 "HasGenuinePole" RHFormalization/Basic.lean RHFormalization/PoleGeometry.lean RHFormalization/HMeromorphicPackage.lean 2>/dev/null | head -30 >> $OUT
grep -rn -B1 -A6 -e "MeromorphicOnC" -e "HolomorphicOnC" RHFormalization/Basic.lean RHFormalization/AnnexSpine.lean 2>/dev/null | head -25 >> $OUT
echo "===== 2. FULL MainTheorem.lean (the endpoint catalog) =====" >> $OUT
cat RHFormalization/MainTheorem.lean >> $OUT
echo "===== 3. HSidePoleWitness builder signatures =====" >> $OUT
sed -n '150,215p' RHFormalization/HSidePoleWitness.lean >> $OUT
wc -l $OUT && cat $OUT
