#!/bin/zsh
OUT=p_api_ground_truth.txt
echo "===== 1. HasGenuinePole definition =====" > $OUT
grep -rn -B3 -A15 -e "def HasGenuinePole" -e "structure HasGenuinePole" RHFormalization/ --include='*.lean' | head -40 >> $OUT
echo "===== 2. Htot definition =====" >> $OUT
grep -rn -B3 -A15 "def Htot" RHFormalization/ --include='*.lean' | head -30 >> $OUT
echo "===== 3. polePoint definition =====" >> $OUT
grep -rn -B3 -A10 "def polePoint" RHFormalization/ --include='*.lean' | head -20 >> $OUT
echo "===== 4. existing H-side concrete candidates (zeta-derived Zpole?) =====" >> $OUT
grep -rn -e "riemannZeta" RHFormalization/ --include='*.lean' | grep -v "Basic.lean\|DefaultZetaZeroFacts\|FinalSpineFromRealZeroFree" | head -20 >> $OUT
echo "===== 5. MeromorphicOnC / HolomorphicOnC defs =====" >> $OUT
grep -rn -B2 -A8 -e "def MeromorphicOnC" -e "def HolomorphicOnC" RHFormalization/ --include='*.lean' | head -30 >> $OUT
echo "===== 6. PoleWitness builders, if any =====" >> $OUT
grep -rn -e "PoleWitnessAPI" RHFormalization/ --include='*.lean' | head -15 >> $OUT
wc -l $OUT && cat $OUT
