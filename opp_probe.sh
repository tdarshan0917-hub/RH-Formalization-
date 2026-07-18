#!/bin/zsh
tar --exclude='.lake' --exclude='*.bak*' -czf ~/Downloads/RHFormalization_ROOT_CLEAN_8673.tar.gz .
OUT=opp_ground_truth.txt
echo "===== 1. OmegaPreperfectAPI + OCI structures =====" > $OUT
grep -rn -B3 -A12 -e "structure OmegaPreperfectAPI" -e "structure OmegaCodiscreteMeromorphicIdentityAPI" RHFormalization/ --include='*.lean' >> $OUT
echo "===== 2. Omega definition + openness lemma =====" >> $OUT
grep -rn -B2 -A6 -e "def Omega" -e "isOpen_Omega" RHFormalization/Basic.lean RHFormalization/OmegaTopology.lean RHFormalization/OmegaConnected.lean 2>/dev/null | head -30 >> $OUT
echo "===== 3. Mathlib Preperfect battery =====" >> $OUT
cat > OPPBattery.lean <<'EOF'
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
import Mathlib.Topology.Perfect
open Set Filter
#check @Preperfect
#check @preperfect_iff_nhds
#check @AccPt
#check @IsOpen.preperfect
#check @Perfect.preperfect
EOF
lake env lean OPPBattery.lean 2>&1 >> $OUT
echo "===== 4. exact? probe: let Lean find the OPP proof =====" >> $OUT
cat > OPPProbe.lean <<'EOF'
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
namespace RHFormalization
open Set
example : Preperfect Ω := by exact?
end RHFormalization
EOF
lake env lean OPPProbe.lean 2>&1 >> $OUT
echo "===== 5. fallback probe: unfold then search =====" >> $OUT
cat > OPPProbe2.lean <<'EOF'
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
namespace RHFormalization
open Set Filter
example : Preperfect Ω := by
  intro x hx
  exact?
end RHFormalization
EOF
lake env lean OPPProbe2.lean 2>&1 >> $OUT
cat $OUT
