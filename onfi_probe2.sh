#!/bin/zsh
M=.lake/packages/mathlib/Mathlib
echo "===== 1. NormalForm.lean tail (609-end) ====="
sed -n '609,760p' $M/Analysis/Meromorphic/NormalForm.lean | grep -n -B1 -A4 "^theorem\|^lemma"
echo "===== 2. preconnected anywhere in Meromorphic/ ====="
grep -rn "reconnected" $M/Analysis/Meromorphic/ | head -15
echo "===== 3. order = top propagation lemmas ====="
grep -rn "orderAt.*⊤\|order.*eq_top\|order_ne_top" $M/Analysis/Meromorphic/Order.lean $M/Analysis/Meromorphic/Divisor.lean 2>/dev/null | grep "theorem\|lemma" | head -15
echo "===== 4. Order.lean full theorem list ====="
grep -n "^theorem\|^lemma" $M/Analysis/Meromorphic/Order.lean | head -40
echo "===== 5. check battery: candidate hinges ====="
cat > ONFIBattery2.lean <<'EOF'
import RHFormalization.OmegaCodiscreteIdentityFromNormalForms
open Filter Set
#check @MeromorphicOn.eqOn_compl_of_preconnected_of_eventuallyEq
#check @MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
#check @MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
#check @MeromorphicNFOn.eqOn_of_preconnected_of_eventuallyEq
#check @MeromorphicOn.codiscreteWithin_setOf_meromorphicNFAt
EOF
lake env lean ONFIBattery2.lean 2>&1
