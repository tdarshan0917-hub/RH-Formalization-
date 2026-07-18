#!/bin/zsh
echo "===== 1. exact ONFI statement (ground truth) ====="
sed -n '30,60p' RHFormalization/OmegaCodiscreteIdentityFromNormalForms.lean
echo "===== 2. MeromorphicOnC definition ====="
grep -rn -A4 "def MeromorphicOnC" RHFormalization/ --include='*.lean' | head -12
echo "===== 3. Mathlib: identity/eqOn lemmas for meromorphic + codiscrete ====="
M=.lake/packages/mathlib/Mathlib
grep -rn "eqOn" $M/Analysis/Meromorphic/ | grep -i -e "preconnected" -e "codiscrete" -e "identity" | head -20
echo "===== 4. Mathlib: analytic identity theorem names ====="
grep -rn "theorem.*eqOn_of_preconnected" $M/Analysis/Analytic/ $M/Analysis/Meromorphic/ 2>/dev/null | head -10
echo "===== 5. Mathlib: MeromorphicNFOn toolbox ====="
grep -rn "^theorem\|^lemma" $M/Analysis/Meromorphic/NormalForm.lean | head -30
echo "===== 6. check battery ====="
cat > ONFIBattery.lean <<'EOF'
import RHFormalization.OmegaCodiscreteIdentityFromNormalForms
open Filter Set
#check @MeromorphicOn.eqOn_of_preconnected_of_eventuallyEq
#check @AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check @MeromorphicNFOn.eqOn_of_eqOn
#check @codiscreteWithin
#check @EventuallyEq.codiscreteWithin
EOF
lake env lean ONFIBattery.lean 2>&1
echo "===== 7. exact? probe on ONFI goal shape ====="
cat > ONFIProbe.lean <<'EOF'
import RHFormalization.OmegaCodiscreteIdentityFromNormalForms
namespace RHFormalization
open Filter Set
example : OmegaNormalFormCodiscreteIdentityAPI := by
  constructor
  intro f g V hV hVne hVsub hf hg hEq
  exact?
end RHFormalization
EOF
lake env lean ONFIProbe.lean 2>&1
