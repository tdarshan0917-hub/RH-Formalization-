#!/bin/zsh
python3 - <<'PY'
import sys
src = open('install_stab.sh').read()
marker = "cat > RHFormalization/HPPStabilization.lean <<'EOF'"
i = src.find(marker)
if i < 0: print("MARKER MISSING"); sys.exit(1)
start = src.find("\n", i) + 1
j = src.find("\nEOF\n", start)
if j < 0: print("TERMINATOR MISSING"); sys.exit(1)
body = src[start:j+1]

o1 = """  \u00b7 simp only [Set.mem_setOf_eq] at hre1 \u22a2
    linarith
  \u00b7 simp only [Set.mem_setOf_eq] at hre2 \u22a2
    linarith"""
n1 = """  \u00b7 linarith
  \u00b7 linarith"""
if o1 not in body: print("FIX1 ANCHOR MISSING"); sys.exit(1)
body = body.replace(o1, n1)

o2 = "rw [hd1, hd2, div_add_div_same, pairGroupedPoleClass_coeff]"
n2 = "rw [hd1, hd2, pairGroupedPoleClass_coeff]"
if o2 not in body: print("FIX2 ANCHOR MISSING"); sys.exit(1)
body = body.replace(o2, n2)

o3 = """    unfold zeroPoleSummand
    exact ((differentiableAt_const _).div
      ((differentiableAt_id.sub (differentiableAt_const _)).congr_of_eventuallyEq
        (by filter_upwards with z; unfold zeroPoleDenom; ring) |>.congr_of_eventuallyEq
        (by filter_upwards with z; rfl))
      hden).differentiableWithinAt"""
n3 = """    refine DifferentiableAt.differentiableWithinAt ?_
    unfold zeroPoleSummand zeroPoleDenom
    unfold zeroPoleDenom at hden
    first
      | exact (differentiableAt_const _).div
          (differentiableAt_id'.add (differentiableAt_const _)) hden
      | exact (differentiableAt_const _).div
          (differentiableAt_id.add (differentiableAt_const _)) hden
      | fun_prop (disch := assumption)"""
if o3 not in body: print("FIX3 ANCHOR MISSING"); sys.exit(1)
body = body.replace(o3, n3)
open('RHFormalization/HPPStabilization.lean','w').write(body)
print(f"stabilization file regenerated with 3 fixes: {len(body)} chars")
PY
if [ $? -ne 0 ]; then echo "PATCH FAILED"; rm -f RHFormalization/HPPStabilization.lean; exit 1; fi
lake build RHFormalization.HPPStabilization 2>&1 | tee stab_b.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" stab_b.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A14 "error" stab_b.log | head -90
  rm RHFormalization/HPPStabilization.lean
  exit 1
fi
if ! grep -q "zeroPolePartial_stabilized' depends on axioms: \[propext, Classical.choice, Quot.sound\]" stab_b.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/HPPStabilization.lean; exit 1
fi
if ! grep -q "remainder_differentiableOn' depends on axioms: \[propext, Classical.choice, Quot.sound\]" stab_b.log; then
  echo "AXIOM CHECK 2 FAILED -> removing"; rm RHFormalization/HPPStabilization.lean; exit 1
fi
grep -qxF "import RHFormalization.HPPStabilization" RHFormalization.lean || printf '\nimport RHFormalization.HPPStabilization\n' >> RHFormalization.lean
lake build 2>&1 | tee stab_root.log | tail -3
grep -q "Build completed successfully" stab_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_STABILIZATION.tar.gz . && echo "SNAPSHOT SAVED: STABILIZATION"
