#!/bin/zsh
python3 - <<'PY'
import sys
src = open('install_pair.sh').read()
marker = "cat > RHFormalization/ReflectionPairPoleClass.lean <<'EOF'"
i = src.find(marker)
if i < 0: print("MARKER MISSING"); sys.exit(1)
start = src.find("\n", i) + 1
j = src.find("\nEOF\n", start)
if j < 0: print("TERMINATOR MISSING"); sys.exit(1)
body = src[start:j+1]
old = """  rw [Finset.sum_pair (offCritical_ne_reflection W)]
  simp"""
new = """  rw [Finset.sum_pair (offCritical_ne_reflection W)]"""
if old not in body: print("FIX ANCHOR MISSING"); sys.exit(1)
body = body.replace(old, new)
if "def pairGroupedPoleClass" not in body: print("BODY BAD"); sys.exit(1)
open('RHFormalization/ReflectionPairPoleClass.lean','w').write(body)
print(f"regenerated, rw-closed proof: {len(body)} chars")
PY
if [ $? -ne 0 ]; then echo "PATCH FAILED"; rm -f RHFormalization/ReflectionPairPoleClass.lean; exit 1; fi
lake build RHFormalization.ReflectionPairPoleClass 2>&1 | tee pair_c.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" pair_c.log; then
  echo "FAILED -> removing (errors below)"
  grep -B3 -A14 "error" pair_c.log | head -60
  rm RHFormalization/ReflectionPairPoleClass.lean
  exit 1
fi
if ! grep -q "pairGroupedPoleClass_coeff' depends on axioms: \[propext, Classical.choice, Quot.sound\]" pair_c.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/ReflectionPairPoleClass.lean; exit 1
fi
grep -qxF "import RHFormalization.ReflectionPairPoleClass" RHFormalization.lean || printf '\nimport RHFormalization.ReflectionPairPoleClass\n' >> RHFormalization.lean
lake build 2>&1 | tee pair_root.log | tail -3
grep -q "Build completed successfully" pair_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_PAIR_CLASS.tar.gz . && echo "SNAPSHOT SAVED: PAIR_CLASS"
