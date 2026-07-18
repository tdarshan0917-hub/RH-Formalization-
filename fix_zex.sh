#!/bin/zsh
python3 - <<'PY'
import sys
src = open('install_zex.sh').read()
marker = "cat > RHFormalization/DefaultZeroExhaustion.lean <<'EOF'"
i = src.find(marker)
if i < 0: print("MARKER MISSING"); sys.exit(1)
start = src.find("\n", i) + 1
j = src.find("\nEOF\n", start)
if j < 0: print("TERMINATOR MISSING"); sys.exit(1)
body = src[start:j+1]

# fix 1: orphan norm_num after simp already closed the 2+I re-goal
old1 = """      simp [Complex.add_re, Complex.I_re]
      norm_num"""
new1 = """      simp [Complex.add_re, Complex.I_re]"""
if old1 not in body: print("FIX1 ANCHOR MISSING"); sys.exit(1)
body = body.replace(old1, new1)

# fix 2: div_le_iff renamed div_le_iff₀ in this Mathlib
body = body.replace("div_le_iff h0", "div_le_iff₀ h0")
body = body.replace("div_le_iff h1re", "div_le_iff₀ h1re")
body = body.replace("div_le_iff hNpos", "div_le_iff₀ hNpos")
if "div_le_iff " in body.replace("div_le_iff₀","DONE"): print("FIX2 LEFTOVER"); sys.exit(1)

if "def defaultZeroExhaustion" not in body: print("BODY BAD"); sys.exit(1)
open('RHFormalization/DefaultZeroExhaustion.lean','w').write(body)
print(f"regenerated with both fixes: {len(body)} chars")
PY
if [ $? -ne 0 ]; then echo "PATCH FAILED"; rm -f RHFormalization/DefaultZeroExhaustion.lean; exit 1; fi
lake build RHFormalization.DefaultZeroExhaustion 2>&1 | tee zex_b.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" zex_b.log; then
  echo "FAILED -> removing (errors below)"
  grep -B3 -A16 "error" zex_b.log | head -80
  rm RHFormalization/DefaultZeroExhaustion.lean
  exit 1
fi
if ! grep -q "defaultZeroExhaustion' depends on axioms: \[propext, Classical.choice, Quot.sound\]" zex_b.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/DefaultZeroExhaustion.lean; exit 1
fi
grep -qxF "import RHFormalization.DefaultZeroExhaustion" RHFormalization.lean || printf '\nimport RHFormalization.DefaultZeroExhaustion\n' >> RHFormalization.lean
lake build 2>&1 | tee zex_root.log | tail -3
grep -q "Build completed successfully" zex_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ZEX_DEFAULT.tar.gz . && echo "SNAPSHOT SAVED: ZEX_DEFAULT"
