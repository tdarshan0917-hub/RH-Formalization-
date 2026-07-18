#!/bin/zsh
echo "===== 1. eta / alternating zeta, whole Mathlib ====="
grep -rln -e "dirichletEta" -e "DirichletEta" .lake/packages/mathlib/Mathlib --include='*.lean' | head -5
grep -rn -e "1 - 2 \^ (1 - s)" -e "(1 - 2 ^ (1 - " -e "alternating.*zeta" -e "zeta.*alternating" .lake/packages/mathlib/Mathlib --include='*.lean' | head -10
echo "===== 2. zeta real-valued / conjugation on reals ====="
grep -rn -e "riemannZeta_ofReal" -e "riemannZeta_conj" -e "conj.*riemannZeta" -e "riemannZeta_real" .lake/packages/mathlib/Mathlib --include='*.lean' | head -10
echo "===== 3. any sign/nonvanishing fact on (0,1) or re pos ====="
grep -rn -e "riemannZeta_ne_zero" -e "riemannZeta_pos" -e "riemannZeta_lt" -e "riemannZeta_neg_" .lake/packages/mathlib/Mathlib --include='*.lean' | grep -v "neg_nat\|neg_two" | head -12
echo "===== 4. check battery: candidate names ====="
cat > ZFCheckBattery.lean <<'EOF'
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
#check @riemannZeta_ne_zero_of_one_le_re
#check @riemannZeta_ofReal
#check @dirichletEta
#check @DirichletEta.eq_zeta
#check @riemannZeta_ne_zero_of_pos_re
#check @riemannZeta_real_lt_zero
#check @riemannZeta_neg_of_mem_Ioo
EOF
lake env lean ZFCheckBattery.lean 2>&1 | tee zf_check_battery.log
