#!/bin/zsh
tar --exclude='.lake' -czf ~/Downloads/RHFormalization_ZERO_CUSTOM_AXIOMS_8604.tar.gz .
echo "===== A. ZetaZeroFacts full definition =====" > zf_ground_truth.txt
grep -rn -B3 -A35 -e "structure ZetaZeroFacts" -e "def ZetaZeroFacts" RHFormalization/ --include='*.lean' | head -70 >> zf_ground_truth.txt
echo "===== B. the default builder, full body =====" >> zf_ground_truth.txt
grep -rln "defaultZetaZeroFacts_of_realZeroFree" RHFormalization/ --include='*.lean' >> zf_ground_truth.txt
grep -rn -B5 -A50 "defaultZetaZeroFacts_of_realZeroFree" RHFormalization/ --include='*.lean' | head -90 >> zf_ground_truth.txt
echo "===== C. Mathlib: zeta sign/nonvanishing on real (0,1) =====" >> zf_ground_truth.txt
grep -rn -e "riemannZeta_neg" -e "riemannZeta_lt_zero" -e "riemannZeta_ne_zero_of" -e "riemannZeta_eq_zero" .lake/packages/mathlib/Mathlib --include='*.lean' | head -20 >> zf_ground_truth.txt
echo "===== D. Mathlib: eta / alternating zeta ingredients =====" >> zf_ground_truth.txt
grep -rn -e "dirichletEta" -e "DirichletEta" -e "eta_eq_zeta" -e "one_sub_two" .lake/packages/mathlib/Mathlib/NumberTheory/LSeries --include='*.lean' | head -15 >> zf_ground_truth.txt
echo "===== E. Mathlib: functional equation + Gamma real values =====" >> zf_ground_truth.txt
grep -rn -e "riemannZeta_one_sub" -e "riemannZeta_neg_nat" -e "Gammaℝ" .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean | head -12 >> zf_ground_truth.txt
cat zf_ground_truth.txt
