#!/bin/zsh
cat > RHFormalization/DefaultZeroMultiplicity.lean <<'EOF'
import RHFormalization.DefaultZeroExhaustion
import RHFormalization.HSidePoleWitness

/-!
# RHFormalization.DefaultZeroMultiplicity

A PROVEN inhabitant of `ZeroMultiplicityData`: `mult ρ` is the genuine analytic
order of vanishing of ζ at ρ. Positivity at a nontrivial zero: the order is
nonzero because ζρ = 0, and finite because ζ is not locally ≡ 0 anywhere in
{re < 1} — the identity-theorem chain from DefaultZeroExhaustion, factored
here as `zeta_not_locally_zero`.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- ζ is not locally identically zero at any point of the half-plane re < 1. -/
theorem zeta_not_locally_zero
    (a : ℂ) (ha : a.re < 1)
    (h : ∀ᶠ z in nhds a, riemannZeta z = 0) : False := by
  have haU1 : a ∈ {s : ℂ | s.re < 1} := ha
  have hEq1 : Set.EqOn riemannZeta 0 {s : ℂ | s.re < 1} :=
    zeta_analyticOnNhd_re_lt_one.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ((convex_halfSpace_re_lt 1).isPreconnected) haU1 h
  have hI_U1 : Complex.I ∈ {s : ℂ | s.re < 1} := by
    simp [Complex.I_re]
  have hcI : riemannZeta =ᶠ[nhds Complex.I] 0 := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hI_U1]
      with z hz
    exact hEq1 hz
  have hI_U2 : Complex.I ∈ {s : ℂ | 0 < s.im} := by
    simp [Complex.I_im]
  have hEq2 : Set.EqOn riemannZeta 0 {s : ℂ | 0 < s.im} :=
    zeta_analyticOnNhd_im_pos.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ((convex_halfSpace_im_gt 0).isPreconnected) hI_U2 hcI
  have h2I : (2 + Complex.I) ∈ {s : ℂ | 0 < s.im} := by
    simp [Complex.add_im, Complex.I_im]
  have hz2I : riemannZeta (2 + Complex.I) = 0 := hEq2 h2I
  have hne2I : riemannZeta (2 + Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp [Complex.add_re, Complex.I_re]
  exact hne2I hz2I

/-- The honest multiplicity: the analytic order of vanishing of ζ. -/
noncomputable def zetaZeroMult (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

/-- A PROVEN inhabitant of the zero-multiplicity structure, carrying the
genuine analytic multiplicity. -/
noncomputable def defaultZeroMultiplicityData : ZeroMultiplicityData :=
  { mult := zetaZeroMult
    h_mult_pos := by
      intro ρ hρ
      obtain ⟨hz, h0, h1⟩ := hρ
      have hA : AnalyticAt ℂ riemannZeta ρ :=
        zeta_analyticOnNhd_re_lt_one ρ h1
      have hne_zero : analyticOrderAt riemannZeta ρ ≠ 0 := by
        intro h
        exact (hA.analyticOrderAt_eq_zero.mp h) hz
      have hne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
        intro h
        exact zeta_not_locally_zero ρ h1 (analyticOrderAt_eq_top.mp h)
      unfold zetaZeroMult
      lift (analyticOrderAt riemannZeta ρ) to ℕ using hne_top with n hn
      simpa using Nat.pos_of_ne_zero (by exact_mod_cast hne_zero) }

#print axioms defaultZeroMultiplicityData
#print axioms zeta_not_locally_zero

end

end RHFormalization
EOF
lake build RHFormalization.DefaultZeroMultiplicity 2>&1 | tee dzm_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" dzm_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B3 -A16 "error" dzm_a.log | head -70
  rm RHFormalization/DefaultZeroMultiplicity.lean
  exit 1
fi
if ! grep -q "defaultZeroMultiplicityData' depends on axioms: \[propext, Classical.choice, Quot.sound\]" dzm_a.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/DefaultZeroMultiplicity.lean; exit 1
fi
grep -qxF "import RHFormalization.DefaultZeroMultiplicity" RHFormalization.lean || printf '\nimport RHFormalization.DefaultZeroMultiplicity\n' >> RHFormalization.lean
lake build 2>&1 | tee dzm_root.log | tail -3
grep -q "Build completed successfully" dzm_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_M_DEFAULT.tar.gz . && echo "SNAPSHOT SAVED: M_DEFAULT"
