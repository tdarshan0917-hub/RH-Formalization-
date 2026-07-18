#!/bin/zsh
echo "===== 0. repair reference: normal-form data + nonzero lemma ====="
grep -rn -B3 -A18 "structure HSideGroupedPoleNormalFormData" RHFormalization/*.lean | head -26
grep -rn -B3 -A12 "groupedResidueCoeff_ne_zero" RHFormalization/*.lean | grep -v Endpoint | head -18
echo "===== 1. install ReflectionPairPoleClass ====="
cat > RHFormalization/ReflectionPairPoleClass.lean <<'EOF'
import RHFormalization.DefaultPoleNormalFormLayer
import RHFormalization.DefaultZeroMultiplicity

/-!
# RHFormalization.ReflectionPairPoleClass

The HONEST grouped pole class at an off-critical witness: the reflection pair
{ρ, 1−ρ}. By the factorization (ρ'−ρ)(ρ'−(1−ρ)) = 0, these are exactly the
zeros sharing the witness pole point; by the functional equation, 1−ρ is a
nontrivial zero whenever ρ is. The grouped residue is m(ρ) + m(1−ρ) — the
coefficient the genuine pole series actually carries (defect-#5 repair).
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- The reflection of a nontrivial zero is a nontrivial zero (functional
equation, forward direction). -/
theorem reflected_zero
    (ρ : ℂ) (h : IsNontrivialZetaZero ρ) :
    IsNontrivialZetaZero (1 - ρ) := by
  obtain ⟨hz, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hn : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
      intro n hcontra
      have : ρ.re = -(n : ℝ) := by
        rw [hcontra]; simp
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [this ▸ h0]
    have hone : ρ ≠ 1 := by
      intro hcontra
      rw [hcontra] at h1
      simp at h1
    rw [riemannZeta_one_sub hn hone, hz, mul_zero]
  · simp [Complex.sub_re, Complex.one_re]
    linarith
  · simp [Complex.sub_re, Complex.one_re]
    linarith

/-- An off-critical zero is not self-reflected. -/
theorem offCritical_ne_reflection
    (W : ZeroWitness) : W.ρ ≠ 1 - W.ρ := by
  intro h
  have hre : W.ρ.re = 1 - W.ρ.re := by
    rw [← Complex.one_re, ← Complex.sub_re, ← h]
  have : W.ρ.re = (1 / 2 : ℝ) := by linarith
  exact W.h_offline this

/-- The reflection pair grouped pole class: the honest class at an
off-critical witness. -/
def pairGroupedPoleClass
    (M : ZeroMultiplicityData)
    (W : ZeroWitness) :
    GroupedPoleClass M W :=
  { zeros := {W.ρ, 1 - W.ρ}
    h_witness_mem := Finset.mem_insert_self W.ρ _
    h_all_zeros := by
      intro ρ hρ
      rcases Finset.mem_insert.mp hρ with h | h
      · subst h; exact W.h_zero
      · rw [Finset.mem_singleton] at h
        subst h
        exact reflected_zero W.ρ W.h_zero
    h_same_pole := by
      intro ρ hρ
      rcases Finset.mem_insert.mp hρ with h | h
      · subst h; exact W.hs0_def.symm
      · rw [Finset.mem_singleton] at h
        subst h
        have hrefl : polePoint (1 - W.ρ) = polePoint W.ρ := by
          unfold polePoint; ring
        rw [hrefl]
        exact W.hs0_def.symm }

/-- The pair class carries the honest two-term residue. -/
theorem pairGroupedPoleClass_coeff
    (M : ZeroMultiplicityData)
    (W : ZeroWitness) :
    groupedResidueCoeff M (pairGroupedPoleClass M W) =
      ((M.mult W.ρ + M.mult (1 - W.ρ) : ℕ) : ℂ) := by
  unfold groupedResidueCoeff groupedMultiplicitySum pairGroupedPoleClass
  rw [Finset.sum_pair (offCritical_ne_reflection W)]
  simp

/-- Slim H-side grouped builder over the HONEST reflection-pair class. -/
def buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair
    (H : ZeroPolePackageAPI)
    (M : ZeroMultiplicityData)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC H.Zpole W.s0
          (groupedResidueCoeff M (pairGroupedPoleClass M W))) :
    HSideGroupedPoleNormalFormData H :=
  { M := M
    groupedClass := fun W => pairGroupedPoleClass M W
    h_principalPart := h_pp
    poleNormalForm := defaultPoleNormalFormLayer }

#print axioms pairGroupedPoleClass
#print axioms pairGroupedPoleClass_coeff
#print axioms buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair

end

end RHFormalization
EOF
lake build RHFormalization.ReflectionPairPoleClass 2>&1 | tee pair_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" pair_a.log; then
  echo "FAILED -> removing (errors below; section 0 has the structures)"
  grep -B3 -A14 "error" pair_a.log | head -70
  rm RHFormalization/ReflectionPairPoleClass.lean
  exit 1
fi
if ! grep -q "pairGroupedPoleClass' depends on axioms: \[propext, Classical.choice, Quot.sound\]" pair_a.log; then
  echo "AXIOM CHECK FAILED -> removing"; rm RHFormalization/ReflectionPairPoleClass.lean; exit 1
fi
grep -qxF "import RHFormalization.ReflectionPairPoleClass" RHFormalization.lean || printf '\nimport RHFormalization.ReflectionPairPoleClass\n' >> RHFormalization.lean
lake build 2>&1 | tee pair_root.log | tail -3
grep -q "Build completed successfully" pair_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_PAIR_CLASS.tar.gz . && echo "SNAPSHOT SAVED: PAIR_CLASS"
