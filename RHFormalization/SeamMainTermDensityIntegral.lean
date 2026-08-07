import RHFormalization.SeamCoreFactoredForm
import Mathlib

/-!
# SeamMainTermDensityIntegral — the compensator bracket as density integral + pole

ROUTE CARD
1. Target: EXACT identities on the P2-4b bracket (M2 bridge ABSENT on disk;
   first-order route per audit stop-order):
   (i) pole split: seamMainTerm = (e^{aR}−1)/a + 1/a, a = 1/2 − √(s+1/4);
   (ii) FTC: (e^{aR}−1)/a = ∫₀^R e^{au} du (a ≠ 0);
   (iii) bracket = [seamArithmeticSum − ∫₀^{admR n} e^{au} du] − 1/a.
   The pole 1/a is n-independent and bounded on every Ω-compact.
2. Raw B on Ω? NO. B−M bare Prop? NO — exact algebra + FTC.
3. Consumer: seamCore_eq_prefactor_mul_bracket bracket (P2-4b) → hSC →
   correctedResidual_locbdd_of_seamCore → HtailExists.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- **Pole split of the seam main term** (pure ring algebra, every n, s). -/
theorem seamMainTerm_pole_split (n : ℕ) (s : ℂ) :
    seamMainTerm n s
      = (Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * (admR n : ℝ)) - 1)
          / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))
        + 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  unfold seamMainTerm
  ring

/-- **FTC leg**: `(e^{aR} − 1)/a = ∫₀^R e^{au} du` for `a ≠ 0`. -/
theorem exp_sub_one_div_eq_integral (a : ℂ) (ha : a ≠ 0) (R : ℝ) :
    (Complex.exp (a * R) - 1) / a
      = ∫ u in (0:ℝ)..R, Complex.exp (a * u) := by
  have h : (∫ u in (0:ℝ)..R, Complex.exp (a * u))
      = (Complex.exp (a * R) - Complex.exp (a * ((0:ℝ):ℂ))) / a := by
    first
      | exact integral_exp_mul_complex ha
      | exact intervalIntegral.integral_exp_mul_complex ha
  rw [h, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- **The compensator IS the density integral plus a bounded pole.** -/
theorem seamMainTerm_eq_densityIntegral_add_pole (n : ℕ) (s : ℂ)
    (ha : ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) ≠ 0) :
    seamMainTerm n s
      = (∫ u in (0:ℝ)..(admR n),
          Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * u))
        + 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  rw [seamMainTerm_pole_split n s,
    exp_sub_one_div_eq_integral _ ha (admR n)]

/-- **The P2-4b bracket in Stieltjes-ready form**: prime sum minus its
density integral, minus the n-independent pole term. -/
theorem seamBracket_eq_stieltjes_sub_pole (n : ℕ) (s : ℂ)
    (ha : ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) ≠ 0) :
    seamArithmeticSum n s - seamMainTerm n s
      = (seamArithmeticSum n s
          - ∫ u in (0:ℝ)..(admR n),
              Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * u))
        - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  rw [seamMainTerm_eq_densityIntegral_add_pole n s ha]
  ring

#print axioms seamMainTerm_pole_split
#print axioms exp_sub_one_div_eq_integral
#print axioms seamMainTerm_eq_densityIntegral_add_pole
#print axioms seamBracket_eq_stieltjes_sub_pole

end

end RHFormalization
