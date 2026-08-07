import RHFormalization.SeamMainTermDensityIntegral
import Mathlib

/-!
# SeamBracketKernelForm — the common kernel of the two seam faces

ROUTE CARD
1. Target: EXACT kernel alignment of the density face:
   `∫₀^R e^{(1/2−w)u} du = ∫₀^R e^u · e^{−(1/2+w)u} du`, exposing the
   common kernel K(u) = e^{−(1/2+w)u} paired against the measure e^u du —
   the Lebesgue face of the Stieltjes pairing ∫ K d(ψ − e^u du). The
   arithmetic face (point masses Λ(q) at log q against the same K) is
   brick 3, pending weightC read.
2. Raw B on Ω? NO. B−M bare Prop? NO — exp algebra inside an integral.
3. Consumer: seamBracket_eq_stieltjes_sub_pole (brick 1) → P2-4b bracket
   → hSC → correctedResidual_locbdd_of_seamCore → HtailExists.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- **Kernel alignment of the density integrand** (pointwise exp algebra). -/
theorem densityIntegrand_kernel_form (w : ℂ) (u : ℝ) :
    Complex.exp (((1/2:ℂ) - w) * (u : ℂ))
      = Complex.exp ((u : ℂ)) * Complex.exp (-((1/2:ℂ) + w) * (u : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **The density integral against the common kernel** `e^{−(1/2+w)u}`. -/
theorem densityIntegral_kernel_form (w : ℂ) (R : ℝ) :
    (∫ u in (0:ℝ)..R, Complex.exp (((1/2:ℂ) - w) * (u : ℂ)))
      = ∫ u in (0:ℝ)..R,
          Complex.exp ((u : ℂ)) * Complex.exp (-((1/2:ℂ) + w) * (u : ℂ)) := by
  apply intervalIntegral.integral_congr
  intro u _
  exact densityIntegrand_kernel_form w u

/-- **The bracket with the density face in common-kernel form**: prime sum
minus `∫ e^u·K(u) du` minus the n-independent pole, K(u) = e^{−(1/2+w)u},
w = √(s+1/4). -/
theorem seamBracket_eq_kernelPaired_sub_pole (n : ℕ) (s : ℂ)
    (ha : ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) ≠ 0) :
    seamArithmeticSum n s - seamMainTerm n s
      = (seamArithmeticSum n s
          - ∫ u in (0:ℝ)..(admR n),
              Complex.exp ((u : ℂ))
                * Complex.exp (-((1/2:ℂ) + Complex.sqrt (s + (1/4:ℂ))) * (u : ℂ)))
        - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  rw [seamBracket_eq_stieltjes_sub_pole n s ha,
    densityIntegral_kernel_form (Complex.sqrt (s + (1/4:ℂ))) (admR n)]

#print axioms densityIntegrand_kernel_form
#print axioms densityIntegral_kernel_form
#print axioms seamBracket_eq_kernelPaired_sub_pole

end

end RHFormalization
