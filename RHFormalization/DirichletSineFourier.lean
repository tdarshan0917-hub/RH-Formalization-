import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# RHFormalization.DirichletSineFourier
**Brick 3, completeness stone 1.** `fourier n (x) − fourier (−n) (x) = 2i·sin(nπx/L)`
on `AddCircle (2L)`. Pure `exp` algebra.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Real

/-- On the circle `AddCircle (2L)`, `fourier n` at a real point `x` is `exp(i·π·n·x/L)`. -/
theorem fourier_two_L_apply (L : ℝ) (hL : L ≠ 0) (n : ℤ) (x : ℝ) :
    fourier n ((x : AddCircle (2 * L))) =
      Complex.exp (Complex.I * (↑n * ↑Real.pi * ↑x / ↑L)) := by
  rw [fourier_coe_apply]
  have h2L : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have harg : (2 * ↑Real.pi * Complex.I * ↑n * ↑x / ↑(2 * L))
      = Complex.I * (↑n * ↑Real.pi * ↑x / ↑L) := by
    push_cast
    field_simp
  rw [harg]

/-- The difference of conjugate Fourier modes is `2i·sin`. -/
theorem fourier_sub_fourier_neg (L : ℝ) (hL : L ≠ 0) (n : ℤ) (x : ℝ) :
    fourier n ((x : AddCircle (2 * L))) - fourier (-n) ((x : AddCircle (2 * L)))
      = 2 * Complex.I * Complex.sin (↑n * ↑Real.pi * ↑x / ↑L) := by
  rw [fourier_two_L_apply L hL, fourier_two_L_apply L hL]
  rw [show ((-n : ℤ) : ℂ) * ↑Real.pi * ↑x / ↑L = -(↑n * ↑Real.pi * ↑x / ↑L) by push_cast; ring]
  rw [show Complex.I * -(↑n * ↑Real.pi * ↑x / ↑L) = -(Complex.I * (↑n * ↑Real.pi * ↑x / ↑L)) by ring]
  rw [Complex.sin]
  have hexp : Complex.exp (Complex.I * (↑n * ↑Real.pi * ↑x / ↑L))
      * Complex.exp (-(Complex.I * (↑n * ↑Real.pi * ↑x / ↑L))) = 1 := by
    rw [← Complex.exp_add]; simp
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

#print axioms fourier_two_L_apply
#print axioms fourier_sub_fourier_neg

end

end RHFormalization
