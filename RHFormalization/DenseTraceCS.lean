import RHFormalization.DenseCenteredTrace
import RHFormalization.DenseFreeDualBound
import RHFormalization.DenseWeightedCS
import RHFormalization.DensePerturbedEnergy
import Mathlib

/-!
# DenseTraceCS — B(i)-8c inst.3c(i): Re/Im foundations for the trace CS bound

Four legs for the assembly `‖denseCenteredTrace‖² ≤ 4·Q^V·S^V`:
transpose symmetry of `denseAV`, its diagonal entry, `denseDnorm² = re²+im²`,
and the Re/Im components of `denseCenteredTrace` as real weighted sums.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- `denseAV` is transpose-symmetric (from PosDef → IsHermitian over ℝ). -/
theorem denseAV_transpose_eq (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Matrix.transpose (denseAV n a) = denseAV n a := by
  have h : Matrix.conjTranspose (denseAV n a) = denseAV n a :=
    (denseAV_posDef n ha).1
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact h

/-- Diagonal entry of `denseAV`: `λ_k + a + V_kk`. -/
theorem denseAV_apply_diag (n : ℕ) (a : ℝ) (k : Fin (denseN n)) :
    denseAV n a k k
      = (galerkinLam (denseL n) (k : ℕ) + a) + denseV n k k := by
  unfold denseAV
  rw [Matrix.add_apply, Matrix.diagonal_apply_eq]

/-- `denseDnorm² = (Re d)² + (Im d)²` — the recombination identity. -/
theorem denseDnorm_sq (n : ℕ) (s : ℂ) (k : Fin (denseN n)) :
    denseDnorm n s k ^ 2
      = (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) (k : ℕ) : ℝ) : ℂ))).re ^ 2
        + (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) (k : ℕ) : ℝ) : ℂ))).im ^ 2 := by
  unfold denseDnorm
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Real part of the centered trace as a real weighted sum. -/
theorem denseCenteredTrace_re (n : ℕ) (s : ℂ) :
    (denseCenteredTrace n s).re
      = (1 / denseL n) * ∑ m : Fin (denseN n),
          denseCenteredMatrix n m m *
            (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ))).re := by
  unfold denseCenteredTrace
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]
  refine congrArg (fun t => (1 / denseL n) * t) ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Imaginary part of the centered trace as a real weighted sum. -/
theorem denseCenteredTrace_im (n : ℕ) (s : ℂ) :
    (denseCenteredTrace n s).im
      = (1 / denseL n) * ∑ m : Fin (denseN n),
          denseCenteredMatrix n m m *
            (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ))).im := by
  unfold denseCenteredTrace
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.im_sum]
  refine congrArg (fun t => (1 / denseL n) * t) ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

#print axioms denseAV_transpose_eq
#print axioms denseAV_apply_diag
#print axioms denseDnorm_sq
#print axioms denseCenteredTrace_re
#print axioms denseCenteredTrace_im

end

end RHFormalization
