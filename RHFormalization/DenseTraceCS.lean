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

/-! ## inst.3c(ii): the recombined trace Cauchy–Schwarz bound -/

set_option maxHeartbeats 1600000

/-- **B(i)-8c inst.3c(ii)**: `‖denseCenteredTrace n s‖² ≤ 4·Q^V·S^V(|d|)`.
Re/Im recombination of `trace_diag_cauchy_schwarz` at the resolvent diagonal.
No Re/Im loss; the factor 4 is exactly the frozen `1/L` vs `1/(2L)`
normalization. -/
theorem denseCenteredTrace_sq_le (n : ℕ) {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ‖denseCenteredTrace n s‖ ^ 2
      ≤ 4 * denseQV n a * denseSVReal n a (denseDnorm n s) := by
  have hL : (0:ℝ) < denseL n := denseL_pos n
  have hApd : (denseAV n a).PosDef := denseAV_posDef n ha
  have hAsym : Matrix.transpose (denseAV n a) = denseAV n a :=
    denseAV_transpose_eq n ha
  have h1 := trace_diag_cauchy_schwarz
    (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
    (denseCenteredMatrix n) (denseAV n a) hApd hAsym
  have h2 := trace_diag_cauchy_schwarz
    (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
    (denseCenteredMatrix n) (denseAV n a) hApd hAsym
  have hSV2 : denseSVReal n a (denseDnorm n s)
      = 1 / (2 * denseL n) *
          ∑ i, denseAV n a i i * denseDnorm n s i ^ 2 := by
    rw [denseSVReal_eq_S0_add_JV]
    unfold denseS0 denseJV
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun t => 1 / (2 * denseL n) * t) ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [denseAV_apply_diag]
    ring
  have hdual :
      (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
        * denseAV n a *
        Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)).trace
      + (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
        * denseAV n a *
        Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)).trace
      = 2 * denseL n * denseSVReal n a (denseDnorm n s) := by
    rw [trace_diag_mul_A_mul_diag, trace_diag_mul_A_mul_diag, hSV2,
      ← Finset.sum_add_distrib, ← mul_assoc, mul_one_div,
      div_self (mul_pos two_pos hL).ne', one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [denseDnorm_sq]
    ring
  have hE :
      (Matrix.transpose (denseCenteredMatrix n) * (denseAV n a)⁻¹
        * denseCenteredMatrix n).trace
      = 2 * denseL n * denseQV n a := by
    unfold denseQV
    rw [← mul_assoc, mul_one_div, div_self (mul_pos two_pos hL).ne', one_mul]
  have hre2 : denseL n * (denseCenteredTrace n s).re
      = (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
        * denseCenteredMatrix n).trace := by
    rw [denseCenteredTrace_re n s, trace_diagonal_mul, ← mul_assoc, mul_one_div,
      div_self hL.ne', one_mul]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have him2 : denseL n * (denseCenteredTrace n s).im
      = (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
        * denseCenteredMatrix n).trace := by
    rw [denseCenteredTrace_im n s, trace_diagonal_mul, ← mul_assoc, mul_one_div,
      div_self hL.ne', one_mul]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hnorm : ‖denseCenteredTrace n s‖ ^ 2
      = (denseCenteredTrace n s).re ^ 2 + (denseCenteredTrace n s).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hkey :
      (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
        * denseCenteredMatrix n).trace ^ 2
      + (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
        * denseCenteredMatrix n).trace ^ 2
      ≤ (2 * denseL n * denseSVReal n a (denseDnorm n s))
          * (2 * denseL n * denseQV n a) := by
    calc (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
        * denseCenteredMatrix n).trace ^ 2
      + (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
        * denseCenteredMatrix n).trace ^ 2
        ≤ (Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
          * denseAV n a *
          Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)).trace
          * (Matrix.transpose (denseCenteredMatrix n) * (denseAV n a)⁻¹
              * denseCenteredMatrix n).trace
        + (Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
          * denseAV n a *
          Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)).trace
          * (Matrix.transpose (denseCenteredMatrix n) * (denseAV n a)⁻¹
              * denseCenteredMatrix n).trace := add_le_add h1 h2
      _ = ((Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
          * denseAV n a *
          Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)).trace
        + (Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
          * denseAV n a *
          Matrix.diagonal
            (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)).trace)
          * (Matrix.transpose (denseCenteredMatrix n) * (denseAV n a)⁻¹
              * denseCenteredMatrix n).trace := by ring
      _ = (2 * denseL n * denseSVReal n a (denseDnorm n s))
          * (2 * denseL n * denseQV n a) := by rw [hdual, hE]
  rw [hnorm]
  have hsq : denseL n ^ 2
        * ((denseCenteredTrace n s).re ^ 2 + (denseCenteredTrace n s).im ^ 2)
      = (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).re)
        * denseCenteredMatrix n).trace ^ 2
      + (Matrix.diagonal
          (fun k : Fin (denseN n) => (1 / (s + (1/4:ℂ) + ((galerkinLam (denseL n) ((k : ℕ)) : ℝ) : ℂ))).im)
        * denseCenteredMatrix n).trace ^ 2 := by
    rw [← hre2, ← him2]
    ring
  have hL2 : (0:ℝ) < denseL n ^ 2 := pow_pos hL 2
  have hkey2 : denseL n ^ 2
        * ((denseCenteredTrace n s).re ^ 2 + (denseCenteredTrace n s).im ^ 2)
      ≤ denseL n ^ 2
        * (4 * denseQV n a * denseSVReal n a (denseDnorm n s)) := by
    rw [hsq]
    calc _ ≤ (2 * denseL n * denseSVReal n a (denseDnorm n s))
          * (2 * denseL n * denseQV n a) := hkey
      _ = denseL n ^ 2
          * (4 * denseQV n a * denseSVReal n a (denseDnorm n s)) := by ring
  exact le_of_mul_le_mul_left hkey2 hL2

#print axioms denseAV_transpose_eq
#print axioms denseAV_apply_diag
#print axioms denseDnorm_sq
#print axioms denseCenteredTrace_re
#print axioms denseCenteredTrace_im
#print axioms denseCenteredTrace_sq_le

end

end RHFormalization
