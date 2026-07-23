-- SENTINEL: FPTRACE-v1
import RHFormalization.AdmissibleFirstOrderDiagonal
import RHFormalization.AdmissibleFreeResolventOp
import RHFormalization.GalerkinOneLetterNormalizationLock
import Mathlib

/-!
# FreePairedTraceIdentity — the free paired trace, in the kernel

`Tr(R₀(s) · T) = Σ_m T_mm / (s + μ_m)` — SINGLE resolvent, diagonal in the
standard basis, so only the diagonal of `T` contributes. Proved by the same
route as the banked `trace_RD_V_RD` (freeResolventOpE_eq_diag →
toEuclideanLin_mul_eq → trace_toEuclideanLin → Matrix.diagonal_mul).

WHY THIS EXISTS: it makes the identification of the free paired transform a
compiled fact instead of a claim, so no future session can re-open "is the
free object the diagonal or the full T" — the kernel answers it.
Consequence: `galerkinSpikeTransform` (Σ T_mm/(s+1/4+μ_m)) IS this trace at
shift 1/4, hence `decodedOneLetterTransform` IS the density-normalized free
paired transform.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

open scoped BigOperators

variable {N : ℕ}

/-- Trace of `diagonal d * V`: only the diagonal of `V` contributes. -/
theorem diag_mul_trace (d : Fin N → ℂ) (V : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.diagonal d * V).trace = ∑ m, d m * V m m := by
  have h : ∀ m, (Matrix.diagonal d * V) m m = d m * V m m := by
    intro m
    rw [Matrix.diagonal_mul]
  first
    | (unfold Matrix.trace Matrix.diag
       exact Finset.sum_congr rfl fun m _ => h m)
    | (rw [Matrix.trace]
       exact Finset.sum_congr rfl fun m _ => h m)
    | simp [Matrix.trace, Matrix.diag, h]

/-- **THE FREE PAIRED TRACE IDENTITY**: `Tr(R₀(s)·T) = Σ_m T_mm/(s+μ_m)`. -/
theorem trace_RD_T (μ : Fin N → ℝ) (T : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * Matrix.toEuclideanLin T)
      = ∑ m, (s + ((μ m : ℝ) : ℂ))⁻¹ * T m m := by
  rw [freeResolventOpE_eq_diag, ← toEuclideanLin_mul_eq,
    trace_toEuclideanLin, diag_mul_trace]

/-- **Corollary — the spike transform IS the paired trace** (shift `1/4`,
real translation matrix `galerkinT`). -/
theorem galerkinSpikeTransform_eq_trace
    (μ : Fin N → ℝ) (L a : ℝ) (s : ℂ) :
    galerkinSpikeTransform (N := N) μ L a s
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
          (freeResolventOpE μ (s + (1/4 : ℂ))
            * Matrix.toEuclideanLin
                (fun i j => ((galerkinT (N := N) L a i j : ℝ) : ℂ))) := by
  rw [trace_RD_T]
  unfold galerkinSpikeTransform
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [one_div]
  ring

#print axioms diag_mul_trace
#print axioms trace_RD_T
#print axioms galerkinSpikeTransform_eq_trace

end RHFormalization
