-- SENTINEL: PAIREDRES-v5
import RHFormalization.AdmissibleSecondResolventIdentity
import RHFormalization.AdmissibleResolventBridge
import RHFormalization.AdmissibleFreeResolventOp
import RHFormalization.AdmissibleFirstOrderDiagonal
import RHFormalization.AdaptivePairedFStage
import Mathlib

/-!
# AdaptivePairedResolventSplit — B2: the T_a-PAIRED resolvent split

Transform-level form of B1's Duhamel split, via the banked second-resolvent
identity `resolvent_sub_eq_neg_RD_V_RH` paired against T. Matrix-* (LinearMap
composition) algebra, NO integrals.

  RH − RD = −(RD·V·RH)         [banked, needs s+μ≠0, s+μ_pert≠0]
  ⟹ RH·T = RD·T − (RD·V·RH)·T
  ⟹ Tr(RH·T) = Tr(RD·T) − Tr(RD·V·RH·T)

Tr(RH·T) = full paired-F transform (measured 2·pairedF/B → 0.95).
Tr(RD·T) = free paired transform. Tr(RD·V·RH·T) = the REMAINDER, B3's
target (measured N-free, ceiling 8.35e-4). Banks the split ONLY.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- **The T_a-paired second-resolvent split** (trace level). -/
theorem paired_resolvent_split
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (s : ℂ)
    (hneF : ∀ i, s + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ i, s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0)
    (T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (perturbedResolventOp μ hV s * T)
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
          (freeResolventOpE μ s * T)
        - LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
            (freeResolventOpE μ s * Matrix.toEuclideanLin V
              * perturbedResolventOp μ hV s * T) := by
  have hid := resolvent_sub_eq_neg_RD_V_RH (N := N) μ hV s hneF hneP
  -- hid : RH - RD = -(RD * V * RH);  multiply on the right by T
  have hmul := congrArg (fun M : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)
      => M * T) hid
  simp only [sub_mul, neg_mul] at hmul
  -- hmul : RH * T - RD * T = -(RD * V * RH * T)
  have htr := congrArg (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))) hmul
  rw [map_sub, map_neg] at htr
  first
    | linear_combination htr
    | (rw [sub_eq_iff_eq_add] at htr; rw [htr]; ring)
    | (rw [eq_sub_iff_add_eq]; linear_combination htr)
    | (rw [← sub_eq_iff_eq_add'] ; linear_combination htr)

#print axioms paired_resolvent_split

end

end RHFormalization
