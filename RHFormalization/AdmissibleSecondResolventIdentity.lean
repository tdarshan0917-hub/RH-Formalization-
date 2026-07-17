import RHFormalization.AdmissibleFreeResolventOp
import Mathlib.Tactic.NoncommRing

/-!
# RHFormalization.AdmissibleSecondResolventIdentity

**Front F-adm, brick 3b-ii.** The exact second-resolvent identities in the
End ring (`* = ∘ₗ`, `1 = id`), from the four banked inverse lemmas:

* I1: `R_H − R_D = −(R_D * V * R_H)`
* I2: `R_H − R_D = −(R_H * V * R_D)`
* I3 (once iterated, canonical orientation):
  `R_H − R_D = −(R_D * V * R_D) + R_D * V * R_H * V * R_D`
* trace-cycled residual: `Tr(R_D V R_H V R_D) = Tr(V R_H V (R_D*R_D))`.

Sign discipline: the first-order term carries the MINUS; it is NOT identified
with `B_stage` here. `FirstOrderWindow` / `SecondResolventResidual` and the
`FadmPrimeStage` connection are brick 3b-iii.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

variable {N : ℕ}

/-- The perturbed operator splits as free + perturbation (`toEuclideanLin` is
additive). -/
theorem perturbedOp_eq_freeOpE_add (μ : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℂ) :
    perturbedOp μ V = freeOpE μ + Matrix.toEuclideanLin V := by
  unfold perturbedOp perturbedMatrix freeOpE
  exact map_add _ _ _

/-- **I1 (left orientation)**: `R_H − R_D = −(R_D * V * R_H)`. -/
theorem resolvent_sub_eq_neg_RD_V_RH (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (hneF : ∀ i, s + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ i, s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0) :
    perturbedResolventOp μ hV s - freeResolventOpE μ s
      = -(freeResolventOpE μ s * Matrix.toEuclideanLin V
          * perturbedResolventOp μ hV s) := by
  set RD := freeResolventOpE μ s
  set RH := perturbedResolventOp μ hV s
  set Vop := Matrix.toEuclideanLin V
  set A : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    s • LinearMap.id + freeOpE μ with hA
  set Bop : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    s • LinearMap.id + perturbedOp μ V with hB
  have hAB : Bop = A + Vop := by
    rw [hB, hA, perturbedOp_eq_freeOpE_add μ V]
    abel
  have hRDA : RD * A = 1 := by
    have h := freeResolvent_left_inverse μ s hneF
    first
      | exact h
      | (rw [LinearMap.mul_eq_comp, LinearMap.one_eq_id]; exact h)
  have hBRH : Bop * RH = 1 := by
    have h := resolvent_right_inverse μ hV s hneP
    first
      | exact h
      | (rw [LinearMap.mul_eq_comp, LinearMap.one_eq_id]; exact h)
  calc RH - RD
      = (RD * A) * RH - RD * (Bop * RH) := by rw [hRDA, hBRH]; noncomm_ring
    _ = RD * A * RH - RD * ((A + Vop) * RH) := by rw [← hAB]
    _ = -(RD * Vop * RH) := by noncomm_ring

/-- **I2 (right orientation)**: `R_H − R_D = −(R_H * V * R_D)`. -/
theorem resolvent_sub_eq_neg_RH_V_RD (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (hneF : ∀ i, s + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ i, s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0) :
    perturbedResolventOp μ hV s - freeResolventOpE μ s
      = -(perturbedResolventOp μ hV s * Matrix.toEuclideanLin V
          * freeResolventOpE μ s) := by
  set RD := freeResolventOpE μ s
  set RH := perturbedResolventOp μ hV s
  set Vop := Matrix.toEuclideanLin V
  set A : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    s • LinearMap.id + freeOpE μ with hA
  set Bop : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    s • LinearMap.id + perturbedOp μ V with hB
  have hAB : Bop = A + Vop := by
    rw [hB, hA, perturbedOp_eq_freeOpE_add μ V]
    abel
  have hARD : A * RD = 1 := by
    have h := freeResolvent_right_inverse μ s hneF
    first
      | exact h
      | (rw [LinearMap.mul_eq_comp, LinearMap.one_eq_id]; exact h)
  have hRHB : RH * Bop = 1 := by
    have h := resolvent_left_inverse μ hV s hneP
    first
      | exact h
      | (rw [LinearMap.mul_eq_comp, LinearMap.one_eq_id]; exact h)
  calc RH - RD
      = RH * (A * RD) - (RH * Bop) * RD := by rw [hARD, hRHB]; noncomm_ring
    _ = RH * (A * RD) - (RH * (A + Vop)) * RD := by rw [← hAB]
    _ = -(RH * Vop * RD) := by noncomm_ring

/-- **I3, once-iterated canonical form**:
`R_H − R_D = −(R_D V R_D) + R_D V R_H V R_D`. First-order term carries the
minus sign; residual in the manuscript orientation. -/
theorem resolvent_sub_eq_first_plus_second (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ)
    (hneF : ∀ i, s + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ i, s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0) :
    perturbedResolventOp μ hV s - freeResolventOpE μ s
      = -(freeResolventOpE μ s * Matrix.toEuclideanLin V
            * freeResolventOpE μ s)
        + freeResolventOpE μ s * Matrix.toEuclideanLin V
            * perturbedResolventOp μ hV s * Matrix.toEuclideanLin V
            * freeResolventOpE μ s := by
  set RD := freeResolventOpE μ s
  set RH := perturbedResolventOp μ hV s
  set Vop := Matrix.toEuclideanLin V
  have hI1 := resolvent_sub_eq_neg_RD_V_RH μ hV s hneF hneP
  have hI2 := resolvent_sub_eq_neg_RH_V_RD μ hV s hneF hneP
  have key : RD - RH = RH * Vop * RD := by
    rw [← neg_sub RH RD, hI2, neg_neg]
  calc RH - RD
      = -(RD * Vop * RH) := hI1
    _ = -(RD * Vop * RD) + RD * Vop * (RD - RH) := by noncomm_ring
    _ = -(RD * Vop * RD) + RD * Vop * (RH * Vop * RD) := by rw [key]
    _ = -(RD * Vop * RD) + RD * Vop * RH * Vop * RD := by noncomm_ring

/-- **Trace-cycled residual** (banked now, per protocol): the residual trace
in V-leading form. -/
theorem residual_trace_cycle (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (s : ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * Matrix.toEuclideanLin V
          * perturbedResolventOp μ hV s * Matrix.toEuclideanLin V
          * freeResolventOpE μ s)
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
          (Matrix.toEuclideanLin V * perturbedResolventOp μ hV s
            * Matrix.toEuclideanLin V
            * (freeResolventOpE μ s * freeResolventOpE μ s)) := by
  set RD := freeResolventOpE μ s
  set RH := perturbedResolventOp μ hV s
  set Vop := Matrix.toEuclideanLin V
  have h1 : RD * Vop * RH * Vop * RD = RD * (Vop * RH * Vop * RD) := by
    noncomm_ring
  have h2 : Vop * RH * Vop * RD * RD = Vop * RH * Vop * (RD * RD) := by
    noncomm_ring
  rw [h1, LinearMap.trace_mul_comm, ← h2]
  all_goals (first
    | rfl
    | (congr 1; noncomm_ring)
    | noncomm_ring)

#print axioms perturbedOp_eq_freeOpE_add
#print axioms resolvent_sub_eq_neg_RD_V_RH
#print axioms resolvent_sub_eq_neg_RH_V_RD
#print axioms resolvent_sub_eq_first_plus_second
#print axioms residual_trace_cycle

end

end RHFormalization
