import RHFormalization.ShiftedLaplaceBranchIdentity
import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.DenseCenteredObservable
import Mathlib

/-!
# U4WitnessTransfer — experimental, downstream, isolated

Continuum resonance normalization for the U4 zero-visibility experiment.
For `w` with `0 < Re w` and `s = w² − 1/4`: the principal branch gives
`√(s + 1/4) = w` (via the banked `sqrt_polePoint_eq_of_re_gt` at `ρ = w + 1/2`),
the shifted-Laplace kernel specializes to `e^{−uw}/(2w)`, and the witness mode
`e^{uw}` resonates: `∫₀^R e^{uw}·K(u,s) du = R/(2w)`.

This module makes NO RH claim, touches NO B(i) file, and formalizes NO
arithmetic/Stieltjes input. The finite Galerkin response is defined only.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The witness spectral point `s = w² − 1/4`. -/
def witnessS (w : ℂ) : ℂ := w ^ 2 - (1/4 : ℂ)

/-- `witnessS w` is the pole point of `ρ = w + 1/2`. -/
theorem witnessS_eq_polePoint (w : ℂ) :
    witnessS w = polePoint (w + (1/2 : ℂ)) := by
  unfold witnessS polePoint
  ring

/-- **Branch lock**: for `0 < Re w`, `√(witnessS w + 1/4) = w`. -/
theorem sqrt_witnessS_add_quarter {w : ℂ} (hw : 0 < w.re) :
    Complex.sqrt (witnessS w + (1/4 : ℂ)) = w := by
  rw [witnessS_eq_polePoint]
  have h : (1/2 : ℝ) < (w + (1/2 : ℂ)).re := by
    simp only [Complex.add_re]
    have h2 : ((1 : ℂ) / 2).re = (1/2 : ℝ) := by norm_num
    rw [h2]
    linarith
  rw [sqrt_polePoint_eq_of_re_gt h]
  ring

/-- **Kernel specialization** at the witness point. -/
theorem shiftedLaplaceHeatKernelC_witness {w : ℂ} (hw : 0 < w.re) (u : ℝ) :
    shiftedLaplaceHeatKernelC u (witnessS w)
      = (1 : ℂ) / (2 * w) * Complex.exp (-(u : ℂ) * w) := by
  show (1 : ℂ) / (2 * Complex.sqrt (witnessS w + (1 / 4 : ℂ))) *
      Complex.exp (-(u : ℂ) * Complex.sqrt (witnessS w + (1 / 4 : ℂ))) = _
  rw [sqrt_witnessS_add_quarter hw]

/-- Continuum witness response `∫₀^R e^{uw}·K(u, witnessS w) du`. -/
def continuumWitnessResponse (w : ℂ) (R : ℝ) : ℂ :=
  ∫ u in (0:ℝ)..R,
    Complex.exp ((u : ℂ) * w) * shiftedLaplaceHeatKernelC u (witnessS w)

/-- **Resonance**: at exact tuning the witness response is `R/(2w)` —
frequency and growth cancel in the kernel, leaving linear accumulation. -/
theorem continuumWitnessResponse_eq {w : ℂ} (hw : 0 < w.re) (R : ℝ) :
    continuumWitnessResponse w R = (R : ℂ) / (2 * w) := by
  unfold continuumWitnessResponse
  have hpt : ∀ u : ℝ,
      Complex.exp ((u : ℂ) * w) * shiftedLaplaceHeatKernelC u (witnessS w)
        = (1 : ℂ) / (2 * w) := by
    intro u
    rw [shiftedLaplaceHeatKernelC_witness hw u]
    have hexp : Complex.exp ((u : ℂ) * w) * Complex.exp (-(u : ℂ) * w) = 1 := by
      rw [← Complex.exp_add]
      have h0 : (u : ℂ) * w + -(u : ℂ) * w = 0 := by ring
      rw [h0, Complex.exp_zero]
    calc Complex.exp ((u : ℂ) * w) * ((1 : ℂ) / (2 * w) * Complex.exp (-(u : ℂ) * w))
        = (1 : ℂ) / (2 * w) *
            (Complex.exp ((u : ℂ) * w) * Complex.exp (-(u : ℂ) * w)) := by ring
      _ = (1 : ℂ) / (2 * w) := by rw [hexp, mul_one]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one_div]

/-- Finite Galerkin witness response over the actual dense kernel.
DEFINITION ONLY — no convergence claim. -/
def finiteWitnessResponse (n : ℕ) (w : ℂ) (R : ℝ) : ℂ :=
  ∫ u in (0:ℝ)..R,
    Complex.exp ((u : ℂ) * w) * denseKernelN n u (witnessS w)

/-- Transfer ratio `T_n(w,R)`. DEFINITION ONLY. -/
def witnessTransfer (n : ℕ) (w : ℂ) (R : ℝ) : ℂ :=
  finiteWitnessResponse n w R / continuumWitnessResponse w R


/-! ## Tier A — exact signed finite-response expansion (no limits, no norms) -/

/-- Schedule-free finite Galerkin witness response at box `L`, resolution `N`,
observation time `R`. -/
def galerkinWitnessResponse (N : ℕ) (L R : ℝ) (w : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..R,
    Complex.exp ((u : ℂ) * w) *
      (((1 / L : ℝ) : ℂ) *
        galerkinSpikeTransform (N := N) (fun m => galerkinLam L (m : ℕ)) L u (witnessS w))

/-- The dense instance is the schedule-free object at the dense schedule. -/
theorem finiteWitnessResponse_eq_galerkin (n : ℕ) (w : ℂ) (R : ℝ) :
    finiteWitnessResponse n w R
      = galerkinWitnessResponse (denseN n) (denseL n) R w := rfl

/-- Exact diagonal of the compressed translation matrix for `0 ≤ u ≤ L`:
`(1 − u/L)·cos(κ_m u) + sin(κ_m u)/((m+1)π)`, `κ_m = (m+1)π/L`. -/
theorem galerkinT_diag_closed {N : ℕ} (L u : ℝ) (hL : 0 < L)
    (hu0 : 0 ≤ u) (huL : u ≤ L) (m : Fin N) :
    galerkinT (N := N) L u m m
      = (1 - u / L) * Real.cos (((m : ℕ) + 1 : ℝ) * Real.pi * u / L)
        + Real.sin (((m : ℕ) + 1 : ℝ) * Real.pi * u / L)
            / ((((m : ℕ) + 1 : ℝ)) * Real.pi) := by
  unfold galerkinT
  rw [TmatrixElement_diag_eval L u hL hu0 huL ((m : ℕ) + 1) (Nat.succ_ne_zero _)]
  push_cast
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk : ((m : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Witness denominator: `witnessS w + 1/4 + λ = w² + λ`. -/
theorem witnessS_denom (w : ℂ) (lam : ℝ) :
    witnessS w + (1/4 : ℂ) + ((lam : ℝ) : ℂ) = w ^ 2 + (lam : ℂ) := by
  unfold witnessS
  ring

/-- **Tier A — exact signed expansion.** For `0 < L`, `0 ≤ R ≤ L`, the finite
witness response is the mode sum
`(1/L)·Σ_{m<N} (w² + λ_m)⁻¹ · ∫₀^R e^{uw}·[(1−u/L)cos(κ_m u) + sin(κ_m u)/((m+1)π)] du`.
Complex and signed throughout; no absolute values enter. -/
theorem galerkinWitnessResponse_expand (N : ℕ) (L R : ℝ) (w : ℂ)
    (hL : 0 < L) (hR0 : 0 ≤ R) (hRL : R ≤ L) :
    galerkinWitnessResponse N L R w
      = ((1 / L : ℝ) : ℂ) *
        ∑ m : Fin N,
          (1 / (w ^ 2 + ((galerkinLam L (m : ℕ) : ℝ) : ℂ))) *
            ∫ u in (0:ℝ)..R,
              Complex.exp ((u : ℂ) * w) *
                (((1 - u / L) * Real.cos (((m : ℕ) + 1 : ℝ) * Real.pi * u / L)
                  + Real.sin (((m : ℕ) + 1 : ℝ) * Real.pi * u / L)
                      / ((((m : ℕ) + 1 : ℝ)) * Real.pi) : ℝ) : ℂ) := by
  unfold galerkinWitnessResponse
  have hpt : Set.EqOn
      (fun u : ℝ => Complex.exp ((u : ℂ) * w) *
        (((1 / L : ℝ) : ℂ) *
          galerkinSpikeTransform (N := N) (fun m => galerkinLam L (m : ℕ)) L u (witnessS w)))
      (fun u : ℝ => ((1 / L : ℝ) : ℂ) *
        ∑ m : Fin N,
          (1 / (w ^ 2 + ((galerkinLam L (m : ℕ) : ℝ) : ℂ))) *
            (Complex.exp ((u : ℂ) * w) *
              (((1 - u / L) * Real.cos (((m : ℕ) + 1 : ℝ) * Real.pi * u / L)
                + Real.sin (((m : ℕ) + 1 : ℝ) * Real.pi * u / L)
                    / ((((m : ℕ) + 1 : ℝ)) * Real.pi) : ℝ) : ℂ)))
      (Set.uIcc 0 R) := by
    intro u hu
    rw [Set.uIcc_of_le hR0] at hu
    have hu0 : 0 ≤ u := hu.1
    have huL : u ≤ L := le_trans hu.2 hRL
    beta_reduce
    unfold galerkinSpikeTransform
    beta_reduce
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [galerkinT_diag_closed L u hL hu0 huL m, witnessS_denom]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [intervalIntegral.integral_const_mul]
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop


#print axioms witnessS_eq_polePoint
#print axioms sqrt_witnessS_add_quarter
#print axioms shiftedLaplaceHeatKernelC_witness
#print axioms continuumWitnessResponse_eq
#print axioms finiteWitnessResponse_eq_galerkin
#print axioms galerkinT_diag_closed
#print axioms witnessS_denom
#print axioms galerkinWitnessResponse_expand

end

end RHFormalization
