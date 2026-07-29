-- SENTINEL: coupling-deriv-v1
import RHFormalization.AdmissibleFirstOrderDiagonal
import Mathlib

/-!
# CouplingDerivativeIdentity — finite-N spectral-derivative identity

  `d/ds Tr(V · R_D(s)) = - Tr(R_D(s) · V · R_D(s))`.

Consumes only banked bricks from `AdmissibleFirstOrderDiagonal`:
`freeResolventOpE_eq_diag`, `toEuclideanLin_mul_eq`, `trace_toEuclideanLin`,
`trace_RD_V_RD`.  New step: `diag_mul_trace`, one-sided mirror of the banked
`diag_conj_trace`.

ROUTE CARD
1. `diag_mul_trace`   : `Tr(V · diagonal d) = ∑ₘ Vₘₘ dₘ`.
2. `trace_V_RD`       : `Tr(V · R_D(s)) = ∑ₘ Vₘₘ (s+μₘ)⁻¹`.
3. `inv_shift_hasDerivAt` : `d/dz (z+c)⁻¹ = -((s+c)⁻¹)²`.
4. `trace_V_RD_hasDerivAt` : THE IDENTITY, termwise `HasDerivAt.sum`.
5. `density_mul_trace_V_RD_hasDerivAt_FirstOrderWindow` :
   `FirstOrderWindow = density * (spectral derivative)`.

NOTE: differentiates in the SPECTRAL variable `s`, NOT in a prime-well coupling
`lambda_q`.  The channelwise coupling derivative (translation `T_log q` paired
against a single well `V_q`) is a separate brick, via
`resolvent_sub_eq_first_plus_second`.  No bound asserted; exact identity only.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators

variable {N : ℕ}

/-- `Tr(V · diagonal d) = ∑ₘ Vₘₘ dₘ`. Mirror of banked `diag_conj_trace`. -/
theorem diag_mul_trace (d : Fin N → ℂ) (V : Matrix (Fin N) (Fin N) ℂ) :
    (V * Matrix.diagonal d).trace = ∑ m, V m m * d m := by
  have h : ∀ m, (V * Matrix.diagonal d) m m = V m m * d m := by
    intro m
    rw [Matrix.mul_diagonal]
  first
    | (unfold Matrix.trace Matrix.diag
       exact Finset.sum_congr rfl fun m _ => h m)
    | (rw [Matrix.trace]
       exact Finset.sum_congr rfl fun m _ => h m)
    | simp [Matrix.trace, Matrix.diag, h]

/-- **Single-resolvent trace form**: `Tr(V · R_D(s)) = ∑ₘ Vₘₘ (s+μₘ)⁻¹`. -/
theorem trace_V_RD (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (Matrix.toEuclideanLin V * freeResolventOpE μ s)
      = ∑ m, V m m * (s + ((μ m : ℝ) : ℂ))⁻¹ := by
  rw [freeResolventOpE_eq_diag, ← toEuclideanLin_mul_eq, trace_toEuclideanLin,
    diag_mul_trace]

/-- Termwise derivative of the shifted inverse. -/
theorem inv_shift_hasDerivAt (c : ℂ) {s : ℂ} (hne : s + c ≠ 0) :
    HasDerivAt (fun z : ℂ => (z + c)⁻¹) (-(((s + c)⁻¹) ^ 2)) s := by
  have hbase : HasDerivAt (fun z : ℂ => z + c) 1 s :=
    (hasDerivAt_id s).add_const c
  have h := hbase.inv hne
  convert h using 1
  field_simp

/-- **THE IDENTITY**: `d/ds Tr(V · R_D(s)) = - Tr(R_D(s) · V · R_D(s))`. -/
theorem trace_V_RD_hasDerivAt (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ)
    (s : ℂ) (hne : ∀ m, s + ((μ m : ℝ) : ℂ) ≠ 0) :
    HasDerivAt
      (fun z : ℂ => LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (Matrix.toEuclideanLin V * freeResolventOpE μ z))
      (-(LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * Matrix.toEuclideanLin V
          * freeResolventOpE μ s))) s := by
  have hfun : (fun z : ℂ => LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
      (Matrix.toEuclideanLin V * freeResolventOpE μ z))
      = fun z : ℂ => ∑ m, V m m * (z + ((μ m : ℝ) : ℂ))⁻¹ := by
    funext z
    exact trace_V_RD μ V z
  rw [hfun, trace_RD_V_RD]
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin N)),
      HasDerivAt (fun z : ℂ => V m m * (z + ((μ m : ℝ) : ℂ))⁻¹)
        (V m m * (-(((s + ((μ m : ℝ) : ℂ))⁻¹) ^ 2))) s := by
    intro m _
    exact (inv_shift_hasDerivAt ((μ m : ℝ) : ℂ) (hne m)).const_mul _
  have hsum : HasDerivAt (fun z : ℂ => ∑ m, V m m * (z + ((μ m : ℝ) : ℂ))⁻¹)
      (∑ m : Fin N, V m m * (-(((s + ((μ m : ℝ) : ℂ))⁻¹) ^ 2))) s := by
    first
      | exact HasDerivAt.sum hterm
      | exact HasDerivAt.fun_sum hterm
      | exact Finset.hasDerivAt_sum _ hterm
  have hneg : -(∑ m : Fin N, V m m * ((s + ((μ m : ℝ) : ℂ))⁻¹) ^ 2)
      = ∑ m : Fin N, V m m * (-(((s + ((μ m : ℝ) : ℂ))⁻¹) ^ 2)) := by
    first
      | (rw [← Finset.sum_neg_distrib]
         exact Finset.sum_congr rfl fun m _ => by ring)
      | (rw [← Finset.neg_sum]
         exact Finset.sum_congr rfl fun m _ => by ring)
      | (simp only [mul_neg, Finset.sum_neg_distrib])
      | (simp only [mul_neg]; rw [Finset.sum_neg_distrib])
  rw [hneg]
  exact hsum

/-- **`FirstOrderWindow = density * (spectral derivative)`**, at `s+SupVConst`. -/
theorem density_mul_trace_V_RD_hasDerivAt_FirstOrderWindow
    (n : ℕ) (s : ℂ)
    (hne : ∀ m, (s + (SupVConst : ℂ))
        + ((galerkinFreeMu (admN n) (admL n) m : ℝ) : ℂ) ≠ 0) :
    HasDerivAt
      (fun z : ℂ =>
        admDensityC n *
          LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
            (Matrix.toEuclideanLin
                (galerkinVC (N := admN n) 1
                  (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                  (admL n))
              * freeResolventOpE (galerkinFreeMu (admN n) (admL n)) z))
      (FirstOrderWindow n s)
      (s + (SupVConst : ℂ)) := by
  have hbase := trace_V_RD_hasDerivAt
      (galerkinFreeMu (admN n) (admL n))
      (galerkinVC (N := admN n) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
      (s + (SupVConst : ℂ)) hne
  have h : HasDerivAt
      (fun z : ℂ =>
        admDensityC n *
          LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
            (Matrix.toEuclideanLin
                (galerkinVC (N := admN n) 1
                  (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                  (admL n))
              * freeResolventOpE (galerkinFreeMu (admN n) (admL n)) z))
      (admDensityC n *
        (-(LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
          (freeResolventOpE (galerkinFreeMu (admN n) (admL n))
              (s + (SupVConst : ℂ))
            * Matrix.toEuclideanLin
                (galerkinVC (N := admN n) 1
                  (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                  (admL n))
            * freeResolventOpE (galerkinFreeMu (admN n) (admL n))
                (s + (SupVConst : ℂ))))))
      (s + (SupVConst : ℂ)) := by
    first
      | exact hbase.const_mul (admDensityC n)
      | exact HasDerivAt.const_mul (admDensityC n) hbase
      | exact (hasDerivAt_const _ (admDensityC n)).mul hbase
  convert h using 1
  rw [FirstOrderWindow_eq_diag_sum n s, ← trace_RD_V_RD]
  ring

#print axioms diag_mul_trace
#print axioms trace_V_RD
#print axioms inv_shift_hasDerivAt
#print axioms trace_V_RD_hasDerivAt
#print axioms density_mul_trace_V_RD_hasDerivAt_FirstOrderWindow

end

end RHFormalization
