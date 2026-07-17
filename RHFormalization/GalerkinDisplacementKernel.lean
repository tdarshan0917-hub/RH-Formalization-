import RHFormalization.PrimePotentialPosition
import RHFormalization.GalerkinFreeHeatDiagonal
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
# Galerkin displacement kernel — BRICK 1 of the canonical-F route

ROUTE CARD
1. Target: the canonical displacement/commutator transform (manuscript
   D.CANONICAL-FUNCTIONAL / D.BRIDGE-II′ / D.K0′). This file supplies the
   FINITE objects: compressed translation matrix, free spike kernel
   g_gal(t,a) = Tr(exp(−tK)·T_a), one-letter spike package.
2. The plain heat trace is displacement-blind (numerically verified flat to
   8 digits); the arithmetic enters ONLY through the T_a pairing. This file
   is the first brick of the F-slot that replaces the auxiliary
   multiplication-bump transform.
3. Consumer: T_a-paired Duhamel (Brick 2), shifted-Laplace bridge to
   B_stage − BcorrWin (Brick 3), canonical stage F-slot (Brick 4).
4. Numeric validation: Tr(e^{−tK}T_a) matches G_t(a)·(box−|a|)₊ to ~1% at
   N=500, converging with N — the D.K0′ Galerkin analogue is real.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The Dirichlet eigenfunction windowed to the physical box `[0, L]`:
zero-extended outside, so that compressed translation is well-defined. -/
def dirichletEigenfunWindowed (m : ℕ) (L : ℝ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) L then dirichletEigenfun m L x else 0

/-- **Compressed translation matrix element** on the Dirichlet sine basis:
`T_a[m,n] = ∫₀ᴸ φₘ(x)·φₙ(x−a)·1_{[0,L]}(x−a) dx` (bare, un-normalized —
mirrors `VmatrixElement`'s convention). -/
def TmatrixElement (L a : ℝ) (m n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..L,
    dirichletEigenfun m L x * dirichletEigenfunWindowed n L (x - a)

/-- **The compressed translation matrix** in the orthonormal-normalized
Galerkin frame (same `2/L` convention as `galerkinV`). -/
def galerkinT (L a : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun m n => (2 / L) * TmatrixElement L a ((m : ℕ) + 1) ((n : ℕ) + 1)

/-- **The free Galerkin spike kernel** `g_gal(t,a) = Tr(exp(−tK)·T_a)` —
the finite-dimensional analogue of the manuscript's
`g_{t,L}(a) = Tr(S_t A_L T_a)` (D.K0′). -/
def galerkinSpikeKernel (L t a : ℝ) : ℝ :=
  (NormedSpace.exp (t • (-(galerkinK (N := N) L))) * galerkinT (N := N) L a).trace

/-- **The one-letter spike package (raw)**: `Σ_q w(q)·g_gal(t, log q)` —
the finite analogue of `P_{L,R}(t)` in Theorem D.ONE-STEP′′. Density
normalization is applied at stage-install time, matching the F-slot
convention. -/
def galerkinOneLetterPackageRaw (qs : Finset ℕ) (w : ℕ → ℝ) (L t : ℝ) : ℝ :=
  ∑ q ∈ qs, w q * galerkinSpikeKernel (N := N) L t (Real.log q)

/-- Unfold lemma for the package. -/
theorem galerkinOneLetterPackageRaw_eq (qs : Finset ℕ) (w : ℕ → ℝ) (L t : ℝ) :
    galerkinOneLetterPackageRaw (N := N) qs w L t
      = ∑ q ∈ qs, w q * galerkinSpikeKernel (N := N) L t (Real.log q) := rfl

/-- Trace of (diagonal · M) is the heat-weighted diagonal sum. -/
theorem trace_diagonal_mul (d : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    (Matrix.diagonal d * M).trace = ∑ m : Fin N, d m * M m m := by
  first
    | simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        ite_mul, zero_mul, Finset.sum_ite_eq]
    | simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal,
        Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq]

/-- **The spike kernel is the heat-weighted diagonal of `T_a`** — the exact
identity the numeric probe computed (`Σ_m e^{−tμ_m}·(T_a)_{mm}`). -/
theorem galerkinSpikeKernel_eq_sum (L t a : ℝ) :
    galerkinSpikeKernel (N := N) L t a
      = ∑ m : Fin N, heatWeight (N := N) L t m * galerkinT (N := N) L a m m := by
  unfold galerkinSpikeKernel
  rw [galerkinFreeHeat_eq_diagonal, trace_diagonal_mul]

/-- **Far-window vanishing**: displacements beyond the box kill the
compressed translation entirely. -/
theorem galerkinT_eq_zero_of_gt (L a : ℝ) (hL : 0 < L) (ha : L < a)
    (m n : Fin N) :
    galerkinT (N := N) L a m n = 0 := by
  unfold galerkinT TmatrixElement
  have h : Set.EqOn
      (fun x => dirichletEigenfun ((m : ℕ) + 1) L x *
        dirichletEigenfunWindowed ((n : ℕ) + 1) L (x - a))
      (fun _ => (0 : ℝ)) (Set.uIcc (0 : ℝ) L) := by
    intro x hx
    rw [Set.uIcc_of_le hL.le] at hx
    have hxa : (x - a) ∉ Set.Icc (0 : ℝ) L := by
      rw [Set.mem_Icc]
      push_neg
      intro h0
      exfalso
      linarith [hx.2]
    simp [dirichletEigenfunWindowed, hxa]
  first
    | (rw [intervalIntegral.integral_congr h]; simp)
    | (have hz := intervalIntegral.integral_congr h
       rw [hz]; simp)
    | simp [intervalIntegral.integral_congr h]

/-- Vanishing propagates to the spike kernel. -/
theorem galerkinSpikeKernel_eq_zero_of_gt (L t a : ℝ) (hL : 0 < L)
    (ha : L < a) :
    galerkinSpikeKernel (N := N) L t a = 0 := by
  rw [galerkinSpikeKernel_eq_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [galerkinT_eq_zero_of_gt (N := N) L a hL ha m m, mul_zero]

#print axioms galerkinT
#print axioms galerkinSpikeKernel
#print axioms galerkinOneLetterPackageRaw
#print axioms trace_diagonal_mul
#print axioms galerkinSpikeKernel_eq_sum
#print axioms galerkinT_eq_zero_of_gt
#print axioms galerkinSpikeKernel_eq_zero_of_gt

end

end RHFormalization
