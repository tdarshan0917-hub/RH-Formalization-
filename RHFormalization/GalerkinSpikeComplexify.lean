import RHFormalization.PairedTraceExpBridge
import RHFormalization.GalerkinSpikeDuhamel
import Mathlib

/-!
# Real→complex spike kernel bridge — BRICK 8b of the canonical-F route
SENTINEL: spike-complexify-v2

ROUTE CARD
1. FINAL WIRING BRICK: the real perturbed spike kernel of Brick 2 equals the
   complex paired heat trace of 8a-iv, hence the eigen-sum
   `pairedPerturbedHeatTrace` and (via Brick 7) the Ω-holomorphic transform.
2. v2: the exp-argument cast is a standalone matrix-level lemma
   (`matC_scaled`, proved by rewrite chain matC_smul → map_neg → map_add →
   structural matches), so the main theorem is pure `rw` — no ext/ring.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Entrywise `ofReal` as a matrix ring hom. -/
def matC : Matrix (Fin N) (Fin N) ℝ →+* Matrix (Fin N) (Fin N) ℂ :=
  RingHom.mapMatrix Complex.ofRealHom

theorem matC_apply (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matC (N := N) A i j = ((A i j : ℝ) : ℂ) := rfl

/-- Entrywise cast is continuous on matrix algebras. -/
theorem matC_continuous : Continuous (matC (N := N)) := by
  first
    | (apply continuous_matrix
       intro i j
       exact Complex.continuous_ofReal.comp (continuous_apply_apply i j))
    | (apply continuous_matrix
       intro i j
       first
         | exact Complex.continuous_ofReal.comp
             ((continuous_apply j).comp (continuous_apply i))
         | continuity)
    | continuity

/-- Cast commutes with the matrix exponential. -/
theorem matC_exp (A : Matrix (Fin N) (Fin N) ℝ) :
    matC (N := N) (NormedSpace.exp A) = NormedSpace.exp (matC (N := N) A) :=
  NormedSpace.map_exp (matC (N := N)) matC_continuous A

/-- Cast commutes with trace. -/
theorem matC_trace (A : Matrix (Fin N) (Fin N) ℝ) :
    ((A.trace : ℝ) : ℂ) = (matC (N := N) A).trace := by
  unfold Matrix.trace
  push_cast
  rfl

/-- Cast commutes with real scalar action. -/
theorem matC_smul (t : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    matC (N := N) (t • A) = ((t : ℝ) : ℂ) • matC (N := N) A := by
  ext i j
  first
    | (simp only [matC_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_mul])
    | (simp [matC, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.smul_apply, smul_eq_mul]
       push_cast
       ring)
    | (show ((t • A) i j : ℂ) = (t : ℂ) * matC (N := N) A i j
       rw [matC_apply]
       push_cast [Matrix.smul_apply, smul_eq_mul]
       ring)

/-- Structural match 1: cast kinetic matrix = free diagonal at the genuine
spectrum. -/
theorem matC_galerkinK (L : ℝ) :
    matC (N := N) (galerkinK (N := N) L) = freeDiag (galerkinFreeMu N L) := by
  unfold galerkinK freeDiag galerkinFreeMu
  ext i j
  by_cases h : i = j
  · subst h
    simp [matC_apply, Matrix.diagonal_apply_eq]
  · simp [matC_apply, Matrix.diagonal_apply_ne _ h]

/-- Structural match 2: cast bump matrix = `galerkinVC`. -/
theorem matC_galerkinV (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    matC (N := N) (galerkinV (N := N) δ qs w L)
      = galerkinVC (N := N) δ qs w L := by
  ext i j
  rfl

/-- Structural match 3: cast translation matrix = `galerkinTC`. -/
theorem matC_galerkinT (L a : ℝ) :
    matC (N := N) (galerkinT (N := N) L a) = galerkinTC (N := N) L a := by
  ext i j
  rfl

/-- **The exp-argument cast, at matrix level**: the cast of `t • (−(K+V))`
is `(−t:ℂ) • perturbedMatrix(galerkinFreeMu, galerkinVC)`. -/
theorem matC_scaled (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t : ℝ) :
    matC (N := N) (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
      = (-(t : ℂ)) • perturbedMatrix (galerkinFreeMu N L)
          (galerkinVC (N := N) δ qs w L) := by
  rw [matC_smul, map_neg, map_add,
    matC_galerkinK (N := N) L, matC_galerkinV (N := N) δ qs w L]
  unfold perturbedMatrix
  rw [smul_neg, ← neg_smul]

/-- **BRICK 8b — THE COMPLEXIFICATION BRIDGE.** -/
theorem galerkinSpikeKernelPerturbed_complexify
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t a : ℝ) :
    ((galerkinSpikeKernelPerturbed (N := N) δ qs w L t a : ℝ) : ℂ)
      = ((NormedSpace.exp ((-(t : ℂ)) •
            perturbedMatrix (galerkinFreeMu N L)
              (galerkinVC (N := N) δ qs w L)))
          * galerkinTC (N := N) L a).trace := by
  unfold galerkinSpikeKernelPerturbed
  rw [matC_trace, map_mul, matC_exp, matC_galerkinT, matC_scaled]

/-- **The full chain**: real spike kernel = eigen-sum paired heat trace. -/
theorem galerkinSpikeKernelPerturbed_eq_pairedHeatTrace
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t a : ℝ) :
    ((galerkinSpikeKernelPerturbed (N := N) δ qs w L t a : ℝ) : ℂ)
      = pairedPerturbedHeatTrace (N := N) (galerkinFreeMu N L)
          (galerkinVC_isHermitian (N := N) δ qs w L)
          (galerkinTC (N := N) L a) t := by
  rw [galerkinSpikeKernelPerturbed_complexify,
    trace_exp_mul_eq_pairedHeatTrace]

#print axioms matC_exp
#print axioms matC_smul
#print axioms matC_scaled
#print axioms galerkinSpikeKernelPerturbed_complexify
#print axioms galerkinSpikeKernelPerturbed_eq_pairedHeatTrace

end

end RHFormalization
