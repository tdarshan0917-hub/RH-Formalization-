import RHFormalization.CosBumpIntegralBound
import RHFormalization.DirichletLaplacianEigenpairs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Brick 2, stone 4: the finite Galerkin matrices `K` and `V`
`K` diagonal (Weyl-growth eigenvalues `((m+1)π/L)²`), `V` the non-diagonal
symmetric matrix of sine-basis matrix elements. The genuine non-commuting pair.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real
open scoped Real BigOperators

variable {N : ℕ}

/-- Kinetic Galerkin matrix `K`: diagonal, entries `((m+1)π/L)²`. -/
noncomputable def galerkinK (L : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun m => (((m : ℝ) + 1) * Real.pi / L) ^ 2)

/-- RAW (unnormalized) potential Galerkin matrix: entry `(m,n) = V_{(m+1)(n+1)}`
in the unnormalized sine family `sin(kπx/L)` (‖φ‖² = L/2). This is the object
the position-space integral identities and entrywise bump bounds attach to. -/
noncomputable def galerkinVRaw (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun m n => VmatrixElement δ qs w L (m + 1) (n + 1)

theorem galerkinVRaw_apply (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : Fin N) :
    galerkinVRaw δ qs w L m n = VmatrixElement δ qs w L (m + 1) (n + 1) := rfl

/-- Potential Galerkin matrix `V` in the ORTHONORMAL Dirichlet sine basis
`√(2/L)·sin(kπx/L)` — the SAME convention as the free block `galerkinK`.
**NORMALIZATION FIX (Session 8):** the multiplication operator's matrix in
the orthonormal basis carries the factor `2/L`; without it the finite stage
mixed two basis conventions and the manuscript's density estimate is false. -/
noncomputable def galerkinV (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun m n => (2 / L) * galerkinVRaw (N := N) δ qs w L m n

/-- **Stone 4a**: `V` entry formula (orthonormal-normalized). -/
theorem galerkinV_apply (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : Fin N) :
    galerkinV δ qs w L m n = (2 / L) * VmatrixElement δ qs w L (m + 1) (n + 1) := rfl

/-- **Stone 4b**: `V` is symmetric. Entrywise, no integral unfolding. -/
theorem galerkinV_symm (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    (galerkinV (N := N) δ qs w L).IsSymm := by
  ext m n
  show galerkinV δ qs w L n m = galerkinV δ qs w L m n
  rw [galerkinV_apply, galerkinV_apply,
    VmatrixElement_symm δ qs w L (n + 1) (m + 1)]

/-- **Stone 4c**: Weyl growth `λ_m ≥ (π/L)²·(m+1)²`. -/
theorem galerkinK_diag_growth (L : ℝ) (hL : 0 < L) (m : Fin N) :
    (Real.pi / L) ^ 2 * ((m : ℝ) + 1) ^ 2 ≤ galerkinK (N := N) L m m := by
  have hentry : galerkinK (N := N) L m m = (((m : ℝ) + 1) * Real.pi / L) ^ 2 := by
    unfold galerkinK; rw [Matrix.diagonal_apply_eq]
  rw [hentry]
  have heq : (((m : ℝ) + 1) * Real.pi / L) ^ 2 = (Real.pi / L) ^ 2 * ((m : ℝ) + 1) ^ 2 := by
    rw [div_pow, div_pow, mul_pow]
    ring
  rw [heq]

#print axioms galerkinV_symm
#print axioms galerkinK_diag_growth
end
end RHFormalization
