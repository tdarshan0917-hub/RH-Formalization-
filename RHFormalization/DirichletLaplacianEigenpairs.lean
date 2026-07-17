import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# RHFormalization.DirichletLaplacianEigenpairs
**Foundation brick 1.** Dirichlet eigenfunctions `sin(nπx/L)` of `−d²/dx²` on `[0,L]`:
eigenvalue equation `−φ'' = (nπ/L)²φ` and Dirichlet BC `φ(0)=φ(L)=0`. Pure calculus.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Real

/-- `n`-th Dirichlet eigenfunction on `[0,L]`: `x ↦ sin(nπx/L)`. -/
noncomputable def dirichletEigenfun (n : ℕ) (L : ℝ) (x : ℝ) : ℝ :=
  Real.sin ((n : ℝ) * Real.pi * x / L)

/-- `n`-th Dirichlet eigenvalue: `(nπ/L)²`. -/
noncomputable def dirichletEigenvalue (n : ℕ) (L : ℝ) : ℝ :=
  ((n : ℝ) * Real.pi / L) ^ 2

/-- The linear inner argument `x ↦ nπx/L` has derivative `nπ/L`. -/
theorem hasDerivAt_arg (n : ℕ) (L : ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (n : ℝ) * Real.pi * x / L)
      ((n : ℝ) * Real.pi / L) x := by
  have h : HasDerivAt (fun x : ℝ => (n : ℝ) * Real.pi * x / L)
      ((n : ℝ) * Real.pi * 1 / L) x :=
    ((hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)).div_const L
  simpa using h

/-- First derivative: `φ'(x) = (nπ/L) cos(nπx/L)`. -/
theorem hasDerivAt_dirichletEigenfun (n : ℕ) (L : ℝ) (x : ℝ) :
    HasDerivAt (dirichletEigenfun n L)
      (((n : ℝ) * Real.pi / L) * Real.cos ((n : ℝ) * Real.pi * x / L)) x := by
  have hsin := (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * x / L)).comp x
    (hasDerivAt_arg n L x)
  have : HasDerivAt (dirichletEigenfun n L)
      (Real.cos ((n : ℝ) * Real.pi * x / L) * ((n : ℝ) * Real.pi / L)) x := hsin
  rwa [mul_comm] at this

/-- Derivative of `φ'`: gives `−(nπ/L)² sin(nπx/L)`. -/
theorem hasDerivAt_deriv_dirichletEigenfun (n : ℕ) (L : ℝ) (x : ℝ) :
    HasDerivAt
      (fun x => ((n : ℝ) * Real.pi / L) * Real.cos ((n : ℝ) * Real.pi * x / L))
      (-(((n : ℝ) * Real.pi / L) ^ 2) * Real.sin ((n : ℝ) * Real.pi * x / L)) x := by
  have hcos := (Real.hasDerivAt_cos ((n : ℝ) * Real.pi * x / L)).comp x
    (hasDerivAt_arg n L x)
  have hfull := hcos.const_mul ((n : ℝ) * Real.pi / L)
  have hrw :
      ((n : ℝ) * Real.pi / L) * (-Real.sin ((n : ℝ) * Real.pi * x / L)
        * ((n : ℝ) * Real.pi / L))
      = -(((n : ℝ) * Real.pi / L) ^ 2) * Real.sin ((n : ℝ) * Real.pi * x / L) := by
    ring
  rwa [hrw] at hfull

/-- **Eigenvalue equation.** `φ'' = −(nπ/L)² φ`. -/
theorem dirichletEigenfun_second_deriv (n : ℕ) (L : ℝ) (x : ℝ) :
    deriv (deriv (dirichletEigenfun n L)) x =
      -(dirichletEigenvalue n L) * dirichletEigenfun n L x := by
  have hderiv1 : deriv (dirichletEigenfun n L) =
      fun x => ((n : ℝ) * Real.pi / L) * Real.cos ((n : ℝ) * Real.pi * x / L) := by
    funext y
    exact (hasDerivAt_dirichletEigenfun n L y).deriv
  rw [hderiv1, (hasDerivAt_deriv_dirichletEigenfun n L x).deriv]
  simp only [dirichletEigenvalue, dirichletEigenfun]

/-- Dirichlet BC at 0. -/
theorem dirichletEigenfun_zero (n : ℕ) (L : ℝ) :
    dirichletEigenfun n L 0 = 0 := by
  simp [dirichletEigenfun]

/-- Dirichlet BC at L: `sin(nπ) = 0`. -/
theorem dirichletEigenfun_atL (n : ℕ) (L : ℝ) (hL : L ≠ 0) :
    dirichletEigenfun n L L = 0 := by
  unfold dirichletEigenfun
  rw [mul_div_assoc, div_self hL, mul_one]
  exact Real.sin_nat_mul_pi n

/-- Eigenvalue nonnegative. -/
theorem dirichletEigenvalue_nonneg (n : ℕ) (L : ℝ) :
    0 ≤ dirichletEigenvalue n L := by
  unfold dirichletEigenvalue; positivity

#print axioms dirichletEigenfun_second_deriv
#print axioms dirichletEigenfun_atL
#print axioms dirichletEigenvalue_nonneg

end

end RHFormalization
