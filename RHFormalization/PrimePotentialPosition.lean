import RHFormalization.DirichletLaplacianEigenpairs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Brick 2, stone 1: the position-space prime potential and its matrix elements

The UNCONDITIONAL route. `V(x) = ∑_q w(q)·W(x − log q)` realized honestly in
position space with a concrete Gaussian bump `W`. Its Dirichlet-sine matrix
element `V_{mn} = ∫₀ᴸ φₘ V φₙ` is NOT diagonal — for `m ≠ n` it is generically
nonzero because `V(x)` is not constant. This is where the non-commutativity of
`H_env = −∂²` and `V` enters, unlike the diagonal `primePotential`.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory
open scoped Real

/-- Normalized Gaussian bump, width `δ`: `W(x) = exp(−x²/(2δ²)) / √(2πδ²)`. -/
noncomputable def gaussBump (δ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (2 * δ ^ 2)) / Real.sqrt (2 * Real.pi * δ ^ 2)

/-- Position-space prime potential `V(x) = ∑_{q ∈ qs} w(q)·W(x − log q)`. -/
noncomputable def primePotentialFn
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ q ∈ qs, w q * gaussBump δ (x - Real.log q)

/-- Matrix element `V_{mn} = ∫₀ᴸ φₘ(x)·V(x)·φₙ(x) dx` in the Dirichlet sine basis. -/
noncomputable def VmatrixElement
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..L,
    dirichletEigenfun m L x * primePotentialFn δ qs w x * dirichletEigenfun n L x

/-- **Stone 1a**: `V(x)` is the finite sum (records it as a genuine function). -/
theorem primePotentialFn_eq_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) :
    primePotentialFn δ qs w x
      = ∑ q ∈ qs, w q * gaussBump δ (x - Real.log q) := rfl

/-- **Stone 1b**: the matrix element is symmetric, `V_{mn} = V_{nm}`. -/
theorem VmatrixElement_symm
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (m n : ℕ) :
    VmatrixElement δ qs w L m n = VmatrixElement δ qs w L n m := by
  unfold VmatrixElement
  congr 1
  funext x
  ring

/-- **Stone 1c**: the Gaussian bump is strictly positive everywhere. -/
theorem gaussBump_pos (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : 0 < gaussBump δ x := by
  unfold gaussBump
  apply div_pos
  · exact Real.exp_pos _
  · apply Real.sqrt_pos.mpr
    have : 0 < δ ^ 2 := by positivity
    positivity

#print axioms primePotentialFn_eq_sum
#print axioms VmatrixElement_symm
#print axioms gaussBump_pos
end
end RHFormalization
