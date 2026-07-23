-- SENTINEL: FPGB-v2
import RHFormalization.GalerkinDiagonalFormula
import RHFormalization.PrimeSideTransformKernelPrototype
import RHFormalization.FreePairedTraceIdentity
import RHFormalization.DirichletGreenKernel
import Mathlib

/-!
# FreePairedGreenBridge — brick 2: free paired transform vs the B-side kernel

MEASURED TARGET (before writing):
  ‖2·F₀(a,s) − K(a,s)‖ ≈ C(s)·a/(2L),  C ≈ 20.2,
  flat across L = 50,100,200,400,800 (err·2L/a = 20.177,20.180,20.184,
  20.193,20.211). So the error law is FIRST ORDER in a/L — a boundary term,
  no L-growth, vanishing at the live schedule (L ~ n³).

STRUCTURE: T_kk = (L−a)/2·cos(kπa/L) + L/(2kπ)·sin(kπa/L)
                = (L/2)(1 − a/L)cos(kπa/L) + (L/2)(1/(kπ))sin(kπa/L).
The (L/2) is the window volume that cancels the 1/(2L) density; the (−a/L)
is exactly the boundary error; the sin-term is the second correction.

This file banks the ALGEBRAIC decomposition of the mode summand into
[main cos term] + [boundary a/L term] + [sin correction], which is the
exact split the three sub-bricks (2a Riemann sum, 2b boundary, 2c
truncation) consume. No convergence claim here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

open scoped BigOperators

variable {N : ℕ}

/-- The mode summand of the free paired transform, split into its three
pieces: main cosine term, boundary `a/L` term, and sine correction. -/
theorem galerkinT_diag_split (L a : ℝ) (hL : 0 < L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (k : ℕ) (hk : k ≠ 0) :
    (2 / L) * TmatrixElement L a k k
      = Real.cos ((k : ℝ) * Real.pi * a / L)
        - (a / L) * Real.cos ((k : ℝ) * Real.pi * a / L)
        + (1 / ((k : ℝ) * Real.pi)) * Real.sin ((k : ℝ) * Real.pi * a / L) := by
  rw [TmatrixElement_diag_eval L a hL ha0 haL k hk]
  have hLne : L ≠ 0 := ne_of_gt hL
  have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  try ring

/-- Nonnegativity of the density weight `2/L`. -/
theorem two_div_L_nonneg (L : ℝ) (hL : 0 < L) : (0:ℝ) ≤ 2 / L := by positivity

/-- The main-term modes: `cos(kπa/L)/(s + 1/4 + (kπ/L)²)` — the Riemann
sum whose limit (times `π/L` spacing) is the Green's value
`e^{−a√(s+1/4)}/(2√(s+1/4))`. This lemma records the summand form
consumed by sub-brick 2a. -/
noncomputable def freeModeMainTerm (L a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  ((Real.cos ((k : ℝ) * Real.pi * a / L) : ℝ) : ℂ)
    / (s + (1/4 : ℂ) + ((((k : ℝ) * Real.pi / L) ^ 2 : ℝ) : ℂ))

/-- The boundary modes carrying the measured `a/L` error. -/
noncomputable def freeModeBoundaryTerm (L a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  ((a / L : ℝ) : ℂ) *
    (((Real.cos ((k : ℝ) * Real.pi * a / L) : ℝ) : ℂ)
      / (s + (1/4 : ℂ) + ((((k : ℝ) * Real.pi / L) ^ 2 : ℝ) : ℂ)))

/-- The sine-correction modes. -/
noncomputable def freeModeSineTerm (L a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  ((1 / ((k : ℝ) * Real.pi) : ℝ) : ℂ) *
    (((Real.sin ((k : ℝ) * Real.pi * a / L) : ℝ) : ℂ)
      / (s + (1/4 : ℂ) + ((((k : ℝ) * Real.pi / L) ^ 2 : ℝ) : ℂ)))

/-- **THE MODE SPLIT** — each mode of the free paired transform is
main − boundary + sine. -/
theorem freeMode_split (L a : ℝ) (hL : 0 < L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (s : ℂ) (k : ℕ) (hk : k ≠ 0)
    (hden : s + (1/4 : ℂ) + ((((k : ℝ) * Real.pi / L) ^ 2 : ℝ) : ℂ) ≠ 0) :
    (((2 / L * TmatrixElement L a k k : ℝ)) : ℂ)
        / (s + (1/4 : ℂ) + ((((k : ℝ) * Real.pi / L) ^ 2 : ℝ) : ℂ))
      = freeModeMainTerm L a s k - freeModeBoundaryTerm L a s k
        + freeModeSineTerm L a s k := by
  unfold freeModeMainTerm freeModeBoundaryTerm freeModeSineTerm
  rw [galerkinT_diag_split L a hL ha0 haL k hk]
  push_cast
  field_simp
  try ring

#print axioms galerkinT_diag_split
#print axioms freeMode_split

end RHFormalization
