import RHFormalization.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic

/-!
# RHFormalization.OmegaTopology

Iteration 13: theorem-backed topology of the slit plane `Ω`.

This file discharges the small topology API left in Iteration 12.

Main point:
`Ω = ℂ \ (-∞,0]` is equivalently

  `{s : ℂ | 0 < s.re ∨ s.im ≠ 0}`.

The right-hand side is open because:
* `{s | 0 < s.re}` is open by continuity of the real-part map;
* `{s | s.im ≠ 0}` is open by continuity of the imaginary-part map;
* a finite union of open sets is open.

Mathlib names used / expected:
* `Complex.continuous_re`;
* `Complex.continuous_im`;
* `isOpen_lt`;
* `isOpen_ne`.

These names are Mathlib-facing and may need minor tactic adjustment under a
specific `lake build`, but the theorem is no longer represented as a mathematical
assumption.
-/


open Complex Topology Filter

namespace RHFormalization

noncomputable section

/-!
## 1. Equivalent membership forms
-/

/--
Membership in `Ω` is equivalent to having positive real part or nonzero
imaginary part.

This is the manuscript-native form of the slit plane:
the only excluded points are real points with nonpositive real part.
-/
theorem mem_Omega_iff_re_pos_or_im_ne_zero
    (s : ℂ) :
    s ∈ Ω ↔ 0 < s.re ∨ s.im ≠ 0 := by
  rw [mem_Omega_iff]
  constructor
  · intro h
    by_cases him : s.im = 0
    · left
      by_cases hre : s.re ≤ 0
      · exfalso
        exact h ⟨him, hre⟩
      · linarith
    · right
      exact him
  · intro h
    intro hcut
    rcases h with h_re_pos | h_im_ne
    · exact (not_le_of_gt h_re_pos) hcut.2
    · exact h_im_ne hcut.1

/--
Set equality version of the membership lemma.
-/
theorem Omega_eq_re_pos_union_im_ne_zero :
    Ω =
      ({s : ℂ | 0 < s.re} ∪ {s : ℂ | s.im ≠ 0}) := by
  ext s
  rw [mem_Omega_iff_re_pos_or_im_ne_zero]
  rfl

/-!
## 2. Openness of Ω
-/

/--
The set `{s : ℂ | 0 < s.re}` is open.
-/
theorem isOpen_re_pos :
    IsOpen {s : ℂ | 0 < s.re} := by
  -- Mathlib-facing proof:
  -- `{s | 0 < s.re}` is `{s | (fun _ => 0) s < (fun s => s.re) s}`.
  simpa using (isOpen_lt continuous_const Complex.continuous_re)

/--
The set `{s : ℂ | s.im ≠ 0}` is open.
-/
theorem isOpen_im_ne_zero :
    IsOpen {s : ℂ | s.im ≠ 0} := by
  -- The set `{s | s.im ≠ 0}` is the complement of the closed set `{s | s.im = 0}`.
  have hclosed : IsClosed {s : ℂ | s.im = 0} := by
    simpa using (isClosed_eq Complex.continuous_im continuous_const)
  simpa [Set.compl_setOf] using hclosed.isOpen_compl

/--
Native theorem-backed openness of the manuscript slit plane `Ω`.
-/
theorem isOpen_Omega_native : IsOpen Ω := by
  rw [Omega_eq_re_pos_union_im_ne_zero]
  exact isOpen_re_pos.union isOpen_im_ne_zero

/--
Project API for the openness of the manuscript slit plane.

This is no longer an assumption: it is built from `isOpen_Omega_native`.
-/
structure OpenOmegaAPI where
  h_isOpen_Omega :
    IsOpen Ω

/-- Default theorem-backed openness package for `Ω`. -/
def defaultOpenOmegaAPI : OpenOmegaAPI :=
  { h_isOpen_Omega := isOpen_Omega_native }

/-!
## 3. Optional bridge to Mathlib's `Complex.slitPlane`
-/

/-- Mathlib's native slit-plane object. -/
abbrev OmegaMathlib : Set ℂ :=
  Complex.slitPlane

/--
Optional compatibility between the manuscript `Ω` and Mathlib's `Complex.slitPlane`.

This is useful for later cleanup but is not required by the F-side wrapper builders.
-/
structure OmegaMathlibCompatibilityAPI extends OpenOmegaAPI where
  h_Omega_eq_slitPlane :
    Ω = OmegaMathlib

/-- Build the optional compatibility API from equality with Mathlib's slit plane. -/
def buildOmegaMathlibCompatibility
    (h_eq : Ω = OmegaMathlib) :
    OmegaMathlibCompatibilityAPI :=
  { h_Omega_eq_slitPlane := h_eq
    h_isOpen_Omega := by
      rw [h_eq]
      exact Complex.isOpen_slitPlane }

end

end RHFormalization
