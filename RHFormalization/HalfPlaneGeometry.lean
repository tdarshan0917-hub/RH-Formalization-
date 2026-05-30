import RHFormalization.GlobalMeromorphicIdentity

/-!
# RHFormalization.HalfPlaneGeometry

Iteration 18: right-half-plane and overlap geometry.

Appendix E/F uses a nonempty right half-plane overlap

  Uσ = {s : ℂ | σ < Re s}

with σ ≥ 0, so that Uσ is an open, nonempty subset of

  Ω = ℂ \ (-∞,0].

Iteration 17 represented this by the API

  `RightHalfPlaneGeometryAPI`

and then used it to build `OverlapGeometryAPI`.

This file reduces that geometry to theorem-backed Lean-facing code.
The only remaining hypothesis for a specific Appendix-E interface is that its threshold
`E.sigma` is nonnegative.
-/


namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-!
## 1. Right half-plane geometry
-/

/--
The right half-plane `{s : ℂ | σ < Re s}` is open.
-/
theorem isOpen_RightHalfPlane
    (σ : ℝ) :
    IsOpen (RightHalfPlane σ) := by
  -- Mathlib-facing proof:
  -- `{s | σ < s.re}` is open by continuity of `Complex.re`.
  simpa [RightHalfPlane] using
    (isOpen_lt continuous_const Complex.continuous_re)

/--
The right half-plane `{s : ℂ | σ < Re s}` is nonempty.
-/
theorem rightHalfPlane_nonempty
    (σ : ℝ) :
    (RightHalfPlane σ).Nonempty := by
  refine ⟨((σ + 1 : ℝ) : ℂ), ?_⟩
  simp [RightHalfPlane]

/--
If `0 ≤ σ`, then the right half-plane lies in `Ω`.

Indeed, `σ < Re s` and `0 ≤ σ` imply `0 < Re s`, so `s` is not on the excluded
nonpositive real axis.
-/
theorem rightHalfPlane_subset_Omega
    (σ : ℝ)
    (hσ : 0 ≤ σ) :
    RightHalfPlane σ ⊆ Ω := by
  intro s hs
  rw [mem_Omega_iff_re_pos_or_im_ne_zero]
  left
  have hpos : 0 < s.re := lt_of_le_of_lt hσ hs
  exact hpos

/--
The full right-half-plane geometry API is theorem-backed.
-/
def defaultRightHalfPlaneGeometryAPI :
    RightHalfPlaneGeometryAPI :=
  { h_open := isOpen_RightHalfPlane
    h_nonempty := rightHalfPlane_nonempty
    h_subset_Omega := rightHalfPlane_subset_Omega }

/-!
## 2. Interface-overlap geometry
-/

/--
Build `OverlapGeometryAPI` from only the nonnegativity of the interface threshold,
using the theorem-backed default right-half-plane geometry.
-/
def buildOverlapGeometryFromSigmaNonnegative
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (S : InterfaceSigmaNonnegativeAPI E) :
    OverlapGeometryAPI D H E :=
  buildOverlapGeometryFromHalfPlane D H E
    defaultRightHalfPlaneGeometryAPI
    S

/--
A direct overlap-geometry theorem for interface data whose threshold is nonnegative.
-/
def defaultOverlapGeometryAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (hσ : 0 ≤ E.sigma) :
    OverlapGeometryAPI D H E :=
  buildOverlapGeometryFromSigmaNonnegative D H E
    { h_sigma_nonneg := hσ }

end

end RHFormalization
