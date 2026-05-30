import RHFormalization.DOperatorExport

/-!
# RHFormalization.DMasterResidualConcrete

Concrete theorem-backed helper layer for D.MASTER-RESIDUAL and D.CAN-REM.

This file is not an RH endpoint.

It replaces the former `True`-shaped residual convergence placeholders by the
actual compact-local convergence statement used by Appendix D.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build `DMasterResidualData` from a holomorphic remainder and compact-local
uniform convergence of the finite residuals.
-/
def buildDMasterResidualDataFromCompactUniform
    (P : DFiniteStagePackage)
    (alpha : ℕ → DFiniteStage)
    (RH : ℂ → ℂ)
    (h_RH_holo : HolomorphicOnC RH Ω)
    (h_R_stage_to_RH :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∀ ε : ℝ,
            0 < ε →
              ∀ᶠ n in Filter.atTop,
                ∀ s : ℂ,
                  s ∈ K →
                    dist (P.R_stage (alpha n) s) (RH s) < ε) :
    DMasterResidualData P :=
  { alpha := alpha
    RH := RH
    h_RH_holo := h_RH_holo
    h_R_stage_to_RH := h_R_stage_to_RH }

/--
Build `DCanRemAPI` from the residual convergence already stored in
`DMasterResidualData`.
-/
def buildDCanRemAPIFromMasterResidual
    (P : DFiniteStagePackage)
    (B : DBcanLimitData P)
    (F : DFHLimitData P)
    (R : DMasterResidualData P) :
    DCanRemAPI P B F R :=
  { h_remainder_holo := R.h_RH_holo
    h_can_rem_convergence := R.h_R_stage_to_RH }

/--
Accessor theorem for compact-local residual convergence.
-/
theorem DMasterResidualData.compact_uniform_residual_convergence
    {P : DFiniteStagePackage}
    (R : DMasterResidualData P)
    (K : Set ℂ)
    (hK : IsCompact K)
    (hKOmega : K ⊆ Ω)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      ∀ s : ℂ,
        s ∈ K →
          dist (P.R_stage (R.alpha n) s) (R.RH s) < ε :=
  R.h_R_stage_to_RH K hK hKOmega ε hε

/--
Accessor theorem for CAN-REM compact-local residual convergence.
-/
theorem DCanRemAPI.compact_uniform_can_rem_convergence
    {P : DFiniteStagePackage}
    {B : DBcanLimitData P}
    {F : DFHLimitData P}
    {R : DMasterResidualData P}
    (C : DCanRemAPI P B F R)
    (K : Set ℂ)
    (hK : IsCompact K)
    (hKOmega : K ⊆ Ω)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      ∀ s : ℂ,
        s ∈ K →
          dist (P.R_stage (R.alpha n) s) (R.RH s) < ε :=
  C.h_can_rem_convergence K hK hKOmega ε hε

end

end RHFormalization
