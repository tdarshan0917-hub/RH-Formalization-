import RHFormalization.DOperatorExport

/-!
# RHFormalization.DFHLimitConcrete

Concrete theorem-backed helper layer for the Appendix-D finite-transform limit.

This file is not an RH endpoint.

It replaces the final `True`-shaped D-export placeholder by the actual
compact-local convergence statement:

  `F_stage (alpha n) → FH`

uniformly on compact subsets of `Ω`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build `DFHLimitData` from a holomorphic limit function and compact-local
uniform convergence of the finite-stage transforms.
-/
def buildDFHLimitDataFromCompactUniform
    (P : DFiniteStagePackage)
    (alpha : ℕ → DFiniteStage)
    (FH : ℂ → ℂ)
    (h_FH_holo : HolomorphicOnC FH Ω)
    (h_F_stage_to_FH :
      ∀ K : Set ℂ,
        IsCompact K →
        K ⊆ Ω →
          ∀ ε : ℝ,
            0 < ε →
              ∀ᶠ n in Filter.atTop,
                ∀ s : ℂ,
                  s ∈ K →
                    dist (P.F_stage (alpha n) s) (FH s) < ε) :
    DFHLimitData P :=
  { alpha := alpha
    FH := FH
    h_FH_holo := h_FH_holo
    h_F_stage_to_FH := h_F_stage_to_FH }

/--
Accessor theorem for compact-local convergence of finite transforms.
-/
theorem DFHLimitData.compact_uniform_F_stage_convergence
    {P : DFiniteStagePackage}
    (F : DFHLimitData P)
    (K : Set ℂ)
    (hK : IsCompact K)
    (hKOmega : K ⊆ Ω)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      ∀ s : ℂ,
        s ∈ K →
          dist (P.F_stage (F.alpha n) s) (F.FH s) < ε :=
  F.h_F_stage_to_FH K hK hKOmega ε hε

end

end RHFormalization
