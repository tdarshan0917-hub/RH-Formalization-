import RHFormalization.MontelSubsequenceAssembly
import RHFormalization.DCanRemFromMontel
import Mathlib

/-!
# D.CAN-REM closes modulo the single Ascoli gap (manuscript p178)

Composing the banked subsequence assembly (`holomorphicMontelConvergence_from_ascoli`)
with the banked D-side wiring (`dcanrem_from_montel`), the ENTIRE D-side reduces to one
named standard-analysis obligation: `AscoliExtraction` (Arzelà–Ascoli for the holomorphic
stage family — the mechanical `C(K,ℂ)` bundling).

Everything else in the Montel discharge is banked:
* equicontinuity (locally-bounded holomorphic ⟹ equicontinuous),
* identity-theorem uniqueness on the slit plane Ω,
* the subsequence assembly (overlap + uniqueness ⟹ full convergence).
-/

namespace RHFormalization
open Filter Topology Complex

/-- **D.CAN-REM modulo Ascoli.** -/
def dcanrem_from_ascoli
    (P : DFiniteStagePackage) (alpha : ℕ → DFiniteStage) (R_H : ℂ → ℂ)
    (h_stage_holo : ∀ n : ℕ, HolomorphicOnC (fun s => P.R_stage (alpha n) s) Ω)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖P.R_stage (alpha n) s‖ ≤ C)
    (h_overlap : ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
        ∀ s ∈ U, Filter.Tendsto (fun n => P.R_stage (alpha n) s) atTop (nhds (R_H s)))
    (h_RH_holo : HolomorphicOnC R_H Ω)
    (h_ascoli : AscoliExtraction (fun n s => P.R_stage (alpha n) s)) :
    DMasterResidualData P :=
  dcanrem_from_montel P alpha R_H h_stage_holo h_loc_bdd h_overlap
    (holomorphicMontelConvergence_from_ascoli h_RH_holo h_ascoli)

#print axioms dcanrem_from_ascoli

end RHFormalization
