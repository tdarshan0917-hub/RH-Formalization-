import RHFormalization.DMasterResidualAlong
import Mathlib

/-!
# D.CAN-REM closure modulo holomorphic Montel (manuscript p178)

The manuscript closes D.CAN-REM (p178) via:
  local boundedness → normal family (Montel) → subsequential limits holomorphic
  → all agree on U_σ₀ (overlap) → identity theorem on connected Ω → unique limit R_H ∈ O(Ω).

`HolomorphicMontelConvergence` names that single standard complex-analysis input
(Montel's theorem + identity-theorem uniqueness). `dcanrem_from_montel` then shows
D.CAN-REM closes — produces `DMasterResidualData P` — from:
  • the banked SECTOR BOUNDS (displacement + local) packaged as local boundedness,
  • the banked STAGE-HOLO (`stageField_R_stage_holo_arithmetic`),
  • the banked WEIERSTRASS engine (`buildDMasterResidualDataAlong`, which wraps
    `FH_holo_from_stage_epsN`),
  • and this Montel interface.

This wires the full D-side chain end-to-end with the one standard gap clearly named.
The remaining work is to DISCHARGE `HolomorphicMontelConvergence` by building
holomorphic Montel from Mathlib primitives (Cauchy estimate `norm_cderiv_le`,
Arzelà-Ascoli `ArzelaAscoli.isCompact_of_equicontinuous`, identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).

Backwards from RH:
  RH ⟸ capstone ⟸ DMasterResidualData ⟸ THIS ⟸ (sector bounds ✅✅) + (Montel interface).
-/

namespace RHFormalization
open Filter Topology

/-- **The Montel interface (manuscript p178), SOUND form with overlap uniqueness.**

The manuscript pins the limit (p178) by THREE inputs, not local boundedness alone:
  • each `F n` holomorphic on `Ω`;
  • the family locally bounded on `Ω`-compacts (⟹ normal family);
  • OVERLAP CONVERGENCE: on a nonempty open `U ⊆ Ω`, `F n → RH` pointwise.
Then by the normal-family / identity-theorem argument, `F n → RH` locally uniformly on
all `Ω`-compacts. Local boundedness ALONE is too weak (it gives subsequential limits, not
convergence to a specific `RH`); the overlap fixes which limit. This is exactly
D.NET-INDEPENDENCE + the p178 identity-theorem propagation. -/
def HolomorphicMontelConvergence (F : ℕ → ℂ → ℂ) (RH : ℂ → ℂ) : Prop :=
  (∀ n, HolomorphicOnC (F n) Ω) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖F n s‖ ≤ C) →
  (∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
      ∀ s ∈ U, Filter.Tendsto (fun n => F n s) atTop (nhds (RH s))) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F n s) (RH s) < ε)

/-- **D.CAN-REM closes modulo Montel.** -/
def dcanrem_from_montel
    (P : DFiniteStagePackage) (alpha : ℕ → DFiniteStage) (R_H : ℂ → ℂ)
    (h_stage_holo : ∀ n : ℕ, HolomorphicOnC (fun s => P.R_stage (alpha n) s) Ω)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖P.R_stage (alpha n) s‖ ≤ C)
    (h_overlap : ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
        ∀ s ∈ U, Filter.Tendsto (fun n => P.R_stage (alpha n) s) atTop (nhds (R_H s)))
    (hMontel : HolomorphicMontelConvergence (fun n s => P.R_stage (alpha n) s) R_H) :
    DMasterResidualData P :=
  buildDMasterResidualDataAlong P alpha R_H h_stage_holo
    (hMontel h_stage_holo h_loc_bdd h_overlap)

#print axioms dcanrem_from_montel

end RHFormalization
