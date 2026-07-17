import RHFormalization.DBFFBcorrWindow
import RHFormalization.DBFFBcorrWindowHolo
import RHFormalization.DBFFCompensator
import RHFormalization.DBFFCompensatorHolo
import RHFormalization.DBFFCorrectedBulkProvider
import Mathlib

namespace RHFormalization
open Complex Filter
open scoped Topology BigOperators

/-- **The corrected-bulk correction term**: window deficit + main-term compensator.
This is the manuscript's `Bcorr = BcorrWin + AclassCorr`. -/
noncomputable def Bcorr (n : ℕ) (s : ℂ) : ℂ :=
  BcorrWin n s + compensatorM n s

/-- **h_Bcorr_overlap0 (D.OP.1 + Brick A).** `Bcorr → 0` pointwise on RHP(1). -/
theorem Bcorr_overlap0 {s : ℂ} (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto (fun n : ℕ => Bcorr n s) atTop (𝓝 (0 : ℂ)) := by
  have hw := BcorrWin_overlap0 hs
  have hm := compensatorM_overlap0 hs
  have := hw.add hm
  simpa [Bcorr] using this

/-- Per-stage Ω-holomorphy of `Bcorr` (not required by the engine, but banked). -/
theorem Bcorr_holo (n : ℕ) : HolomorphicOnC (fun s => Bcorr n s) Ω := by
  have hw := BcorrWin_holo n
  have hm := compensatorM_holo n
  intro z hz
  exact (hw z hz).add (hm z hz)

#print axioms Bcorr
#print axioms Bcorr_overlap0
#print axioms Bcorr_holo

end RHFormalization
