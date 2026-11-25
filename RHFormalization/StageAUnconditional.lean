import RHFormalization.StageAEquivalence
import RHFormalization.RHSemanticLock
import RHVonKoch.VonKoch

/-!
# StageAUnconditional — `HPdense ↔ RH` with no remaining hypothesis

von Koch's theorem (`RHVonKoch.vonKoch_of_RH`, RHC-3, built on PNT+) discharges the
hypothesis of `HPdense_iff_RH` (RHC-4). `RH_semantic_lock` identifies the repo's
`RiemannHypothesis` with Mathlib's.
-/

namespace RHFormalization

/-- von Koch's theorem, stated for the repo's `RiemannHypothesis`. -/
theorem vonKochBound_of_RH (h : RiemannHypothesis) : VonKochBound :=
  RHVonKoch.vonKoch_of_RH (RH_semantic_lock.mp h)

/-- **The Stage A hypothesis is equivalent to RH.** No assumptions. -/
theorem HPdense_iff_RH_unconditional : HPdense ↔ RiemannHypothesis :=
  HPdense_iff_RH vonKochBound_of_RH

/-- Same, with Mathlib's `RiemannHypothesis`. -/
theorem HPdense_iff_RH_mathlib : HPdense ↔ _root_.RiemannHypothesis :=
  HPdense_iff_RH_unconditional.trans RH_semantic_lock

#print axioms HPdense_iff_RH_unconditional
#print axioms HPdense_iff_RH_mathlib

end RHFormalization
