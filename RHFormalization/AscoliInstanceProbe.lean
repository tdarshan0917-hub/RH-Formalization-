import RHFormalization.Basic
import RHFormalization.MontelUniqueLimit
import Mathlib

/-!
Foundation probe: verify ↥Ω (the slit-plane subtype) has the topological instances
needed for the C(↥Ω, ℂ) compact-convergence route.
-/

namespace RHFormalization
open Filter Topology Complex

example : IsOpen (Ω : Set ℂ) := isOpen_Omega

example : WeaklyLocallyCompactSpace (Ω : Set ℂ) := by
  have : LocallyCompactSpace (Ω : Set ℂ) := isOpen_Omega.locallyCompactSpace
  infer_instance

example : SigmaCompactSpace (Ω : Set ℂ) := by
  have : LocallyCompactSpace (Ω : Set ℂ) := isOpen_Omega.locallyCompactSpace
  infer_instance

example : IsCountablyGenerated (uniformity (C(Ω, ℂ))) := by
  have : LocallyCompactSpace (Ω : Set ℂ) := isOpen_Omega.locallyCompactSpace
  infer_instance

end RHFormalization
