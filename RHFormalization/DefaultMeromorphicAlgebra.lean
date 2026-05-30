import Mathlib
import RHFormalization.GlobalMeromorphicIdentity

/-!
# RHFormalization.DefaultMeromorphicAlgebra

Theorem-backed default implementation of `MeromorphicAlgebraAPI`.

The key point is that `HolomorphicOnC f U` is analytic *within* `U`.
To convert this to ambient meromorphicity on `U`, we require `IsOpen U`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
A holomorphic function on an open set is meromorphic on that set.
-/
theorem holomorphicOnC_to_meromorphicOnC
    (f : ℂ → ℂ)
    (U : Set ℂ)
    (hU : IsOpen U)
    (hf : HolomorphicOnC f U) :
    MeromorphicOnC f U := by
  intro z hz
  exact (hf.analyticAt (hU.mem_nhds hz)).meromorphicAt

/--
A holomorphic function minus a meromorphic function is meromorphic on an open set.
-/
theorem holomorphicOnC_sub_meromorphicOnC
    (f g : ℂ → ℂ)
    (U : Set ℂ)
    (hU : IsOpen U)
    (hf : HolomorphicOnC f U)
    (hg : MeromorphicOnC g U) :
    MeromorphicOnC (fun s => f s - g s) U := by
  intro z hz
  simpa [Pi.sub_apply] using
    ((hf.analyticAt (hU.mem_nhds hz)).meromorphicAt.sub (hg z hz))

/--
Default theorem-backed meromorphic algebra package.
-/
def defaultMeromorphicAlgebraAPI : MeromorphicAlgebraAPI :=
  { h_holomorphic_to_meromorphic :=
      holomorphicOnC_to_meromorphicOnC
    h_holomorphic_sub_meromorphic :=
      holomorphicOnC_sub_meromorphicOnC }

end

end RHFormalization
