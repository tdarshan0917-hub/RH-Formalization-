import Mathlib
import RHFormalization.OmegaTopology
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic


/-!
# RHFormalization.AnalyticWrappers

Mathlib-facing analytic wrappers.

Iteration 12 update:
the F-side local arguments now use `OpenOmegaAPI` from `OmegaTopology.lean`,
not the stronger optional `OmegaMathlibCompatibilityAPI`.

The easy wrappers are tied to Mathlib-facing notions:

* `HolomorphicOnC := AnalyticOn ℂ`
* `HolomorphicAtC := AnalyticAt ℂ`
* `LocalEqAtC := EventuallyEq at the neighbourhood filter`

The hard wrappers remain explicit project APIs for now:

* `MeromorphicOnC`
* `HasGenuinePole`
* `HasPrincipalPartAtC`
* `LocallyUniformConvergesOnC`
-/


open Complex Topology Filter

namespace RHFormalization

noncomputable section

/-!
## 1. Holomorphy wrappers tied to Mathlib analytic predicates
-/

/-- Project wrapper for holomorphy on a set. -/
abbrev HolomorphicOnC (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  AnalyticOn ℂ f U

/-- Project wrapper for holomorphy at a point. -/
abbrev HolomorphicAtC (f : ℂ → ℂ) (z : ℂ) : Prop :=
  AnalyticAt ℂ f z

/-- Project wrapper for local equality near a point. -/
abbrev LocalEqAtC (f g : ℂ → ℂ) (z : ℂ) : Prop :=
  f =ᶠ[𝓝 z] g

/-- Definition check for the holomorphy-on wrapper. -/
theorem holomorphicOnC_iff_analyticOn
    (f : ℂ → ℂ)
    (U : Set ℂ) :
    HolomorphicOnC f U ↔ AnalyticOn ℂ f U := by
  rfl

/--
Holomorphic-on to holomorphic-at transfer.

This uses only openness of `Ω`; equality with `Complex.slitPlane` is not needed.
-/
theorem HolomorphicOnC.holomorphicAt
    {f : ℂ → ℂ}
    {z : ℂ}
    (O : OpenOmegaAPI)
    (hf : HolomorphicOnC f Ω)
    (hz : z ∈ Ω) :
    HolomorphicAtC f z := by
  exact hf.analyticAt (O.h_isOpen_Omega.mem_nhds hz)

/--
Local equality extraction from `Set.EqOn` on `Ω`.

This uses only openness of `Ω`.
-/
theorem localEqAtC_of_eqOn_Omega
    {f g : ℂ → ℂ}
    {z : ℂ}
    (O : OpenOmegaAPI)
    (hz : z ∈ Ω)
    (hEq : Set.EqOn f g Ω) :
    LocalEqAtC f g z := by
  filter_upwards [O.h_isOpen_Omega.mem_nhds hz] with y hy
  exact hEq hy

/--
Congruence for holomorphy at a point under local equality.

This wraps Mathlib's `AnalyticAt.congr` in project language.
-/
theorem holomorphicAtC_congr
    {f g : ℂ → ℂ}
    {z : ℂ}
    (hf : HolomorphicAtC f z)
    (hfg : LocalEqAtC f g z) :
    HolomorphicAtC g z := by
  exact hf.congr hfg

/-!
## 2. Hard analytic wrappers still left as explicit APIs
-/

/--
Project wrapper for meromorphicity on a set.

This is now backed by Mathlib's native `MeromorphicOn`.
-/
abbrev MeromorphicOnC (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  MeromorphicOn f U

/--
Project wrapper for local uniform convergence of function sequences on a set.

This is now backed by Mathlib's native local-uniform convergence predicate.
-/
abbrev LocallyUniformConvergesOnC
    (F : ℕ → ℂ → ℂ)
    (f : ℂ → ℂ)
    (U : Set ℂ) : Prop :=
  TendstoLocallyUniformlyOn F f Filter.atTop U

/--
Project wrapper for a principal part at a pole.

TODO: replace by a Laurent-series or meromorphic-normal-form definition.
-/
abbrev HasPrincipalPartAtC
    (f : ℂ → ℂ)
    (z coeff : ℂ) : Prop :=
  ∃ h : ℂ → ℂ,
    HolomorphicAtC h z ∧
      (∀ᶠ w in 𝓝 z, w ≠ z → f w = coeff / (w - z) + h w)

/--
Project wrapper for a genuine uncancelled pole.

TODO: replace by a Mathlib/project-local definition in terms of meromorphic normal
forms or Laurent coefficients.
-/
abbrev HasGenuinePole
    (f : ℂ → ℂ)
    (z : ℂ) : Prop :=
  ∃ coeff : ℂ, coeff ≠ 0 ∧ HasPrincipalPartAtC f z coeff

end

end RHFormalization
