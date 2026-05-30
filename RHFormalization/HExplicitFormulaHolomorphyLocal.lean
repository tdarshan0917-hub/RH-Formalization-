import RHFormalization.HExplicitFormulaSplit

/-!
# RHFormalization.HExplicitFormulaHolomorphyLocal

Local-to-global holomorphy bridge for the H/E explicit-formula cancellation.

After `HExplicitFormulaSplit`, the remaining H-side input is

  HolomorphicOnC (fun s => Y.B.Cshared.Bshared s + Zpole s) Ω.

This file reduces that global holomorphy target to local holomorphic extensions
at every point of Ω.  The next real analytic theorem is then to construct those
local extensions from principal-part cancellation.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If a function is holomorphic at every point of a set, then it is holomorphic on
that set in the project wrapper sense.
-/
theorem holomorphicOnC_of_forall_holomorphicAtC
    (f : ℂ → ℂ)
    (U : Set ℂ)
    (h : ∀ z : ℂ, z ∈ U → HolomorphicAtC f z) :
    HolomorphicOnC f U := by
  intro z hz
  exact (h z hz).analyticWithinAt

/--
A local holomorphic extension at every point of a set gives holomorphy on that
set.
-/
theorem holomorphicOnC_of_local_holomorphic_extensions
    (f : ℂ → ℂ)
    (U : Set ℂ)
    (hlocal :
      ∀ z : ℂ,
        z ∈ U →
          ∃ h : ℂ → ℂ,
            HolomorphicAtC h z ∧
              LocalEqAtC h f z) :
    HolomorphicOnC f U := by
  apply holomorphicOnC_of_forall_holomorphicAtC
  intro z hz
  rcases hlocal z hz with ⟨h, hholo, hlocalEq⟩
  exact holomorphicAtC_congr hholo hlocalEq

/--
The H/E holomorphy frontier reduced to local holomorphic extensions.

This is the current analytic bridge we need: construct local holomorphic
extensions of `Bshared + Zpole` on Ω.
-/
theorem Harch_holomorphic_from_local_extensions
    (Y : DDetailedConstructionWithOperatorLegality)
    (Zpole : ℂ → ℂ)
    (hlocal :
      ∀ z : ℂ,
        z ∈ Ω →
          ∃ h : ℂ → ℂ,
            HolomorphicAtC h z ∧
              LocalEqAtC h
                (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
                z) :
    HolomorphicOnC
      (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
      Ω :=
  holomorphicOnC_of_local_holomorphic_extensions
    (fun s : ℂ => Y.B.Cshared.Bshared s + Zpole s)
    Ω
    hlocal

end

end RHFormalization
