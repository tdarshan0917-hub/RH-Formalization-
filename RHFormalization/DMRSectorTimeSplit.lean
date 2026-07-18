-- SENTINEL: dmr-sector-time-split-v1
import RHFormalization.BSideHeatKernelLaplaceConnector
import RHFormalization.GalerkinBSideLaplace
import RHFormalization.GalerkinHeadHolo
import RHFormalization.CanonicalPrimePowerPackage
import Mathlib

/-!
# D.MR.3 — the time split (brick 1 of the sector campaign)

The manuscript's sector decomposition (D.MR.3) begins by splitting the
heat-time integral of every canonical kernel at a fixed `t0`:
short-time head `∫_(0,t0]` (entire in `s` — the germ of the Ω-extension)
plus large-time tail `∫_(t0,∞)`. This file makes that split for the
concrete `shiftedLaplaceHeatKernelC` and lifts it to the finite canonical
prime-power package — the exact `B_stage` object of `compensatedBFamily`.

Foundations (all banked, axiom-clean):
* `shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane`
* `shiftedHeatIntegrand_integrableOn` (on `Ioi 0`, `0 < re s`)
* `shiftedHeatIntegrand_integrableOn_Ioc` (on `Ioc 0 t0`, ANY `z`)
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators Classical

/-- **Short-time (head) part** of the canonical kernel: `∫_(0,t0]`.
Defined for every `s : ℂ` (the integrand is entire in `s` and the head
integral converges for all `s` — the Ω-extension germ). -/
def kernelShortPart (a t0 : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioc (0:ℝ) t0, shiftedHeatIntegrand a s t

/-- **Large-time (tail) part** of the canonical kernel: `∫_(t0,∞)`. -/
def kernelTailPart (a t0 : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi t0, shiftedHeatIntegrand a s t

/-- **The kernel time split** (D.MR.3, kernel level): on the Laplace
half-plane, `K(a,s) = short + tail` at every cut point `t0 > 0`. -/
theorem shiftedLaplaceHeatKernelC_eq_short_add_tail
    (a : ℝ) (ha : 0 ≤ a) (t0 : ℝ) (ht0 : 0 < t0)
    (s : ℂ) (hs : 0 < s.re) :
    shiftedLaplaceHeatKernelC a s
      = kernelShortPart a t0 s + kernelTailPart a t0 s := by
  have hrep := shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG_halfplane a ha s hs
  have hIoc : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s t)
      (Ioc (0:ℝ) t0) volume :=
    shiftedHeatIntegrand_integrableOn_Ioc a s t0 ht0
  have hIoi0 : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s t)
      (Ioi (0:ℝ)) volume :=
    shiftedHeatIntegrand_integrableOn a s hs
  have hIoit0 : IntegrableOn (fun t : ℝ => shiftedHeatIntegrand a s t)
      (Ioi t0) volume :=
    hIoi0.mono_set (Ioi_subset_Ioi ht0.le)
  have hunion : Ioc (0:ℝ) t0 ∪ Ioi t0 = Ioi (0:ℝ) :=
    Ioc_union_Ioi_eq_Ioi ht0.le
  have hdisj : Disjoint (Ioc (0:ℝ) t0) (Ioi t0) := by
    first
      | exact Ioc_disjoint_Ioi le_rfl
      | (rw [Set.disjoint_left]
         intro x hx hx'
         exact absurd hx.2 (not_le.mpr hx'))
  calc shiftedLaplaceHeatKernelC a s
      = ∫ t in Ioi (0:ℝ), shiftedHeatIntegrand a s t := hrep
    _ = ∫ t in Ioc (0:ℝ) t0 ∪ Ioi t0, shiftedHeatIntegrand a s t := by
        rw [hunion]
    _ = (∫ t in Ioc (0:ℝ) t0, shiftedHeatIntegrand a s t)
          + ∫ t in Ioi t0, shiftedHeatIntegrand a s t := by
        first
          | exact setIntegral_union hdisj measurableSet_Ioi hIoc hIoit0
          | exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoit0
          | exact MeasureTheory.integral_union hdisj measurableSet_Ioi hIoc hIoit0
    _ = kernelShortPart a t0 s + kernelTailPart a t0 s := rfl

/-- **Short-time (head) sector of the canonical prime-power package.** -/
def canonicalPackageShort (I : Finset PrimePowerPair) (t0 : ℝ) (s : ℂ) : ℂ :=
  ∑ q ∈ I, q.weightC * kernelShortPart q.center t0 s

/-- **Large-time (tail) sector of the canonical prime-power package.** -/
def canonicalPackageTail (I : Finset PrimePowerPair) (t0 : ℝ) (s : ℂ) : ℂ :=
  ∑ q ∈ I, q.weightC * kernelTailPart q.center t0 s

/-- **The package time split** (D.MR.3, package level): the concrete
`B_stage` object splits exactly as head + tail at every `t0 > 0`, on the
Laplace half-plane, provided all active centers are nonnegative. -/
theorem finiteCanonicalPrimePowerPackage_eq_short_add_tail
    (I : Finset PrimePowerPair) (hI : ∀ q ∈ I, 0 ≤ q.center)
    (t0 : ℝ) (ht0 : 0 < t0) (s : ℂ) (hs : 0 < s.re) :
    finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC s
      = canonicalPackageShort I t0 s + canonicalPackageTail I t0 s := by
  unfold finiteCanonicalPrimePowerPackage canonicalPackageShort canonicalPackageTail
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [shiftedLaplaceHeatKernelC_eq_short_add_tail q.center (hI q hq) t0 ht0 s hs]
  ring

#print axioms shiftedLaplaceHeatKernelC_eq_short_add_tail
#print axioms finiteCanonicalPrimePowerPackage_eq_short_add_tail

end

end RHFormalization
