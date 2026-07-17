/-
ZpoleFromSeries.lean — Campaign C, installment 1 (snapshot target: CONV_C2).

Defines the H-side pole series as a tsum over the subtype of nontrivial zeros,
and constructs ZeroPoleLocalUniformConvergenceAPI for it from a single
per-compact summable envelope via the Weierstrass M-test
(tendstoUniformlyOn_tsum), transported to the ℕ-indexed exhaustion partials
through the CONV_C1 infrastructure (subtypeStage_tendsto, subtypeStage_sum_eq).
-/
import RHFormalization.ConvergenceInfrastructure

namespace RHFormalization

open Filter

/-- The H-side pole series, DEFINED as the tsum over all nontrivial zeros. -/
noncomputable def ZpoleSeries (M : ZeroMultiplicityData) (s : ℂ) : ℂ :=
  ∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}, zeroPoleSummand M ρ.1 s

/-- Per-compact summable envelope: the single M-test input of Campaign C. -/
structure ZeroPoleEnvelopeData (M : ZeroMultiplicityData) where
  u : CompactAwayFromZeroPoles → {ρ : ℂ // IsNontrivialZetaZero ρ} → ℝ
  h_summable : ∀ K, Summable (u K)
  h_bound : ∀ K, ∀ ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}, ∀ x ∈ K.K,
    ‖zeroPoleSummand M ρ.1 x‖ ≤ u K ρ

/-- Precomposing a uniformly convergent Finset-net with a tendsto index map. -/
theorem tendstoUniformlyOn_index_comp
    {ι : Type*} {F : Finset ι → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoUniformlyOn F f atTop s)
    {φ : ℕ → Finset ι} (hφ : Tendsto φ atTop atTop) :
    TendstoUniformlyOn (fun n => F (φ n)) f atTop s := by
  intro u hu
  exact hφ.eventually (h u hu)

/-- M-test convergence of the exhaustion partials to ZpoleSeries on each
compact away from the pole set. -/
theorem zpoleSeries_luc
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M)
    (K : CompactAwayFromZeroPoles) :
    LocallyUniformConvergesOnC
      (fun n s => zeroPolePartial M defaultZeroExhaustion n s)
      (ZpoleSeries M) K.K := by
  have hM : TendstoUniformlyOn
      (fun (t : Finset {ρ : ℂ // IsNontrivialZetaZero ρ}) x =>
        ∑ ρ ∈ t, zeroPoleSummand M ρ.1 x)
      (fun x => ∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
        zeroPoleSummand M ρ.1 x)
      atTop K.K :=
    tendstoUniformlyOn_tsum (D.h_summable K)
      (fun ρ x hx => D.h_bound K ρ x hx)
  have hcomp := tendstoUniformlyOn_index_comp hM subtypeStage_tendsto
  have hfinal : TendstoUniformlyOn
      (fun n s => zeroPolePartial M defaultZeroExhaustion n s)
      (ZpoleSeries M) atTop K.K := by
    refine hcomp.congr ?_
    filter_upwards with n
    intro x _
    exact subtypeStage_sum_eq M n x
  exact hfinal.tendstoLocallyUniformlyOn

/-- THE CONSTRUCTOR: the convergence API for the defined series, from the
single envelope input. -/
noncomputable def buildZeroPoleLUCAPIFromEnvelope
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M) :
    ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion (ZpoleSeries M) where
  h_luc := fun K => zpoleSeries_luc M D K

#print axioms zpoleSeries_luc
#print axioms buildZeroPoleLUCAPIFromEnvelope

end RHFormalization
