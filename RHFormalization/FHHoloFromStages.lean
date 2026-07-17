import RHFormalization.AnalyticWrappers
import RHFormalization.DefaultOmegaPreperfect
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# RHFormalization.FHHoloFromStages

Real engine brick (no holes): the global operator transform `FH` is holomorphic
on `Ω` whenever the finite-stage transforms `F_stage n` are each holomorphic on `Ω`
and converge to `FH` locally uniformly on `Ω`.

This is the Weierstrass / locally-uniform-limit theorem specialised to `Ω`.
It discharges holomorphy from convergence of holomorphic stages — the paper's
actual mechanism — with no witness-cancellation and no zero-location input.

The two hypotheses are exactly the genuine analytic inputs:
* each stage holomorphic on `Ω`;
* locally-uniform convergence on `Ω`-compacts (the `h_F_stage_to_FH` shape).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric

/-- Bridge: the raw ε–N "uniform on every compact `K ⊆ Ω`" condition used by the
`DLimitPayload` is exactly `TendstoLocallyUniformlyOn` on `Ω`, because `Ω` is
locally compact (open in `ℂ`) so local-uniform = uniform-on-compacts. -/
theorem tendstoLocallyUniformlyOn_of_compact_epsN
    (F : ℕ → ℂ → ℂ) (FH : ℂ → ℂ)
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F n s) (FH s) < ε) :
    TendstoLocallyUniformlyOn F FH atTop Ω := by
  -- Use the compact-exhaustion characterisation of local uniform convergence
  -- on a locally compact open set.
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Omega_native]
  intro K hKsub hKcpt
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h K hKcpt hKsub ε hε] with n hn s hs
  simpa [dist_comm] using hn s hs

/-- **Engine brick.** A locally-uniform limit on `Ω` of functions holomorphic on
`Ω` is holomorphic on `Ω`. Conclusion is `HolomorphicOnC FH Ω`; the only inputs
are stage holomorphy and locally-uniform convergence. -/
theorem FH_holo_from_locally_uniform_stages
    (F : ℕ → ℂ → ℂ) (FH : ℂ → ℂ)
    (hstage : ∀ n, HolomorphicOnC (F n) Ω)
    (hconv : TendstoLocallyUniformlyOn F FH atTop Ω) :
    HolomorphicOnC FH Ω := by
  -- HolomorphicOnC = AnalyticOn; on the open set Ω, AnalyticOn ↔ DifferentiableOn.
  have hdiff_stage : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) Ω := by
    filter_upwards with n
    exact (hstage n).differentiableOn
  have hdiffFH : DifferentiableOn ℂ FH Ω :=
    hconv.differentiableOn hdiff_stage isOpen_Omega_native
  -- back to AnalyticOn on the open set Ω
  exact hdiffFH.analyticOn isOpen_Omega_native

/-- Combined form matching the payload field shape directly: from the raw ε–N
convergence plus stage holomorphy, conclude `HolomorphicOnC FH Ω`. -/
theorem FH_holo_from_stage_epsN
    (F : ℕ → ℂ → ℂ) (FH : ℂ → ℂ)
    (hstage : ∀ n, HolomorphicOnC (F n) Ω)
    (hconv : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F n s) (FH s) < ε) :
    HolomorphicOnC FH Ω :=
  FH_holo_from_locally_uniform_stages F FH hstage
    (tendstoLocallyUniformlyOn_of_compact_epsN F FH hconv)

#print axioms tendstoLocallyUniformlyOn_of_compact_epsN
#print axioms FH_holo_from_locally_uniform_stages
#print axioms FH_holo_from_stage_epsN

end

end RHFormalization
