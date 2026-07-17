/-
PILLAR (c) — ASSEMBLY AND CLOSURE.
Fixed := punctured-limit regularization of HarchΩ = model + ZpoleRepSeries.
Analytic on all of Ω (witness case: banked PP cancellation; regular case:
banked pointwise analyticity). Instantiates HArchPackage unconditionally.
Fixed = raw off the witness set, so pillar (d) still reduces to
Bshared = model on the half-plane.
-/
import RHFormalization.ShiftedLaplaceHarchOmegaRegular
import RHFormalization.ShiftedLaplaceHarchOmegaWitness

namespace RHFormalization

noncomputable section

open Complex Filter Topology Set

/-- Riemann-style regularization of the honest Harch candidate. -/
noncomputable def shiftedLaplaceHarchOmegaFixed (s : ℂ) : ℂ :=
  limUnder (𝓝[≠] s) shiftedLaplaceHarchOmega

/-- Generic: a punctured-local holomorphic extension at `z` makes the
punctured-limit regularization analytic at `z`. -/
theorem limUnderReg_analyticAt
    {f : ℂ → ℂ} {z : ℂ} {h : ℂ → ℂ}
    (hholo : AnalyticAt ℂ h z)
    (heq : ∀ᶠ w in 𝓝 z, w ≠ z → f w = h w) :
    AnalyticAt ℂ (fun s => limUnder (𝓝[≠] s) f) z := by
  obtain ⟨U, hU, hUopen, hzU⟩ := eventually_nhds_iff.mp heq
  obtain ⟨V, hV, hVopen, hzV⟩ :=
    eventually_nhds_iff.mp hholo.eventually_analyticAt
  have hkey : ∀ w ∈ U ∩ V, limUnder (𝓝[≠] w) f = h w := by
    intro w hw
    haveI : (𝓝[≠] w).NeBot := by
      first
        | infer_instance
        | exact Module.punctured_nhds_neBot ℝ ℂ w
    have hmem : U ∩ {z}ᶜ ∈ 𝓝[≠] w := by
      by_cases hwz : w = z
      · subst hwz
        exact Filter.inter_mem
          (mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hw.1))
          self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds
          ((hUopen.inter isOpen_compl_singleton).mem_nhds
            ⟨hw.1, Set.mem_compl_singleton_iff.mpr hwz⟩)
    have htend : Tendsto h (𝓝[≠] w) (𝓝 (h w)) :=
      (hV w hw.2).continuousAt.continuousWithinAt
    have hfeq : h =ᶠ[𝓝[≠] w] f :=
      Filter.eventuallyEq_of_mem hmem
        (fun w' hw' =>
          (hU w' hw'.1 (Set.mem_compl_singleton_iff.mp hw'.2)).symm)
    exact (htend.congr' hfeq).limUnder_eq
  have hUV : U ∩ V ∈ 𝓝 z := (hUopen.inter hVopen).mem_nhds ⟨hzU, hzV⟩
  exact hholo.congr
    (Filter.eventuallyEq_of_mem hUV (fun w hw => (hkey w hw).symm))

/-- Fixed is analytic at every witness point (PP cancellation, banked). -/
theorem shiftedLaplaceHarchOmegaFixed_analyticAt_witness (W : ZeroWitness) :
    AnalyticAt ℂ shiftedLaplaceHarchOmegaFixed W.s0 := by
  obtain ⟨h, hholo, heq⟩ := shiftedLaplaceHarchOmega_localExt_at_witness W
  unfold shiftedLaplaceHarchOmegaFixed
  exact limUnderReg_analyticAt hholo heq

/-- Fixed is analytic at every non-witness point of Ω (regular case, banked). -/
theorem shiftedLaplaceHarchOmegaFixed_analyticAt_regular
    {z : ℂ} (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    AnalyticAt ℂ shiftedLaplaceHarchOmegaFixed z := by
  unfold shiftedLaplaceHarchOmegaFixed
  exact limUnderReg_analyticAt
    (shiftedLaplaceHarchOmega_analyticAt_regular hzΩ hznw)
    (by filter_upwards with w hw using rfl)

/-- Pointwise analyticity on all of Ω. -/
theorem shiftedLaplaceHarchOmegaFixed_analyticAt_Omega :
    ∀ z ∈ Ω, AnalyticAt ℂ shiftedLaplaceHarchOmegaFixed z := by
  intro z hz
  by_cases hw : ∃ W : ZeroWitness, z = W.s0
  · obtain ⟨W, rfl⟩ := hw
    exact shiftedLaplaceHarchOmegaFixed_analyticAt_witness W
  · push_neg at hw
    exact shiftedLaplaceHarchOmegaFixed_analyticAt_regular hz hw

/-- **PILLAR (c): holomorphy on Ω.** -/
theorem shiftedLaplaceHarchOmegaFixed_holo :
    HolomorphicOnC shiftedLaplaceHarchOmegaFixed Ω := by
  have h := shiftedLaplaceHarchOmegaFixed_analyticAt_Omega
  first
    | exact h
    | exact fun z hz => h z hz
    | exact fun z hz => (h z hz).analyticWithinAt
    | exact fun z hz => (h z hz).differentiableAt.differentiableWithinAt
    | exact fun z hz => (h z hz).differentiableAt
    | exact fun z hz => (h z hz).differentiableWithinAt

/-- **PILLAR (c) CLOSED: the unconditional HArchPackage.** -/
noncomputable def unconditionalHArchPackage : HArchPackage :=
{ Harch := shiftedLaplaceHarchOmegaFixed
  h_Harch_holo := shiftedLaplaceHarchOmegaFixed_holo }

/-- Off the witness set, Fixed agrees with the raw sum. -/
theorem shiftedLaplaceHarchOmegaFixed_eq_raw_of_regular
    {z : ℂ} (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    shiftedLaplaceHarchOmegaFixed z = shiftedLaplaceHarchOmega z := by
  haveI : (𝓝[≠] z).NeBot := by
    first
      | infer_instance
      | exact Module.punctured_nhds_neBot ℝ ℂ z
  have ht : Tendsto shiftedLaplaceHarchOmega (𝓝[≠] z)
      (𝓝 (shiftedLaplaceHarchOmega z)) :=
    (shiftedLaplaceHarchOmega_analyticAt_regular hzΩ hznw).continuousAt.continuousWithinAt
  unfold shiftedLaplaceHarchOmegaFixed
  exact ht.limUnder_eq

/-- Pillar-(d) reduction for the Fixed function: at every non-witness point
of Ω, `Fixed − ZpoleRep = model`. Pole points all have negative real part,
so this covers every right half-plane inside Ω. -/
theorem shiftedLaplaceHarchOmegaFixed_sub_Zpole_eq_model
    {z : ℂ} (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    shiftedLaplaceHarchOmegaFixed z
      - ZpoleRepSeries defaultZeroMultiplicityData z
      = shiftedLaplaceLogDerivModel z := by
  rw [shiftedLaplaceHarchOmegaFixed_eq_raw_of_regular hzΩ hznw]
  exact shiftedLaplaceHarchOmega_sub_Zpole_eq_model z

#print axioms shiftedLaplaceHarchOmegaFixed_holo
#print axioms unconditionalHArchPackage
#print axioms shiftedLaplaceHarchOmegaFixed_sub_Zpole_eq_model

end

end RHFormalization
