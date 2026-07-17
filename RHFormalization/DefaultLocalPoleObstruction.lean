import RHFormalization.PoleObstruction

namespace RHFormalization

noncomputable section
open Complex Topology Filter

/-- Local pole obstruction, proved. -/
def defaultLocalPoleObstructionAPI
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H) :
    LocalPoleObstructionAPI D H E :=
{ h_no_pole_from_local_identity := by
    intro W hlocal hFH hHtot hpole
    have hZ_holo : HolomorphicAtC H.Zpole W.s0 := by
      have hdiff : HolomorphicAtC (fun s => Htot D H s - D.FH s) W.s0 := hHtot.sub hFH
      have heq : (fun s => Htot D H s - D.FH s) =ᶠ[𝓝 W.s0] H.Zpole := by
        filter_upwards [hlocal] with w hw
        have : H.Zpole w = Htot D H w - D.FH w := by rw [hw]; ring
        rw [this]
      exact hdiff.congr heq
    obtain ⟨coeff, hcoeff, h, hh_holo, hrep⟩ := hpole
    -- g(w) := (w - s0) * (Zpole w - h w). It is analytic (hence continuous) at s0,
    -- equals coeff on the punctured nbhd, and equals 0 at s0. So coeff = 0.
    set g : ℂ → ℂ := fun w => (w - W.s0) * (H.Zpole w - h w) with hg_def
    have hg_holo : HolomorphicAtC g W.s0 :=
      (analyticAt_id.sub analyticAt_const).mul (hZ_holo.sub hh_holo)
    have hg_cont : ContinuousAt g W.s0 := hg_holo.continuousAt
    -- on the punctured nbhd, g w = coeff
    have hg_eq : g =ᶠ[𝓝[≠] W.s0] (fun _ => coeff) := by
      have hpunct : ∀ᶠ w in 𝓝[≠] W.s0, w ≠ W.s0 := self_mem_nhdsWithin
      filter_upwards [hrep.filter_mono nhdsWithin_le_nhds, hpunct] with w hw hwne
      have hZ := hw hwne
      have hwsub : w - W.s0 ≠ 0 := sub_ne_zero.mpr hwne
      simp only [hg_def, hZ]
      field_simp
      ring
    -- limit of g along 𝓝[≠] s0 is coeff (from hg_eq) and is g s0 = 0 (continuity)
    have hlim_const : Tendsto g (𝓝[≠] W.s0) (𝓝 coeff) := by
      rw [tendsto_congr' hg_eq]; exact tendsto_const_nhds
    have hlim_g : Tendsto g (𝓝[≠] W.s0) (𝓝 (g W.s0)) :=
      hg_cont.tendsto.mono_left nhdsWithin_le_nhds
    have hg_s0 : g W.s0 = 0 := by simp [hg_def]
    have : coeff = 0 := by
      have := tendsto_nhds_unique hlim_const hlim_g
      rw [hg_s0] at this
      exact this
    exact hcoeff this }


end

end RHFormalization
