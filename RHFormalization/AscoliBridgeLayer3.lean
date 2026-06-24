import RHFormalization.AscoliBridgeLayer1
import RHFormalization.AscoliBridgeLayer2
import Mathlib

/-!
# Ascoli bridge, layer 3: assemble AscoliExtraction from AscoliRelativelyCompact

Bundles holomorphic `F n` into `C(↥Ω, ℂ)`, composes the banked subseq-extraction (layer 1)
and the loc-unif-dist bridge (layer 2), and (via Weierstrass) the holomorphy of the limit,
to produce `AscoliExtraction F` — modulo the one named hard lemma `AscoliRelativelyCompact`.
-/

namespace RHFormalization
open Filter Topology Complex

/-- Bundle a holomorphic-on-Ω function into `C(↥Ω, ℂ)`. -/
noncomputable def bundleC (f : ℂ → ℂ) (hf : HolomorphicOnC f Ω) : C(Ω, ℂ) :=
  ⟨(Ω : Set ℂ).restrict f, by
    apply ContinuousOn.restrict
    have hfN : AnalyticOnNhd ℂ f Ω := (isOpen_Omega.analyticOn_iff_analyticOnNhd).mp hf
    exact hfN.continuousOn⟩

@[simp] theorem bundleC_apply (f : ℂ → ℂ) (hf : HolomorphicOnC f Ω) (s : ℂ) (hs : s ∈ Ω) :
    (bundleC f hf) ⟨s, hs⟩ = f s := rfl

/-- The `AscoliRelativelyCompact` hypothesis specialized to the bundled holomorphic family. -/
def AscoliExtractionHyp (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ (hF : ∀ n, HolomorphicOnC (F n) Ω),
    AscoliRelativelyCompact (fun n => bundleC (F n) (hF n))

/-- **Layer 3 (main assembly).** -/
theorem ascoliExtraction_of_relativelyCompact
    {F : ℕ → ℂ → ℂ} (hRC : AscoliExtractionHyp F) :
    AscoliExtraction F := by
  intro hF _hbdd φ hφ
  set G : ℕ → C(Ω, ℂ) := fun n => bundleC (F n) (hF n) with hG
  obtain ⟨ψ, hψ_mono, gC, hψ_conv⟩ := ascoli_subseq_in_C (hRC hF) φ hφ
  classical
  set g : ℂ → ℂ := fun s => if hs : s ∈ Ω then gC ⟨s, hs⟩ else 0 with hgdef
  have hdist : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K → dist (F (φ (ψ n)) s) (g s) < ε := by
    intro K hK hKΩ ε hε
    have hL2 := ascoli_C_tendsto_to_locunif hψ_conv K hK hKΩ ε hε
    filter_upwards [hL2] with n hn
    intro s hsK
    have hsΩ : s ∈ Ω := hKΩ hsK
    have hb := hn s hsΩ hsK
    simp only [bundleC_apply] at hb
    rw [hgdef]
    simp only [hsΩ, dif_pos]
    exact hb
  have hg_holo : HolomorphicOnC g Ω := by
    have hTLU : TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) g atTop Ω := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Omega]
      intro K hKΩ hK
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hd := hdist K hK hKΩ ε hε
      filter_upwards [hd] with n hn s hsK
      rw [dist_comm]; exact hn s hsK
    have hED : ∀ᶠ n in (atTop : Filter ℕ), DifferentiableOn ℂ (F (φ (ψ n))) Ω := by
      filter_upwards with n
      exact ((isOpen_Omega.analyticOn_iff_analyticOnNhd).mp (hF (φ (ψ n)))).differentiableOn
    have hdiff : DifferentiableOn ℂ g Ω :=
      hTLU.differentiableOn hED isOpen_Omega
    rw [show HolomorphicOnC g Ω = AnalyticOn ℂ g Ω from rfl,
        isOpen_Omega.analyticOn_iff_analyticOnNhd]
    exact hdiff.analyticOnNhd isOpen_Omega
  exact ⟨ψ, hψ_mono, g, hg_holo, hdist⟩

#print axioms ascoliExtraction_of_relativelyCompact

end RHFormalization
