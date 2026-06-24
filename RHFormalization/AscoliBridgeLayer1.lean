import RHFormalization.AscoliFactored
import Mathlib

/-!
# Ascoli bridge, layer 1: subsequence extraction in C(↥Ω, ℂ)

Given `AscoliRelativelyCompact G`, any subsequence `φ` of the bundled sequence `G` has a
further subsequence `ψ` converging IN `C(↥Ω, ℂ)` to some limit `gC`. (Pure consequence of
`IsCompact.tendsto_subseq`, which is unconditional.)
-/

namespace RHFormalization
open Filter Topology Complex

/-- From relative compactness, every subsequence has a `C(↥Ω,ℂ)`-convergent sub-subsequence. -/
theorem ascoli_subseq_in_C
    {G : ℕ → C(Ω, ℂ)} (hRC : AscoliRelativelyCompact G)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ gC : C(Ω, ℂ),
      Tendsto (fun n => G (φ (ψ n))) atTop (nhds gC) := by
  obtain ⟨S, hS_compact, hG_mem⟩ := hRC
  -- surface the instances making C(↥Ω,ℂ) first-countable (countably-generated uniformity)
  have hlc : LocallyCompactSpace (Ω : Set ℂ) := isOpen_Omega.locallyCompactSpace
  have hcg : IsCountablyGenerated (uniformity (C(Ω, ℂ))) := inferInstance
  have hfc : FirstCountableTopology (C(Ω, ℂ)) := UniformSpace.firstCountableTopology _
  have hmem : ∀ n, G (φ n) ∈ S := fun n => hG_mem (φ n)
  obtain ⟨gC, _hgC_mem, ψ, hψ_mono, hψ_tendsto⟩ := hS_compact.tendsto_subseq hmem
  exact ⟨ψ, hψ_mono, gC, hψ_tendsto⟩

#print axioms ascoli_subseq_in_C

end RHFormalization
