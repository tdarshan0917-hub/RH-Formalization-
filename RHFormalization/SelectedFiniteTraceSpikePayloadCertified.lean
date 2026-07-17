import RHFormalization.SelectedFiniteTraceSpikePayloadFromImageBridge

/-!
# Certified selected finite trace/spike payload

The scratch check showed that raw `SelectedFiniteTraceSpikePayload` is too weak:
empty/zero data can inhabit it.

This file strengthens the certificate so that a selected payload must carry
nontrivial Appendix-D-style provenance.  In particular, the Nat-indexed active
set must be complete for `α.diagonalSpikeActive`, not merely sound.
-/

namespace RHFormalization

noncomputable section

/--
A constructible certificate that a `SelectedFiniteTraceSpikePayload` is not an
arbitrary dummy payload.

The key anti-dummy field is `h_activeIndices_complete`: the finite active set
must contain every stage-active diagonal spike.  The zero/empty scratch payload
cannot prove this for arbitrary finite stages.

The remaining fields record the finite Nat→PrimePower identification used by
the canonical finite package.
-/
structure IsCertifiedFiniteAppendixDExtraction
    (Pld : SelectedFiniteTraceSpikePayload) : Type 1 where
  /-- Active-index soundness, repeated here as part of the certificate API. -/
  h_activeIndices_sound :
    ∀ (α : DFiniteStage), ∀ q ∈ Pld.activeIndices α,
      α.diagonalSpikeActive q

  /--
  Active-index completeness.  This is the crucial field missing from the raw
  payload API: the selected finite active set must include all active diagonal
  spikes.
  -/
  h_activeIndices_complete :
    ∀ (α : DFiniteStage), ∀ q : ℕ,
      α.diagonalSpikeActive q → q ∈ Pld.activeIndices α

  /-- Finite Nat-to-prime-power map used to identify the canonical package. -/
  toPP :
    DFiniteStage → ℕ → PrimePowerPair

  /-- The stored prime-power indices are exactly the image of the active Nat indices. -/
  h_ppIndices_eq_image :
    ∀ (α : DFiniteStage),
      Pld.ppIndices α = (Pld.activeIndices α).image (toPP α)

  /-- The Nat-to-prime-power map is injective on each active finite set. -/
  hinj :
    ∀ (α : DFiniteStage), ∀ m ∈ Pld.activeIndices α, ∀ n ∈ Pld.activeIndices α,
      toPP α m = toPP α n → m = n

  /-- Canonical coefficient compatibility on active indices. -/
  hcoeff :
    ∀ (α : DFiniteStage), ∀ n ∈ Pld.activeIndices α,
      α.canonicalSpikeContribution n = (toPP α n).weightC

  /-- Kernel compatibility on active indices. -/
  hkernel :
    ∀ (α : DFiniteStage), ∀ n ∈ Pld.activeIndices α, ∀ s : ℂ,
      Pld.spikeKernel α n s =
        Pld.ppKernel α (toPP α n).center s

/--
Certified selected finite trace/spike payload.

Downstream selected construction should use this, not raw
`SelectedFiniteTraceSpikePayload`.
-/
structure CertifiedSelectedFiniteTraceSpikePayload where
  payload : SelectedFiniteTraceSpikePayload
  certified : IsCertifiedFiniteAppendixDExtraction payload

/--
Build the finite operator layer only from a certified trace/spike payload.
-/
def buildSelectedFiniteOperatorLayerFromCertifiedTraceSpikePayload
    (Pld : CertifiedSelectedFiniteTraceSpikePayload) :
    DFiniteStagePackageFromOperatorLayer :=
  buildSelectedFiniteOperatorLayerFromTraceSpikePayload Pld.payload

end

end RHFormalization
