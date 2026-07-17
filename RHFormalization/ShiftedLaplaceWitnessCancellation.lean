import RHFormalization.ShiftedLaplaceHoloLocalReduction
import RHFormalization.AnalyticWrappers

/-!
# RHFormalization.ShiftedLaplaceWitnessCancellation

This file attacks the `h_witness` input for shifted/Laplace h_holo.

It proves the local cancellation mechanism:

If near a witness point z,

  B(s) = -c/(s-z) + hB(s)
  Z(s) =  c/(s-z) + hZ(s)

with hB,hZ holomorphic, and the center value is compatible, then
B+Z has a local holomorphic extension at z.

This is the pole-cancellation geometry needed for Appendix H.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Explicit opposite-principal-part cancellation gives a local holomorphic extension.

The `hpoint` hypothesis is the center-value compatibility needed because
`LocalEqAtC` is equality on a full neighborhood, not merely a punctured one.
-/
theorem local_extension_from_opposite_principal_parts_explicit
    (B Z hB hZ : ℂ → ℂ)
    (z c : ℂ)
    (hB_holo : HolomorphicAtC hB z)
    (hZ_holo : HolomorphicAtC hZ z)
    (hB_pp :
      ∀ᶠ w in 𝓝 z,
        w ≠ z → B w = (-c) / (w - z) + hB w)
    (hZ_pp :
      ∀ᶠ w in 𝓝 z,
        w ≠ z → Z w = c / (w - z) + hZ w)
    (hpoint : hB z + hZ z = B z + Z z) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h z ∧
        LocalEqAtC h (fun s : ℂ => B s + Z s) z := by
  refine ⟨fun w : ℂ => hB w + hZ w, ?_, ?_⟩
  · exact hB_holo.add hZ_holo
  · filter_upwards [hB_pp, hZ_pp] with w hBw hZw
    by_cases hw : w = z
    · subst w
      simpa using hpoint
    · have hBcalc := hBw hw
      have hZcalc := hZw hw
      calc
        hB w + hZ w
            = ((-c) / (w - z) + hB w) + (c / (w - z) + hZ w) := by
                ring
        _ = B w + Z w := by
                rw [← hBcalc, ← hZcalc]

/-- Data package for witness cancellation against a chosen B and Z. -/
structure WitnessCancellationData
    (B Z : ℂ → ℂ)
    (W : ZeroWitness) : Type where
  coeff : ℂ
  hB : ℂ → ℂ
  hZ : ℂ → ℂ
  hB_holo : HolomorphicAtC hB W.s0
  hZ_holo : HolomorphicAtC hZ W.s0
  hB_pp :
    ∀ᶠ w in 𝓝 W.s0,
      w ≠ W.s0 → B w = (-coeff) / (w - W.s0) + hB w
  hZ_pp :
    ∀ᶠ w in 𝓝 W.s0,
      w ≠ W.s0 → Z w = coeff / (w - W.s0) + hZ w
  hpoint :
    hB W.s0 + hZ W.s0 = B W.s0 + Z W.s0

/--
Witness cancellation data gives the exact local-extension witness expected by
`shiftedLaplace_holo_from_localExtensions`.
-/
theorem witness_extension_from_cancellation_data
    (B Z : ℂ → ℂ)
    (W : ZeroWitness)
    (D : WitnessCancellationData B Z W) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h W.s0 ∧
        LocalEqAtC h (fun s : ℂ => B s + Z s) W.s0 :=
  local_extension_from_opposite_principal_parts_explicit
    B Z D.hB D.hZ W.s0 D.coeff
    D.hB_holo D.hZ_holo
    D.hB_pp D.hZ_pp
    D.hpoint

/-- Shifted/Laplace witness-cancellation data at a zero witness. -/
abbrev ShiftedLaplaceWitnessCancellationData
    (sigma0 : ℝ)
    (W : ZeroWitness) : Type :=
  WitnessCancellationData
    (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
    (ZpoleSeries defaultZeroMultiplicityData)
    W

/--
If shifted/Laplace witness-cancellation data is supplied at every witness,
then the `h_witness` input for the shifted/Laplace local holomorphy reduction is discharged.
-/
theorem shiftedLaplace_witness_extensions_from_cancellation_data
    (sigma0 : ℝ)
    (hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W) :
    ∀ W : ZeroWitness,
      ∃ h : ℂ → ℂ,
        HolomorphicAtC h W.s0 ∧
          LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) W.s0 := by
  intro W
  simpa [shiftedLaplaceAppendixHFunction,
    ShiftedLaplaceWitnessCancellationData] using
    witness_extension_from_cancellation_data
      (fun s : ℂ => (shiftedLaplacePrimePackageAt sigma0).Bshared s)
      (ZpoleSeries defaultZeroMultiplicityData)
      W
      (hcancel W)

#print axioms local_extension_from_opposite_principal_parts_explicit
#print axioms WitnessCancellationData
#print axioms witness_extension_from_cancellation_data
#print axioms ShiftedLaplaceWitnessCancellationData
#print axioms shiftedLaplace_witness_extensions_from_cancellation_data

end

end RHFormalization
