/-
STAGE B(i) — Brick 1: dense zero-tilt centered observable + pairing pins.
AMENDMENT to signed B1 (reported to GPT): the E1 donor `tiltedCenteredEntry`
takes codes `qs : Finset ℕ` and uses `Real.log q` OF THE CODE — but
ppCode = Nat.pair p m is an interleaved pairing integer, so log(code) ≠ center
(the repo documents this trap at PrimePotentialDecodedCenter.lean). The dense
observable is therefore defined pairs-indexed with q.center explicitly; same
E1 entrywise shape, η = 0 baked in. Also pins: K_n(u,s) = (1/L)·spikeTransform
(GPT's 2τ(D_s T(u)) kernel), the normalization 2·densePaired = P^gal, and
galerkinLam = galerkinFreeMu (rfl) for B4.
-/

import RHFormalization.DenseGalerkinStage
import RHFormalization.TiltedEnergyDefinitions
import RHFormalization.GalerkinOneLetterNormalizationLock
import RHFormalization.DenseDefectLocBdd

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- **Dense zero-tilt centered entry** (pairs-indexed, correct centers):
`Σ_q w(q)·T(q.center)_{kj} − ∫₀^R e^{u/2}·T(u)_{kj} du`. -/
def denseCenteredEntry (n : ℕ) (k j : Fin (denseN n)) : ℝ :=
  (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightReal * galerkinT (N := denseN n) (denseL n) q.center k j)
    - ∫ u in (0:ℝ)..(admR n),
        Real.exp (u / 2) * galerkinT (N := denseN n) (denseL n) u k j

/-- **Dense centered matrix** `C_n`, assembled entrywise. -/
def denseCenteredMatrix (n : ℕ) : Matrix (Fin (denseN n)) (Fin (denseN n)) ℝ :=
  fun k j => denseCenteredEntry n k j

theorem denseCenteredMatrix_apply (n : ℕ) (k j : Fin (denseN n)) :
    denseCenteredMatrix n k j = denseCenteredEntry n k j := rfl

/-- **GPT's pinned finite kernel**: `K_n(u,s) := 2τ_n(D_s T(u)) =
(1/L)·galerkinSpikeTransform(u)`. Definitionally the diagonal trace pairing. -/
def denseKernelN (n : ℕ) (u : ℝ) (s : ℂ) : ℂ :=
  ((1 / denseL n : ℝ) : ℂ) *
    galerkinSpikeTransform (N := denseN n)
      (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s

/-- The spike transform IS the diagonal trace pairing (definitional pin). -/
theorem galerkinSpikeTransform_eq_diag_pairing (n : ℕ) (u : ℝ) (s : ℂ) :
    galerkinSpikeTransform (N := denseN n)
        (fun m => galerkinLam (denseL n) (m : ℕ)) (denseL n) u s
      = ∑ m : Fin (denseN n),
          ((galerkinT (N := denseN n) (denseL n) u m m : ℝ) : ℂ) *
            (1 / (s + (1/4 : ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ))) := rfl

/-- **B4 pin (GPT amendment)**: the diagonal eigenvalues and the free-μ
sequence are the same formula. -/
theorem galerkinLam_eq_freeMu (n : ℕ) (m : Fin (denseN n)) :
    galerkinLam (denseL n) (m : ℕ) = galerkinFreeMu (denseN n) (denseL n) m := rfl

/-- **Normalization lemma**: `2·denseFreePairedTransform = P^gal
= Σ_q w(q)·K_n(q.center, s)` — the factor convention pinned exactly. -/
theorem two_densePaired_eq_Pgal (n : ℕ) (s : ℂ) :
    (2 : ℂ) * denseFreePairedTransform n s
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightC * denseKernelN n q.center s := by
  have hL0 : denseL n ≠ 0 := (denseL_pos n).ne'
  unfold denseFreePairedTransform decodedOneLetterTransform denseKernelN
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hcast : (2 : ℂ) * ((1 / (2 * denseL n) : ℝ) : ℂ)
      = ((1 / denseL n : ℝ) : ℂ) := by
    push_cast
    field_simp
  first
    | (rw [← mul_assoc, ← mul_assoc, hcast]; ring)
    | (push_cast; field_simp; ring)
    | ring_nf

#print axioms denseCenteredMatrix_apply
#print axioms galerkinSpikeTransform_eq_diag_pairing
#print axioms galerkinLam_eq_freeMu
#print axioms two_densePaired_eq_Pgal

end

end RHFormalization
