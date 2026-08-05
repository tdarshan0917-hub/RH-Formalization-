import RHFormalization.SpikeSumPrimeReindex
import RHFormalization.BumpMatrixElementErrorBound
import Mathlib

/-!
# PrimeSpikeProfileSplit — the per-prime spike transform in D.BFF profile form

ROUTE CARD
1. Target: EXACT split of the per-prime squared-resolvent transform:
   `primeSpikeResolventSq δ q L s
      = densityPart − oscPart + errPart`, where
   densityPart = (1/L)·Σ(s+λ_m)⁻² (q-INDEPENDENT: the density/main term),
   oscPart = (1/L)·Σ Full(2(m+1))·(s+λ_m)⁻² (Gaussian-suppressed profile:
     Full(j) = cos(jπ log q/L)·e^{−(jπ/L)²δ²/2}, banked closed form),
   errPart = (2/L)·Σ err_m·(s+λ_m)⁻² with err_m defined as the bump-vs-
     closed difference, bounded per-m by banked gaussianDecayBound (B10).
   Uses Full(0) = 1 (unit bump mass; closed form at j=0).
2. Raw B on Ω? NO. B−M bare Prop? NO — exact identity + a banked bound.
3. Consumer: h_expansion of DBFFCorrectedBulkProvider — densityPart is the
   q-independent main-term profile, oscPart the J_loc-class correction,
   errPart the eps-class remainder (decay beats w(q)=Λ(q)/√q). This is the
   D.SPIKE-TRANSFER content at the s-side.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Real
open scoped BigOperators

variable {N : ℕ}

/-- The per-m closed-form error of the diagonal bump element. -/
def primeSpikeErr (δ : ℝ) (q : ℕ) (L : ℝ) (m : ℕ) : ℝ :=
  bumpMatrixElement δ q L (m + 1) (m + 1)
    - ((1/2) - (1/2) * cosBumpIntegralFull δ q L (2 * ((m : ℝ) + 1)))

/-- The q-independent density part: `(1/L)·Σ (s+λ_m)⁻²`. -/
def primeSpikeDensityPart (L : ℝ) (s : ℂ) : ℂ :=
  ((1 / L : ℝ) : ℂ) *
    ∑ m : Fin N, ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹

/-- The Gaussian-suppressed oscillatory part. -/
def primeSpikeOscPart (δ : ℝ) (q : ℕ) (L : ℝ) (s : ℂ) : ℂ :=
  ((1 / L : ℝ) : ℂ) *
    ∑ m : Fin N,
      ((cosBumpIntegralFull δ q L (2 * ((m : ℕ) + 1 : ℝ)) : ℝ) : ℂ) *
        ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹

/-- The error part. -/
def primeSpikeErrPart (δ : ℝ) (q : ℕ) (L : ℝ) (s : ℂ) : ℂ :=
  ((2 / L : ℝ) : ℂ) *
    ∑ m : Fin N,
      ((primeSpikeErr δ q L (m : ℕ) : ℝ) : ℂ) *
        ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹

/-- Full(0) = 1: the bump has unit mass against the zero-frequency cosine. -/
theorem cosBumpIntegralFull_zero (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) :
    cosBumpIntegralFull δ q L 0 = 1 := by
  rw [cosBumpIntegralFull_closed δ hδ q L 0]
  norm_num

/-- **THE PROFILE SPLIT** (exact, every s; needs only δ > 0). -/
theorem primeSpikeResolventSq_eq_split
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (s : ℂ) :
    primeSpikeResolventSq (N := N) δ q L s
      = primeSpikeDensityPart (N := N) L s
        - primeSpikeOscPart (N := N) δ q L s
        + primeSpikeErrPart (N := N) δ q L s := by
  unfold primeSpikeResolventSq primeSpikeDensityPart primeSpikeOscPart
    primeSpikeErrPart
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hb : ((bumpMatrixElement δ q L ((m : ℕ) + 1) ((m : ℕ) + 1) : ℝ) : ℂ)
      = ((1/2 : ℝ) : ℂ)
        - ((1/2 : ℝ) : ℂ) *
            ((cosBumpIntegralFull δ q L (2 * ((m : ℕ) + 1 : ℝ)) : ℝ) : ℂ)
        + ((primeSpikeErr δ q L (m : ℕ) : ℝ) : ℂ) := by
    unfold primeSpikeErr
    push_cast
    ring
  rw [hb]
  push_cast
  ring

/-- **The error is Gaussian-tail small, per m, uniformly in m** (banked B10 +
Full(0)=1). Needs the center inside the box: `0 < log q < L`. -/
theorem primeSpikeErr_abs_le
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (m : ℕ)
    (hq : 0 < Real.log q) (hL : Real.log q < L) :
    ‖primeSpikeErr δ q L m‖ ≤ gaussianDecayBound δ q L := by
  unfold primeSpikeErr
  have h := bumpMatrixElement_sub_closed_norm_le δ hδ q L (m + 1) (m + 1) hq hL
  push_cast at h
  have hfreq0 : ((m : ℝ) + 1) - ((m : ℝ) + 1) = 0 := by ring
  have hfreq2 : ((m : ℝ) + 1) + ((m : ℝ) + 1) = 2 * ((m : ℝ) + 1) := by ring
  rw [hfreq0, hfreq2, cosBumpIntegralFull_zero δ hδ q L] at h
  first
    | exact h
    | (convert h using 3
       ring)
    | (convert h using 2
       ring)
    | (have hgoal : (1/2 : ℝ) - (1/2) * cosBumpIntegralFull δ q L (2 * ((m : ℝ) + 1))
          = (1/2) * 1 - (1/2) * cosBumpIntegralFull δ q L (2 * ((m : ℝ) + 1)) := by
         ring
       rw [hgoal]
       exact h)

#print axioms primeSpikeErr
#print axioms primeSpikeDensityPart
#print axioms primeSpikeOscPart
#print axioms primeSpikeErrPart
#print axioms cosBumpIntegralFull_zero
#print axioms primeSpikeResolventSq_eq_split
#print axioms primeSpikeErr_abs_le
end

end RHFormalization
