import RHFormalization.DBFFCompensator
import RHFormalization.DecodedWindowCorrectionBound

/-!
# DBFFDecodedProfiles — P2-1: the fixed J_free profile shapes (D.BFF)

ROUTE CARD
1. Target: the fixed Ω-holomorphic profile shapes of D.BULK-FINITE-FORM at
   the decoded stage. This file: the J_free compensator shape + the exact
   factorization `compensatorM n = expFactor n · shape`.
2. J_env = J_left = 0 at the decoded stage: the frozen operator confines by
   the Dirichlet box (`galerkinLam L m = ((m+1)π/L)²`); the manuscript marks
   the confinement choice as not load-bearing (§2.2/§2.7, Appendix A).
3. Raw B on Ω? NO. B_stage − M targeted as a Prop? NO (frozen rule 4): the
   compensated object is bounded ONLY via the profile expansion (P2-3/P2-5).
4. Consumer: P2-3 decomposition identity (D.BFF.1) for `DBFFO3CompensatedB`.
5. Manuscript: Theorem D.BULK-FINITE-FORM (D.BFF.1, profile classes).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **J_free pole-factor shape**: `(1/2 − √(s+1/4))⁻¹`, fixed, α-free. -/
def bulkProfilePoleFactor (s : ℂ) : ℂ :=
  ((1/2 : ℂ) - Complex.sqrt (s + (1/4:ℂ)))⁻¹

/-- **THE J_free compensator shape**: `(2√(s+1/4))⁻¹ · (1/2 − √(s+1/4))⁻¹`,
fixed, α-free — the profile Φ whose stage coefficient carries all
`admR n` dependence. -/
def bulkProfileFreeM (s : ℂ) : ℂ :=
  invSqrtFactor s * bulkProfilePoleFactor s

/-- **The stage exponential factor** of the compensator. -/
def bulkProfileExpFactor (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * (admR n : ℝ))

/-- **P2-1 FACTORIZATION**: the compensator is exactly
`expFactor n · Φ_free` — all stage dependence in the scalar front factor,
the profile fixed. -/
theorem compensatorM_eq_expFactor_mul_profile (n : ℕ) (s : ℂ) :
    compensatorM n s = bulkProfileExpFactor n s * bulkProfileFreeM s := by
  unfold compensatorM bulkProfileExpFactor bulkProfileFreeM
    bulkProfilePoleFactor invSqrtFactor
  first
    | ring
    | (field_simp ; ring)

/-- The pole factor is analytic at every point of Ω. -/
theorem bulkProfilePoleFactor_analyticAt {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ bulkProfilePoleFactor z := by
  have hsqrt : AnalyticAt ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) z :=
    sqrtShiftFun_analyticAt hz
  have hsub : AnalyticAt ℂ
      (fun s : ℂ => (1/2 : ℂ) - Complex.sqrt (s + (1/4:ℂ))) z :=
    analyticAt_const.sub hsqrt
  have hne : (1/2 : ℂ) - Complex.sqrt (z + (1/4:ℂ)) ≠ 0 := by
    first
      | exact sub_ne_zero_of_ne (Ne.symm (sqrt_ne_half hz))
      | exact sub_ne_zero.mpr (Ne.symm (sqrt_ne_half hz))
  have hinv : AnalyticAt ℂ
      (fun s : ℂ => ((1/2 : ℂ) - Complex.sqrt (s + (1/4:ℂ)))⁻¹) z :=
    hsub.inv hne
  exact hinv

/-- The full J_free compensator shape is analytic at every point of Ω. -/
theorem bulkProfileFreeM_analyticAt {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ bulkProfileFreeM z := by
  have hsqrt : AnalyticAt ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) z :=
    sqrtShiftFun_analyticAt hz
  have hmul : AnalyticAt ℂ
      (fun s : ℂ => (2:ℂ) * Complex.sqrt (s + (1/4:ℂ))) z :=
    analyticAt_const.mul hsqrt
  have hne2 : (2:ℂ) * Complex.sqrt (z + (1/4:ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (sqrt_ne_zero' hz)
  have hinvS : AnalyticAt ℂ invSqrtFactor z := by
    have h := hmul.inv hne2
    first
      | exact h
      | simpa [invSqrtFactor] using h
  exact hinvS.mul (bulkProfilePoleFactor_analyticAt hz)

/-- **Ω-holomorphy of the J_free profile shape** (D.BFF Φ ∈ O(Ω)). -/
theorem bulkProfileFreeM_holo : HolomorphicOnC bulkProfileFreeM Ω := by
  intro z hz
  exact (bulkProfileFreeM_analyticAt hz).analyticWithinAt

/-- Ω-holomorphy of the pole factor. -/
theorem bulkProfilePoleFactor_holo : HolomorphicOnC bulkProfilePoleFactor Ω := by
  intro z hz
  exact (bulkProfilePoleFactor_analyticAt hz).analyticWithinAt

#print axioms compensatorM_eq_expFactor_mul_profile
#print axioms bulkProfilePoleFactor_analyticAt
#print axioms bulkProfileFreeM_analyticAt
#print axioms bulkProfileFreeM_holo
#print axioms bulkProfilePoleFactor_holo

end

end RHFormalization
