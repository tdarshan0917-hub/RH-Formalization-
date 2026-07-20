import RHFormalization.GalerkinTailHolo

/-!
# FreeSpectralTailClosed — H3: the FREE box spectral tail, closed form

ROUTE CARD
1. Target: the free analogue of galFTailClosed — same shape, FREE box
   spectrum galerkinLam (no spikes) — Ω-holomorphic per stage. This is
   the subtraction object of Htail := lim(perturbed) − lim(free).
2. Consumer: H4 (the title identity at tail level) → HtailExists →
   RH_from_Htail → RiemannHypothesis.
3. Raw B on Ω? NO — purely spectral.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- Shifted FREE box eigenvalue of the admissible stage. -/
noncomputable def admMuFree (n : ℕ) (i : Fin (admN n)) : ℝ :=
  galerkinLam (admL n) (i : ℕ) + SupVConst

theorem admMuFree_nonneg (n : ℕ) (i : Fin (admN n)) : (0:ℝ) ≤ admMuFree n i := by
  unfold admMuFree
  have h1 : (0:ℝ) ≤ galerkinLam (admL n) (i : ℕ) := by
    unfold galerkinLam
    positivity
  have h2 : (0:ℝ) ≤ SupVConst := by
    unfold SupVConst
    first
      | exact tsum_nonneg (fun k => mul_nonneg (abs_nonneg _) (by
          unfold bumpEnvelope
          positivity))
      | exact tsum_nonneg (fun k => mul_nonneg (abs_nonneg _)
          (bumpEnvelope_nonneg k))
      | positivity
  linarith

/-- **The closed-form FREE spectral tail** — free twin of galFTailClosed. -/
noncomputable def freeSpectralTailClosed (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n * ∑ i : Fin (admN n),
    Complex.exp (-(s + ((admMuFree n i : ℝ) : ℂ)) * (spikeT0:ℂ))
      / (s + ((admMuFree n i : ℝ) : ℂ))

/-- One free resolvent term is Ω-holomorphic (clone of the banked pattern). -/
theorem freeSpectralTail_term_holo (n : ℕ) (i : Fin (admN n)) :
    HolomorphicOnC
      (fun s => Complex.exp (-(s + ((admMuFree n i : ℝ) : ℂ)) * (spikeT0:ℂ))
        / (s + ((admMuFree n i : ℝ) : ℂ))) Ω := by
  have hres := resolvent_term_holo_on_Omega _ (admMuFree_nonneg n i)
  intro z hz
  have hexp : AnalyticAt ℂ
      (fun s : ℂ => Complex.exp (-(s + ((admMuFree n i : ℝ) : ℂ)) * (spikeT0:ℂ))) z := by
    apply AnalyticAt.cexp; fun_prop
  have hmul := hexp.analyticWithinAt.mul (hres z hz)
  simpa only [div_eq_mul_inv] using hmul

/-- **The free spectral tail is Ω-holomorphic.** -/
theorem freeSpectralTailClosed_holo (n : ℕ) :
    HolomorphicOnC (freeSpectralTailClosed n) Ω := by
  have hsum : HolomorphicOnC
      (fun s => ∑ i : Fin (admN n),
        Complex.exp (-(s + ((admMuFree n i : ℝ) : ℂ)) * (spikeT0:ℂ))
          / (s + ((admMuFree n i : ℝ) : ℂ))) Ω :=
    Finset.analyticOn_fun_sum Finset.univ (fun i _ => freeSpectralTail_term_holo n i)
  unfold freeSpectralTailClosed
  intro z hz
  exact (analyticWithinAt_const).mul (hsum z hz)

/-- **The per-stage Htail candidate**: perturbed tail minus free tail —
Ω-holomorphic per stage. -/
noncomputable def htailStage (n : ℕ) (s : ℂ) : ℂ :=
  galFTailClosed n s - freeSpectralTailClosed n s

theorem htailStage_holo (n : ℕ) : HolomorphicOnC (htailStage n) Ω := by
  intro z hz
  exact ((galFTailClosed_holo n) z hz).sub ((freeSpectralTailClosed_holo n) z hz)

#print axioms freeSpectralTailClosed_holo
#print axioms htailStage_holo

end

end RHFormalization
