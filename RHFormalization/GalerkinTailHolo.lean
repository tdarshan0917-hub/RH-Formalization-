import RHFormalization.GalerkinFTailBound
import RHFormalization.ResolventTraceHolo
import RHFormalization.BSideHeatKernelLaplaceEnvelope
import Mathlib

/-!
# GalerkinTailHolo — Ω-holomorphy of the closed-form F-tail

ROUTE CARD
1. Target: the closed-form F-tail `galFTailClosed n` is `HolomorphicOnC … Ω`,
   and equals `∫_{Ioi t₀} galFIntegrand n s` on RHP(0).
2. Objects: `galF_tail_eq_resolvent_sum` (banked), `resolvent_term_holo_on_Omega`
   (banked), `AnalyticAt.cexp`, `Finset.analyticOn_fun_sum`, `analyticOn_const.mul`.
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.ANCHOR — the closed form continues to Ω; the *integral*
   representation only holds on the half-plane.
7. Consumer: head-holomorphy (`head = R_stage − tail`); thence Montel on the head.

WHY DEFINE THE CLOSED FORM SEPARATELY. `∫_{Ioi t₀} galFIntegrand n s` only
converges for `Re s > 0`. Its value there, `admDensityC n · ∑ᵢ e^{-t₀(s+μᵢ)}/(s+μᵢ)`,
is holomorphic on all of Ω (poles at `s = -μᵢ ≤ 0`, off the slit plane). So the
closed form IS the analytic continuation, definitionally — no identity theorem needed.

NOT PROVED HERE, AND DELIBERATELY SO. There is no `n`-uniform bound on the B-tail
`∫_{Ioi t₀} galBIntegrand`. Its `q`-sum has mass `∑_{q ≤ e^{admR n}} Λ(q)/√q ≍ 2 e^{admR n /2}`,
and for `t ≥ t₀` the Gaussian supplies no decay. By `B_sub_compensator_eq` +
`galerkin_B_stage_eq_vonMangoldt_partial_sum`, an `n`-uniform B-side bound at parabola
depth IS `DBFFO3ParabolaDepthHstar`. Bounding the B-tail is not a step toward O3;
it is O3. See §5 of the handoff: reduction mirage.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory
open scoped BigOperators

/-- The shifted eigenvalue of the admissible stage. -/
noncomputable def admMu (n : ℕ) (i : Fin (admN n)) : ℝ :=
  admPerturbedLam n i + SupVConst

theorem admMu_nonneg (n : ℕ) (i : Fin (admN n)) : (0:ℝ) ≤ admMu n i :=
  admShiftedLam_nonneg' n i

/-- **The closed-form F-tail.** Defined on all of `ℂ`; holomorphic on `Ω`. -/
noncomputable def galFTailClosed (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n * ∑ i : Fin (admN n),
    Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (spikeT0:ℂ))
      / (s + ((admMu n i : ℝ) : ℂ))

/-- One resolvent term of the closed-form tail is `Ω`-holomorphic. -/
theorem galFTail_term_holo (n : ℕ) (i : Fin (admN n)) :
    HolomorphicOnC
      (fun s => Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (spikeT0:ℂ))
        / (s + ((admMu n i : ℝ) : ℂ))) Ω := by
  have hres := resolvent_term_holo_on_Omega _ (admMu_nonneg n i)
  intro z hz
  have hexp : AnalyticAt ℂ
      (fun s : ℂ => Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (spikeT0:ℂ))) z := by
    apply AnalyticAt.cexp; fun_prop
  have hmul := hexp.analyticWithinAt.mul (hres z hz)
  simpa only [div_eq_mul_inv] using hmul

/-- **THE CLOSED-FORM F-TAIL IS Ω-HOLOMORPHIC.** No half-plane. -/
theorem galFTailClosed_holo (n : ℕ) :
    HolomorphicOnC (galFTailClosed n) Ω := by
  have hsum : HolomorphicOnC
      (fun s => ∑ i : Fin (admN n),
        Complex.exp (-(s + ((admMu n i : ℝ) : ℂ)) * (spikeT0:ℂ))
          / (s + ((admMu n i : ℝ) : ℂ))) Ω :=
    Finset.analyticOn_fun_sum Finset.univ (fun i _ => galFTail_term_holo n i)
  unfold galFTailClosed
  intro z hz
  exact (analyticWithinAt_const).mul (hsum z hz)

/-- On RHP(0), the closed form equals the F-tail integral. -/
theorem galFTailClosed_eq_integral (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galFTailClosed n s = ∫ t in Set.Ioi spikeT0, galFIntegrand n s t := by
  rw [galF_tail_eq_resolvent_sum n s hs]
  rfl

/-- The F-tail integral, on RHP(0), inherits the closed-form bound. -/
theorem galFTailClosed_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) (hne : K.Nonempty) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ (n : ℕ), ∀ s ∈ K, 0 < s.re →
      ‖galFTailClosed n s‖ ≤ Ctail := by
  obtain ⟨C, hC0, hbd⟩ := galF_tail_uniform_bound K hK hKO hne
  refine ⟨C, hC0, fun n s hs hsre => ?_⟩
  rw [galFTailClosed_eq_integral n s hsre]
  exact hbd n s hs hsre

#print axioms admMu_nonneg
#print axioms galFTail_term_holo
#print axioms galFTailClosed_holo
#print axioms galFTailClosed_eq_integral
#print axioms galFTailClosed_uniform_bound

end RHFormalization
