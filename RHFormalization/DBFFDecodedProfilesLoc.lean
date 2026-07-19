import RHFormalization.DBFFDecodedProfiles
import RHFormalization.AdaptiveGalerkinDefectGate

/-!
# DBFFDecodedProfilesLoc — P2-1b: the J_loc spike-transform holomorphy

ROUTE CARD
1. Target: Ω-holomorphy of the finite spike transform (Laplace transform of
   the pillar-1 c₁ profile `t·Σ V_mm e^{−tλ_m}`) — the J_loc profile class
   of D.BULK-FINITE-FORM, at generic nonneg spectrum and at the decoded
   adaptive stage.
2. Raw B on Ω? NO. 3. B_stage − M targeted as a Prop? NO.
4. Consumer: P2-3 decomposition identity (D.BFF.1) for DBFFO3CompensatedB.
5. Poles of every term lie on the cut: `s + 1/4 + μ = 0` forces
   `s ∈ (−∞,0]`, hence off Ω — banked `add_real_ne_zero_of_mem_Omega`.
Pin fact honored: `.mul`/`Finset.analyticAt_sum` produce Pi-forms — congr
via `Pi.mul_apply` / `Finset.sum_apply` (DBFFBcorrWindowHolo pattern).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- Per-point analyticity of the finite spike transform on Ω, for any
nonnegative free spectrum. -/
theorem galerkinSpikeTransform_analyticAt {N : ℕ}
    (μ : Fin N → ℝ) (hμ : ∀ m, 0 ≤ μ m) (L a : ℝ)
    {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ (fun s => galerkinSpikeTransform (N := N) μ L a s) z := by
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin N)),
      AnalyticAt ℂ (fun s : ℂ =>
        ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
          (1 / (s + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ)))) z := by
    intro m _
    have hden : AnalyticAt ℂ
        (fun s : ℂ => s + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ)) z :=
      (analyticAt_id.add analyticAt_const).add analyticAt_const
    have hcast : z + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ)
        = z + (((1 / 4 + μ m : ℝ)) : ℂ) := by
      push_cast
      ring
    have hne : z + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ) ≠ 0 := by
      rw [hcast]
      exact add_real_ne_zero_of_mem_Omega hz
        (by have := hμ m ; linarith)
    have hinv : AnalyticAt ℂ
        (fun s : ℂ => (s + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ))⁻¹) z :=
      hden.inv hne
    have hmul : AnalyticAt ℂ
        ((fun _ : ℂ => ((galerkinT (N := N) L a m m : ℝ) : ℂ)) *
          fun s : ℂ => (s + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ))⁻¹) z :=
      analyticAt_const.mul hinv
    refine hmul.congr ?_
    filter_upwards with s
    first
      | simp [Pi.mul_apply, one_div]
      | (simp only [Pi.mul_apply, one_div])
      | (simp only [Pi.mul_apply]
         ring)
  have hsum0 : AnalyticAt ℂ
      (∑ m ∈ (Finset.univ : Finset (Fin N)),
        fun s : ℂ =>
          ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
            (1 / (s + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ)))) z :=
    Finset.analyticAt_sum (Finset.univ : Finset (Fin N)) hterm
  refine hsum0.congr ?_
  filter_upwards with s
  first
    | simp [galerkinSpikeTransform, Finset.sum_apply]
    | (simp only [Finset.sum_apply]
       rfl)
    | rfl

/-- The decoded free spectrum is nonnegative. -/
theorem galerkinLam_nonneg (L : ℝ) (m : ℕ) : 0 ≤ galerkinLam L m := by
  unfold galerkinLam
  first
    | exact sq_nonneg _
    | positivity

/-- **Ω-holomorphy of the J_loc profile at the decoded stage**: the spike
transform at box spectrum `galerkinLam (adaptiveL c n)`, any center. -/
theorem decodedSpikeTransform_holo (c : ℝ) (n : ℕ) (a : ℝ) :
    HolomorphicOnC
      (fun s => galerkinSpikeTransform (N := adaptiveN c n)
        (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
        (adaptiveL c n) a s) Ω := by
  intro z hz
  exact (galerkinSpikeTransform_analyticAt
    (fun m => galerkinLam (adaptiveL c n) (m : ℕ))
    (fun m => galerkinLam_nonneg (adaptiveL c n) (m : ℕ))
    (adaptiveL c n) a hz).analyticWithinAt

#print axioms galerkinSpikeTransform_analyticAt
#print axioms galerkinLam_nonneg
#print axioms decodedSpikeTransform_holo

end

end RHFormalization
