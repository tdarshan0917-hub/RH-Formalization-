import RHFormalization.AdmissibleBOmegaForced
import RHFormalization.AdmissibleRStageHolo
import RHFormalization.MontelSubsequenceAssembly

/-!
# `hBconv` from Montel: RH from B-side LOCAL BOUNDEDNESS + Ascoli

Applying the banked Montel subsequence assembly to the B-stage family along
the admissible net.  Banked inputs: per-stage holomorphy
(`galerkinStagePackage_B_stage_holo_admissible`) and overlap pointwise
convergence on `RightHalfPlane 1` (`admissible_hB`).  Remaining inputs:

* `Bω` holomorphic on Ω agreeing with the canonical limit on the overlap
  (the manuscript's continued pole-package object);
* **local boundedness of the B-stages on Ω-compacts** — the S(t,R)
  density-normalized anchor estimate (the genuine analytic gap);
* `AscoliExtraction` — standard Arzelà–Ascoli, already reduced elsewhere to
  the single BOXED obligation (no RH content).

Endpoint: `RH_from_admissible_B_montel`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- The admissible B-stage family (the object Montel is applied to). -/
def admissibleBStageFamily : ℕ → ℂ → ℂ :=
  fun n s => galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s

/-- Per-stage Ω-holomorphy of the family (banked). -/
theorem admissibleBStageFamily_holo (n : ℕ) :
    HolomorphicOnC (admissibleBStageFamily n) Ω :=
  admissible_B_stage_holo n

/-- **RH from B-side local boundedness + Ascoli.**  The Montel engine turns
uniform-on-compact BOUNDEDNESS of the admissible B-stages (plus the standard
Ascoli extraction and the continued overlap object `Bω`) into the full
`hBconv`, closing the V10 chain. -/
theorem RH_from_admissible_B_montel
    (Bω : ℂ → ℂ) (hBω_holo : HolomorphicOnC Bω Ω)
    (hBω_overlap : ∀ s ∈ RightHalfPlane (1 : ℝ),
        Bω s = galerkinBcanLimitData.Bcan s)
    (h_loc_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖admissibleBStageFamily n s‖ ≤ C)
    (h_ascoli : AscoliExtraction admissibleBStageFamily) :
    RiemannHypothesis := by
  have hMontel :=
    holomorphicMontelConvergence_from_ascoli hBω_holo h_ascoli
  -- the overlap set: an open nonempty subset of RHP(1)
  set U : Set ℂ := {z : ℂ | (2 : ℝ) < z.re} with hUdef
  have hUopen : IsOpen U := by
    first
      | exact isOpen_lt continuous_const Complex.continuous_re
      | (rw [hUdef]; exact isOpen_lt continuous_const Complex.continuous_re)
  have hUne : U.Nonempty := by
    refine ⟨((3 : ℝ) : ℂ), ?_⟩
    show (2 : ℝ) < ((3 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    norm_num
  have hU_sub_RHP : U ⊆ RightHalfPlane (1 : ℝ) := by
    intro z hz
    have h2 : (2 : ℝ) < z.re := hz
    first
      | (show (1 : ℝ) < z.re
         linarith)
      | (show (1 : ℝ) ≤ z.re
         linarith)
      | (unfold RightHalfPlane
         show (1 : ℝ) < z.re
         linarith)
      | (unfold RightHalfPlane
         simp only [Set.mem_setOf_eq]
         linarith)
      | (simp only [RightHalfPlane, Set.mem_setOf_eq]
         linarith)
  have hRHP_sub_Omega : RightHalfPlane (1 : ℝ) ⊆ Ω := by
    first
      | exact rightHalfPlane_subset_Omega (1 : ℝ) (by norm_num)
      | exact rightHalfPlane_subset_Omega 1 one_pos
      | exact rightHalfPlane_subset_Omega _ (by norm_num)
  have hU_sub_Omega : U ⊆ Ω := fun z hz => hRHP_sub_Omega (hU_sub_RHP hz)
  have hUconv : ∀ z ∈ U,
      Tendsto (fun n => admissibleBStageFamily n z) atTop (𝓝 (Bω z)) := by
    intro z hz
    have hzR : z ∈ RightHalfPlane (1 : ℝ) := hU_sub_RHP hz
    rw [hBω_overlap z hzR]
    exact admissible_hB z hzR
  have hBconv := hMontel admissibleBStageFamily_holo h_loc_bdd
    ⟨U, hUopen, hUne, hU_sub_Omega, hUconv⟩
  exact RH_from_admissible_B_conv Bω hBω_holo hBconv

#print axioms admissibleBStageFamily_holo
#print axioms RH_from_admissible_B_montel

end

end RHFormalization
