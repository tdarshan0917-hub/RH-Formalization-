import RHFormalization.AdaptiveCombinedFreeR
import Mathlib

/-!
# AdaptiveCombinedSectorAssembly — indexed four-sector assembly for Hcomb

The generic three-sector builder is wrapped around a fixed-μ aligned layer
(type-incompatible with the varying `adaptiveN c n`); we reuse only its
triangle-inequality pattern, indexed by ℕ, targeting the COMBINED object
`adaptiveCombinedFreeR` (where the compensator/free cancellation happens
before norms), with a fourth window/bulk sector unless a proved identity
later absorbs it.

Contents:
- D.ADM fuel: `adaptiveDensityAnchor ∈ [0,1]` from the banked certificate;
- `adaptive_combined_bound_from_four_sectors` (per-sector compact constants);
- anchor-factored variant for the local sector's natural D.LOC shape;
- end-to-end: four sector bounds + HshortA ⇒ `DBFFO3CompensatedBBound`.

Everything here is bookkeeping. The analytic content lives in the four
concrete sector providers and the exact decomposition identity, next.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology BigOperators

/-- The density-normalized D.ADM anchor at the adaptive stage. -/
def adaptiveDensityAnchor (c : ℝ) (n : ℕ) : ℝ :=
  adaptiveAnchor c n / (2 * adaptiveL c n)

theorem adaptiveDensityAnchor_nonneg (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ adaptiveDensityAnchor c n := by
  unfold adaptiveDensityAnchor adaptiveAnchor
  have hnum : 0 ≤ decodedAdmissibleLocalAnchor 1 (admR n) c :=
    decodedAnchor_nonneg_live (admR n) c hc
  have hden : 0 ≤ 2 * adaptiveL c n := by
    have := adaptiveL_pos c n
    linarith
  exact div_nonneg hnum hden

/-- **The D.ADM certificate as sector fuel**: the density anchor is ≤ 1 at
every stage. -/
theorem adaptiveDensityAnchor_le_one (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    adaptiveDensityAnchor c n ≤ 1 :=
  adaptiveGalerkinStage_DADM c hc n

/-- **Indexed four-sector assembly, per-sector constants**: an exact
decomposition of the combined object plus compact-uniform bounds on the four
sectors give Hcomb. -/
theorem adaptive_combined_bound_from_four_sectors
    (c : ℝ)
    (Qloc Qdisp Rtail Qwindow : ℕ → ℂ → ℂ)
    (h_decomp : ∀ n : ℕ, ∀ s : ℂ, s ∈ Ω →
        adaptiveCombinedFreeR c n s
          = Qloc n s + Qdisp n s + Rtail n s + Qwindow n s)
    (h_loc_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cl : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Qloc n s‖ ≤ Cl)
    (h_disp_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cd : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Qdisp n s‖ ≤ Cd)
    (h_tail_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Ct : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Rtail n s‖ ≤ Ct)
    (h_window_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cw : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Qwindow n s‖ ≤ Cw) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cc : ℝ, ∀ n : ℕ, ∀ s ∈ K,
        ‖adaptiveCombinedFreeR c n s‖ ≤ Cc := by
  intro K hK hKO
  obtain ⟨Cl, hl⟩ := h_loc_le K hK hKO
  obtain ⟨Cd, hd⟩ := h_disp_le K hK hKO
  obtain ⟨Ct, ht⟩ := h_tail_le K hK hKO
  obtain ⟨Cw, hw⟩ := h_window_le K hK hKO
  refine ⟨Cl + Cd + Ct + Cw, ?_⟩
  intro n s hs
  rw [h_decomp n s (hKO hs)]
  have h1 : ‖Qloc n s + Qdisp n s + Rtail n s + Qwindow n s‖
      ≤ ‖Qloc n s + Qdisp n s + Rtail n s‖ + ‖Qwindow n s‖ :=
    norm_add_le _ _
  have h2 : ‖Qloc n s + Qdisp n s + Rtail n s‖
      ≤ ‖Qloc n s + Qdisp n s‖ + ‖Rtail n s‖ :=
    norm_add_le _ _
  have h3 : ‖Qloc n s + Qdisp n s‖ ≤ ‖Qloc n s‖ + ‖Qdisp n s‖ :=
    norm_add_le _ _
  have hl' := hl n s hs
  have hd' := hd n s hs
  have ht' := ht n s hs
  have hw' := hw n s hs
  linarith

/-- Anchor-factored sector bound converter: the D.LOC natural shape
`‖Q n s‖ ≤ anchor n · factor K` with the D.ADM certificate `anchor ≤ 1`
yields the per-sector-constant shape. -/
theorem sector_bound_of_anchor_factored
    (Q : ℕ → ℂ → ℂ) (anchor : ℕ → ℝ)
    (h_anchor_le_one : ∀ n, anchor n ≤ 1)
    (h_fact : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ F : ℝ, 0 ≤ F ∧ ∀ n : ℕ, ∀ s ∈ K, ‖Q n s‖ ≤ anchor n * F) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Q n s‖ ≤ C := by
  intro K hK hKO
  obtain ⟨F, hF0, hF⟩ := h_fact K hK hKO
  refine ⟨F, ?_⟩
  intro n s hs
  calc ‖Q n s‖ ≤ anchor n * F := hF n s hs
    _ ≤ 1 * F := mul_le_mul_of_nonneg_right (h_anchor_le_one n) hF0
    _ = F := one_mul F

/-- **End-to-end**: four sector bounds + decomposition + HshortA give the
O3 layer's exact input Prop. -/
theorem adaptive_compensatedB_bounded_from_four_sectors
    (c : ℝ)
    (Qloc Qdisp Rtail Qwindow : ℕ → ℂ → ℂ)
    (h_decomp : ∀ n : ℕ, ∀ s : ℂ, s ∈ Ω →
        adaptiveCombinedFreeR c n s
          = Qloc n s + Qdisp n s + Rtail n s + Qwindow n s)
    (h_loc_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cl : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Qloc n s‖ ≤ Cl)
    (h_disp_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cd : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Qdisp n s‖ ≤ Cd)
    (h_tail_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Ct : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Rtail n s‖ ≤ Ct)
    (h_window_le : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cw : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖Qwindow n s‖ ≤ Cw)
    (HshortA :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cs : ℝ, ∀ n : ℕ, ∀ s ∈ K,
          ‖adaptiveShortResidual c n s‖ ≤ Cs) :
    DBFFO3CompensatedBBound :=
  adaptive_compensatedB_bounded_from_combined c
    (adaptive_combined_bound_from_four_sectors c
      Qloc Qdisp Rtail Qwindow
      h_decomp h_loc_le h_disp_le h_tail_le h_window_le)
    HshortA

#print axioms adaptiveDensityAnchor_le_one
#print axioms adaptive_combined_bound_from_four_sectors
#print axioms sector_bound_of_anchor_factored
#print axioms adaptive_compensatedB_bounded_from_four_sectors

end

end RHFormalization
