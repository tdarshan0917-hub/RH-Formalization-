import RHFormalization.AdmissibleSecondResolventIdentity

/-!
# RHFormalization.AdmissiblePrimeFirstOrderSplit

**Front F-adm, brick 3b-iii.** The manuscript-faithful finite split of the
prime layer (GPT Gate 2 layering, sign explicit):

  `FadmPrimeStage n s = FirstOrderWindow n s + SecondResolventResidual n s`

with `FirstOrderWindow := −admDensityC·Tr(R_D V R_D)` (the MINUS is part of
the definition — NOT identified with `B_stage` here; that comparison is the
WindowError front) and `SecondResolventResidual := +admDensityC·Tr(R_D V R_H V R_D)`
(combined, hQint discipline). Everything at the shifted point `s + SupVConst`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module

/-- Shift lemma: adding `M` to every eigenvalue = shifting the argument. -/
theorem FstageFinite_shift {N : ℕ} (lam : Fin N → ℝ) (M : ℝ) (s : ℂ) :
    FstageFinite (fun i => lam i + M) s = FstageFinite lam (s + (M : ℂ)) := by
  unfold FstageFinite
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  push_cast
  ring

/-- Shift lemma, commuted form (matches 2b-i's free slot `SupV + μ`). -/
theorem FstageFinite_comm_shift {N : ℕ} (lam : Fin N → ℝ) (M : ℝ) (s : ℂ) :
    FstageFinite (fun i => M + lam i) s = FstageFinite lam (s + (M : ℂ)) := by
  unfold FstageFinite
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  push_cast
  ring

/-- **FirstOrderWindow** (sign carried in the definition): the density-normalized
first-order resolvent trace `−admDensityC·Tr(R_D V R_D)` at `s + SupVConst`. -/
def FirstOrderWindow (n : ℕ) (s : ℂ) : ℂ :=
  -(admDensityC n *
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
      (freeResolventOpE (galerkinFreeMu (admN n) (admL n)) (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (galerkinVC (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
        * freeResolventOpE (galerkinFreeMu (admN n) (admL n)) (s + (SupVConst : ℂ))))

/-- **SecondResolventResidual** (combined, positive orientation):
`+admDensityC·Tr(R_D V R_H V R_D)` at `s + SupVConst`. -/
def SecondResolventResidual (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n *
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
      (freeResolventOpE (galerkinFreeMu (admN n) (admL n)) (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (galerkinVC (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
        * perturbedResolventOp (galerkinFreeMu (admN n) (admL n))
            (galerkinVC_isHermitian (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
            (s + (SupVConst : ℂ))
        * Matrix.toEuclideanLin
            (galerkinVC (N := admN n) 1
              (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
        * freeResolventOpE (galerkinFreeMu (admN n) (admL n)) (s + (SupVConst : ℂ)))

/-- **BRICK 3b-iii: the finite manuscript-faithful split.** -/
theorem FadmPrimeStage_eq_first_plus_second (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    FadmPrimeStage n s
      = FirstOrderWindow n s + SecondResolventResidual n s := by
  set μ := galerkinFreeMu (admN n) (admL n) with hμdef
  set hV := galerkinVC_isHermitian (N := admN n) 1
    (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n)
    with hVdef
  set w : ℂ := s + (SupVConst : ℂ) with hwdef
  have hμnn : ∀ k, 0 ≤ μ k := by
    intro k
    rw [hμdef]
    first
      | exact galerkinFreeMu_nonneg _ _ k
      | (unfold galerkinFreeMu; positivity)
      | exact sq_nonneg _
  have hneF : ∀ i, w + ((μ i : ℝ) : ℂ) ≠ 0 := by
    intro i
    have hcast : w + ((μ i : ℝ) : ℂ)
        = s + ((SupVConst + μ i : ℝ) : ℂ) := by
      rw [hwdef]; push_cast; ring
    rw [hcast]
    first
      | exact add_real_ne_zero_of_mem_Omega hs
          (add_nonneg SupVConst_nonneg_adm (hμnn i))
      | (intro h0
         obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact {s}
           isCompact_singleton (Set.singleton_subset_iff.mpr hs)
         have h := hδ s (Set.mem_singleton s) (SupVConst + μ i)
           (add_nonneg SupVConst_nonneg_adm (hμnn i))
         rw [h0, norm_zero] at h
         linarith)
  have hneP : ∀ i, w + ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0 := by
    intro i
    have hlamnn : 0 ≤ perturbedEigenvalues μ hV i := by
      have h := admissibleEigenvalue_nonneg (admL n) (admL_pos n)
        (activePrimePowerCodesCenterBelow (admR n)) μ hμnn i
      first
        | exact h
        | (rw [hVdef]; exact h)
    have hcast : w + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)
        = s + ((SupVConst + perturbedEigenvalues μ hV i : ℝ) : ℂ) := by
      rw [hwdef]; push_cast; ring
    rw [hcast]
    first
      | exact add_real_ne_zero_of_mem_Omega hs
          (add_nonneg SupVConst_nonneg_adm hlamnn)
      | (intro h0
         obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact {s}
           isCompact_singleton (Set.singleton_subset_iff.mpr hs)
         have h := hδ s (Set.mem_singleton s) (SupVConst + perturbedEigenvalues μ hV i)
           (add_nonneg SupVConst_nonneg_adm hlamnn)
         rw [h0, norm_zero] at h
         linarith)
  have hstep1 : FadmPrimeStage n s
      = admDensityC n *
          (FstageFinite (perturbedEigenvalues μ hV) w - FstageFinite μ w) := by
    rw [FadmPrimeStage_eq_trace_diff n s]
    have e1 : FstageFinite (fun i => admPerturbedLam n i + SupVConst) s
        = FstageFinite (perturbedEigenvalues μ hV) w := by
      rw [FstageFinite_shift (admPerturbedLam n) SupVConst s]
      first
        | rfl
        | (unfold admPerturbedLam; rw [hμdef, hVdef, hwdef])
        | (congr 1)
    have e2 : FstageFinite
          (fun i : Fin (admN n) => SupVConst + galerkinFreeMu (admN n) (admL n) i) s
        = FstageFinite μ w := by
      rw [FstageFinite_comm_shift (galerkinFreeMu (admN n) (admL n)) SupVConst s]
    rw [e1, e2]
  have hRHtr : FstageFinite (perturbedEigenvalues μ hV) w
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
          (perturbedResolventOp μ hV w) :=
    (perturbedResolventOp_trace μ hV w).symm
  have hRDtr : FstageFinite μ w
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (admN n)))
          (freeResolventOpE μ w) :=
    (freeResolventOpE_trace μ w).symm
  rw [hstep1, hRHtr, hRDtr, ← map_sub,
    resolvent_sub_eq_first_plus_second μ hV w hneF hneP,
    map_add, map_neg]
  unfold FirstOrderWindow SecondResolventResidual
  first
    | ring
    | (rw [← hμdef, ← hwdef]; ring)
    | (rw [← hμdef]; ring)
    | (push_cast; ring)
    | rfl

#print axioms FstageFinite_shift
#print axioms FstageFinite_comm_shift
#print axioms FadmPrimeStage_eq_first_plus_second

end

end RHFormalization
