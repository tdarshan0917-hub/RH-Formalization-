import RHFormalization.PrimePerturbedOperatorLayerAligned
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.ResolventStageFinsetAtTop
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.PrimePerturbedPayload
import RHFormalization.PrimePowerCutoffCardDivergence
import RHFormalization.DFHLimitConcrete
import RHFormalization.PrimePerturbedFStage
import RHFormalization.PrimeAlignedOverlapFromFAndB
import RHFormalization.ArithmeticShiftedLaplaceBStageConvergence
import RHFormalization.ArithmeticShiftedLaplaceBStageFiniteCanonical
import RHFormalization.ShiftedLaplaceModelPackageProbe
import RHFormalization.DesignedRCutoffS
import RHFormalization.HalfPlaneGeometry
import Mathlib

set_option autoImplicit false

/-!
# Eventual constancy of the aligned stage active-index set.

N FIXED. activeIdx n (the Fin N indices on at stage n) is monotone (banked
concretePrimePowerBelowCutoff_mono). Each index, once on, stays on. Taking the
finite sup over Fin N of per-index activation thresholds gives a stage past which
activeIdx is constant -- the core fact behind h_F_stage_to_FH.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Finset

variable {N : Nat}

/-- The Fin N indices active at stage n. -/
def activeIdx (n : Nat) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => i.val ∈ ppStageCodes n)

theorem ppStageCodes_mono {a b : Nat} (hab : a <= b) :
    ppStageCodes a ⊆ ppStageCodes b := by
  unfold ppStageCodes
  apply Finset.image_subset_image
  apply concretePrimePowerBelowCutoff_mono
  have : (a : Real) <= (b : Real) := by exact_mod_cast hab
  linarith

theorem activeIdx_mono : Monotone (activeIdx (N := N)) := by
  intro a b hab i hi
  simp only [activeIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ppStageCodes_mono hab hi

/-- Once an index is active it stays active (membership monotone). -/
theorem mem_activeIdx_mono {i : Fin N} {a b : Nat} (hab : a <= b)
    (hi : i ∈ activeIdx (N := N) a) : i ∈ activeIdx (N := N) b :=
  activeIdx_mono hab hi

open Classical in
/-- The stage at which index i first activates, if it ever does (0 otherwise). -/
noncomputable def activationStage (i : Fin N) : Nat :=
  if h : ∃ n, i ∈ activeIdx (N := N) n then Nat.find h else 0

open Classical in
theorem activationStage_eq_find {i : Fin N} (hex : ∃ m, i ∈ activeIdx (N := N) m) :
    activationStage (N := N) i = Nat.find hex := by
  unfold activationStage
  rw [dif_pos hex]

open Classical in
theorem mem_activeIdx_of_activationStage_le {i : Fin N} {n : Nat}
    (hex : ∃ m, i ∈ activeIdx (N := N) m)
    (hle : activationStage (N := N) i <= n) :
    i ∈ activeIdx (N := N) n := by
  have hfind : i ∈ activeIdx (N := N) (Nat.find hex) := Nat.find_spec hex
  rw [activationStage_eq_find hex] at hle
  exact mem_activeIdx_mono hle hfind

/-- **Eventual constancy.** Past the sup of all activation stages, activeIdx is constant. -/
theorem activeIdx_eventually_const :
    ∃ NN : Nat, ∀ n : Nat, NN <= n -> activeIdx (N := N) n = activeIdx (N := N) NN := by
  classical
  set NN : Nat := Finset.univ.sup (fun i : Fin N => activationStage (N := N) i) with hNN
  refine ⟨NN, ?_⟩
  intro n hn
  apply Finset.Subset.antisymm
  · -- activeIdx n SUBSET activeIdx NN: every i active at n is active at NN
    intro i hi
    have hex : ∃ m, i ∈ activeIdx (N := N) m := ⟨n, hi⟩
    have hle : activationStage (N := N) i <= NN := Finset.le_sup (Finset.mem_univ i)
    exact mem_activeIdx_of_activationStage_le hex hle
  · -- activeIdx NN SUBSET activeIdx n: monotone since NN <= n
    exact activeIdx_mono hn

/-- Membership in activeIdx is exactly i.val in ppStageCodes. -/
theorem mem_activeIdx_iff {n : Nat} {i : Fin N} :
    i ∈ activeIdx (N := N) n ↔ i.val ∈ ppStageCodes n := by
  simp [activeIdx]

/-- **The prime stage weights are eventually constant.** Past NN (where activeIdx
stabilizes), primeStageWeights n = primeStageWeights NN as functions Fin N -> Real. -/
theorem primeStageWeights_eventually_const :
    ∃ NN : Nat, ∀ n : Nat, NN <= n ->
      primeStageWeights (N := N) n = primeStageWeights (N := N) NN := by
  obtain ⟨NN, hNN⟩ := activeIdx_eventually_const (N := N)
  refine ⟨NN, ?_⟩
  intro n hn
  funext i
  -- i.val in ppStageCodes n  iff  i in activeIdx n  iff  i in activeIdx NN  iff  i.val in ppStageCodes NN
  by_cases hi : i.val ∈ ppStageCodes n
  · have hiA : i ∈ activeIdx (N := N) n := mem_activeIdx_iff.mpr hi
    have hiANN : i ∈ activeIdx (N := N) NN := by rw [hNN n hn] at hiA; exact hiA
    have hiNN : i.val ∈ ppStageCodes NN := mem_activeIdx_iff.mp hiANN
    rw [primeStageWeights_active n i hi, primeStageWeights_active NN i hiNN]
  · have hiA : i ∉ activeIdx (N := N) n := fun h => hi (mem_activeIdx_iff.mp h)
    have hiANN : i ∉ activeIdx (N := N) NN := by rw [hNN n hn] at hiA; exact hiA
    have hiNN : i.val ∉ ppStageCodes NN := fun h => hiANN (mem_activeIdx_iff.mpr h)
    rw [primeStageWeights_inactive n i hi, primeStageWeights_inactive NN i hiNN]

/-- **F_stage weight index along primePowerStage is eventually constant.**
The weight index primePerturbedStageIndex(primePowerStage n) = card(below cutoff)
diverges to atTop (banked), and primeStageWeights stabilizes for large argument,
so primeStageWeights (primePerturbedStageIndex (primePowerStage n)) is eventually
constant in n. -/
theorem primeStageWeights_stageIndex_eventually_const :
    ∃ M : Nat, ∀ n : Nat, M <= n ->
      primeStageWeights (N := N) (primePerturbedStageIndex (primePowerStage n))
        = primeStageWeights (N := N) (primePerturbedStageIndex (primePowerStage M)) := by
  classical
  obtain ⟨NN, hNN⟩ := primeStageWeights_eventually_const (N := N)
  have hcard : Tendsto
      (fun n : Nat => primePerturbedStageIndex (primePowerStage n)) atTop atTop := by
    simpa [primePerturbedStageIndex, resolventIndices] using
      concretePrimePowerBelowCutoff_card_atTop.comp primePowerStage_R_tendsto_atTop
  have hev : ∀ᶠ n in atTop, NN <= primePerturbedStageIndex (primePowerStage n) :=
    (tendsto_atTop.1 hcard) NN
  obtain ⟨M2, hM2⟩ := eventually_atTop.1 hev
  refine ⟨M2, ?_⟩
  intro n hn
  have hn_idx : NN <= primePerturbedStageIndex (primePowerStage n) := hM2 n hn
  have hM2_idx : NN <= primePerturbedStageIndex (primePowerStage M2) := hM2 M2 (le_refl M2)
  rw [hNN _ hn_idx, hNN _ hM2_idx]

/-- **F_stage is eventually constant along primePowerStage** (for any weights mu).
Direct corollary: equal stage-weights give equal resolvent traces. -/
theorem aligned_F_stage_eventually_const (mu : Fin N -> Real) :
    ∃ M : Nat, ∀ n : Nat, M <= n -> ∀ s : Complex,
      primePerturbedFStage mu
        (primeStageWeights (primePerturbedStageIndex (primePowerStage n))) s
      = primePerturbedFStage mu
        (primeStageWeights (primePerturbedStageIndex (primePowerStage M))) s := by
  obtain ⟨M, hM⟩ := primeStageWeights_stageIndex_eventually_const (N := N)
  refine ⟨M, ?_⟩
  intro n hn s
  rw [hM n hn]

/-- The aligned F-limit FH at the stabilization threshold M. -/
noncomputable def alignedFH (mu : Fin N -> Real) (M : Nat) : Complex -> Complex :=
  primePerturbedFStage mu (primeStageWeights (primePerturbedStageIndex (primePowerStage M)))

/-- **h_F_stage_to_FH for the aligned layer along primePowerStage.**
F_stage is eventually equal to alignedFH (weights stabilize), so the compact-uniform
convergence is trivial: past M the values coincide, dist = 0 < eps. -/
theorem aligned_h_F_stage_to_FH (mu : Fin N -> Real) :
    ∃ M : Nat,
      ∀ K : Set Complex, IsCompact K -> K ⊆ Ω ->
        ∀ eps : Real, 0 < eps ->
          ∀ᶠ n in Filter.atTop,
            ∀ s : Complex, s ∈ K ->
              dist ((primePerturbedOperatorLayerAligned mu).toStagePackage.F_stage
                      (primePowerStage n) s) (alignedFH mu M s) < eps := by
  obtain ⟨M, hM⟩ := aligned_F_stage_eventually_const (N := N) mu
  refine ⟨M, ?_⟩
  intro K hK hKsub eps heps
  rw [Filter.eventually_atTop]
  refine ⟨M, ?_⟩
  intro n hn s hs
  have heq : (primePerturbedOperatorLayerAligned mu).toStagePackage.F_stage
              (primePowerStage n) s = alignedFH mu M s := by
    show primePerturbedFStage mu
        (primeStageWeights (primePerturbedStageIndex (primePowerStage n))) s = _
    unfold alignedFH
    exact hM n hn s
  rw [heq, dist_self]
  exact heps

/-- **FH is holomorphic on Omega**, given the perturbed-prime spectrum at the
saturated weights is nonnegative (the globally-shifted positivity regime). -/
theorem alignedFH_holo (mu : Fin N -> Real) (M : Nat)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues mu
      (primePotential_isHermitian
        (primeStageWeights (primePerturbedStageIndex (primePowerStage M)))) i) :
    HolomorphicOnC (alignedFH mu M) Ω := by
  unfold alignedFH
  exact primePerturbedFStage_holo mu
    (primeStageWeights (primePerturbedStageIndex (primePowerStage M))) hpos

/-- **The aligned-layer DFHLimitData** along primePowerStage, given FH-positivity.
This discharges the F premise of the close on the genuine prime operator. -/
noncomputable def alignedDFHLimit (mu : Fin N -> Real)
    (M : Nat)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues mu
      (primePotential_isHermitian
        (primeStageWeights (primePerturbedStageIndex (primePowerStage M)))) i)
    (hM : ∀ n : Nat, M ≤ n -> ∀ s : Complex,
      (primePerturbedOperatorLayerAligned mu).toStagePackage.F_stage (primePowerStage n) s
        = alignedFH mu M s) :
    DFHLimitData (primePerturbedOperatorLayerAligned mu).toStagePackage :=
  buildDFHLimitDataFromCompactUniform
    (primePerturbedOperatorLayerAligned mu).toStagePackage
    primePowerStage
    (alignedFH mu M)
    (alignedFH_holo mu M hpos)
    (by
      intro K hK hKsub eps heps
      rw [Filter.eventually_atTop]
      refine ⟨M, ?_⟩
      intro n hn s hs
      rw [hM n hn s, dist_self]
      exact heps)

/-- B-stage along primePowerStage equals the concrete cutoff package
(generic B-stage identity + the primePowerStage index identity). -/
theorem aligned_BStage_primePowerStage_eq_concrete (n : Nat) (s : Complex) :
    arithmeticShiftedLaplaceBStage (primePowerStage n) s =
      finiteCanonicalPrimePowerPackage
        (concretePrimePowerBelowCutoff ((n : Real) + 1))
        shiftedLaplaceHeatKernelC s := by
  rw [arithmeticShiftedLaplaceBStage_eq_finiteCanonicalPrimePowerPackage_image]
  congr 1
  exact designed_indices_primePowerStage n

/-- B-stage along primePowerStage converges to Bshared on RightHalfPlane 1. -/
theorem aligned_BStage_primePowerStage_tendsto (s : Complex)
    (hs : s ∈ RightHalfPlane (1 : Real)) :
    Tendsto (fun n : Nat => arithmeticShiftedLaplaceBStage (primePowerStage n) s)
      atTop (nhds ((shiftedLaplaceModelPackageAt 1).Bshared s)) := by
  have hconv := shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1 s hs
  refine hconv.congr' ?_
  filter_upwards with n
  exact (aligned_BStage_primePowerStage_eq_concrete n s).symm

/-- **h_overlap for the aligned layer**: R_stage converges on RightHalfPlane 1 to
FH - Bshared, via the banked Tendsto.sub bridge fed our F-convergence and the
banked B-convergence. -/
theorem aligned_h_overlap (mu : Fin N -> Real) (M : Nat)
    (hM : ∀ n : Nat, M ≤ n -> ∀ s : Complex,
      primePerturbedFStage mu
        (primeStageWeights (primePerturbedStageIndex (primePowerStage n))) s
        = alignedFH mu M s) :
    PrimePerturbedAlignedOverlap mu primePowerStage
      (fun s => alignedFH mu M s - (shiftedLaplaceModelPackageAt 1).Bshared s) := by
  apply primePerturbedAlignedOverlap_from_F_and_B mu primePowerStage
    (alignedFH mu M) (fun s => (shiftedLaplaceModelPackageAt 1).Bshared s)
  · -- F-half: eventual equality gives Tendsto to the constant alignedFH
    intro s hs
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop M] with n hn
    exact (hM n hn s).symm
  · -- B-half: banked
    intro s hs
    exact aligned_BStage_primePowerStage_tendsto s hs


end

end RHFormalization
