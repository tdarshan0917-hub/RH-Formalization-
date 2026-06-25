import RHFormalization.ResolventHConvCore
import RHFormalization.ResolventStageFinsetAtTop
import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.ShiftedLaplaceLocalMTest
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceRegionFacts
import RHFormalization.ShiftedLaplaceModelPackageProbe
import Mathlib

/-!
# h_conv on the abs-conv region (hypothesis-free)

Discharges the `hBunif` hypothesis of `resolvent_R_stage_conv_on_region` from the banked
B-side local-uniform convergence on the abs-conv region:
* `shiftedLaplace_tlu_on_absConvRegion_from_local_mtest 1 shiftedLaplaceLocalMTest`
  (B → (shiftedLaplacePrimePackageAt 1).Bshared, locally uniform on absConvRegion);
* TLU → per-compact uniform via `tendstoLocallyUniformlyOn_iff_forall_isCompact`;
* Finset-atTop → ℕ reindex via `resolventStage_card_atTop`;
* `shiftedLaplace_Bshared_eqOn_model` rewrites the limit to the model Bshared,
  matching `(shiftedLaplaceModelPackageAt 1).Bshared` used by `resolventRH`.
Result: R_stage → resolventRH compact-uniformly on absConvRegion, unconditional.
-/

namespace RHFormalization
open Filter Topology Complex
open scoped Classical

/-- B-side compact-uniform convergence on abs-conv-region compacts, to the MODEL Bshared. -/
theorem resolvent_B_stage_unif_on_absConv
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ shiftedLaplaceAbsConvRegion)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
      dist (finiteCanonicalPrimePowerPackage
              (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
           ((shiftedLaplaceModelPackageAt 1).Bshared s) < ε := by
  -- banked TLU of B to the package Bshared on the region
  have hTLU := shiftedLaplace_tlu_on_absConvRegion_from_local_mtest 1 shiftedLaplaceLocalMTest
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact shiftedLaplaceAbsConvRegion_isOpen] at hTLU
  have hUnif := hTLU K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hUnif
  -- uniform over Finset I along Finset.atTop; pull out ε
  have hI : ∀ᶠ (I : Finset PrimePowerPair) in atTop, ∀ x ∈ K,
      dist ((shiftedLaplacePrimePackageAt 1).Bshared x)
        (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC x) < ε := hUnif ε hε
  -- unpack the Finset.atTop threshold
  rw [Filter.eventually_atTop] at hI
  obtain ⟨I0, hI0⟩ := hI
  -- I0's pairs that matter are valid; but we only need I0 ⊆ resolventIndices eventually,
  -- and resolventIndices_eventually_superset needs validity of I0's members.
  -- Restrict to the valid sub-finset; invalid members contribute 0 to both packages.
  have hI0valid : ∀ q ∈ I0.filter (fun q => IsPrimePowerPair q), IsPrimePowerPair q := by
    intro q hq; exact (Finset.mem_filter.mp hq).2
  have hsuper := resolventIndices_eventually_superset
    (I0.filter (fun q => IsPrimePowerPair q)) hI0valid
  filter_upwards [hsuper] with n hn
  intro s hs
  -- Apply hI0 at J = resolventIndices(primePowerStage n) ∪ I0 (which contains I0).
  set J := resolventIndices (primePowerStage n) ∪ I0 with hJdef
  have hJ : I0 ≤ J := by rw [hJdef]; exact le_sup_right
  have hbnd := hI0 J hJ s hs
  -- finiteCanonical J = finiteCanonical (resolventIndices n): extra pairs are invalid (weightC=0).
  have hpkgeq : finiteCanonicalPrimePowerPackage J shiftedLaplaceHeatKernelC s
      = finiteCanonicalPrimePowerPackage
          (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s := by
    unfold finiteCanonicalPrimePowerPackage
    symm
    apply Finset.sum_subset
    · rw [hJdef]; exact Finset.subset_union_left
    · intro q hqJ hqnotres
      have hqI0 : q ∈ I0 := by
        rcases Finset.mem_union.mp hqJ with h | h
        · exact absurd h hqnotres
        · exact h
      have hqinvalid : ¬ IsPrimePowerPair q := by
        intro hval
        have hmem : q ∈ I0.filter (fun q => IsPrimePowerPair q) :=
          Finset.mem_filter.mpr ⟨hqI0, hval⟩
        exact hqnotres (hn hmem)
      have hw : q.weightC = 0 := by
        simp [PrimePowerPair.weightC, PrimePowerPair.weightReal, hqinvalid]
      rw [hw, zero_mul]
  rw [hpkgeq] at hbnd
  rw [dist_comm] at hbnd
  have heq : (shiftedLaplacePrimePackageAt 1).Bshared s
      = (shiftedLaplaceModelPackageAt 1).Bshared s := by
    have hmodel := shiftedLaplace_Bshared_eqOn_model 1 (hKU hs)
    rw [shiftedLaplaceModelPackageAt_Bshared_eq_model]
    exact hmodel
  rw [heq] at hbnd
  exact hbnd

/-- **h_conv on the abs-conv region (unconditional).** R_stage → resolventRH
compact-uniformly on every compact `K ⊆ shiftedLaplaceAbsConvRegion`. -/
theorem resolvent_h_conv_absConv :
    ∀ K : Set ℂ, IsCompact K → K ⊆ shiftedLaplaceAbsConvRegion →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
          dist (spectralResolventPartial (primePowerStage n) s -
                  finiteCanonicalPrimePowerPackage
                    (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
               (resolventRH s) < ε := by
  apply resolvent_R_stage_conv_on_region
    shiftedLaplaceAbsConvRegion shiftedLaplaceAbsConvRegion_subset_Omega
  intro K hK hKU ε hε
  exact resolvent_B_stage_unif_on_absConv K hK hKU ε hε

#print axioms resolvent_h_conv_absConv

end RHFormalization
