# RH FORMALIZATION — SESSION STATUS (paste this to Claude FIRST, every session)

## THE DIAGONAL (top to bottom; ✓ = banked green + axiom-clean)
RH
 ⟸ RH_follows_from_packaged_spine        [MainTheorem.lean — PROVEN ✓]
 ⟸ RigidityNoPoleAPI (D,H,E)             [buildRigidityNoPole GlobalRigidity.lean — PROVEN ✓]
 ⟸ OperatorResolventBridge (D)           [resolventOperatorBridgeDirect — PROVEN ✓]
      ├─ B  resolventDBcanLimit          ✓
      ├─ F  resolventDFHLimit            ✓
      ├─ R  DMasterResidualData          ← THE SOLE FRONTIER
      └─ O  DOverlapIdentityAPI          [derivative from R]
 ⟸ R via buildDMasterResidualDataAlong, needs ONLY:
      h_stage_holo  [banked content, wiring]
      h_conv        ← THE ONE OPEN GOAL

## THE ONE OPEN GOAL (exact Lean shape)
h_conv : ∀ K, IsCompact K → K ⊆ Ω → ∀ ε>0, ∀ᶠ n in atTop, ∀ s∈K,
           dist (R_stage (primePowerStage n) s) (resolventRH s) < ε
  where R_stage = spectralResolventPartial − finiteCanonical(resolventIndices α) shiftedLaplaceHeatKernelC
        resolventRH s = resolventFH s − (shiftedLaplaceModelPackageAt 1).Bshared s
Plan: prove on abs-conv region (resolvent_h_conv_absConv), then VITALI-extend to all Ω.

## BANKED THEOREMS (name → meaning) — DO NOT REBUILD THESE
- resolvent_R_stage_overlap_tendsto      : R_stage → resolventRH POINTWISE on RightHalfPlane 1
- resolvent_R_stage_conv_on_region (U,hUΩ,hBunif) : R_stage→RH compact-uniform on any U where B unif converges (ε/2+ε/2 core)
- resolventIndices_eventually_superset (I0, valid) : ∀ᶠ n, I0 ⊆ resolventIndices(primePowerStage n)  [Finset→ℕ reindex bridge]
- correctedResolvent_F_bound             : F compact-uniformly bounded ∀ stages on Ω-compacts
- resolvent_F_stage_to_FH                : F compact-uniform → resolventFH on ALL Ω-compacts
- finiteCanonical_tendsto_tsum_of_kernel_error_tendsto_zero_valid (I,K,Kshared,s,hmem,hsummable,herror) : finiteCanonical→tsum POINTWISE, support-aware (handles invalid pairs via weightC=0)
- resolvent_h_conv_absConv : h_conv (R_stage->resolventRH compact-uniform) UNCONDITIONAL on abs-conv region ✓ NEW
- resolvent_B_stage_unif_on_absConv : B compact-uniform -> model Bshared on abs-conv-region compacts ✓ NEW
- shiftedLaplace_tlu_on_absConvRegion_from_local_mtest (σ₀, D) : B locally-uniform on abs-conv region
- shiftedLaplaceLocalMTest                : constructed ShiftedLaplaceAbsConvLocalMTestData
- shiftedLaplace_Bshared_eqOn_model (σ₀)  : package.Bshared =ᵉ logDerivModel on abs-conv region
- shiftedLaplaceModelPackageAt_Bshared_eq_model : model package Bshared = logDerivModel (rfl)
- shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1 : B→Bshared pointwise on RHP 1
- correctedResolventPayload_R_stage_bound_of_F_B_bounds : F-bound + B-bound → R compact bound (generic P)
- R_stage_bound_of_sector_bounds (generic P) : 4 sector bounds → R compact bound
- shiftedLaplaceAbsConvRegion_subset_Omega, rightHalfPlane_subset_Omega, ...geometry
- weightC = 0 on non-prime-power pairs (CanonicalPrimePowerFiniteKernelErrorSum:242, etc.)

## KEY FACTS
- weightC = weightReal = von Mangoldt-type, ZERO on invalid (non-prime-power) pairs.
- resolventIndices α = concretePrimePowerBelowCutoff α.R  (DEFEQ)
- (primePowerStage n).R = (n:ℝ)+1  (DEFEQ)
- B converges (abs) ONLY on shiftedLaplaceAbsConvRegion = {½ < Re√(s+¼)} ⊊ Ω.
  F converges on ALL Ω. So R=F−B unif converges on abs-conv region; Vitali lifts to Ω.
- B-TLU is indexed by I:Finset along Finset.atTop → reindex to ℕ via resolventIndices_eventually_superset.

## FROZEN-FORBIDDEN (never touch)
designedY, selectedFiniteOperatorLayer, RH:=fun _=>0, R_stage=0 (ResolventPayload.lean DEAD),
displacementCanonicalKernel (s-discarding), model route, ∀α:DFiniteStage all-stage bounds,
Final*Probe/HChosen* capstones, RH_from_designed_*.

## WORKING METHOD
- Travis runs ALL builds (Mac), pastes output. Claude has NO network, cannot build Lean.
- Patches via: python3 - << 'PYEOF' / src = r'''...''' / open(path,"w").write(src) / PYEOF  (avoids heredoc mangling).
- DONE = compiles + #print axioms clean [propext,Classical.choice,Quot.sound] no sorryAx + committed.

## LAST STATE
- Green committed: ResolventDOverlapInput, ResolventHConvCore, ResolventStageFinsetAtTop, ResolventHConvAbsConv.
- DONE: h_conv UNCONDITIONAL on abs-conv region (resolvent_h_conv_absConv, axiom-clean, no sorry).
- NEXT: VITALI extension — lift h_conv from abs-conv region to ALL Ω-compacts.
  Family R_stage(primePowerStage n) is: holomorphic on Ω (stage_holo), locally bounded on Ω
  (F-bound banked; B-bound = the open piece OR via Vitali only needs bdd+converges-on-subregion),
  converges on abs-conv region (just banked). Vitali/Porter ⟹ converges loc-unif on all Ω.
- THEN: feed full-Ω h_conv + h_stage_holo to buildDMasterResidualDataAlong → R, then O, bridge → RH.
- REMAINING UNCONDITIONAL: (1) Vitali abs-conv→Ω  (2) h_stage_holo wiring to live primePowerStage.
