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


## SHARPENED ENDGAME (the WHOLE proof now funnels to ONE classical lemma)
RH <= ... <= R (DMasterResidualData) <= dcanrem_from_ascoli, 5 inputs:
  h_stage_holo  : banked content, live-route wiring
  h_loc_bdd     : banked F-bound + residual bound (correctedResolventPayload_R_stage_bound_of_F_B_bounds, generic)
  h_overlap     : BANKED (resolvent_R_stage_overlap_tendsto on RHP1; resolvent_h_conv_absConv on abs-conv region)
  h_RH_holo     : from Montel (the shield)
  h_ascoli      : holomorphicMontelConvergence_from_ascoli PROVEN, <= AscoliExtraction
                  <= AscoliRelativelyCompact <= AscoliRelCompactObligation
                  <= ToFunImageCompact  <-- THE SOLE REMAINING GAP (classical, NON-RH)
ALL reduction layers PROVEN (no sorry). Montel engine PROVEN.
ToFunImageCompact: toFun '' (range G) compact in product topology. Arzela-Ascoli image-compactness
  on non-compact domain Omega. RECIPE (in AscoliObligationDischarge.lean):
  EquicontinuousOn.isClosed_range_pi_of_uniformOnFun' (Ascoli.lean:374) -> closedness;
  Tychonoff Set.pi univ (closedBall 0 (M.)) compact (C ProperSpace) -> of_isClosed_subset.
  Equicontinuity banked: uniformEquicontinuousOn_ball_of_bounded_holo.


## ASCOLI GAP CLOSED (the real last classical lemma — banked)
ascoliRelCompactObligation_direct : AscoliRelCompactObligation  [AscoliObligationDirect.lean, GREEN, axiom-clean]
  Proof: ArzelaAscoli.isCompact_closure_of_isClosedEmbedding with
    F_clemb = isClosedEmbedding_toUOFC_Omega (uniform embedding + closed range)
    closed range: range_toUniformOnFunIsCompact = {Continuous}, closed via
      UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
      (needs haveI LocallyCompactSpace Omega := isOpen_Omega.locallyCompactSpace)
    s_eqcont = hequi.equicontinuousOn ; s_pointwiseCompact: Q = closedBall 0 (M x).
LESSON: ToFunImageCompact (raw-image compact) was FALSE (1/(n+1) counterexample).
  TRUE target is closure-compact. When a Prop asserts compactness/closedness of a RAW
  (non-closure) set from ptwise-bdd+equicont, it is almost certainly too strong -> use closure.
LESSON: do NOT write fancy unicode (->u arrow) in type annotations; use plain UniformOnFun X Y S.
LESSON: IsClosedEmbedding from embedding+closed-range = anonymous constructor <hemb, hclosed>.

## NEXT (chain now lit): wire ascoliRelCompactObligation_direct -> AscoliExtraction ->
  dcanrem_from_ascoli to BUILD R : DMasterResidualData on the resolvent layer. Then O, bridge, RH.
  Need also: h_stage_holo (live wiring) + h_loc_bdd (banked F+B bounds) + h_RH_holo (shield).


## dcanrem_from_ascoli INPUT TRACKER (building R : DMasterResidualData, live resolvent layer)
  [1] h_stage_holo  : resolvent_stage_holo_primePowerStage  [ResolventStageHolo.lean] BANKED ✓
        = F(spectralResolventPartial finite-sum holo) - B(finiteCanonical_shiftedLaplace_holo_of_mem_Omega), .sub
  [2] h_loc_bdd     : F-bound (correctedResolvent_F_bound) + B-bound (correctedResolvent_B_bound_target)
        + combiner (correctedResolventPayload_R_stage_bound_of_F_B_bounds) — all BANKED, needs assembly to live family
  [3] h_overlap     : resolvent_R_stage_overlap_tendsto  BANKED ✓ (need to wrap as ∃U open nonempty ⊆Ω shape)
  [4] h_RH_holo     : from Montel limit (the g in ascoliExtraction_of_relativelyCompact is proven holo) — derive
  [5] h_ascoli      : AscoliExtraction — ascoliRelCompactObligation_direct BANKED ✓; needs M + Equicontinuous glue
        via ascoliExtraction_of_relativelyCompact + ascoliRelativelyCompact_of_obligation
KEY: HolomorphicAtC = AnalyticAt C, HolomorphicOnC = AnalyticOn C (AnalyticWithinAt). Use AnalyticAt for .sub,
     lift to OnC via holomorphicOnC_of_forall_holomorphicAtC.
NEXT: input [2] h_loc_bdd assembly to live family (wire 3 banked bounds), then [3] overlap wrap, then [5] ascoli glue.


=== PRIME-PERTURBED OPERATOR CORRECTION (firewall check, this session) ===
CRITICAL: resolventOperatorLayer was built on the FREE operator (spectralResolventPartial,
  lamShifted = (n*pi)^2) — the WRONG F. The genuine manuscript operator is the
  PRIME-PERTURBED operator (primePerturbedFStage). GPT firewall check exposed this;
  section-C grep found NO identification theorem between them. They are different objects.

NEW GREEN FILES (axiom-clean, on the RIGHT operator):
  - PrimePerturbedPayload.lean : primePerturbedPayload (mu : Fin N -> R)
      F_stage = primePerturbedFStage mu (primeStageWeights (resolventIndices alpha).card)
      B_stage = finiteCanonicalPrimePowerPackage (resolventIndices alpha) shiftedLaplaceHeatKernelC
      R_stage = F - B, sigma0 = 1.  Same template as correctedResolventPayload, F swapped.
  - PrimePerturbedOperatorLayer.lean : primePerturbedOperatorLayer (mu : Fin N -> R)
      = buildSelectedFiniteOperatorLayerFromCanonicalPayload (primePerturbedPayload mu)

EXISTING PRIME-PERTURBED SCAFFOLDING (on the right operator, to reuse):
  - ArithmeticPrimeStageHolo : stage-holo, built FOR buildDMasterResidualDataAlong
  - stageField_R_stage_bound_of_F_B_bounds (ArithmeticPrimeRStageBoundSplit) : residual-split, axiom-clean
  - PerturbedFstageLipschitz, ArithmeticPrimeFStageBound, ArithmeticPrimeOperatorResidual

NEXT: re-point R-constructor (resolventDMasterResidual_from_obligations) at
  primePerturbedOperatorLayer instead of resolventOperatorLayer. Then O -> bridge -> H-side spine.
  The spine is operator-generic (uses only D.FH/D.hFH_holo) so it accepts the right R.

NOTE: today's resolventDMasterResidual_from_obligations / ResolventDMasterResidualBuild
  were built on the FREE layer — they are the wrong-operator versions. Re-point, don't reuse as-is.


=== BALL->COMPACT LIFT GREEN (this session) ===
PrimePerturbedRStageLocBdd.lean : perturbedResidual_bound_on_compact_of_ball_bounds
  AXIOM-CLEAN, sorry-free. Lifts closed-ball residual bound -> bound on every compact K subset Omega
  via finite subcover (IsCompact.elim_finite_subcover over subtype K) + Finset.sup'.
  Pure topology. Takes (ball_bound : forall closed ball subset Omega, residual bounded) as hypothesis.

FOUR GREEN FILES THIS SESSION on the RIGHT (prime-perturbed) operator:
  1. PrimePerturbedPayload.lean       (F = primePerturbedFStage)
  2. PrimePerturbedOperatorLayer.lean (the operator layer)
  3. PrimePerturbedRStageHolo.lean    (h_stage_holo, shifted-Laplace B)
  4. PrimePerturbedRStageLocBdd.lean  (ball->compact residual-bound lift)

NEXT (step 2): WIRE ArithmeticPrimeDExport_on_closedBall_shiftedLaplaceBStage
  (the BANKED closed-ball residual estimate, gap self-discharged) as the ball_bound input
  to perturbedResidual_bound_on_compact_of_ball_bounds -> gives h_loc_bdd on prime operator.
  Watch: transfer perturbedResidual <-> primePerturbedPayload.R_stage
  (arithmeticPrimeResidual_eq_perturbedResidual + the payload R_stage defeq).


=== D.A2 LAPLACE-RESOLVENT BRIDGE GREEN (this session) — the frequency↔time hinge ===
DA2LaplaceResolvent.lean:
  integral_cexp_neg_mul_Ioi : ∫ Ioi 0, exp(-a t) = a⁻¹  (Re a > 0)   [via Mathlib integral_exp_mul_complex_Ioi]
  inv_eq_laplace_exp        : (s+λ)⁻¹ = ∫ Ioi 0, exp(-(s+λ)t)  (Re s>0, λ≥0)   AXIOM-CLEAN
DA2HeatTrace.lean:
  FstageFinite_eq_laplace_heatTrace :
    FstageFinite λ s = ∫ Ioi 0, ∑ᵢ exp(-(s+λᵢ)t)   (Re s>0, λᵢ≥0)   AXIOM-CLEAN
    = manuscript D.A2 p163 line 19: F(s) = ∫ e^{-st} Tr(e^{-tH}) dt
  THIS IS THE HINGE connecting frequency-side F = ∑(s+λᵢ)⁻¹ to time-side heat trace
  ∑ e^{-tλᵢ} that the banked Galerkin/Duhamel bounds control.

LADDER TO h_loc_bdd (= D.USR, the one open chain link):
  [DONE]  1. (s+λ)⁻¹ = ∫ e^{-(s+λ)t}                          inv_eq_laplace_exp ✅
  [DONE]  2. F = ∫ e^{-st} Tr(e^{-tH})                         FstageFinite_eq_laplace_heatTrace ✅
  [NEXT]  3. B = ∫ e^{-st}(Bulk+Spikes)                        B-side Laplace identity (finite spike sum)
          4. R = F - B = ∫ e^{-st}(Mix+Tail) = ∫ e^{-st} Q_res  subtraction (p164 line 13)
          5. ‖R(s)‖ ≤ ∫ e^{-Re(s)t}|Q_res| ≤ densityAnchor·compactFactor   via disp_transform_bounded + Galerkin/Duhamel (BANKED)
          6. DAdmissibleShortResidualData record → DUniformShortResidualBound (=h_loc_bdd, contract PROVEN)
  Then: h_loc_bdd → dcanrem_from_montel → R:DMasterResidualData → bridge → RH.


=== STIELTJES POLE-PACKAGE IDENTITY GREEN (mod ONE named connector) — this session ===
THE B-SIDE LADDER (all green, sorryAx = single named connector only):
  BSideHeatKernelLaplace.lean:
    shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG  ◀━ THE ONE CARRIED CONNECTOR (sorry)
      shiftedLaplaceHeatKernelC a s = ∫ Ioi 0, e^{-st}·e^{-t/4}·heatKernelG t a
      = classical Gaussian heat-kernel Laplace transform. Mathlib lacks it. Statement typechecks.
  BStageLaplaceLift.lean:
    arithmeticShiftedLaplaceBStage_eq_laplace  (B = ∫ e^{-st}·summed heat spikes)  [green mod connector]
  ResidualLaplaceRep.lean:
    arithmeticPrimeResidual_eq_laplace_qRes  (R = F−B = ∫ e^{-st}·Q_res)  [green mod connector]
    = THE STIELTJES POLE-PACKAGE IDENTITY (manuscript title, p164 line 13).

CHAIN STATUS: RH ⟸ ... ⟸ h_loc_bdd ⟸ DAdmissibleShortResidualData
  R = ∫ e^{-st} Q_res  ✅ (this session, mod connector)
  NEXT: ‖R(s)‖ ≤ ∫|Q_res| ≤ densityAnchor·compactFactor   via disp_transform_bounded + Galerkin/anchor (BANKED)
        → fill DAdmissibleShortResidualData record → h_loc_bdd → chain closes.
  The ENTIRE RH formalization now reduces to the single connector
  shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG (one classical Gaussian Laplace identity)
  PLUS the bound-rung wiring (banked ingredients) PLUS discharging the integrability side-hyps.


=== h_loc_bdd ⟸ hQ REDUCTION GREEN (axiom-clean, no sorry) — this session ===
AlongNetBoundFromQRes.lean:
  primePerturbedAligned_along_bound_from_qRes_bound   [AXIOM-CLEAN]
  primePerturbedAligned_h_loc_bdd_from_qRes_bound     [AXIOM-CLEAN]
  → h_loc_bdd reduces cleanly to hQ = (∀K⋐Ω ∃C≥0 ∀n ∀s∈K, ‖R_stage(alpha n) s‖ ≤ C).

ALIGNMENT CONFIRMED (PrimePerturbedPayloadAligned.lean):
  F_stage = primePerturbedFStage μ (primeStageWeights ...)
  B_stage = arithmeticShiftedLaplaceBStage
  R_stage = F_stage - B_stage   ← exactly the F,B whose Laplace rep is green (ResidualLaplaceRep).

REMAINING TWO LEAVES for fully closed RH chain:
  (1) shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG  (the ONE Gaussian connector, sorry)
  (2) hQ from: R_stage = ∫ e^{-st} Q_res (green mod (1)) + ‖∫‖≤∫|·| + Galerkin uniform bound (BANKED, cutoff-indep)
  abs_trace_galerkin_duhamel_uniform RHS = (∑|w|bumpMass)²·(heat factors), INDEPENDENT of N → the ∀n uniformity.

CHAIN: RH ⟸ h_conv ⟸ dcanrem_from_montel ⟸ h_loc_bdd ⟸ hQ ⟸ [Stieltjes rep + Galerkin]. 
  Everything green except leaf (1) the Gaussian connector and the leaf-(2) assembly wiring.


=== ★★★ h_loc_bdd FULLY REDUCED TO TWO NAMED LEAVES (this session) ★★★ ===
HLocBddFromIntegralBound.lean:
  primePerturbedAligned_qRes_bound_from_integral_bound   [AXIOM-CLEAN]
  primePerturbedAligned_h_loc_bdd_from_integral_bound    [AXIOM-CLEAN]
  → h_loc_bdd ⟸ (hRep ∧ hQint), via triangle inequality. NO sorry in the reduction.

THE COMPLETE CHAIN, backwards, with the frontier:
  RH ⟸ ... ⟸ h_conv ⟸ dcanrem_from_montel ⟸ h_loc_bdd   [all GREEN]
  h_loc_bdd ⟸ TWO LEAVES (everything else green/axiom-clean):
    LEAF 1 — hRep: R_stage = ∫ e^{-st} Q_res  (Stieltjes pole-package identity)
      = arithmeticPrimeResidual_eq_laplace_qRes (ResidualLaplaceRep.lean), GREEN modulo:
        • shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG  (THE ONE Gaussian connector, the only sorry)
        • integrability side-hyps (hintF/hintB/hintSpike — standard, dischargeable)
        • stage-index defeq (primePerturbedStageIndex alignment — should be rfl/simp)
    LEAF 2 — hQint: ∫|Q_res| ≤ C cutoff-independent on each compact
      = banked Galerkin uniform bound (abs_trace_galerkin_duhamel_uniform, RHS independent of N)
        wired onto ∫|qResIntegrand|. TO WIRE (banked ingredient, not new analysis).

SEVEN GREEN FILES BUILT THIS SESSION (the full Laplace-representation spine):
  DA2LaplaceResolvent, DA2HeatTrace (F-side, AXIOM-CLEAN),
  BSideHeatKernelLaplace (connector, 1 sorry), BStageLaplaceLift, ResidualLaplaceRep (B-side + Stieltjes, mod connector),
  AlongNetBoundFromQRes, HLocBddFromIntegralBound (reductions, AXIOM-CLEAN).

NEXT SESSION: (a) prove or keep-carrying LEAF 1 (Gaussian Laplace transform); (b) wire LEAF 2 from banked Galerkin.
  Both leaves are NAMED, ISOLATED, and the chain is green around them.


=== ★ HONEST FRONTIER CORRECTION (this session, end) — TWO genuine pieces, not one ★ ===
Leaf 2 is NOT mere wiring. Reads confirmed:
  • diagonalSpikeContribution = raw PrimePowerPair.weightC (NOT density-normalized — no 1/(2L) shrink).
  • diagonalSpikeActiveIndices = activePrimePowerCodesCenterBelow Rstage — GROWS with cutoff.
  • NO bridge exists (grep empty) from bStageHeatIntegrand (position-space spike sum)
    to galerkinV Duhamel trace (spectral Fin N matrix). They are different objects.
  • CanonicalPrimePowerProductWindowError.lean:15 SELF-DOCUMENTS: naive ∑‖weightC‖ mass bound is
    "too strong over exhausting prime powers" — the σ=½ wall, stated in-repo.

THEREFORE the cutoff-independent hQint (∫‖Q_res‖ ≤ C uniform in cutoff) has TWO routes, both gapped:
  (A) triangle / mass-bound ∑‖weightC‖ : repo says too strong, NOT uniform. DEAD for the all-Ω bound.
  (B) Galerkin cancellation abs_trace_galerkin_duhamel_uniform : genuinely cutoff-indep, but
      NO bridge from position-space spike sum → galerkinV matrix trace. UNBUILT.

TRUE FRONTIER = TWO genuine analytic pieces (not one leaf):
  LEAF 1: shiftedLaplaceHeatKernelC_eq_laplace_heatKernelG (Gaussian Laplace transform, named/carried)
  LEAF 2: position-space residual ↔ spectral Galerkin Duhamel cancellation bridge (gives cutoff-indep ∫‖Q_res‖≤C)
          This is where the manuscript D.USR three-sector + density normalization actually lives.

GREEN THIS SESSION (all real, all correct, sorryAx = leaf 1 only or axiom-clean):
  DA2LaplaceResolvent, DA2HeatTrace (F-side AXIOM-CLEAN),
  BSideHeatKernelLaplace (leaf 1 carried), BStageLaplaceLift, ResidualLaplaceRep (Stieltjes id, mod leaf 1),
  AlongNetBoundFromQRes, HLocBddFromIntegralBound (reductions AXIOM-CLEAN),
  QResNormBound, QResSpikeNormBound, QResCombinedNormBound (pointwise ‖Q_res‖ bounds, AXIOM-CLEAN —
    CORRECT but lead to route (A) which is too-strong; do NOT integrate these for hQint).

CHAIN: RH ⟸ ... ⟸ h_loc_bdd ⟸ (hRep ∧ hQint).  hRep green mod LEAF 1. hQint needs LEAF 2 (the real D.USR core).
NEXT SESSION: LEAF 2 is the priority — build the position-space↔Galerkin-Duhamel bridge (the genuine
  cutoff-uniformity / density-normalization mechanism), NOT the triangle (which the repo marks too-strong).


=== ★★★ D.TAIL SECTOR COMPLETE (manuscript p179-180, the honest D.USR route) ★★★ ===
Reconciled with GPT: the all-Ω uniform bound does NOT use the σ>1/2 spike sum. The manuscript
D.USR proof (p173-180) has THREE sectors, each uniform-in-α by a DIFFERENT mechanism:
  D.LOC  (p174): density-normalized local loops, |Q_loc| ≤ C_loc·t^{3/2}, C_loc indep of α via D.ADM.
  D.DISP (p175): genuine displacement gets Gaussian e^{-c(log q)²/t}, super-poly decay. LARGELY BANKED
                 (disp_majorant_superpoly). NO σ>1/2.
  D.TAIL (p178-180): Feynman-Kac free-Dirichlet domination, (1/2L)Tr(e^{-t0 H̃}) ≤ (4πt0)^{-1/2}.

D.TAIL NOW BUILT — 4 GREEN AXIOM-CLEAN RUNGS (this session):
  1. DTailDensityFreeBound.lean / dTail_density_normalized_bound:
       (1/2L)·(2L·c) = c — the L-CANCELLATION density normalization (p179). freeHeatDiagonal t = 1/√(4πt).
  2. DTailSpectralBound.lean / dTail_spectral_termwise:
       ‖e^{-t0(s+λᵢ)}/(s+λᵢ)‖ ≤ e^{t0 M}·(1/δ)·e^{-t0 λᵢ}  (p180 termwise, M=sup|Re s|, δ=inf‖s+λ‖).
  3. DTailSumBound.lean / dTail_sum_bound:
       ‖∑ tail‖ ≤ e^{t0 M}·(1/δ)·∑ e^{-t0 λᵢ}  (sum of termwise).
  4. DTailUniformBound.lean / dTail_uniform_bound:
       (1/2L)·‖∑ tail‖ ≤ e^{t0 M}·(1/δ)·(4πt0)^{-1/2}  — α-INDEPENDENT (RHS has no L, no n).
       Named premise h_fk = Feynman-Kac (1/2L)·∑e^{-t0λ} ≤ (4πt0)^{-1/2} (the operator content,
       Mathlib-absent, a PREMISE not the conclusion — honest, NOT the certificate trap).

ALL ASCII (t0/delta not t₀/δ) — λ char breaks Lean parsing even in comments. rm file before rewrite (stale-file bug).

REMAINING for h_loc_bdd (the ONE open link, RH green above it):
  - D.DISP: wire disp_majorant_superpoly (banked) into the displacement sector uniform bound.
  - D.LOC: the density anchor M(R_α)/(2L_α) ≤ 1 (anchor_admissible partial) + |Q_loc| ≤ C_loc·t^{3/2}.
  - COMBINE three sectors → h_shortResidual_le → DAdmissibleShortResidualData → DUniformShortResidualBound
    (proven consumer) → h_loc_bdd → dcanrem_from_montel → ... → RH.
  - Connect dTail_uniform_bound to the actual primePerturbed R_tail (the spectral tail of R_stage).
  - h_fk (Feynman-Kac) + the prime spectral Weyl bound: discharge or keep as the one named operator premise.


=== ★★★ CONTRACT ASSEMBLY CHAIN WIRED (this session) — 3 proven links bolt → consumer → builder ★★★ ===
The deferred builder (AppendixDKeyFormShortContract.lean:9) is now FILLED. Full chain to h_loc_bdd,
every link a PROVEN axiom-clean theorem except the three sector-estimate inputs:

  RH ⟸ [banked endpoints] ⟸ DMasterResidualData ⟸ dcanrem_from_montel (needs h_loc_bdd, rest banked)
  h_loc_bdd ⟸ primePerturbedAligned_h_loc_bdd_from_shortContract   [BOLT ✅ HLocBddFromShortResidualContract.lean]
  DUniformShortResidualBound ⟸ DUniformShortResidualBound_from_admissibleShortData  [PROVEN ✅, pre-existing]
  DAdmissibleShortResidualData ⟸ buildDAdmissibleShortResidualData_from_AppendixD_estimates
     [BUILDER ✅ BuildAdmissibleShortFromEstimates.lean — this session, triangle of 3 factored sector bounds]
  ⟸ THREE SECTOR ESTIMATES (form: ∀K⋐Ω ∀n ∀s∈K ‖Q_sector(αn)s‖ ≤ anchor n · factor K) + decomposition:
       D.TAIL ✅ dTail_uniform_bound (DTailUniformBound.lean) — REPACKAGE to anchor·factor next
       D.DISP ◻ disp_transform_bounded (banked) — put in factored form
       D.LOC  ◻ anchor_integrand_integrable + anchor_admissible (banked) — put in factored form
       h_decomp: R_stage = Q_loc+Q_disp+R_tail — the operator Duhamel split, named premise (Mathlib-absent,
                 like h_fk; the manuscript's p173-176 word-length sorting). HONEST premise, not certificate.

BUILDER SIGNATURE (the assembly endpoint, use this):
  buildDAdmissibleShortResidualData_from_AppendixD_estimates
    (alpha) (Rstage Qloc Qdisp Rtail) (anchor factor)
    (h_anchor_nonneg) (h_anchor_bound) (h_factor_nonneg)
    (h_decomp : ∀ n s, Rstage(αn)s = Qloc+Qdisp+Rtail)
    (h_loc_le h_disp_le h_tail_le : ∀K⋐Ω ∀n ∀s∈K ‖Q_·(αn)s‖ ≤ anchor n · factor K)
    : DAdmissibleShortResidualData

D.TAIL BUILT (4 rungs, prior): dTail_density_normalized_bound, dTail_spectral_termwise, dTail_sum_bound,
  dTail_uniform_bound. anchor_admissible gives anchor:=1, A=1 (h_anchor_bound trivial). factor K absorbs
  e^{t0 M_K}/δ_K·(4πt0)^{-1/2}.

NEXT: repackage dTail_uniform_bound into h_tail_le form (anchor·factor); then D.DISP, D.LOC; then the
  decomposition premise; then instantiate the builder for the prime layer → consumer → bolt → h_loc_bdd → RH.
ALL ASCII (t0/delta), rm file before rewrite, grep λ before build.


=== ★★★★ D.USR FULLY ASSEMBLED → h_loc_bdd (this session) ★★★★ ===
primePerturbedAligned_h_loc_bdd_from_three_sectors (PrimeDUSRAssembly.lean) GREEN AXIOM-CLEAN.
Produces h_loc_bdd for the prime layer from the three D.USR sector bounds + decomposition,
via three proven theorem-links. NO σ>1/2, NO spike sum, NO certificate.

THE COMPLETE D.USR → h_loc_bdd CHAIN (every link GREEN axiom-clean):
  THREE SECTOR BOUNDS (each ∀K⋐Ω ∀n ∀s∈K ‖Q_·(αn)s‖ ≤ anchor n · factor K):
    D.LOC  ✅ dLoc_sector_bound  (DLocSectorBound.lean)   — density-normalized, p174
    D.DISP ✅ dDisp_sector_bound (DDispSectorBound.lean)  — Gaussian super-poly, p175
    D.TAIL ✅ dTail_uniform_bound (DTailUniformBound.lean + 3 rungs) — Feynman-Kac, p179-180
  + h_decomp (R_stage = Q_loc+Q_disp+R_tail, named operator premise — Duhamel word-sort p173-176)
    → buildDAdmissibleShortResidualData_from_AppendixD_estimates  [BUILDER ✅ BuildAdmissibleShortFromEstimates]
    → DUniformShortResidualBound_from_admissibleShortData          [CONSUMER ✅ pre-existing]
    → primePerturbedAligned_h_loc_bdd_from_shortContract           [BOLT ✅ HLocBddFromShortResidualContract]
    → h_loc_bdd  ✅ primePerturbedAligned_h_loc_bdd_from_three_sectors  [ASSEMBLY ✅ PrimeDUSRAssembly]

REMAINING TO RH (the named premises the assembly consumes — the genuine operator content):
  1. h_decomp: R_stage = Q_loc + Q_disp + R_tail  (Duhamel word-length sort, p173-176, Mathlib-absent)
  2. per-sector transform-forms: Q_loc/Q_disp = ∫e^{-st}g, R_tail = (1/2L)∑e^{-t(s+λ)}/(s+λ)  (identifications)
  3. per-sector integral/density bounds: ∫g_loc, ∫g_disp ≤ Ig (D.ADM/super-poly); h_fk Feynman-Kac (D.TAIL)
  4. wire h_loc_bdd (this theorem) + h_stage_holo (banked) + h_overlap (banked) into dcanrem_from_montel → DMasterResidualData → [banked endpoints] → RH

NEXT: connect primePerturbedAligned_h_loc_bdd_from_three_sectors into dcanrem_from_montel (the chain
  link that consumes h_loc_bdd), confirming h_stage_holo + h_overlap are banked for the prime layer,
  yielding DMasterResidualData → RH. Then discharge/name the premises (1-3) as the manuscript operator inputs.
ALL ASCII, rm before rewrite, grep λ before build.
