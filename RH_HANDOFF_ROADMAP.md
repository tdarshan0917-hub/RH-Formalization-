
## 2026-07-15 — DEFECT GATE CLOSED (cold-audited)
loc_bdd BANKED: `adaptiveGalerkinTransformDefect_loc_bdd` (AdaptiveDefectLocBdd.lean),
constant 5/c₀(K)+1/c₀(K)², via ladder L1a ComplexRiemannError → L1b CosResolventDerivMajorant
→ L1c CosResolventTailBound → L1d SineResolventSumBound → L1e PerSpikeTransformDefectBound
→ L2 AdaptiveDefectStageBound → L3a AdaptiveStageBoundUniform → L3b. Adapter fired:
`adaptiveGalerkinTransformDefect_eps0` (AdaptiveDefectGateClosed.lean), interface shape:
  ∀ (c : ℝ) (K : Set ℂ), IsCompact K → K ⊆ Ω → ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ s ∈ K, dist (adaptiveGalerkinTransformDefect c n s) 0 < ε
All cold-audited [propext, Classical.choice, Quot.sound], zero sorryAx.
Key reusable bricks: perSpikeTransformDefect_norm_le (three-term per-spike bound),
cosResolvent_integral_eq_pi_kernel_Omega (πK identity on Ω), resolventDenom_lower_bound
(compact floor c(1+ξ²)), partition_riemann_error_C / slice_riemann_error_C (ℂ Riemann error),
floor_at_shift, stageBound_uniform.
NEXT FRONTIER: post-gate sequence — canonical F-stage installation → ONE-STEP′′ →
corrected residual → corrected-bulk provider → RH_from_DBFF_corrected_bulk.

## POST-GATE MAP (extracted 2026-07-15, greps A–H)
RH ⟸ RH_from_DBFF_corrected_bulk(P); P never constructed. Banked for P: Bcorr
(=BcorrWin+compensatorM, overlap0+holo), h_overlap wiring, freeStage→FHadmFree,
vanishingError→0, BcorrWin→0, defect eps0 (today). OPEN PILLAR: compensated-B
(B_stage − compensatorM) bounded on Ω-compacts = DBFFO3CompensatedBBound, via
adaptive_compensatedB_bounded_from_four_sectors (banked assembly; needs concrete
h_decomp identity + Qloc/Qdisp/Rtail/Qwindow bounds + HshortA — "next" per route
card, not yet built). Then P-construction file: h_expansion from split
(R_stage=(free−B)+vanishing, banked) + window lock + compensated-B; eps :=
defect+vanishing (today's gate gives h_eps0); fixed profiles {free-side,
Bshared-side}. Schedule alignment adaptive↔admissible to check (provider on
admissibleGalerkinStageSeq; gate/sectors on adaptive). grep note: --include
matches basenames only — use --include="*.lean" with dir arg, never a path glob.

## FINAL LADDER TO RH (scoped 2026-07-15, greps I1–I3; next session starts at S0)
Objects: adaptiveCombinedFreeR c n s = (adaptiveFreeStage − compensatorM) − R_stage(adaptiveSeq)
(AdaptiveCombinedFreeR.lean:32); = CompensatedB − ShortResidual on Ω (banked rewrite :38).
adaptiveShortResidual = adaptiveFirstOrderWindow + adaptiveSecondResolventResidual (banked defs).
NO concrete sectors exist yet (grep I2 empty). Consumer chain banked: four-sector assembly
(AdaptiveCombinedSectorAssembly.lean:115) → DBFFO3CompensatedBBound → Hstar → 
canonicalResidual_bounded_of_hstar (= ‖R_stage + Bcorr‖ ≤ C, the provider's canonical residual).
- S0: schedule alignment audit — sectors/gate on adaptive seq, provider+Hfree on admissible seq;
  find or build the transfer (adaptiveL = max(admL, anchor), admN ≤ adaptiveN).
- S1: concrete sector defs Qloc/Qdisp/Rtail/Qwindow + h_decomp exact identity for
  adaptiveCombinedFreeR (manuscript D.LOC/D.DISP/tail/window split). ALGEBRA + design.
- S2–S5: four sector Ω-compact bounds. Reuse: D.ADM anchor ≤ 1 (banked, anchor-factored
  converter banked) for Qloc; A.ENV-DOM envelope ladder for Rtail; TODAY'S per-spike +
  floor + gate machinery for Qwindow. ← THE LAST ANALYTIC PILLAR (old HR, canonical form).
- S6: HshortA — adaptive FOW/residual bounds (admissible epsN versions banked; transfer or re-derive).
- S7: fire assembly → CompensatedBBound → Hstar → canonical residual bounded (all consumers banked).
- S8: P-construction file — h_expansion from banked split + lock + S7; eps := defect +
  vanishingError (today's gate = h_eps0, loc_bdd = h_eps_bdd); fixed profiles; Bcorr slot banked;
  then RH_from_DBFF_corrected_bulk P : RiemannHypothesis. WIRING.
Working rules unchanged: grep before brick (--include="*.lean" + dir arg), one green piece at a
time, canonical objects only, stop condition = RH-strength estimate forces halt + obstruction report.

## ⚠ FROZEN WIRING FACT (2026-07-16 — the fact that kept getting rediscovered)
DBFFCorrectedBulkProvider.h_expansion is HARD-PINNED to admissibleGalerkinStageSeq,
whose constructor galerkinOperatorDFiniteStage_ofShift uses the RAW CODE-CENTER
potential galerkinVC (Real.log of encoded Nat codes). The decoded layer
(decodedGalerkinOperatorDFiniteStage_ofShift, physical centers (ppDecode q).center)
exists to replace exactly that operator. grep-verified 2026-07-16: NO bridge theorem
between the two constructors exists. Therefore the DBFF corrected provider is a
STALE-SHAPED endpoint for the decoded route. THE LIVE ENDPOINT is the bypass:
buildDMasterResidualDataAlong (DMasterResidualAlong.lean:20) — takes α : ℕ → DFiniteStage
FREE, needs only h_stage_holo + h_conv (R_stage(α n) → RH locally uniformly on
Ω-compacts). Plug α = decodedAdaptiveGalerkinStageSeq c. No admissible bridge needed.
Chain per memories: RH_from_selectedFiniteOperatorLayer_raw_inputs ⇐
selectedOperatorResolventBridgeDirect (consumes B,F,R,overlap directly) ⇐
DMasterResidualData ⇐ buildDMasterResidualDataAlong. FROZEN RULE unchanged: never
target ∀α : DFiniteStage or h_R_stage_bound (stale selected-Y wrapper, bypassed).

## 2026-07-16 SESSION: h_stage_holo BANKED (decoded net)
Verdict on inline paste: EXIT 0 | errors 0 | sorryAx 0 | axioms [propext, Classical.choice, Quot.sound].
- DecodedSelectedBStageHolo.lean: decoded_selected_B_stage_holo (E1 pattern, generic in stage.R).
- DecodedEigenvalueFloor.lean: continuous_decodedPrimePotentialFn_gen, decodedGalerkinV_form_eq_integral_L, decodedGalerkinV_form_nonneg_L, decodedGalerkinVC_re_form_nonneg_L, decodedEigenvalue_nonneg. Center-generic port of AdmissibleWeightNonneg + AdmissibleEigenvalueFloor; confirmed no log-exploitation in donors (form = integral of potential×trial², potential pointwise nonneg via ppWeightReal_nonneg + gaussBump_pos).
- DecodedSelectedFStageHolo.lean: decodedShiftedFStage_holo (S1 pattern: perturbedFStage_shift_eq + FstageFinite_holo_on_Omega + floor + SupVConst_nonneg_adm), decoded_selected_F_stage_holo (N4 rfl bridge: F-slot = adaptiveDensityC c n × shifted decoded F).
- DecodedSelectedRStageHolo.lean v4: decoded_selected_R_stage_holo = F − B. CONSUMER: buildDMasterResidualDataAlong.h_stage_holo (DMasterResidualAlong.lean:24) at alpha = decodedAdaptiveGalerkinStageSeq c.
PIN-FACTS added: package F-slot is α.appendixDFiniteFStage(s + SupVConst) (GalerkinStagePackage.lean:19); decoded stage F-field rfl-unfolds through decodedAdaptiveGalerkinStageSeq_F_stage with density factor; _ofShift M-shift lives in the operator only, NOT in the F-field; decoded eigenvalue floor needs NO shift (form nonneg outright, same as admissible).
REMAINING OPEN (§3): (2) h_conv [THE PILLAR], (3) decoded DFHLimitData sibling (pointwise-on-overlap may suffice; try derivation from R+B first), (4) assembly.
NEXT: h_conv route contract extraction — pin RH candidate + 1/2-density accounting BEFORE any proof Lean.

## 2026-07-16 OBSTRUCTION FINDING (route-level, audit-closed pending repair)
The pair (F : DFHLimitData, R : DMasterResidualData) with hR_alpha : R.alpha = F.alpha is
JOINTLY UNINHABITABLE for every alpha. Proof from printed structures: both convergence
fields are all-Ω-compact uniform (DOperatorExport.lean:408/514); stage split F = B + R
(GalerkinStagePackage.lean, definitional); so joint inhabitance ⟹ B = F − R compact-uniform
on all Ω-compacts ⟹ contradicts B_stage pointwise divergence inside the abs-conv parabola
(Session-9 audit, PNT main term; B net-independent by decodedAdaptiveGalerkinStage_B_stage_eq rfl;
parabola-depth points ∈ Ω). Admissible net: F conv, R div (known). Decoded net: R conv (h_conv
claim), F = R + B div. Every selectedOperatorResolventBridgeDirect_* variant printed takes this
pair ⟹ all are vacuous-shaped AS INPUT SIGNATURES.
NOT a mathematical loss: the bridge extracts from F only FH + holomorphy + POINTWISE convergence
on RightHalfPlane sigma0 (DOverlapPointwiseFromCompactUniform.lean:26; SelectedDirectDRoute.lean
takes manual pointwise hF/hB/hR) — on the overlap, F → RH + Bcan is classical. REPAIR CLASS:
overlap-scoped F structure or bridge variant consuming (FH, holo, pointwise-overlap conv) directly.
PENDING VERIFICATION before repair: which F/R structure fields the BASE bridge
(SelectedOperatorResolventBridgeDirect.lean) actually consumes.
h_conv (the pillar) is UNAFFECTED as a target: DMasterResidualData alone along the decoded net
remains the live objective; only the F-companion structure needs rescoping.

## 2026-07-16 REPAIR BANKED: decodedDirectOperatorBridge (the DFHLimitData bypass)
Verdict inline: EXIT 0 | errors 0 | sorryAx 0 | axioms [propext, Classical.choice, Quot.sound].
DecodedDirectOperatorBridge.lean: builds the FLAT OperatorResolventBridge (AnnexSpine.lean:32)
directly from (R : DMasterResidualData galerkinStagePackage, hF overlap-pointwise → FHadmFree,
hB overlap-pointwise → galerkinBcanLimitData.Bcan). h_split via stage split + tendsto_nhds_unique
(Y2 pattern). NO DFHLimitData anywhere — the jointly-uninhabitable pair is OFF the live route.
CONSUMER: RH_from_D_E (HonestEndpointV6.lean:23): D + E ⟹ RiemannHypothesis.
LIVE ROUTE (rev. 2026-07-16-b):
  h_conv [PILLAR] + h_stage_holo [BANKED today]
    → buildDMasterResidualDataAlong (alpha = decodedAdaptiveGalerkinStageSeq c, RH = pinned candidate)
    → R : DMasterResidualData galerkinStagePackage
  + hB overlap-pointwise [admissible_hB banked; decoded-net transfer by B_stage rfl]
  + hF overlap-pointwise [DERIVABLE: F = B + R pointwise + hB + R.pointwise ⟹ F → Bcan + RH;
      then need Bcan + RH = FHadmFree on overlap — THE CANDIDATE-PINNING IDENTITY, one obligation]
    → decodedDirectOperatorBridge → RH_from_D_E(D, E).
REMAINING OPEN (supersedes §3): (1) h_conv [pillar, unchanged]; (2) the overlap identity
FHadmFree = Bcan + RH_candidate (pins the candidate; classical domain Re s > 1);
(3) E : InterfaceBridgeNonnegativeAPI — status being mapped; needs D.B = H.Bzero on a threshold
half-plane, i.e. Bshared(prime side) = Bzero(zero side) — the manuscript's bridge identity.
DEPRECATED AS TARGETS: all selectedOperatorResolventBridgeDirect_* variants, selected_direct_final_RH*,
RH_from_selectedFiniteOperatorLayer_raw_inputs (all consume the uninhabitable pair or h_R_stage_bound).

## 2026-07-16 TERMINUS BANKED: RH_from_decoded_route_inputs
Verdict inline: EXIT 0 | errors 0 | sorryAx 0 | axioms [propext, Classical.choice, Quot.sound].
DecodedRouteTerminus.lean: RiemannHypothesis from exactly FOUR inputs along any alpha:
  (1) h_stage_holo — BANKED (decoded_selected_R_stage_holo, at alpha = decodedAdaptiveGalerkinStageSeq c);
  (2) h_conv — THE PILLAR (only remaining compact-uniform analysis);
  (3) hF : F_stage → FHadmFree pointwise on Re s > 1 — derivable from hB + pointwise-R once
      candidate identity FHadmFree = Bcan + RHcand on Re s > 1 is proven (pins RHcand);
  (4) hB : B_stage → Bcan pointwise on Re s > 1 — admissible_hB banked, decoded transfer by B_stage rfl.
Chain: buildDMasterResidualDataAlong → decodedDirectOperatorBridge → interfaceFromPrimeIdentity
  (E = rfl for our D: B := Bshared(prime,1), sigma0 = 1) → RH_from_D_with_prime_interface → RH.
Every link printed from disk this session. E is NOT open. DFHLimitData is OFF the route.
NEXT SESSION OPENS WITH: the h_conv contract file — pin RHcand via the candidate identity,
resolve the 1/2-density accounting on paper (seal: oneLetter = (1/2)B − BcorrWin + defect),
freeze DecodedHConvTarget, THEN the exact finite-stage error identity, THEN estimates.
Stop condition unchanged: any step needing an RH-strength global raw bound → HALT, roadmap.

## 2026-07-17B: hShort CAMPAIGN — SESSION HANDOFF (context near limit)
BANKED this session (all axiom-clean, inline-verified): decoded route wired
(2026-07-17A entries) + hShort bricks: DecodedVEntryBound
(abs_decodedVmatrixElement_le — decoded entry ≤ Σ|w|, bumpMass-free),
DecodedColumnNormBound (decodedGalerkinVC_column_norm_sq_le ≤ N·((2/L)S1)²;
abs_decodedGalerkinV_entry_le_S1), DecodedFirstOrderVanish
(decodedFirstOrderWindow_uniform_bound ≤ C/(n+2) — brick 1 DONE),
DecodedResidualUniform v3/v4 (decodedSecondResolventResidual_norm_le via
TEXTUAL CLONE of raw wrapper — method of record for decoded clones:
extract raw theorem text, substitute identifiers, build).
IN FLIGHT: decoded_residual_schedule_collapse (adaptive N/L/S1 arithmetic,
bound C₀³·146) — v4 build pending. THEN: brick 2b assembly
(uniform bound = norm_le + collapse + δ:=1/C₀ reciprocal trick from
inv_norm_le_on_compact; NO new gap provider needed), THEN hShort assembly
(FOW bound + O2 bound → decodedAdaptiveShortResidual bound), plugging into
RH_from_decoded_combined_and_short. Remaining frontier after hShort: hComb
(sector engines dDisp_sector_bound/dLoc_sector_bound/gaussian_penalty/
DTail all PROVED on disk — assembly against decodedAdaptiveCombinedFreeR).
METHOD NOTES: raw proofs' first-guards survive substitution; admR=log(n+2)/2
so e^{admR}=√(n+2), S1≤4(n+2); adaptiveN=max(admN,⌈Lad(n+2)⌉)≤3Lad(n+2);
phantom names burned twice (galerkinVC_opNorm_le, omega_compact_gap,
toEuclideanLin_opNorm_le_of_column_bound in wrong file) — ALWAYS grep before
citing. Manuscript at /tmp/ms.txt (Claude container): D.MR.2 proof 9690-9790,
D.BULK-FINITE-FORM 9152.

## 2026-07-17B: hShort CAMPAIGN — SESSION HANDOFF (context near limit)
BANKED this session (all axiom-clean, inline-verified): decoded route wired
(2026-07-17A entries) + hShort bricks: DecodedVEntryBound
(abs_decodedVmatrixElement_le — decoded entry ≤ Σ|w|, bumpMass-free),
DecodedColumnNormBound (decodedGalerkinVC_column_norm_sq_le ≤ N·((2/L)S1)²;
abs_decodedGalerkinV_entry_le_S1), DecodedFirstOrderVanish
(decodedFirstOrderWindow_uniform_bound ≤ C/(n+2) — brick 1 DONE),
DecodedResidualUniform v3/v4 (decodedSecondResolventResidual_norm_le via
TEXTUAL CLONE of raw wrapper — method of record for decoded clones:
extract raw theorem text, substitute identifiers, build).
IN FLIGHT: decoded_residual_schedule_collapse (adaptive N/L/S1 arithmetic,
bound C₀³·146) — v4 build pending. THEN: brick 2b assembly
(uniform bound = norm_le + collapse + δ:=1/C₀ reciprocal trick from
inv_norm_le_on_compact; NO new gap provider needed), THEN hShort assembly
(FOW bound + O2 bound → decodedAdaptiveShortResidual bound), plugging into
RH_from_decoded_combined_and_short. Remaining frontier after hShort: hComb
(sector engines dDisp_sector_bound/dLoc_sector_bound/gaussian_penalty/
DTail all PROVED on disk — assembly against decodedAdaptiveCombinedFreeR).
METHOD NOTES: raw proofs' first-guards survive substitution; admR=log(n+2)/2
so e^{admR}=√(n+2), S1≤4(n+2); adaptiveN=max(admN,⌈Lad(n+2)⌉)≤3Lad(n+2);
phantom names burned twice (galerkinVC_opNorm_le, omega_compact_gap,
toEuclideanLin_opNorm_le_of_column_bound in wrong file) — ALWAYS grep before
citing. Manuscript at /tmp/ms.txt (Claude container): D.MR.2 proof 9690-9790,
D.BULK-FINITE-FORM 9152.

## 2026-07-17C: FINAL HANDOFF ADDENDUM (session ended mid-brick-2b; DO NOT RE-AUDIT)
FIRST ACTION NEXT SESSION (before anything else):
  cat /tmp/b2_v4_build.log | grep -E "error" | head -15
  (v4 of DecodedResidualUniform.lean FAILED; the log holds the exact errors.
  The norm_le theorem inside it was GREEN in v3 — if v4 broke it, restore by
  rerunning the v3 generation script from transcript, then re-add ONLY the
  collapse lemma. The failure is in decoded_residual_schedule_collapse or a
  substitution artifact — read the log, fix the NAMED line, nothing else.)

STATE — BANKED AND UNTOUCHABLE (verify by #print axioms, never reprove):
  RH_from_compensatedB_locbdd | RH_from_tailSector_locbdd |
  RH_from_parabola_depth_hstar | RH_from_pairedTransform_locbdd/only |
  RH_from_decoded_combined_and_short  ← THE LIVE ENDPOINT (RH ⇐ hComb+hShort)
  decodedAdaptiveCombinedFreeR_eq | decodedFadmPrimeStage_eq_first_plus_second
  hShort brick 1 DONE: abs_decodedVmatrixElement_le,
    decodedGalerkinVC_column_norm_sq_le, decodedFirstOrderWindow_uniform_bound
  hShort brick 2 half-done: decodedSecondResolventResidual_norm_le (v3 GREEN,
    9048 jobs — if v4 regressed it, restore v3)

REMAINING PATH (exact, no alternatives, no new routes permitted):
  2b-i  fix/land decoded_residual_schedule_collapse (arith only: S1≤4(n+2),
        adaptiveN≤3·Lad·(n+2), Lad≥(n+2)³ ⟹ ratio ≤ 146)
  2b-ii decodedSecondResolventResidual_uniform_bound :=
        norm_le + collapse + δ:=1/C₀ trick (from inv_norm_le_on_compact via
        ‖z⁻¹‖≤C₀ ⟹ 1/C₀≤‖z‖; NO new gap provider — omega_compact_gap is a
        PHANTOM, does not exist)
  3     hShort assembly: decodedAdaptiveShortResidual = FOW + O2res (defn),
        triangle both banked bounds → hShort
  4     hComb: assemble against PROVED sector engines (dDisp_sector_bound,
        dLoc_sector_bound, gaussian_penalty_le_pow, DTail machinery, decoded
        Duhamel tower incl. decodedPairedOrder1Package_eq_same_add_mixed) —
        read DDispSectorBound/DLocSectorBound consumers FIRST to find the
        intended assembler; manuscript D.MR.4–7 at /tmp/ms.txt lines 9690-9790
  5     RH_from_decoded_combined_and_short hComb hShort → RiemannHypothesis

ANTI-CIRCLE RULES (violations burned money tonight — enforce):
  - PHANTOM NAMES burned 3 builds: galerkinVC_opNorm_le, omega_compact_gap,
    AdmissibleOpNormBound.lean. NEVER cite an identifier without grep proof.
  - METHOD OF RECORD for decoded clones: textual substitution of the raw
    theorem's printed text (worked first-try for norm_le). Do NOT hand-write
    clones of unseen proofs.
  - NO new reductions among O3 guises (GalerkinRStageEquivO3 audit, frozen).
  - NO re-derivation of banked bricks; grep RH_INVENTORY.md + this file first.
  - Raw-era objects (adaptiveCombinedFreeR etc.) FROZEN — decoded only.

## CORRECTION 2026-07-18 (supersedes "sector engines PROVED")
hShort CLOSED unconditionally (decoded_hShort, DecodedShortAssembly.lean,
axiom-clean). SOLE REMAINING FRONTIER: hComb.
AUDIT FINDING: dDisp_sector_bound, dLoc_sector_bound, and
R_stage_bound_of_sector_bounds are CONDITIONAL SHELLS — h_transform,
hg_intbound, h_recombine, h_sector_bound are HYPOTHESES/API fields, not
proved. Do NOT record them as engines. hComb = instantiate the sector
data for the decoded stage per manuscript D.MR.4–7: (i) concrete defs of
short/window/tail/bulk parts of decodedAdaptiveCombinedFreeR, (ii) prove
recombination identity, (iii) prove transform forms, (iv) prove density
integral bounds. NO direct estimate of CompensatedB (circularity trap).
INVENTORY RULE (new, frozen): every banked theorem is tagged
UNCONDITIONAL or CONDITIONAL-ON-{named hypotheses}. "Proved" alone is
banned from handoffs.

## SESSION 2026-07-18 STATE + CAMPAIGN ORDER (GPT constraints accepted)
BANKED TONIGHT (all axiom-clean): 2b-i collapse, 2b-ii O2 uniform bound,
decoded_hShort (hShort CLOSED), DMRSectorTimeSplit (kernel+package
short/tail split), DMROverlapBStageBound (B_stage bounded on Re s >= sigma
via banked sqrt_shift_re_ge + starDirichletPartial_bounded_off_parabola).
CONSTRAINTS (frozen): (1) hComb is SUFFICIENT for RH, equivalence not
established — but galerkin_B_stage_eq_vonMangoldt_partial_sum (banked)
shows B−M is a psi-type Dirichlet remainder; never attack it directly.
(2) No new endpoints/wrappers/providers/Montel adapters. Concrete decoded
objects only. (3) Bulk sector may NOT be defined as combined-minus-rest
unless its independent finite-profile expansion (D.BULK-FINITE-FORM,
ms p166+) is proved immediately after.
NEXT FILE: DecodedCanonicalSectorDecomposition.lean — concrete sector
defs for decodedAdaptiveCombinedFreeR over decodedAdaptiveGalerkinStageSeq
+ exact recombination from the decoded Duhamel tower. Then wire:
short := decoded_hShort object (banked) | window := BcorrWin/defect gate
(banked eps0 + BcorrWin_uniform_bound) | tail := h_fk_perturbed_galerkin
+ dTail_uniform_bound (banked cores, wiring needed) | bulk := THE open
frontier, decoded D.BULK-FINITE-FORM expansion = real pass/fail point.
TAIL ASSETS (verified on disk): DTailDensityFreeBound, DTailFreeHeatTrace-
Bound, DTailPerturbedTraceDomination (h_fk_perturbed_galerkin), DTail-
SpectralBound, DTailSumBound, DTailUniformBound, sum_heatWeight_le_sqrt,
galF_tail_uniform_bound, galFTailClosed_holo, galHead_normal_family.
GREP RULE REINFORCED: sqrt_shift_re_ge pre-existed (ShiftedLaplaceSqrtRe-
LowerBound, strict <, implicit args) — collision cost one build tonight.

## SESSION 2026-07-18 FINAL STATE — NEAR QUEUE COMPLETE
BANKED THIS SESSION (all hypothesis-free, axiom-clean, error-free):
2b-i, 2b-ii, decoded_hShort (hShort CLOSED), DMRSectorTimeSplit (x2),
DMROverlapBStageBound, sector decomposition (x2), window flank,
DMRBTailHalfplaneBound (x3), DMRRStageHalfplaneBound (x3, D.MR.2 overlap
leg), DMRFTailOmegaBound (x3, F-tail on ALL Omega-compacts + Omega-core
normal family), DMROmegaCoreMontel (proven-input AscoliExtraction),
DMROverlapLedger (x2). ~20 theorems.
DISCOVERY: admissible_hB (banked) = B_stage -> Bcan on RightHalfPlane 1.
Near queue B0-B3 DONE.
CONSUMPTION POINT: RH_from_admissible_galerkin_F_R needs DFHLimitData +
DMasterResidualData at the admissible stage; the open content of
DMasterResidualData.h_conv is the Omega-story of the arithmetic tail —
same seam as always, now fenced by ~20 theorems on every side.
NEXT BLOCK (the manuscript core, multi-session): D.SPIKE-TRANSFER finite
heat expansion (ms D.BFF.5) -> bulk profiles -> sector Omega-formulas ->
h_conv for the SECTOR-DEFINED residual -> RH_unconditional. No
conditional theorem may ever be written; every brick proves an estimate.

## CORE BLOCK OPENED — D.SPIKE-TRANSFER (ms Prop. at line ~8126, D.BFF.5)
Finite-stage skeleton BANKED: galerkinFullSandwich_trace_split (trace-level
order-1 + quad split) + quadRemainder_trace_le_integral_abs (reduction to
integral of abs trace). CORE BRICK 1 (next): pointwise integrand bound
|trace(D(t-u)·(-V)·exp((u-s)(-K))·(-V)·exp(s(-(K+V))))| <= C(n) with C(n)
explicit from heatWeight <= 1, exp-norm bounds (grep first: linftyOp
instances required, linarith fails on matrices, use abel), and the banked
column/envelope V-bounds; then integrate: quad remainder <= C(n)·u, outer
Duhamel integral gives the t^2 rate = finite-stage D.SPIKE-TRANSFER M=2.
Then: correction profile c_1 identification (the banked
galerkinFirstSplitTerm_eq_neg_duhamel1 + diagonal formula), then M
general, then bulk profiles (D.BFF), sector Omega-formulas, h_conv,
RH_unconditional. NO conditional theorems.
CORE INVENTORY UPDATE: integral_abs_duhamel2Integrand_le_const is BANKED
(N- and t-independent integrated order-2 bound, Duhamel2IntegralAbsBound).
SPIKE-TRANSFER skeleton on disk: trace split + quad reduction + order-2
integrated bound. CORE BRICK 1 (revised) = the small-t RATE: refine the
banked majorant to |E_2(t)| <= C(L,R)*t^2 on 0 < t <= t0 (D.BFF.5, M=2),
by bounding heat factors by 1 and keeping explicit t-powers instead of
the Beta-integral route. Read first: duhamel2Integrand def +
abs_duhamel2Integrand_le_sqrt statement.
CORE BRICKS 1-4 BANKED (all first-build, gated, axiom-clean, error-free):
integrand rate constant, |E1| <= B^2 N^2 t, c1 identity (order-1 integral
= t*Tr(V e^{-tK})), c1 gap O(t^2). Finite-stage D.SPIKE-TRANSFER M=2
expansion SHAPE complete. BRICK 5 = assembly into manuscript form:
Tr(full) = Tr(free) - t*Tr(V) + E2, |E2| explicit, via
galerkinDuhamel_trace_eq + trace_integral_comm_real +
galerkinFreeHeat_eq_diagonal + FullSandwich split + bricks 3-4 + DBFFO2
Born-split for the full-exp quad remainder. PROTOCOL (frozen, agreed with
GPT): gate-based CLOSES/FAILS only, no probabilities; Claude sole
builder; GPT verifier of pasted output; manuscript unaltered.
BRICK 6a BANKED (trace Frobenius-CS, self-contained). 6b LADDER (pinned):
6b-i frobSq A = Tr(A^T * A) (entry algebra); 6b-ii (exp S)^T = exp S for
symmetric S (probe: Matrix.exp_transpose vs transpose_exp under
NormedSpace.exp); 6b-iii exp S * exp S = exp(2S) (probe:
NormedSpace.exp_add_of_commute self-commute); 6b-iv REAL spectral trace
bridge Tr(exp(-tM)) = sum exp(-t*eig(M)) for real symmetric M — genuinely
new sub-brick (clone PairedTraceExpBridge's LinearMap.trace_eq_sum_inner
pattern over R, or complexify via matC banked cast + the C-typed bridge
at T = 1); then 6c: |sandwich trace| <= frob products <= via banked FK ->
|E2| <= C t^2. K+V symmetric: K diagonal + galerkinV_symm (banked).
