
## ===== UPDATE (session 3) — R1-R4 COMPLETE, only R5 remains =====
ALL GREEN, standard axioms, zero sorry, in EtaPositivity.lean:
- R1: etaA_locallyIntegrableOn (integrableOn_of_bounded on Ioo 0 b; IntegrableAtFilter via Ioo nbhd)
- R3a: etaA_mellin_Ioi_zero_eq_Ioi_one (Ioi 0 = Ioi 1; setIntegral_union + Ioc_disjoint_Ioi_same + setIntegral_eq_zero_of_ae_eq_zero, {1} null via Real.volume_singleton + compl_mem_ae_iff)
- R3b: etaI_eq_mellin (etaI s = s * mellin etaA (-s); smul_eq_mul, mul_comm, setIntegral_congr_fun)
- R4: mellin_etaA_differentiableAt + etaI_differentiableAt + etaI_analyticOnNhd
   (mellin_differentiableAt_of_isBigO_rpow a=0 b=-s.re-1; DifferentiableAt.mul/.comp; differentiable_neg; congr_of_eventuallyEq via IsOpen.mem_nhds; DifferentiableOn.analyticOnNhd)
- support: etaA_mellin_integrableOn, etaA_isBigO_atTop/_zero/_zero_param, etaA_measurable, etaA_eq_zero_of_lt_one, etaA_norm_le_one

COMPOSED: etaI_analyticOnNhd discharges etaI_eq_LFunction_of_re_pos's hypothesis.
Therefore etaI s = ZMod.LFunction etaCoeff s for ALL 0 < s.re (UNCONDITIONAL).
The integral rep = the analytic continuation. The hard analytic core is DONE.

## R5 (the ONLY remaining lemma — capstone, fresh session):
TARGET: h_real_zero_free : forall s, s.im=0, 0<s.re, s.re<1, riemannZeta s != 0.
EASY scaffolding first:
- real x in (0,1) implies (1 - 2*(2:C)^(-x)) != 0  [2^(-x) in (1/2,1), Real.rpow monotone]
- s.im=0 implies s=(s.re:C)
- with etaLFunction_eq_factor_zeta: LFunction etaCoeff x != 0 AND factor != 0 implies zeta x != 0.
HARD core: LFunction etaCoeff x != 0 for real x in (0,1).
- = etaI x != 0 (R3+R4+3b-4) = x*mellin etaA(-x); x>0 so need mellin etaA(-x) != 0.
- KEY: etaI x = (l:C), l = 3a real sum, l>0 by etaSeries_pos.
- TOOL: tendsto_sum_mul_atTop_nhds_one_sub_integral0 (AbelSummation:300).
- TEMPLATE: LSeries_eq_mul_integral_aux (SumCoeff.lean:95-135), follow line by line, adapt to etaCoeff at real s=x.
  hyps: hf_diff (ofReal_cpow_const), hf_int (integrableOn_Ioi_deriv_ofReal_cpow), h_lim (partialsum*tail to l), hg_dom/hg_int (IsBigO.mul_atTop_rpow + integrableAtFilter_rpow_atTop_iff).
- R-to-C: 3a real partial sums = ofReal of complex; etaCoeff_natCast relates etaCoeff to (-1)^(k+1).
- l>0 implies (l:C)!=0 implies done. DIFFICULTY >= R3, budget a full session.
AFTER R5: Pieces 1+2+3a+3b = complete machine-checked zeta != 0 on real (0,1), discharges RH-conditional hypothesis (1).

## ===== UPDATE 2 (session 4) — R5a DONE; R5b recon complete, all shortcuts ruled out =====
GREEN now (standard axioms, 0 sorry): factor_ne_zero (R5a) — (1 - 2*(2:C)^(-x)) != 0 for real x in (0,1).
  Proof: hb bridges (2:C)^(-(x:C)) = ofReal((2:R)^(-x)) via explicit ofReal on base+exponent then Complex.ofReal_cpow; then Real.rpow_lt_one_of_one_lt_of_neg (2^(-x)<1) and rpow_lt_rpow_left_iff with 1/2=2^(-1) (2^(-x)>1/2); factor real and <0.

R5b SHORTCUTS RULED OUT (do NOT re-investigate these — confirmed dead ends):
- LSeriesSummable on (0,1): NO. LSeriesSummable_of_isBigO_rpow needs f=O(n^(x-1)) for summability re>x; etaCoeff is O(1)=O(n^0) so only re>1. Bounded-coeff lemmas also only give re>1. The LSeries genuinely diverges on (0,1).
- ZMod.LFunction continuity/tendsto lemma usable below re=1: NONE (only residue-at-1 Tendsto at ZMod.lean:137).
- dirichletEta in Mathlib: does not exist.
- LFunction_ne_zero / riemannZeta_ne_zero shortcut: none applicable.
=> The analytic continuation IS essential and MUST be connected to the conditional sum via Abel summation. No way around it.

R5b REQUIRED ROUTE (the only path):
  GOAL: LFunction etaCoeff (x:C) != 0 for real x in (0,1). Have etaI x = LFunction etaCoeff x (etaI_eq_LFunction_of_re_pos discharged by etaI_analyticOnNhd, UNCONDITIONAL). x>0.
  Show etaI x = (l:C), l = 3a sum > 0 (etaSeries_pos), via:
  TOOL: tendsto_sum_mul_atTop_nhds_one_sub_integral0 (AbelSummation.lean:300).
  TEMPLATE (copy line-by-line, it discharges the EXACT 6 hyps for general f at complex s; adapt to etaCoeff at real x):
    LSeries_eq_mul_integral_aux, SumCoeff.lean:95-135.
    Useful helpers seen in aux: differentiableAt_id.ofReal_cpow_const (hf_diff), integrableOn_Ioi_deriv_ofReal_cpow (hf_int), deriv_ofReal_cpow_const, IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow + .mul_atTop_rpow_of_isBigO_rpow (hg_dom), integrableAtFilter_rpow_atTop_iff (hg_int).
  Also our etaI_eq_LFunction_of_one_lt_re (line ~130) already uses LSeries_eq_mul_integral for re>1 — mirror its etaCoeff_sum_isBigO input.
  R->C transfer: Complex.ofReal_tsum (Complex/Basic.lean:533); 3a real partial sums ∑(-1)^i*etaAbsTerm x i = ofReal-image of complex LSeries partial sums; etaCoeff_natCast: etaCoeff(k:ZMod 2)=(-1)^(k+1).
  Finish: l>0 => (l:C) != 0 (Complex.ofReal_ne_zero) => etaI x != 0 => LFunction etaCoeff x != 0.
  DIFFICULTY: = R3 (hardest). Budget full focused session. ~25-line aux template is the Rosetta stone.

R5c (after R5b, easy assembly):
  h_real_zero_free: combine R5b + factor_ne_zero (R5a) + etaLFunction_eq_factor_zeta + (s.im=0 => s=(s.re:C) via Complex.ext/ofReal_re_im).

## ===== MILESTONE (session 5): h_real_zero_free COMPLETE — eta track CLOSED =====
ALL GREEN, standard axioms [propext, Classical.choice, Quot.sound], ZERO sorry (grep -c sorry = 0). Build: 8463 jobs OK.

Final chain in EtaPositivity.lean:
- R5b-2 etaLSeries_partial_eq_ofReal (412): C partial sum = ofReal(real alt sum), by induction on N.
- R5b-3 etaLSeries_partial_tendsto_pos (436): C partial sums -> (l:C), l>0.
- R5b-4 piece1: etaCoeff' (zero-padded), etaCoeff'_sum_eq/_sum_isBigO/_Icc_zero_eq (444-471).
- R5b-4 piece2 etaCoeff'_engine_tendsto (521): THE Abel engine applied at real x in (0,1) where LSeries diverges. tendsto_sum_mul_atTop_nhds_one_sub_integral0 with all 6 hyps discharged. KEY LESSONS: mul_atTop_rpow_of_isBigO_rpow has a,b,c IMPLICIT (pass by name (a:=)(b:=)(c:=), not positional); isBigO_deriv_ofReal_cpow_const_atTop is BARE (no namespace); integrableOn_Ici_iff_integrableOn_Ioi is BARE; rewrite exponent (-x-1).re+0 -> -x-1 via Complex.sub_re before applying.
- R5b-4 piece3 engine_integral_eq_etaI (548): engine integral = etaI x. deriv_ofReal_cpow_const + setIntegral_congr_fun + integral_const_mul + etaA defeq.
- R5b-4 piece4 etaLSeries_partial_tendsto_etaI (558): partial sums -> etaI x.
- R5b-4 finish etaI_ne_zero_of_real (590): tendsto_nhds_unique(partial->etaI, partial->l) => etaI x = (l:C) != 0. hseq bridges Icc0/Icc1 (cases + insert 0) + mul_comm + norm_cast for double-cast.
- R5b-5 etaLFunction_ne_zero_of_real (599): LFunction etaCoeff x != 0, via etaI_eq_LFunction_of_re_pos etaI_analyticOnNhd.
- R5c h_real_zero_free (602): forall s, im=0, 0<re<1 => zeta s != 0. THE DELIVERABLE. Via etaLFunction_eq_factor_zeta + factor_ne_zero.

SCOPE: this discharges hypothesis (1) of the 3-part RH-conditional (zeta != 0 on real (0,1)). NOT a proof of RH. The other two hypotheses (hsum: zero-density summability; h_holo: explicit-formula holomorphy) are the SEPARATE track in their own files (GPT-driven), untouched here. File hygiene held: only EtaPositivity.lean edited; CurrentFrontierEndpoint.lean + root import frozen.

## ===== hsum PILLAR 2 (counting bound): bricks 1-3 GREEN + full reduction banked =====
File RHFormalization/ZetaGrowthBound.lean — ALL GREEN, standard axioms, 0 sorry:
- norm_Gamma_le_real_Gamma : ‖Γ(s)‖ ≤ Γ_ℝ(re s) for 0<re s. (Euler integral + norm_integral_le_integral_norm + norm_cpow_eq_rpow_re_of_pos.)
- norm_Gamma_vertical_le : ‖Γ(σ+it)‖ ≤ Γ_ℝ(σ) uniformly in t.
- real_Gamma_continuousOn_Icc + norm_Gamma_strip_le : ‖Γ(s)‖ ≤ C on any strip a≤re s≤b (0<a). (differentiableAt_Gamma → continuousAt → IsCompact.exists_isMaxOn.)

REMAINING pillar-2 chain to hsum (all from-scratch; Mathlib lacks these):
  (2) Γ GROWTH as ‖s‖→∞ (order 1) — NOT in Mathlib (only real stirlingSeq→√π, NatCast). From-scratch: extend Stirling to complex via Gamma_add_one recursion + integral. SUBSTANTIAL.
  (3) ξ growth = Γ-factor growth × ζ vertical-strip bound — ζ strip bound also NOT in Mathlib.
  (4) Jensen (MeromorphicOn.circleAverage_log_norm EXISTS) → N(r)=O(r log r) → strip count N(T)=O(T log T).
  (5) dyadic shells → dominating b:ℕ→ℝ → summable_density_of_enum_dominated (GREEN) → hsum.

ALREADY GREEN downstream (ZetaZeroCounting.lean): nontrivialZeros_countable (pillar 1 DONE), exists_zero_enum, summable_density_of_enum_dominated, hsum_of_zeroDensityData. hsum reduces to: produce summable b dominating density along the enum (= the counting bound, = steps 2-4).

## ===== PIVOTAL: Mathlib HAS the zero-counting theorem (AnalyticOnNhd.sum_divisor_le) =====
JensenFormula.lean:389 — AnalyticOnNhd.sum_divisor_le:
  (r_pos: 0<|r|) (r_lt_R: |r|<|R|) (hM: 1≤M) (h₁f: AnalyticOnNhd ℂ f (closedBall c |R|))
  (h₂f: f c ≠ 0) (f_bound: ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M)
  : ∑ᶠ u, divisor f (closedBall c |r|) u ≤ log(M/‖f c‖)/log(R/r)
This is the COUNTING BOUND, pre-packaged. divisor f U z = (analyticOrderAt f z).untop₀ (Divisor.lean:72) — matches our zetaZeroMult = (analyticOrderAt ζ ρ).toNat.
Mathlib also has differentiable_completedZeta₀ (completedRiemannZeta₀ ENTIRE, RiemannZeta.lean).

REVISED pillar-2 path (NO hand-rolled Jensen needed):
  (A) ‖completedRiemannZeta₀ z‖ ≤ M on spheres radius R — from our 8 Γ-bricks + a ζ bound. [the M input]
  (B) apply sum_divisor_le → weighted zero count in ball radius r ≤ log(M/‖f c‖)/log(R/r). [Mathlib]
  (C) relate divisor of completedRiemannZeta₀ to nontrivial-zero mult (zeros of ξ in strip = nontrivial ζ zeros).
  (D) dyadic radii R_k=2^k → per-shell count O(R log R) → dominating b:ℕ→ℝ.
  (E) summable_density_of_enum_dominated (GREEN) → hsum.

8 GREEN Γ-bricks banked (ZetaGrowthBound.lean): norm_Gamma_le_real_Gamma, norm_Gamma_vertical_le, norm_Gamma_strip_le, real_Gamma_continuousOn_Icc, norm_Gamma_add_one, norm_Gamma_add_nat, norm_add_nat_le, prod_norm_add_le, norm_Gamma_add_nat_le. These feed step (A).

## ===== hsum STATE after 18 bricks (both original hard nodes cleared) =====
GREEN & BANKED (ZetaCountingBound.lean, all standard axioms, 0 sorry):
- completedZeta₀_analyticOnNhd : Λ₀ analytic on every closed ball.
- completedZeta_ne_zero_of_one_lt_re : Λ ≠ 0 for re>1.
- Gammaℝ_analyticAt : Γ_ℝ analytic on {re>0}.
- analyticOrderAt_completedZeta_eq : **order Λ = order ζ on strip** (DIVISOR CORRESPONDENCE — the hard node, DONE).
- completedZeta_analyticOnNhd_of_avoid : Λ analytic on balls avoiding {0,1}.
- divisor_completedZeta_eq_mult : **Jensen divisor Λ = our zetaZeroMult** at strip points (bridge DONE).
Plus 8 Γ-growth bricks (ZetaGrowthBound.lean) + pillar-1 countability + reduction (ZetaZeroCounting.lean).

KEY EXTERNAL TOOL: AnalyticOnNhd.sum_divisor_le (Mathlib Jensen) : analytic + ‖f‖≤M on sphere ⟹ ∑ divisor ≤ log(M/‖fc‖)/log(R/r).

REMAINING to hsum:
  (i) [MECHANICAL] invoke sum_divisor_le on Λ at a strip-disc; M EXISTS for free via compactness (Λ ContinuousOn compact sphere avoiding 0,1, IsCompact.exists_isMaxOn). Gives per-disc finiteness.
  (ii) [THE LAST HARD PIECE — from-scratch] quantitative ‖Λ(σ+iT)‖ = O(T^k) polynomial growth on vertical lines. Mathlib LACKS this. Needed so log M(T) grows slowly enough for the dyadic sum to converge. Our 8 Γ-bricks feed the Γ_ℝ factor (Λ=Γ_ℝ·ζ); still need ζ vertical polynomial bound (approx functional equation / Euler-Maclaurin) — comparable to the Γ-engine in size.
  (iii) [MECHANICAL] dyadic height-shells R_k=2^k → per-shell counts via (i)+(ii) → dominating b:ℕ→ℝ → summable_density_of_enum_dominated (GREEN) → hsum.

HONEST: per-disc finiteness reachable now; full Summable hsum still needs sub-build (ii). Two of three hard pieces done.

## ===== 22 BRICKS — piece (ii) vertical bound DONE via Mellin =====
NEW (MellinBound.lean, all standard axioms, 0 sorry):
- norm_mellin_le : ‖mellin f s‖ ≤ ∫ t^(re s -1)‖f t‖  (Mellin triangle ineq — T-independence at source).
- norm_Lambda0_le : abstract WeakFEPair, ‖Λ₀ s‖ ≤ ∫ t^(re s -1)‖f_modif‖.
- norm_completedRiemannZeta0_le : ‖Λ₀_ζ(s)‖ ≤ (∫ t^(s.re/2 -1)‖f_modif‖)/2 — T-UNIFORM (depends on re s only).
- norm_completedRiemannZeta_le : ‖Λ(s)‖ ≤ ‖Λ₀(s)‖ + 1/‖s‖ + 1/‖1-s‖ (transfer via Λ=Λ₀-poles).

KEY WIN: vertical growth control (feared as Euler-Maclaurin epic) DONE via Mellin in 4 bricks. ‖Λ(σ+iT)‖ bounded UNIFORMLY in T by a function of σ.

REMAINING for hsum:
  (ii-rest) relate vertical bound to Jensen M on a sphere; the bound integral ∫ t^(σ/2-1)‖f_modif‖ is finite (Mellin converges) and bounded on compact σ-range → concrete M. [MECHANICAL-ish]
  (ii-subtle) center-value control: log(M/‖Λ(center)‖) in sum_divisor_le needs ‖Λ(center)‖ not too small. Classical RvM technique (good center / averaging). [REAL remaining content]
  (iii) dyadic height-shells → per-shell counts → dominating b → summable_density_of_enum_dominated (GREEN) → hsum. [MECHANICAL]

HONEST: T-uniform vertical bound done (worst fear cleared). Center-value control + dyadic sum remain — tractable but real bookkeeping, not trivial.

## ===== 23 BRICKS — growth→Nevanlinna proximity bridge DONE =====
NEW (NevanlinnaBound.lean): proximity_completedRiemannZeta0_le : proximity Λ₀ ⊤ r ≤ log⁺ M(r), M = circle-sup of ‖Λ₀‖ (via compactness). Connects our Mellin growth bound to Nevanlinna proximity.

MATHLIB NEVANLINNA MACHINERY CONFIRMED PRESENT (Analysis/Complex/ValueDistribution/):
- proximity f a = circleAverage log⁺‖f-a‖ ; proximity_top, proximity_nonneg, proximity_inv.
- logCounting f a (Nevanlinna N(r)); logCounting f 0 = zeros, logCounting f ⊤ = poles; logCounting_inv: N(f⁻¹,⊤)=N(f,0); logCounting_top=0 for entire.
- characteristic = proximity + logCounting ; First Main Theorem: characteristic_sub_characteristic_inv_le (|T(f,⊤)-T(f⁻¹,⊤)| ≤ const), abs_characteristic_sub_characteristic_shift_le.
- LIMITATION: Asymptotic.lean only has BOUNDED-iff-analytic (qualitative). The QUANTITATIVE N=O(log) is explicitly TODO in Mathlib — we assemble it ourselves from FMT pieces.

REMAINING CHAIN to hsum (pieces exist, multi-brick assembly):
  - logCounting Λ₀ 0 ≤ characteristic Λ₀ 0 (proximity≥0) [1 brick]
  - characteristic Λ₀ 0 = characteristic Λ₀ ⊤ + O(1) via FMT + logCounting_inv [few bricks]
  - characteristic Λ₀ ⊤ = proximity Λ₀ ⊤ (logCounting⊤=0, entire) [1 brick]
  → N(r)=logCounting Λ₀ 0 r ≤ log⁺ M(r)+O(1) [integrated zero count bounded by growth]
  - integrated N(r) → raw per-disk count n(r): use sum_divisor_le (HAVE) or N-monotonicity [bricks]
  - STRIP-HEIGHT SEPARATION: logCounting counts origin-disks (mixes trivial zeros + all heights). Isolate critical-strip zeros by height. [THE fiddly remaining piece]
  - M(r) growth control (Mellin σ-growth) + dyadic sum → dominating b → summable_density_of_enum_dominated (GREEN) → hsum [bricks]

HONEST: growth→proximity DONE. Remaining = real multi-session RvM assembly; every piece exists or has our analogue; tractable but substantial. Hardest conceptual fears (growth bound, Nevanlinna framework) resolved.

## ===== 28 BRICKS — SEGMENT C COMPLETE: growth → integrated zero count =====
NEW bricks (NevanlinnaBound.lean), all GREEN, standard axioms:
  23. proximity_completedRiemannZeta0_le : proximity Λ₀ ⊤ r ≤ log⁺ M (M = circle-sup, compactness)
  24. logCounting_le_characteristic : N(r) ≤ T(r) (proximity ≥ 0)
  25. logCounting_completedZeta0_top_eq_zero : logCounting Λ₀ ⊤ = 0 (entire, no poles)
  26. characteristic_completedZeta0_top_le : T(Λ₀,⊤) ≤ log⁺ M (combines 23+25)
  27. characteristic_completedZeta0_zero_eq_inv_top : T(Λ₀,0) = T(Λ₀⁻¹,⊤) (proximity_inv+logCounting_inv)
  28. logCounting_completedZeta0_zero_le : N(r)=logCounting Λ₀ 0 r ≤ log⁺ M + C  [SEGMENT C DONE]
     (chain: N ≤ T(0) = T(f⁻¹,⊤) ≤ T(⊤)+C ≤ log⁺M+C, FMT via characteristic_sub_characteristic_inv_le)

STRUCTURAL BRIDGE COMPLETE: Mellin growth bound → full Nevanlinna apparatus → integrated zero count N(r) ≤ log⁺M(r)+C. The "growth controls integrated zero count" half of RvM is machine-checked.

KEY SIMPLIFICATIONS DISCOVERED:
  - Λ₀ zeros = nontrivial ζ-zeros EXACTLY (trivial zeros cancelled by Γ-poles in completion). NO trivial-zero separation needed in the count — Λ₀ is clean.
  - For nontrivial ρ: 0<re<1 so |ρ| ~ |γ|. Origin-disks |z|≤r ≈ height-bands |γ|≤r. Strip-height separation reduces to this bounded-real-part observation.
  - Convergence arithmetic CONFIRMED: ∑_ρ 1/(1+γ²) = ∑_k n(k)/(1+k²), n(k)=#{ρ: γ∈[k,k+1)}. RvM n(k)=O(log k) ⟹ ∑ log(k)/k² CONVERGES.

REMAINING TO hsum:
  SEGMENT E1 (THE CRUX): M(r)=sup_{|z|=r}‖Λ₀‖ ≤ exp(O(r log r)). Needs UPPER bound on Mellin integral ∫ t^(σ/2-1)‖f_modif‖ ~ Γ(σ/2) ≤ exp(O(σ log σ)). 
    Mathlib Stirling.lean = FACTORIAL version (le_factorial_stirling lower bound, factorial_isEquivalent_stirling ~, le_log_factorial_stirling). NOT Gamma directly, mostly LOWER bounds.
    → SUB-BUILD needed: bridge factorial-Stirling → Γ upper bound (via Γ(n+1)=n!, BohrMollerup log-convexity for non-integer, + upper direction). Several bricks, tractable.
  SEGMENT D: integrated N(r) → raw n(r) (logCounting_monotoneOn: n(r)log2 ≤ N(2r)-N(r); OR our sum_divisor_le).
  SEGMENT E2: connect n(r) to ∑ over nontrivial zeros |ρ|≤r via |ρ|~|γ|; dyadic height-shells.
  SEGMENT F: dyadic sum → dominating b:ℕ→ℝ → summable_density_of_enum_dominated (GREEN) → hsum.

HONEST: Structural bridge DONE (28 bricks). Remaining = convergence rate (Segment E1 needs Γ-upper-bound sub-build, bridging extant factorial-Stirling) + assembly (D,E2,F, pieces confirmed). NO conceptual wall remains — all pieces exist or are tractable bridges. Substantial but mechanical.

## ===== 32 BRICKS — hsum FULLY REDUCED to one count-rate statement =====
NEW reduction bricks (all GREEN, standard axioms):
  29. summable_density_of_partialSum_bdd (DensityPartialSum.lean): hsum ⟸ ∀ finite S, ∑_S density ≤ C. Via summable_of_sum_le (nonneg+bdd partial sums).
  30. hsum_of_band_bound (DensityBandBound.lean): hsum ⟸ summable nonneg bound:ℕ→ℝ with band-k density-sum ≤ bound k. Partition by ⌊|im|⌋₊ via sum_fiberwise_of_maps_to.
  31. band_density_le_count_div (BandDensityWeight.lean): band-k density-sum ≤ (band-k mult-sum)/(1+k²). Via k≤|im| ⟹ 1+k²≤1+im², sq_le_sq.
  32. hsum_of_count_rate (HsumFromRate.lean): **MASTER REDUCTION**. hsum ⟸ ∃ rate:ℕ→ℝ, (nonneg) ∧ (∀ finite S, band-k mult-sum ≤ rate k) ∧ (Summable (rate k/(1+k²))).

REDUCTION INFRASTRUCTURE COMPLETE. hsum ⟺ produce `rate : ℕ→ℝ` with:
  (a) rate k ≥ 0
  (b) ∀ finite S of nontrivial zeros, ∑_{ρ∈S, ⌊|im ρ|⌋₊=k} mult(ρ) ≤ rate k   [the COUNT]
  (c) Summable (fun k => rate k/(1+k²))                                          [RvM CONVERGENCE]

REMAINING = construct this `rate` (Segment D + E1). HONEST DIFFICULTY:
  - (b) the COUNT: band-k zeros sit in disk ~radius 1 around (1/2)+i(k+1/2) (k=0 needs shift to avoid 0,1). Use sum_divisor_le on Λ (have completedZeta_analyticOnNhd_of_avoid, divisor_completedZeta_eq_mult). Gives rate k = log(M_k/‖Λ(center_k)‖)/log(R/r). Real geometric+finsum bricks.
  - (c) CONVERGENCE is THE CRUX: need rate k = O(log k) (true RvM) for ∑ log(k)/k² < ∞. But naive rate k ~ log(M_k) where M_k ~ ‖Λ‖ ~ Γ(k)·poly ~ exp(k log k), giving rate k ~ k log k ⟹ ∑ log(k)/k DIVERGES. 
    Getting O(log k) needs SHARP count: log(M_k/‖Λ(center)‖) small, requiring BOTH Γ-Stirling UPPER bound (numerator M_k) AND center-value LOWER bound ‖Λ(center)‖ (so ratio is small). Center lower bound = choosing centers where ζ doesn't dip — genuinely delicate.
    THIS IS THE HARD HEART OF RvM. Mathlib has neither the Γ-Stirling upper bound (only factorial-Stirling lower) nor center lower bounds. Multi-session analytic sub-build.

STATUS: Reduction DONE (32 bricks) — hsum is ONE clean statement. Remaining `rate` construction = sharp RvM (Γ-Stirling upper + center lower bounds), genuinely hard, Mathlib doesn't provide. The reduction is real substantial progress; the final analytic core remains the deep part.
