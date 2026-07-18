import RHFormalization.HMeromorphicPackage
import RHFormalization.DNativeUnboundedOperator
import RHFormalization.DHeatTraceSummability
import RHFormalization.DResolventTraceSummability
import RHFormalization.DSuperSmoothing
import RHFormalization.CanonicalPrimePowerPackage


/-!
# RHFormalization.DOperatorExport

Iteration 8: Appendix-D operator-side export skeleton.

The manuscript's Appendix D must export the operator-side package consumed in
Appendices E and F:

  FH ∈ O(Ω), RH ∈ O(Ω),
  FH(s) = Bcan(s) + RH(s) on a nonempty overlap half-plane.

It does **not** export global holomorphy of `Bcan`.

This file makes the Appendix-D chain explicit:

1. finite cutoff/window stages;
2. canonical window normalization;
3. finite-stage split;
4. residual sector bounds;
5. master residual/Montel package;
6. CAN-REM;
7. D.EXPORT, which builds `OperatorResolventBridge`.

Hard analytic estimates remain API-level, but the formal dependencies are now
visible and faithful to the manuscript.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Finite cutoff/window stages
-/

/--
A finite Appendix-D cutoff stage.

`L` is the window scale and `R` is the prime-power cutoff.
The actual Hilbert-space/operator data are not represented here yet; this is the
interface index used by the D export layer.
-/
structure DFiniteStage where
  L : ℝ
  R : ℝ
  hL_pos :
    0 < L
  hR_pos :
    0 < R

  /-- Native Hilbert-space carrier for the fixed finite-stage operator. -/
  E : Type

  /-- Normed additive group structure on the native Hilbert space. -/
  [instNormed : NormedAddCommGroup E]

  /-- Complex inner-product-space structure on the native Hilbert space. -/
  [instInner : InnerProductSpace ℂ E]

  /-- Completeness of the native Hilbert space. -/
  [instComplete : CompleteSpace E]

  /-- Mathlib-native unbounded self-adjoint operator core. -/
  native :
    NativeUnboundedDStage E

  /-- Spectral eigenvalue proxy for the finite-stage heat trace. -/
  heatEigenvalue :
    ℕ → ℝ

  /-- Positive scale for the finite-stage eigenvalue lower-growth bound. -/
  heatScale :
    ℝ

  /-- Positivity of the heat-trace scale. -/
  h_heatScale_pos :
    0 < heatScale

  /-- Linear lower-growth bound sufficient for heat-series summability. -/
  h_heatEigenvalue_linear_lower :
    ∀ n : ℕ, (n : ℝ) ≤ heatEigenvalue n / heatScale

  /-- Spectral summand proxy for the finite-stage resolvent trace. -/
  resolventTraceTerm :
    ℂ → ℕ → ℂ

  /-- Constant controlling the resolvent trace summand by a p-series bound. -/
  resolventBoundConstant :
    ℂ → ℝ

  /-- Nonnegativity of the resolvent comparison constant on Ω. -/
  h_resolventBoundConstant_nonneg :
    ∀ s : ℂ, s ∈ Ω → 0 ≤ resolventBoundConstant s

  /-- p-series comparison bound for the finite-stage resolvent trace summand. -/
  h_resolventTraceBound :
    ∀ s : ℂ, s ∈ Ω →
      ∀ n : ℕ,
        ‖resolventTraceTerm s n‖ ≤
          resolventBoundConstant s * ((1 : ℝ) / (n : ℝ) ^ 2)

  /-- Nonnegative trace-norm size of the fixed-stage Duhamel/Dyson terms. -/
  duhamelTraceNormTerm :
    ℕ → ℝ

  /-- Nonnegativity of the trace-norm term sequence. -/
  h_duhamelTraceNormTerm_nonneg :
    ∀ k : ℕ, 0 ≤ duhamelTraceNormTerm k

  /-- Summable majorant for the Duhamel/Dyson trace-norm terms. -/
  duhamelMajorant :
    ℕ → ℝ

  /-- Nonnegativity of the Duhamel majorant. -/
  h_duhamelMajorant_nonneg :
    ∀ k : ℕ, 0 ≤ duhamelMajorant k

  /-- Duhamel trace-norm term controlled by the summable majorant. -/
  h_duhamelTraceNormTerm_bound :
    ∀ k : ℕ, duhamelTraceNormTerm k ≤ duhamelMajorant k

  /-- Summability of the Duhamel/Dyson majorant. -/
  h_duhamelMajorant_summable :
    Summable duhamelMajorant

  /-- Nonnegative size sequence for mixed-word/super-smoothing remainders. -/
  mixedWordRemainder :
    ℕ → ℝ

  /-- Nonnegativity of the mixed-word remainder size sequence. -/
  h_mixedWordRemainder_nonneg :
    ∀ k : ℕ, 0 ≤ mixedWordRemainder k

  /-- Super-polynomial decay certificate for the mixed-word remainder. -/
  h_mixedWordSuperPolynomialDecay :
    SuperPolynomialDecay mixedWordRemainder

  /-- Predicate selecting the active finite-stage prime-power spike indices. -/
  diagonalSpikeActive :
    ℕ → Prop

  /-- The actual diagonal/first-order contribution extracted from the finite-stage operator. -/
  diagonalSpikeContribution :
    ℕ → ℂ

  /-- The canonical prime-power spike contribution with the manuscript's frozen normalization. -/
  canonicalSpikeContribution :
    ℕ → ℂ

  /--
  Fixed-stage diagonal spike extraction certificate.

  This is the formal placeholder for the Appendix-D calculation proving that the
  diagonal/first-order contribution equals the canonical prime-power spike package
  on the active finite-stage prime-power indices.
  -/
  h_diagonalSpikeExtraction :
    ∀ q : ℕ,
      diagonalSpikeActive q →
        diagonalSpikeContribution q = canonicalSpikeContribution q

/--
Finite-stage functions produced by Appendix D.

`F_stage` is the finite regularized/canonical transform.
`B_stage` is the finite shifted canonical prime-power package on the overlap.
`R_stage` is the finite remainder.
-/
structure DFiniteStagePackage where
  F_stage : DFiniteStage → ℂ → ℂ
  B_stage : DFiniteStage → ℂ → ℂ
  R_stage : DFiniteStage → ℂ → ℂ
  sigma0 : ℝ

/--
Finite-stage split on the overlap half-plane.

This represents the fixed-cutoff identity:
`F_{L,R} = B_{L,R} + R_{L,R}`.
-/
structure DFiniteStageSplitAPI
    (P : DFiniteStagePackage) where
  h_stage_split :
    ∀ α : DFiniteStage,
    ∀ s : ℂ, s ∈ RightHalfPlane P.sigma0 →
      P.F_stage α s = P.B_stage α s + P.R_stage α s

/-!
## 2. Canonical window normalization
-/

/--
The finite-window displacement kernel used in D.CANONICAL-WINDOW.

`gbar_stage α a` is the density-normalized finite-window kernel
corresponding to `(2L)^{-1} g_{t,L}(a)` after fixing the time parameter.
-/
structure DCanonicalWindowData where
  gbar_stage : DFiniteStage → ℝ → ℂ
  G_limit : ℝ → ℂ
  c_w : ℂ

/--
D.CANONICAL-WINDOW.

On compact `a`-intervals, the density-normalized finite-window kernel converges
to the canonical heat kernel with normalization constant `c_w`.

For the manuscript's centered sharp window, `c_w = 1`.
-/
structure DCanonicalWindowAPI
    (W : DCanonicalWindowData) where

  /--
  The finite-stage exhaustion along which the window kernels converge.
  -/
  alpha :
    ℕ → DFiniteStage

  h_cw_eq_one :
    W.c_w = 1

  /--
  D.CANONICAL-WINDOW as an explicit compact-uniform epsilon statement.

  On every compact real displacement set `A`, the finite-window kernel
  `gbar_stage (alpha n)` converges uniformly to `c_w • G_limit`.

  Since `h_cw_eq_one` later gives `c_w = 1`, this becomes convergence to the
  canonical limiting heat kernel `G_limit`.
  -/
  h_local_uniform_window :
    ∀ A : Set ℝ,
      IsCompact A →
        ∀ ε : ℝ,
          0 < ε →
            ∀ᶠ n in Filter.atTop,
              ∀ a : ℝ,
                a ∈ A →
                  dist
                    (W.gbar_stage (alpha n) a)
                    (W.c_w * W.G_limit a) < ε

/--
Prime-power normalization used by Appendix D.

The full prime-power indexing layer is not yet formalized; this records the
same scalar convention as the manuscript:
`w(q)=Λ(q)/√q`.
-/
structure DPrimePowerNormalization where
  center : ℝ → ℝ

  /--
  The von Mangoldt / prime-power numerator assigned to the real prime-power
  parameter `q`.
  -/
  lambdaWeight : ℝ → ℝ

  /--
  The actual D-side prime-power weight.
  -/
  weight : ℝ → ℝ

  /--
  The weight is exactly the manuscript normalization

    `lambdaWeight q / sqrt q`.

  Equivalently, `weight q = spikeWeight (lambdaWeight q) q`.
  -/
  h_weight_eq_spikeWeight :
    ∀ q : ℝ, weight q = spikeWeight (lambdaWeight q) q

/-!
## 3. Canonical package limits
-/

/--
Canonical package limit on the overlap half-plane.

This is the D-side limiting package `Bcan` used only on an overlap half-plane.
Appendix D does not claim that `Bcan` is holomorphic on all of `Ω`.
-/
structure DBcanLimitData
    (P : DFiniteStagePackage) where
  Bcan : ℂ → ℂ

  /--
  The shared canonical prime-power package represented by the D-side limiting
  package on the overlap half-plane.
  -/
  Cshared : CanonicalPrimePowerPackage

  /--
  The D-side overlap half-plane is at least as far right as the intrinsic
  convergence half-plane of the shared package.
  -/
  h_Cshared_sigma_le :
    Cshared.sigma0 ≤ P.sigma0

  /--
  Appendix-D package identity against the shared canonical package on the
  overlap half-plane.
  -/
  h_Bcan_matches_shared :
    ∀ s : ℂ, s ∈ RightHalfPlane P.sigma0 →
      Bcan s = Cshared.Bshared s

/--
Canonical transform limit.

This is the eventual `FH` exported by Appendix D.
-/
structure DFHLimitData
    (P : DFiniteStagePackage) where

  /--
  Ordered finite-stage exhaustion along which the finite canonical transforms
  converge.
  -/
  alpha :
    ℕ → DFiniteStage

  FH : ℂ → ℂ
  h_FH_holo : HolomorphicOnC FH Ω

  /--
  D.FH-LIMIT compact-local convergence.

  On every compact `K ⊆ Ω`, the finite-stage transforms `F_stage (alpha n)`
  converge uniformly to `FH`.
  -/
  h_F_stage_to_FH :
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∀ ε : ℝ,
          0 < ε →
            ∀ᶠ n in Filter.atTop,
              ∀ s : ℂ,
                s ∈ K →
                  dist (P.F_stage (alpha n) s) (FH s) < ε

/-!
## 4. Residual sector decomposition
-/

/-- The four residual sectors used by D.MASTER-RESIDUAL. -/
inductive DResidualSector where
  | short
  | window
  | tail
  | bulk
  deriving Repr, DecidableEq

/--
Residual sector functions.

Each sector is a finite-stage holomorphic/remainder contribution whose compact
bounds feed the master residual theorem.
-/
structure DResidualSectorData
    (P : DFiniteStagePackage) where
  sectorPart : DResidualSector → DFiniteStage → ℂ → ℂ

/--
Sector compact-bound API.

This represents the concrete estimates for short/window/tail/bulk sectors.
-/
structure DResidualSectorBoundsAPI
    (P : DFiniteStagePackage)
    (S : DResidualSectorData P) where

  /--
  Compact-uniform sector bound.

  For each residual sector and each compact `K ⊆ Ω`, the finite-stage sector
  contribution is uniformly bounded on `K`, independently of the finite stage.
  This is the explicit estimate input needed by `D.MASTER-RESIDUAL`.
  -/
  h_sector_bound :
    ∀ sector : DResidualSector,
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∃ C : ℝ,
          0 ≤ C ∧
            ∀ α : DFiniteStage,
            ∀ s : ℂ,
              s ∈ K →
                ‖S.sectorPart sector α s‖ ≤ C

/--
Sector recombination API.

The finite remainder is the sum of the four sector pieces.
-/
structure DResidualSectorSplitAPI
    (P : DFiniteStagePackage)
    (S : DResidualSectorData P) where
  h_recombine :
    ∀ α : DFiniteStage,
    ∀ s : ℂ,
      P.R_stage α s =
        S.sectorPart DResidualSector.short α s
        + S.sectorPart DResidualSector.window α s
        + S.sectorPart DResidualSector.tail α s
        + S.sectorPart DResidualSector.bulk α s

/-!
## 5. D.MASTER-RESIDUAL and D.CAN-REM
-/

/--
Master residual data.

`RH` is the canonical holomorphic remainder obtained after ordered cutoff removal.
-/
structure DMasterResidualData
    (P : DFiniteStagePackage) where

  /--
  Ordered finite-stage exhaustion along which the residuals converge.
  -/
  alpha :
    ℕ → DFiniteStage

  RH : ℂ → ℂ
  h_RH_holo : HolomorphicOnC RH Ω

  /--
  D.MASTER-RESIDUAL compact-local convergence.

  On every compact `K ⊆ Ω`, the finite-stage residuals `R_stage (alpha n)`
  converge uniformly to the canonical holomorphic remainder `RH`.
  -/
  h_R_stage_to_RH :
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∀ ε : ℝ,
          0 < ε →
            ∀ᶠ n in Filter.atTop,
              ∀ s : ℂ,
                s ∈ K →
                  dist (P.R_stage (alpha n) s) (RH s) < ε

/--
D.MASTER-RESIDUAL.

From the sector split and compact sector bounds, obtain the canonical holomorphic
remainder on `Ω`.

This packages the Montel/normal-family/uniqueness step.
-/
structure DMasterResidualAPI
    (P : DFiniteStagePackage)
    (S : DResidualSectorData P) where
  h_master :
    DResidualSectorSplitAPI P S →
    DResidualSectorBoundsAPI P S →
    DMasterResidualData P

/--
D.CAN-REM.

The canonical remainders converge locally uniformly on `Ω`-compacts to a
holomorphic `RH`, and the overlap identity is available once the finite split
and package limits are combined.
-/
structure DCanRemAPI
    (P : DFiniteStagePackage)
    (B : DBcanLimitData P)
    (F : DFHLimitData P)
    (R : DMasterResidualData P) where
  h_remainder_holo :
    HolomorphicOnC R.RH Ω

  /--
  D.CAN-REM compact-local residual convergence.

  This is the same convergence exported by `DMasterResidualData`, restated at
  the CAN-REM layer so downstream D.EXPORT code can consume it directly.
  -/
  h_can_rem_convergence :
    ∀ K : Set ℂ,
      IsCompact K →
      K ⊆ Ω →
        ∀ ε : ℝ,
          0 < ε →
            ∀ᶠ n in Filter.atTop,
              ∀ s : ℂ,
                s ∈ K →
                  dist (P.R_stage (R.alpha n) s) (R.RH s) < ε

/--
Overlap identity exported by Appendix D:
`FH = Bcan + RH` on the overlap half-plane.
-/
structure DOverlapIdentityAPI
    (P : DFiniteStagePackage)
    (B : DBcanLimitData P)
    (F : DFHLimitData P)
    (R : DMasterResidualData P) where
  h_overlap :
    ∀ s : ℂ, s ∈ RightHalfPlane P.sigma0 →
      F.FH s = B.Bcan s + R.RH s

/-!
## 6. D.EXPORT
-/

/--
Appendix-D export layer.

This is the precise D-side object needed by the D/H/E/F spine.
It owns:
* `FH ∈ O(Ω)`;
* `RH ∈ O(Ω)`;
* local overlap split `FH = Bcan + RH`.

It deliberately does not assert `Bcan ∈ O(Ω)`.
-/
structure DExportLayer where
  P : DFiniteStagePackage
  B : DBcanLimitData P
  F : DFHLimitData P
  R : DMasterResidualData P
  canRem : DCanRemAPI P B F R
  overlap : DOverlapIdentityAPI P B F R

/-- Build the abstract `OperatorResolventBridge` consumed by E/F from D.EXPORT. -/
def buildOperatorResolventBridgeFromDExport
    (D : DExportLayer) :
    OperatorResolventBridge :=
  { FH := D.F.FH
    B := D.B.Bcan
    RH := D.R.RH
    sigma0 := D.P.sigma0
    hFH_holo := D.F.h_FH_holo
    hRH_holo := D.R.h_RH_holo
    h_split := D.overlap.h_overlap }

/-!
## 7. Constructor from detailed D ingredients
-/

/--
Full Appendix-D construction scaffold.

This collects the detailed ingredients and produces the final export layer.
-/
structure DDetailedConstructionLayer where
  W : DCanonicalWindowData
  Wapi : DCanonicalWindowAPI W
  P : DFiniteStagePackage
  finiteSplit : DFiniteStageSplitAPI P
  B : DBcanLimitData P
  F : DFHLimitData P
  sectors : DResidualSectorData P
  sectorSplit : DResidualSectorSplitAPI P sectors
  sectorBounds : DResidualSectorBoundsAPI P sectors
  master : DMasterResidualAPI P sectors
  overlapBuilder :
    let Rdata := master.h_master sectorSplit sectorBounds
    DOverlapIdentityAPI P B F Rdata

/-- Extract the D export layer from the detailed Appendix-D construction data. -/
def DDetailedConstructionLayer.toDExportLayer
    (X : DDetailedConstructionLayer) :
    DExportLayer :=
  let Rdata := X.master.h_master X.sectorSplit X.sectorBounds
  { P := X.P
    B := X.B
    F := X.F
    R := Rdata
    canRem :=
      { h_remainder_holo := Rdata.h_RH_holo
        h_can_rem_convergence := Rdata.h_R_stage_to_RH }
    overlap := X.overlapBuilder }

/-- Extract the operator bridge directly from the detailed Appendix-D construction. -/
def DDetailedConstructionLayer.toOperatorResolventBridge
    (X : DDetailedConstructionLayer) :
    OperatorResolventBridge :=
  buildOperatorResolventBridgeFromDExport X.toDExportLayer

end

end RHFormalization
