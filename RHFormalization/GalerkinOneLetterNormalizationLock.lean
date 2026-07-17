import RHFormalization.GalerkinDisplacementKernel
import RHFormalization.GalerkinStagePackage
import RHFormalization.DBFFBcorrWindow
import Mathlib

/-!
# One-letter normalization lock — BRICK 3a of the canonical-F route

ROUTE CARD
1. Target: the exact interface between the displacement-paired one-letter
   transform and the banked arithmetic package. Repo box is `[0,L]`
   (dirichletEigenfun), density is `1/(2L)` (admDensityC) — manuscript's
   `2L` convention on a width-`L` box. Continuum window factor is therefore
   `(L−a)₊`, numerically verified (ratio → 1 with N).
2. THE LOCK (this file, pure Finset algebra): density-normalized windowed
   package = `(1/2)·B_stage − BcorrWin`. The factor `1/2` is the honest
   box-width bookkeeping; the F-slot density choice for the canonical stage
   resolves it (flagged decision, certified here, decided at install time).
3. Also defined: the finite spike transform (explicit rational sum — the
   Laplace transform of `g_gal` in finite dimension) and the finite-N
   defect object (the continuum formula is NOT exact at finite N; the
   defect must become window-sector/eps content).
4. Everything pair-indexed with physical `q.center` — no code/center mixing.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- **Windowed canonical package** on the width-`L` box: the arithmetic image
of the continuum one-letter kernel `G_t(a)·(L−a)₊` after density
normalization `1/(2L)` and the shifted Laplace transform. -/
def windowedCanonicalPackage
    (I : Finset PrimePowerPair) (L : ℝ) (K : CanonicalKernelC) (s : ℂ) : ℂ :=
  ∑ q ∈ I, q.weightC * (((L - q.center) / (2 * L) : ℝ) : ℂ) * K q.center s

/-- Cast helper: the window factor splits as `1/2 − a/(2L)`. -/
theorem windowFactor_split (L a : ℝ) (hL : L ≠ 0) :
    (((L - a) / (2 * L) : ℝ) : ℂ)
      = (1 / 2 : ℂ) - ((a / (2 * L) : ℝ) : ℂ) := by
  have h : ((L - a) / (2 * L) : ℝ) = 1 / 2 - a / (2 * L) := by
    first
      | (field_simp; ring)
      | field_simp
      | (rw [sub_div]; congr 1; field_simp)
  rw [h]
  push_cast
  ring

/-- **THE NORMALIZATION LOCK.** The windowed package is exactly half the bare
canonical package minus the window deficit — every normalization (weight,
kernel, shift, branch, `1/(2w)`, window factor, density) certified in one
identity. Pure algebra. -/
theorem windowedCanonicalPackage_lock
    (I : Finset PrimePowerPair) (L : ℝ) (hL : L ≠ 0)
    (K : CanonicalKernelC) (s : ℂ) :
    windowedCanonicalPackage I L K s
      = (1 / 2 : ℂ) * finiteCanonicalPrimePowerPackage I K s
        - ∑ q ∈ I, q.weightC * ((q.center / (2 * L) : ℝ) : ℂ) * K q.center s := by
  unfold windowedCanonicalPackage finiteCanonicalPrimePowerPackage
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [windowFactor_split L q.center hL]
  ring

/-- **The lock at the admissible stage**: windowed package =
`(1/2)·B_stage − BcorrWin`. Certifies the interface against the LIVE banked
objects (closed definitionally — B_stage and BcorrWin match on the nose). -/
theorem windowedCanonical_eq_half_Bstage_sub_BcorrWin (n : ℕ) (s : ℂ) :
    windowedCanonicalPackage
        (activePrimePowerPairsCenterBelow (admR n)) (admL n)
        shiftedLaplaceHeatKernelC s
      = (1 / 2 : ℂ) *
          galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - BcorrWin n s := by
  have hL : admL n ≠ 0 := (admL_pos' n).ne'
  exact windowedCanonicalPackage_lock
    (activePrimePowerPairsCenterBelow (admR n)) (admL n) hL
    shiftedLaplaceHeatKernelC s

/-- **Finite spike transform**: the shifted Laplace transform of
`g_gal(t,a) = Σ_m e^{−tμ_m}(T_a)_{mm}` in finite dimension — an explicit
rational sum. Generic in the free spectrum `μ`. -/
def galerkinSpikeTransform (μ : Fin N → ℝ) (L a : ℝ) (s : ℂ) : ℂ :=
  ∑ m : Fin N,
    ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
      (1 / (s + (1 / 4 : ℂ) + ((μ m : ℝ) : ℂ)))

/-- **Density-normalized decoded one-letter transform** — the arithmetic
face of the new F-slot's one-letter sector, physical centers throughout. -/
def decodedOneLetterTransform
    (μ : Fin N → ℝ) (I : Finset PrimePowerPair) (L : ℝ) (s : ℂ) : ℂ :=
  ((1 / (2 * L) : ℝ) : ℂ) *
    ∑ q ∈ I, q.weightC * galerkinSpikeTransform (N := N) μ L q.center s

/-- **The finite-N defect** (the continuum overlap formula is NOT exact at
finite N; this object must be provider-legal — window sector or eps — and
tend to 0 along the net). -/
def galerkinOneLetterDefect
    (μ : Fin N → ℝ) (I : Finset PrimePowerPair) (L : ℝ)
    (K : CanonicalKernelC) (s : ℂ) : ℂ :=
  decodedOneLetterTransform (N := N) μ I L s
    - windowedCanonicalPackage I L K s

theorem galerkinOneLetterDefect_def
    (μ : Fin N → ℝ) (I : Finset PrimePowerPair) (L : ℝ)
    (K : CanonicalKernelC) (s : ℂ) :
    decodedOneLetterTransform (N := N) μ I L s
      = windowedCanonicalPackage I L K s
        + galerkinOneLetterDefect (N := N) μ I L K s := by
  unfold galerkinOneLetterDefect
  ring

#print axioms windowedCanonicalPackage
#print axioms windowFactor_split
#print axioms windowedCanonicalPackage_lock
#print axioms windowedCanonical_eq_half_Bstage_sub_BcorrWin
#print axioms galerkinSpikeTransform
#print axioms decodedOneLetterTransform
#print axioms galerkinOneLetterDefect
#print axioms galerkinOneLetterDefect_def

end

end RHFormalization
