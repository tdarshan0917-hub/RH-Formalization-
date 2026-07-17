-- SENTINEL: L1e-per-spike-defect-bound-v3
import RHFormalization.ComplexRiemannError
import RHFormalization.CosResolventKernelIdentityOmega
import RHFormalization.CosResolventDerivMajorant
import RHFormalization.CosResolventTailBound
import RHFormalization.SineResolventSumBound
import RHFormalization.GalerkinOneLetterNormalizationLock
import RHFormalization.GalerkinDiagonalFormula
import Mathlib

/-!
# L1e — The per-spike transform-defect bound
For 0 < L, 0 ≤ a ≤ L, 0 < N, s ∈ Ω with floor c:
  ‖(1/(2L))·galerkinSpikeTransform(galerkinLam) − ((L−a)/(2L))·K(a,s)‖
    ≤ (1/(2L))·((a/c)(π/2)+1/c²) + L/(2cπ²N) + (1+log N)/(2Lcπ).
Chain: galerkinT_diag_formula split → cosSum = Σ f(ξ_k) → Riemann
(L1a+L1b) + truncation (L1c) + continuum = πK (L0c) + sine sum (L1d).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

variable {N : ℕ}

/-- The cosine spectral sum (resolvent-weighted). -/
def cosSumC (N : ℕ) (L a : ℝ) (s : ℂ) : ℂ :=
  ∑ m : Fin N,
    ((Real.cos (((m : ℝ) + 1) * Real.pi * a / L) : ℝ) : ℂ)
      * (1 / (s + (1/4 : ℂ) + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)))

/-- The sine spectral sum (resolvent-weighted, harmonic-damped). -/
def sinSumC (N : ℕ) (L a : ℝ) (s : ℂ) : ℂ :=
  ∑ m : Fin N,
    ((Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
        / ((((m : ℝ)) + 1) * Real.pi) : ℝ) : ℂ)
      * (1 / (s + (1/4 : ℂ) + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)))

/-- **Split** via the banked diagonal formula. -/
theorem spikeTransform_split (L a : ℝ) (hL : 0 < L) (ha0 : 0 ≤ a)
    (haL : a ≤ L) (s : ℂ) :
    galerkinSpikeTransform (N := N) (fun m => galerkinLam L (m : ℕ)) L a s
      = (((1 - a/L : ℝ)) : ℂ) * cosSumC N L a s + sinSumC N L a s := by
  unfold galerkinSpikeTransform cosSumC sinSumC
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [galerkinT_diag_formula L a hL ha0 haL m]
  push_cast
  ring

/-- The cosine sum is a plain sum of integrand values at the mesh points. -/
theorem cosSumC_eq_sum_integrand (L a : ℝ) (hL : 0 < L) (s : ℂ) :
    cosSumC N L a s
      = ∑ k ∈ Finset.range N,
          cosResolventIntegrand a s (((k : ℝ) + 1) * (Real.pi / L)) := by
  unfold cosSumC
  rw [← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => cosResolventIntegrand a s (((k : ℝ) + 1) * (Real.pi / L))) N]
  apply Finset.sum_congr rfl
  intro m _
  have h1 : (((m : ℕ) : ℝ) + 1) * (Real.pi / L) * a
      = (((m : ℕ) : ℝ) + 1) * Real.pi * a / L := by ring
  have h2 : (((((m : ℕ) : ℝ) + 1) * (Real.pi / L) : ℝ) : ℂ)^2
      = ((galerkinLam L (m : ℕ) : ℝ) : ℂ) := by
    unfold galerkinLam
    push_cast
    ring
  unfold cosResolventIntegrand
  rw [h1, h2]
  ring

/-- **The exact per-spike identity**: defect = scaled (Riemann − ∫) + sine part. -/
theorem perSpike_identity (L a : ℝ) (hL : 0 < L) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (s : ℂ) (hs : s ∈ Ω) :
    ((1 / (2 * L) : ℝ) : ℂ)
        * galerkinSpikeTransform (N := N) (fun m => galerkinLam L (m : ℕ)) L a s
      - (((L - a) / (2 * L) : ℝ) : ℂ) * shiftedLaplaceHeatKernelC a s
    = (((1 - a/L) / (2 * Real.pi) : ℝ) : ℂ)
        * (((Real.pi / L : ℝ) : ℂ) * cosSumC N L a s
            - ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ)
      + ((1 / (2 * L) : ℝ) : ℂ) * sinSumC N L a s := by
  have hK := cosResolvent_integral_eq_pi_kernel_Omega a ha0 hs
  rw [spikeTransform_split L a hL ha0 haL s, hK]
  have hLne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hL)
  have hπne : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast
  field_simp
  ring

/-- **L1e — the per-spike transform-defect bound.** -/
theorem perSpikeTransformDefect_norm_le (hN : 0 < N) (L a : ℝ) (hL : 0 < L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (s : ℂ) (hs : s ∈ Ω) (c : ℝ) (hc : 0 < c)
    (hfl : ∀ ξ : ℝ, c * (1 + ξ^2) ≤ ‖s + (1/4 : ℂ) + (ξ : ℂ)^2‖) :
    ‖((1 / (2 * L) : ℝ) : ℂ)
          * galerkinSpikeTransform (N := N) (fun m => galerkinLam L (m : ℕ)) L a s
        - (((L - a) / (2 * L) : ℝ) : ℂ) * shiftedLaplaceHeatKernelC a s‖
      ≤ (1 / (2 * L)) * ((a / c) * (Real.pi / 2) + 1 / c^2)
        + L / (2 * c * Real.pi^2 * (N : ℝ))
        + (1 / (2 * L * c * Real.pi)) * (1 + Real.log N) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  set h : ℝ := Real.pi / L with hhdef
  have hh : (0:ℝ) < h := by rw [hhdef]; positivity
  set M : ℝ := (N : ℝ) * h with hMdef
  have hM : (0:ℝ) < M := by
    rw [hMdef]
    have : (0:ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    positivity
  -- Riemann-sum error (L1a + L1b)
  have hRie : ‖(∑ k ∈ Finset.range N,
        ((h : ℝ) : ℂ) * cosResolventIntegrand a s (((k:ℝ)+1)*h))
        - ∫ x in (0:ℝ)..M, cosResolventIntegrand a s x‖
      ≤ h * ((a / c) * (Real.pi / 2) + 1 / c^2) := by
    have hpart := partition_riemann_error_C
      (fun x => cosResolventIntegrand a s x)
      (fun x => cosResolventXiDeriv a s x) h hh N
      (fun x _ => cosResolvent_xi_hasDerivAt a s hs x)
      (cosResolventXiDeriv_continuous a s hs).continuousOn
    have hTV := integral_norm_cosResolventXiDeriv_le a M ha0 hM.le s hs c hc hfl
    calc ‖(∑ k ∈ Finset.range N,
          ((h : ℝ) : ℂ) * cosResolventIntegrand a s (((k:ℝ)+1)*h))
          - ∫ x in (0:ℝ)..M, cosResolventIntegrand a s x‖
        ≤ h * ∫ x in (0:ℝ)..M, ‖cosResolventXiDeriv a s x‖ := by
          rw [hMdef]; exact hpart
      _ ≤ h * ((a / c) * (Real.pi / 2) + 1 / c^2) :=
          mul_le_mul_of_nonneg_left hTV hh.le
  -- truncation tail (L1c)
  have hTail := cosResolvent_interval_vs_Ioi a M hM s c hc hfl
  -- Riemann-sum = (π/L)·cosSum
  have hSum : ((h : ℝ) : ℂ) * cosSumC N L a s
      = ∑ k ∈ Finset.range N,
          ((h : ℝ) : ℂ) * cosResolventIntegrand a s (((k:ℝ)+1)*h) := by
    rw [cosSumC_eq_sum_integrand L a hL s, Finset.mul_sum]
  -- combined main-term bound
  have hMain : ‖((h : ℝ) : ℂ) * cosSumC N L a s
        - ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ‖
      ≤ h * ((a / c) * (Real.pi / 2) + 1 / c^2) + 1 / (c * M) := by
    have hdecomp : ((h : ℝ) : ℂ) * cosSumC N L a s
          - ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ
        = (((h : ℝ) : ℂ) * cosSumC N L a s
            - ∫ x in (0:ℝ)..M, cosResolventIntegrand a s x)
          + ((∫ x in (0:ℝ)..M, cosResolventIntegrand a s x)
            - ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ) := by ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    have h1' : ‖((h : ℝ) : ℂ) * cosSumC N L a s
        - ∫ x in (0:ℝ)..M, cosResolventIntegrand a s x‖
        ≤ h * ((a / c) * (Real.pi / 2) + 1 / c^2) := by
      rw [hSum]; exact hRie
    linarith [h1', hTail]
  -- sine part (L1d)
  have hμ : ∀ m : Fin N, (0:ℝ) ≤ galerkinLam L (m : ℕ) := by
    intro m
    unfold galerkinLam
    positivity
  have hSin := sineResolventSum_norm_le N a L s
    (fun m => galerkinLam L (m : ℕ)) hμ c hc hfl
  -- assemble via the identity
  rw [perSpike_identity L a hL ha0 haL s hs]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  -- scalar factor bounds
  have haLdiv : a / L ≤ 1 := (div_le_one hL).mpr haL
  have haLdiv0 : (0:ℝ) ≤ a / L := by positivity
  have hs1 : |(1 - a/L) / (2 * Real.pi)| ≤ 1 / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hs2 : |1 / (2 * L)| = 1 / (2 * L) := abs_of_pos (by positivity)
  have hMainNN : (0:ℝ) ≤ h * ((a / c) * (Real.pi / 2) + 1 / c^2) + 1 / (c * M) := by
    positivity
  have hT1 : |(1 - a/L) / (2 * Real.pi)|
        * ‖((h : ℝ) : ℂ) * cosSumC N L a s
            - ∫ ξ in Set.Ioi (0:ℝ), cosResolventIntegrand a s ξ‖
      ≤ (1 / (2 * Real.pi))
        * (h * ((a / c) * (Real.pi / 2) + 1 / c^2) + 1 / (c * M)) :=
    mul_le_mul hs1 hMain (norm_nonneg _) (by positivity)
  have hT2 : |1 / (2 * L)| * ‖sinSumC N L a s‖
      ≤ (1 / (2 * L)) * ((1 / (c * Real.pi)) * (1 + Real.log N)) := by
    rw [hs2]
    exact mul_le_mul_of_nonneg_left hSin (by positivity)
  -- final arithmetic: convert the two products to the target shape
  have e1 : (1 / (2 * Real.pi)) * (h * ((a / c) * (Real.pi / 2) + 1 / c^2))
      = (1 / (2 * L)) * ((a / c) * (Real.pi / 2) + 1 / c^2) / 1 := by
    rw [hhdef]
    field_simp
  have e2 : (1 / (2 * Real.pi)) * (1 / (c * M))
      = L / (2 * c * Real.pi^2 * (N : ℝ)) := by
    rw [hMdef, hhdef]
    have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
    field_simp
  have e3 : (1 / (2 * L)) * ((1 / (c * Real.pi)) * (1 + Real.log N))
      = (1 / (2 * L * c * Real.pi)) * (1 + Real.log N) := by
    field_simp
  have hexpand : (1 / (2 * Real.pi))
        * (h * ((a / c) * (Real.pi / 2) + 1 / c^2) + 1 / (c * M))
      = (1 / (2 * Real.pi)) * (h * ((a / c) * (Real.pi / 2) + 1 / c^2))
        + (1 / (2 * Real.pi)) * (1 / (c * M)) := by ring
  have e1' : (1 / (2 * Real.pi)) * (h * ((a / c) * (Real.pi / 2) + 1 / c^2))
      = (1 / (2 * L)) * ((a / c) * (Real.pi / 2) + 1 / c^2) := by
    rw [e1]; ring
  linarith [hT1, hT2, hexpand ▸ (le_refl ((1 / (2 * Real.pi))
    * (h * ((a / c) * (Real.pi / 2) + 1 / c^2) + 1 / (c * M)))),
    e1'.le, e1'.ge, e2.le, e2.ge, e3.le, e3.ge]

#print axioms spikeTransform_split
#print axioms cosSumC_eq_sum_integrand
#print axioms perSpike_identity
#print axioms perSpikeTransformDefect_norm_le

end

end RHFormalization
