import RHFormalization.ShiftedLaplaceBsharedMeromorphic

namespace RHFormalization

open Complex Filter Topology

/-- The continued B-side model: the ζ log-derivative pulled back through φ,
times the analytic prefactor. Defined on all of Ω (and beyond). -/
noncomputable def shiftedLaplaceLogDerivModel (s : ℂ) : ℂ :=
  - (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) *
      logDeriv riemannZeta (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))

/-- For `s ∈ Ω`, `s + 1/4 ≠ 0` (slitPlane excludes 0). -/
theorem shift_ne_zero_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    (s + (1/4:ℂ)) ≠ 0 := by
  have hslit := shift_mem_slitPlane_of_mem_Omega hs
  rw [mem_slitPlane_iff] at hslit
  rcases hslit with hre | him
  · intro h; rw [h] at hre; simp at hre
  · intro h; rw [h] at him; simp at him

/-- For `s ∈ Ω`, `√(s+1/4) ≠ 0`. -/
theorem sqrt_shift_ne_zero_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    Complex.sqrt (s + (1/4:ℂ)) ≠ 0 := by
  have hne : (s + (1/4:ℂ)) ≠ 0 := shift_ne_zero_of_mem_Omega hs
  unfold Complex.sqrt
  exact Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.mpr hne

/-- The analytic prefactor `−1/(2√(s+1/4))` is analytic at each point of Ω. -/
theorem prefactor_analyticAt_of_mem_Omega {s : ℂ} (hs : s ∈ Ω) :
    AnalyticAt ℂ (fun z => - (1 / (2 * Complex.sqrt (z + (1/4:ℂ))))) s := by
  have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane := shift_mem_slitPlane_of_mem_Omega hs
  have hsqrt_ne : Complex.sqrt (s + (1/4:ℂ)) ≠ 0 := sqrt_shift_ne_zero_of_mem_Omega hs
  -- √(·+1/4) is analytic on Ω (already have differentiability route)
  have hsqrtA : AnalyticAt ℂ (fun z => Complex.sqrt (z + (1/4:ℂ))) s := by
    have hopen : IsOpen {z : ℂ | (z + (1/4:ℂ)) ∈ Complex.slitPlane} :=
      isOpen_slitPlane.preimage (by fun_prop)
    have hmem : s ∈ {z : ℂ | (z + (1/4:ℂ)) ∈ Complex.slitPlane} := hslit
    have hdiff : DifferentiableOn ℂ (fun z => Complex.sqrt (z + (1/4:ℂ)))
        {z : ℂ | (z + (1/4:ℂ)) ∈ Complex.slitPlane} := by
      intro z hz
      have hshift : DifferentiableAt ℂ (fun w : ℂ => w + (1/4:ℂ)) z :=
        (differentiableAt_id).add_const _
      exact ((Complex.differentiableAt_sqrt hz).comp z hshift).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hmem)
  have h2sqrt : AnalyticAt ℂ (fun z => 2 * Complex.sqrt (z + (1/4:ℂ))) s :=
    analyticAt_const.mul hsqrtA
  have h2sqrt_ne : (fun z => 2 * Complex.sqrt (z + (1/4:ℂ))) s ≠ 0 := by
    simp only; exact mul_ne_zero (by norm_num) hsqrt_ne
  have hinv : AnalyticAt ℂ (fun z => 1 / (2 * Complex.sqrt (z + (1/4:ℂ)))) s := by
    have := h2sqrt.inv h2sqrt_ne
    simpa only [one_div] using this
  exact hinv.neg

/-- **The continued B-side model is meromorphic on Ω.** -/
theorem shiftedLaplaceLogDerivModel_meromorphicOn_Omega :
    MeromorphicOn shiftedLaplaceLogDerivModel Ω := by
  intro s hs
  have hpre : AnalyticAt ℂ (fun z => - (1 / (2 * Complex.sqrt (z + (1/4:ℂ))))) s :=
    prefactor_analyticAt_of_mem_Omega hs
  have hlog : MeromorphicAt
      (fun z => logDeriv riemannZeta (Complex.sqrt (z + (1/4:ℂ)) + (1/2:ℂ))) s :=
    logDeriv_zeta_comp_phi_meromorphicAt hs
  have hmul := hpre.meromorphicAt.mul hlog
  exact hmul

#print axioms shiftedLaplaceLogDerivModel_meromorphicOn_Omega

end RHFormalization
