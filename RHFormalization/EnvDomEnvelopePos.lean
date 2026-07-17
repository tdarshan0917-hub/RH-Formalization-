import Mathlib
import RHFormalization.EnvDomShellPosHead
import RHFormalization.EnvDomShellPosTail
import RHFormalization.EnvDomShellPosShiftTail
import RHFormalization.EnvDomShellSummable
import RHFormalization.PolyExpBound
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Real Finset

namespace RHFormalization

/-- Full u>0 summand is summable: the tail (k ≥ N ≥ 2u) is dominated by the
`κ'/4` shell series, and prepending a finite head preserves summability. -/
theorem shell_pos_summable
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : 0 < u) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * u)
  rw [← summable_nat_add_iff N]
  have hκ'4 : 0 < κ' / 4 := by linarith
  have hsumm4 : Summable (fun k : ℕ => (((k + N : ℕ) : ℝ) + 1)
      * Real.exp (((k + N : ℕ) : ℝ) / 2)
      * Real.exp (-(κ' / 4) * ((k + N : ℕ) : ℝ) ^ 2)) := by
    have := (summable_nat_add_iff N).mpr (summable_shell_coeff (κ' / 4) hκ'4)
    simpa using this
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hsumm4
  intro k
  have hkN2u : 2 * u ≤ ((k + N : ℕ) : ℝ) := by
    have : (N : ℝ) ≤ ((k + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N k
    linarith
  exact shell_pos_tail_term_le κ' hκ' u hu (k + N) hkN2u

/-- **A.ENV-DOM envelope, u>0, final shape.** For `u > 0`, the shell tsum is
bounded by `K·(1 + u² + e^u)`. Head `k < N = ⌈2u⌉` gives `≤ N²·e^{u/2+1/(16κ')}`,
absorbed via `sq_le_four_mul_exp` (head `≤ 73·e^u·F`); tail `k ≥ N` is the banked
shifted-tail constant `Kt` (manuscript p.55). -/
theorem envelope_pos_final
    (κ' : ℝ) (hκ' : 0 < κ') (u : ℝ) (hu : 0 < u) :
    ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
        * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
      ≤ (Real.exp (1 / (16 * κ')) * 73
          + ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
              * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2))
        * (1 + u ^ 2 + Real.exp u) := by
  set N : ℕ := ⌈2 * u⌉₊ with hNdef
  have hN2u : 2 * u ≤ (N : ℝ) := Nat.le_ceil _
  have hsumm := shell_pos_summable κ' hκ' u hu
  rw [← Summable.sum_add_tsum_nat_add N hsumm]
  have hhead := shell_pos_head_sum_le κ' hκ' u N
  have htail := shell_pos_shifted_tail_le κ' hκ' u hu N hN2u
  set Kt : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2)
      * Real.exp (-(κ' / 4) * (k : ℝ) ^ 2) with hKtdef
  set E : ℝ := Real.exp (u / 2 + 1 / (16 * κ')) with hEdef
  have hNnn : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNle : (N : ℝ) ≤ 2 * u + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 2 * u)
    linarith [this]
  have hN2 : (N : ℝ) ^ 2 ≤ (2 * u + 1) ^ 2 := by nlinarith [hNle, hNnn, hu]
  have hEpos : 0 < E := Real.exp_pos _
  have hhead2 : ∑ k ∈ Finset.range N,
      ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2)
        ≤ (2 * u + 1) ^ 2 * E := by
    refine le_trans hhead ?_
    have hrw : (N : ℝ) * ((N : ℝ) * E) = (N : ℝ) ^ 2 * E := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hN2 (le_of_lt hEpos)
  have hEsplit : E = Real.exp (u / 2) * Real.exp (1 / (16 * κ')) := by
    rw [hEdef, ← Real.exp_add]
  set F : ℝ := Real.exp (1 / (16 * κ')) with hFdef
  have hFpos : 0 < F := Real.exp_pos _
  have hehalf_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have heu_pos : 0 < Real.exp u := Real.exp_pos _
  have hexphalf_le : Real.exp (u / 2) ≤ Real.exp u := by
    apply Real.exp_le_exp.mpr; linarith
  have hu_le : u ≤ 2 * Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2); nlinarith [this, hehalf_pos]
  have huhalf : u * Real.exp (u / 2) ≤ 2 * Real.exp u := by
    have h1 : u * Real.exp (u / 2) ≤ (2 * Real.exp (u / 2)) * Real.exp (u / 2) :=
      mul_le_mul_of_nonneg_right hu_le (le_of_lt hehalf_pos)
    have h2 : (2 * Real.exp (u / 2)) * Real.exp (u / 2) = 2 * Real.exp u := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [h2] at h1; exact h1
  have hu2q : u ^ 2 ≤ 16 * Real.exp (u / 2) := by
    have := sq_le_four_mul_exp (u / 2) (by linarith)
    nlinarith [this]
  have hu2half : u ^ 2 * Real.exp (u / 2) ≤ 16 * Real.exp u := by
    have h1 : u ^ 2 * Real.exp (u / 2) ≤ (16 * Real.exp (u / 2)) * Real.exp (u / 2) :=
      mul_le_mul_of_nonneg_right hu2q (le_of_lt hehalf_pos)
    have h2 : (16 * Real.exp (u / 2)) * Real.exp (u / 2) = 16 * Real.exp u := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [h2] at h1; exact h1
  have hkey : (2 * u + 1) ^ 2 * Real.exp (u / 2) ≤ 73 * Real.exp u := by
    have hexpand : (2 * u + 1) ^ 2 * Real.exp (u / 2)
        = 4 * (u ^ 2 * Real.exp (u / 2)) + 4 * (u * Real.exp (u / 2))
          + Real.exp (u / 2) := by ring
    rw [hexpand]; nlinarith [hu2half, huhalf, hexphalf_le, heu_pos]
  have henv1 : (1:ℝ) ≤ 1 + u ^ 2 + Real.exp u := by nlinarith [sq_nonneg u, heu_pos]
  have heu_le_env : Real.exp u ≤ 1 + u ^ 2 + Real.exp u := by nlinarith [sq_nonneg u]
  have hKtnn : 0 ≤ Kt := by
    rw [hKtdef]; apply tsum_nonneg; intro k; positivity
  calc (∑ k ∈ Finset.range N,
          ((k : ℝ) + 1) * Real.exp ((k : ℝ) / 2) * Real.exp (-κ' * (u - (k : ℝ)) ^ 2))
        + ∑' k : ℕ, (((k + N : ℕ) : ℝ) + 1) * Real.exp (((k + N : ℕ) : ℝ) / 2)
            * Real.exp (-κ' * (u - ((k + N : ℕ) : ℝ)) ^ 2)
      ≤ (2 * u + 1) ^ 2 * E + Kt := by
        apply add_le_add hhead2
        rw [hKtdef]; exact htail
    _ = (2 * u + 1) ^ 2 * Real.exp (u / 2) * F + Kt := by rw [hEsplit, hFdef]; ring
    _ ≤ (73 * Real.exp u) * F + Kt := by
        have hstep : (2 * u + 1) ^ 2 * Real.exp (u / 2) * F ≤ (73 * Real.exp u) * F :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hFpos)
        linarith [hstep]
    _ ≤ (F * 73 + Kt) * (1 + u ^ 2 + Real.exp u) := by
        set env : ℝ := 1 + u ^ 2 + Real.exp u with hEnvDef
        have hKtenv : Kt ≤ Kt * env := by nlinarith [hKtnn, henv1]
        have hFe : 73 * Real.exp u * F ≤ 73 * env * F :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left heu_le_env (by norm_num : (0:ℝ) ≤ 73))
            (le_of_lt hFpos)
        have hExpand : (F * 73 + Kt) * env = 73 * env * F + Kt * env := by ring
        rw [hExpand]
        calc 73 * Real.exp u * F + Kt
            ≤ 73 * env * F + Kt := by linarith [hFe]
          _ ≤ 73 * env * F + Kt * env := by linarith [hKtenv]

#print axioms shell_pos_summable
#print axioms envelope_pos_final

end RHFormalization
