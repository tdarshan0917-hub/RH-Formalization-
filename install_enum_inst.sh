#!/bin/zsh
cat > RHFormalization/ConcretePrimePowerEnumeration.lean <<'EOF'
import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration

/-!
# RHFormalization.ConcretePrimePowerEnumeration

First concrete inhabitant of the (repaired) prime-power cutoff enumeration:
`belowCutoff R` is the finite set of VALID prime-power pairs with center ≤ R,
realized inside the product range `[0, ⌈e^R⌉] × [0, ⌈e^R⌉]`.

Completeness: a valid pair with `log(p^m) ≤ R` has `p^m ≤ e^R`, hence
`p ≤ p^m ≤ ⌈e^R⌉` and `m < 2^m ≤ p^m ≤ ⌈e^R⌉`.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- Concrete finite enumeration of valid prime-power pairs below a real cutoff. -/
noncomputable def concretePrimePowerBelowCutoff (R : ℝ) : Finset PrimePowerPair :=
  ((Finset.range (⌈Real.exp R⌉₊ + 1)) ×ˢ (Finset.range (⌈Real.exp R⌉₊ + 1))).filter
    (fun q => IsPrimePowerPair q ∧ q.center ≤ R)

/-- The concrete enumeration instance. -/
noncomputable def concretePrimePowerEnum : PrimePowerWeightCutoffEnumerationData :=
  { belowCutoff := concretePrimePowerBelowCutoff
    h_mem_belowCutoff := by
      intro R q hq hcenter
      have h2 : (2 : ℕ) ≤ q.natValue := by
        have hp : 2 ≤ q.p := hq.1.two_le
        have hpow : q.p ≤ q.p ^ q.m := Nat.le_self_pow hq.2.ne' q.p
        calc (2 : ℕ) ≤ q.p := hp
          _ ≤ q.p ^ q.m := hpow
          _ = q.natValue := rfl
      have hpos : (0 : ℝ) < ((q.natValue : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast h2
        linarith
      have hle_exp : ((q.natValue : ℕ) : ℝ) ≤ Real.exp R := by
        have hexp := Real.exp_le_exp.mpr hcenter
        rwa [PrimePowerPair.center, Real.exp_log hpos] at hexp
      have hnat_le : q.natValue ≤ ⌈Real.exp R⌉₊ := by
        have : ((q.natValue : ℕ) : ℝ) ≤ ((⌈Real.exp R⌉₊ : ℕ) : ℝ) :=
          hle_exp.trans (Nat.le_ceil _)
        exact_mod_cast this
      have hp_le : q.p ≤ q.natValue := Nat.le_self_pow hq.2.ne' q.p
      have hm_lt : q.m < q.natValue := by
        have h2m : q.m < 2 ^ q.m := by
          first
            | exact Nat.lt_two_pow q.m
            | exact Nat.lt_two_pow_self
        have hle : 2 ^ q.m ≤ q.p ^ q.m :=
          Nat.pow_le_pow_left hq.1.two_le q.m
        exact lt_of_lt_of_le h2m hle
      refine Finset.mem_filter.mpr ⟨?_, hq, hcenter⟩
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hp_le.trans hnat_le))
      · exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le ((Nat.le_of_lt hm_lt).trans hnat_le)) }

#print axioms concretePrimePowerEnum

end

end RHFormalization
EOF
lake build RHFormalization.ConcretePrimePowerEnumeration 2>&1 | tee einst_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" einst_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A10 "error" einst_a.log | head -50
  rm RHFormalization/ConcretePrimePowerEnumeration.lean
  exit 1
fi
grep -qxF "import RHFormalization.ConcretePrimePowerEnumeration" RHFormalization.lean || printf '\nimport RHFormalization.ConcretePrimePowerEnumeration\n' >> RHFormalization.lean
lake build 2>&1 | tee einst_root.log | tail -3
grep -q "Build completed successfully" einst_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_ENUM_INSTANCE.tar.gz . && echo "SNAPSHOT SAVED: ENUM_INSTANCE"
