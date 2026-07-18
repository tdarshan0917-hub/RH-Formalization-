#!/bin/zsh
echo "===== 0. sum_subtype name probe ====="
cat > SSProbe.lean <<'EOF'
import RHFormalization.MeromorphyAssembly
open Classical RHFormalization
example (s : Finset ℂ) (p : ℂ → Prop) (hp : ∀ x ∈ s, p x) (f : ℂ → ℂ) :
    Finset.sum (s.subtype p) (fun x => f x.1) = Finset.sum s f := by
  first
    | exact Finset.sum_subtype_of_mem f hp
    | (rw [Finset.sum_subtype_map_embedding (fun _ _ => rfl)]; simp)
    | (rw [← Finset.sum_attach s f]
       refine Finset.sum_nbij' (fun x => ⟨x.1, hp x.1 x.2⟩) (fun x => ⟨x.1, by
         have := x.2; simpa [Finset.mem_subtype] using this⟩) ?_ ?_ ?_ ?_ ?_ <;>
         (intros; simp_all [Finset.mem_subtype, Finset.mem_attach]))
    | sorry
EOF
lake env lean SSProbe.lean 2>&1 | grep -e "error" -e "warning: 'sorry'" | head -6
echo "===== 1. install ConvergenceInfrastructure ====="
cat > RHFormalization/ConvergenceInfrastructure.lean <<'EOF'
import RHFormalization.MeromorphyAssembly

/-!
# RHFormalization.ConvergenceInfrastructure

Campaign C, installment 1: (a) on any compact away from the pole set, the
pole-distance is uniformly bounded below; (b) the exhaustion stages, viewed as
finsets of the zero SUBTYPE, tend to atTop in the Finset lattice; (c) subtype
sums match the original stage sums.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped Classical

/-- The zero subtype: the index of the canonical pole series. -/
abbrev ZetaZero := {ρ : ℂ // IsNontrivialZetaZero ρ}

/-- (a) Uniform pole-distance on a compact away from the poles. -/
theorem compact_uniform_pole_distance (K : CompactAwayFromZeroPoles) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ →
        ∀ s ∈ K.K, δ ≤ dist s (polePoint ρ) := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ (ρ : ℂ) (s : ℂ),
      IsNontrivialZetaZero ρ ∧ s ∈ K.K ∧
        dist s (polePoint ρ) < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ρ, h1, s, h2, h3⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨ρ, s, h1, h2, h3⟩
  choose z w hz_zero hw_mem hzw_dist using hseq
  obtain ⟨x, hxK, φ, hφ, htend⟩ := K.h_compact.tendsto_subseq hw_mem
  have hxΩ : x ∈ Ω := K.h_subset_Omega hxK
  have hxnp : x ∉ ZeroPoleSet := K.h_avoid x hxK
  obtain ⟨r, hr, hiso⟩ := nonpole_isolated x hxΩ hxnp
  -- eventually w is r/2-close to x, while its pole is 1/(k+1)-close to w
  have hclose : ∀ᶠ k in Filter.atTop, dist (w (φ k)) x < r / 2 :=
    (Metric.tendsto_nhds.mp htend) (r / 2) (by linarith)
  have hsmall : ∀ᶠ k in Filter.atTop,
      (1 : ℝ) / ((φ k : ℝ) + 1) < r / 2 := by
    have hb : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (nhds 0) :=
      hb.comp (hφ.tendsto_atTop)
    exact (Metric.tendsto_nhds.mp hc (r / 2) (by linarith)).mono
      (by intro k hk; simpa [Real.dist_eq, abs_of_pos
        (by positivity : (0:ℝ) < 1 / ((φ k : ℝ) + 1))] using hk)
  obtain ⟨k, hk1, hk2⟩ := (hclose.and hsmall).exists
  have hd := hiso (z (φ k)) (hz_zero (φ k))
  have htri : dist x (polePoint (z (φ k))) ≤
      dist x (w (φ k)) + dist (w (φ k)) (polePoint (z (φ k))) :=
    dist_triangle _ _ _
  rw [dist_comm x (w (φ k))] at htri
  have hsm : dist (w (φ k)) (polePoint (z (φ k))) < r / 2 :=
    lt_trans (hzw_dist (φ k)) hk2
  rw [dist_comm x (polePoint (z (φ k)))] at hd
  linarith
/-- (b) The subtype-stage map. -/
def subtypeStage (n : ℕ) : Finset ZetaZero :=
  (defaultZeroExhaustion.zeroSet n).subtype IsNontrivialZetaZero

/-- The subtype stages tend to atTop in the Finset lattice. -/
theorem subtypeStage_tendsto :
    Tendsto subtypeStage atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  have hstage : ∀ ρ : ZetaZero, ρ ∈ b →
      ∃ N, ρ.1 ∈ defaultZeroExhaustion.zeroSet N := by
    intro ρ _
    exact defaultZeroExhaustion.h_eventually_contains ρ.1 ρ.2
  choose stage hstage using hstage
  classical
  refine ⟨b.attach.sup (fun ρ => stage ρ.1 ρ.2), fun a ha => ?_⟩
  rw [Finset.le_iff_subset]
  intro ρ hρb
  rw [subtypeStage, Finset.mem_subtype]
  refine defaultZeroExhaustion_mono ?_ (hstage ρ hρb)
  exact le_trans (Finset.le_sup (Finset.mem_attach b ⟨ρ, hρb⟩)) ha

/-- (c) Subtype sums match the stage sums. -/
theorem subtypeStage_sum_eq
    (M : ZeroMultiplicityData) (n : ℕ) (s : ℂ) :
    Finset.sum (subtypeStage n) (fun ρ => zeroPoleSummand M ρ.1 s) =
      zeroPolePartial M defaultZeroExhaustion n s := by
  unfold zeroPolePartial finiteZeroPoleSeries subtypeStage
  first
    | exact Finset.sum_subtype_of_mem _ (defaultZeroExhaustion.h_all_zeros n)
    | (rw [← Finset.sum_attach (defaultZeroExhaustion.zeroSet n)
        (fun ρ => zeroPoleSummand M ρ s)]
       refine Finset.sum_nbij'
         (fun x => ⟨x.1, by have := x.2; rwa [Finset.mem_subtype] at this⟩)
         (fun x => ⟨x.1, defaultZeroExhaustion.h_all_zeros n x.1 x.2⟩)
         ?_ ?_ ?_ ?_ ?_ <;>
         (intros; simp_all [Finset.mem_subtype, Finset.mem_attach]))

#print axioms compact_uniform_pole_distance
#print axioms subtypeStage_tendsto
#print axioms subtypeStage_sum_eq

end

end RHFormalization
EOF
lake build RHFormalization.ConvergenceInfrastructure 2>&1 | tee c1_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" c1_a.log; then
  echo "FAILED -> removing (errors below)"
  grep -B2 -A16 "error" c1_a.log | head -110
  rm RHFormalization/ConvergenceInfrastructure.lean
  exit 1
fi
for thm in compact_uniform_pole_distance subtypeStage_tendsto subtypeStage_sum_eq; do
  if ! grep -q "$thm' depends on axioms: \[propext, Classical.choice, Quot.sound\]" c1_a.log; then
    echo "AXIOM CHECK FAILED ($thm) -> removing"; rm RHFormalization/ConvergenceInfrastructure.lean; exit 1
  fi
done
grep -qxF "import RHFormalization.ConvergenceInfrastructure" RHFormalization.lean || printf '\nimport RHFormalization.ConvergenceInfrastructure\n' >> RHFormalization.lean
lake build 2>&1 | tee c1_root.log | tail -3
grep -q "Build completed successfully" c1_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CONV_C1.tar.gz . && echo "SNAPSHOT SAVED: CONV_C1"
