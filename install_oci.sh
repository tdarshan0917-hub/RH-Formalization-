#!/bin/zsh
echo "===== 1. create DefaultOmegaCodiscreteIdentity.lean ====="
cat > RHFormalization/DefaultOmegaCodiscreteIdentity.lean <<'EOF'
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
import RHFormalization.OmegaConnected

/-!
# RHFormalization.DefaultOmegaCodiscreteIdentity

Theorem-backed discharge of `OmegaCodiscreteMeromorphicIdentityAPI`.

This is the meromorphic identity principle on the slit plane Ω, proved from
Mathlib's order theory: if two meromorphic functions agree on a nonempty open
subset of Ω, their difference has meromorphic order ⊤ there, order ⊤ propagates
across the preconnected set Ω (`meromorphicOrderAt_ne_top_of_isPreconnected`),
hence the functions agree codiscretely within Ω.
-/

namespace RHFormalization

noncomputable section

open Complex Filter Set Topology

theorem omega_codiscrete_identity_native
    (f g : ℂ → ℂ) (V : Set ℂ)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVsub : V ⊆ Ω)
    (hf : MeromorphicOnC f Ω) (hg : MeromorphicOnC g Ω)
    (hEq : Set.EqOn f g V) :
    f =ᶠ[Filter.codiscreteWithin Ω] g := by
  have hsub : MeromorphicOn (f - g) Ω := hf.sub hg
  obtain ⟨x₀, hx₀⟩ := hVne
  have hx₀Ω : x₀ ∈ Ω := hVsub hx₀
  have h0 : (f - g) =ᶠ[𝓝[≠] x₀] 0 := by
    filter_upwards [nhdsWithin_le_nhds (hVopen.mem_nhds hx₀)] with z hz
    simp [Pi.sub_apply, hEq hz]
  have htop : meromorphicOrderAt (f - g) x₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 h0
  have hall : ∀ y, y ∈ Ω → meromorphicOrderAt (f - g) y = ⊤ := by
    intro y hy
    by_contra hne
    exact (hsub.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_Omega_native hy hx₀Ω hne) htop
  have hmem : {z | f z = g z} ∈ Filter.codiscreteWithin Ω := by
    rw [mem_codiscreteWithin]
    intro x hx
    rw [Filter.disjoint_principal_right]
    have hx0 : (f - g) =ᶠ[𝓝[≠] x] 0 := meromorphicOrderAt_eq_top_iff.1 (hall x hx)
    filter_upwards [hx0] with z hz
    have hz' : f z = g z := by
      have h : f z - g z = 0 := by simpa [Pi.sub_apply] using hz
      exact sub_eq_zero.mp h
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
    exact fun _ => hz'
  exact Filter.eventuallyEq_of_mem hmem (fun z hz => hz)

/-- Theorem-backed default codiscrete meromorphic identity package for Ω. -/
def defaultOmegaCodiscreteIdentityAPI : OmegaCodiscreteMeromorphicIdentityAPI :=
  { h_codiscrete_identity := omega_codiscrete_identity_native }

#print axioms defaultOmegaCodiscreteIdentityAPI

end

end RHFormalization
EOF
echo "===== 2. build new module (live) ====="
lake build RHFormalization.DefaultOmegaCodiscreteIdentity 2>&1 | tee oci_a.log | grep -e "error" -e "Built RHFormalization.DefaultOmegaCodiscreteIdentity" -e "depends on axioms" -e "Build completed"
if grep -q "error" oci_a.log; then
  echo "MODULE FAILED -> parking, project untouched"
  rm RHFormalization/DefaultOmegaCodiscreteIdentity.lean
  exit 1
fi
echo "===== 3. rewire canonical endpoint: drop identity hypothesis ====="
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/cfe.bak
cat > RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'
import RHFormalization.MainTheoremFromRealZeroFreeOmegaCodiscrete
import RHFormalization.DefaultOmegaPreperfect
import RHFormalization.DefaultOmegaCodiscreteIdentity

namespace RHFormalization
noncomputable section
open Complex

theorem RH_current_frontier
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
        Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI) :
    RiemannHypothesis :=
  mainTheorem_from_realZeroFree_omegaCodiscreteIdentity
    h_real_zero_free Y X E
    defaultOmegaCodiscreteIdentityAPI defaultOmegaPreperfectAPI

#print axioms RH_current_frontier

end
end RHFormalization
EOF
grep -qxF "import RHFormalization.DefaultOmegaCodiscreteIdentity" RHFormalization.lean || printf '\nimport RHFormalization.DefaultOmegaCodiscreteIdentity\n' >> RHFormalization.lean
echo "===== 4. build endpoint (live) ====="
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee oci_b.log | grep -e "error" -e "RH_current_frontier" -e "depends on axioms" -e "Build completed"
if grep -q "error" oci_b.log; then
  echo "ENDPOINT FAILED -> restoring known-good endpoint"
  cp /tmp/cfe.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -3
  exit 1
fi
echo "===== 5. warm root replay + snapshot ====="
lake build 2>&1 | tail -5 | tee oci_root.log
grep -q "Build completed successfully" oci_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_OCI_DISCHARGED.tar.gz . && echo "SNAPSHOT SAVED: OCI_DISCHARGED"
