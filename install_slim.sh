#!/bin/zsh
cat > RHFormalization/DefaultPoleNormalFormLayer.lean <<'EOF'
import RHFormalization.PoleNormalForm

/-!
# RHFormalization.DefaultPoleNormalFormLayer

Definitional discharges of the pole-normal-form layer, plus the canonical
singleton grouped-pole class and the slim H-side grouped builder.

`PrincipalPartNormalForm` is literally `(coeff ≠ 0, principal part, principal
part)`, and `HasGenuinePole` is `∃ coeff ≠ 0, principal part`, so both layer
APIs are anonymous constructors. The singleton class `{W.ρ}` is supplied
entirely by the witness's own fields. The resulting slim builder reduces the
H-side grouped layer to one analytic input: `Zpole` has a principal part with
coefficient `(M.mult W.ρ : ℂ)` at each witness pole point.
-/

namespace RHFormalization

noncomputable section

open Complex

def defaultPrincipalPartToNormalFormAPI : PrincipalPartToNormalFormAPI :=
  { h_to_normal_form := fun _f _s0 _c hc hpp =>
      { h_coeff_ne_zero := hc
        h_principalPart := hpp
        h_localModel := hpp } }

def defaultNormalFormImpliesGenuinePoleAPI : NormalFormImpliesGenuinePoleAPI :=
  { h_genuine := fun _f _s0 c NF =>
      ⟨c, NF.h_coeff_ne_zero, NF.h_principalPart⟩ }

def defaultPoleNormalFormLayer : PoleNormalFormLayer :=
  { principalPartToNormalForm := defaultPrincipalPartToNormalFormAPI
    normalFormToGenuinePole := defaultNormalFormImpliesGenuinePoleAPI }

/-- Canonical singleton grouped-pole class `{W.ρ}`: every field is supplied
by the witness itself. -/
def defaultGroupedPoleClass
    (M : ZeroMultiplicityData)
    (W : ZeroWitness) :
    GroupedPoleClass M W :=
  { zeros := {W.ρ}
    h_witness_mem := Finset.mem_singleton_self W.ρ
    h_all_zeros := by
      intro ρ hρ
      rw [Finset.mem_singleton] at hρ
      subst hρ
      exact W.h_zero
    h_same_pole := by
      intro ρ hρ
      rw [Finset.mem_singleton] at hρ
      subst hρ
      exact W.hs0_def.symm }

/-- Slim H-side grouped builder: the only analytic input left is the
principal-part statement with multiplicity coefficient. -/
def buildHSideGroupedPoleNormalFormDataFromPrincipalParts
    (H : ZeroPolePackageAPI)
    (M : ZeroMultiplicityData)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC H.Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    HSideGroupedPoleNormalFormData H :=
  { M := M
    groupedClass := fun W => defaultGroupedPoleClass M W
    h_principalPart := h_pp
    poleNormalForm := defaultPoleNormalFormLayer }

#print axioms defaultPoleNormalFormLayer
#print axioms buildHSideGroupedPoleNormalFormDataFromPrincipalParts

end

end RHFormalization
EOF
echo "===== build module (live) ====="
lake build RHFormalization.DefaultPoleNormalFormLayer 2>&1 | tee slim_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" slim_a.log; then
  echo "FAILED -> removing, project untouched (errors below)"
  grep -B2 -A8 "error" slim_a.log | head -40
  rm RHFormalization/DefaultPoleNormalFormLayer.lean
  exit 1
fi
grep -qxF "import RHFormalization.DefaultPoleNormalFormLayer" RHFormalization.lean || printf '\nimport RHFormalization.DefaultPoleNormalFormLayer\n' >> RHFormalization.lean
echo "===== warm root replay + snapshot ====="
lake build 2>&1 | tail -4 | tee slim_root.log
grep -q "Build completed successfully" slim_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_X_GROUPED_SLIMMED.tar.gz . && echo "SNAPSHOT SAVED: X_GROUPED_SLIMMED"
