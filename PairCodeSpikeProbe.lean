import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration
import Mathlib.Data.Nat.Pairing

namespace RHFormalization

noncomputable section

def ppCode (q : PrimePowerPair) : ℕ :=
  Nat.pair q.1 q.2

def ppDecode (n : ℕ) : PrimePowerPair :=
  Nat.unpair n

theorem ppDecode_ppCode (q : PrimePowerPair) :
    ppDecode (ppCode q) = q := by
  rcases q with ⟨p, m⟩
  simp [ppDecode, ppCode, Nat.unpair_pair]

theorem ppCode_ppDecode (n : ℕ) :
    ppCode (ppDecode n) = n := by
  simp [ppDecode, ppCode, Nat.pair_unpair]

theorem ppCode_injective :
    Function.Injective ppCode := by
  intro q r h
  calc
    q = ppDecode (ppCode q) := by
      simpa using (ppDecode_ppCode q).symm
    _ = ppDecode (ppCode r) := by
      rw [h]
    _ = r := ppDecode_ppCode r

theorem ppDecode_injective :
    Function.Injective ppDecode := by
  intro m n h
  calc
    m = ppCode (ppDecode m) := by
      simpa using (ppCode_ppDecode m).symm
    _ = ppCode (ppDecode n) := by
      rw [h]
    _ = n := ppCode_ppDecode n

#check ppCode
#check ppDecode
#check ppDecode_ppCode
#check ppCode_ppDecode
#check ppCode_injective
#check ppDecode_injective

end

end RHFormalization
