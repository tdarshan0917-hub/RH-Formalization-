import RHFormalization.CanonicalPrimePowerCutoffMassEnumeration
import Mathlib.Data.Nat.Pairing

/-!
# RHFormalization.AppendixDPrimePowerPairCode

Nat coding helpers for Appendix-D finite spike indices.

The `DFiniteStage` API uses Nat indices together with a map

  diagonalSpikeToPP : ℕ → PrimePowerPair

so the Nat index can be a code for the prime-power pair `(p,m)`.
This file records the pair-code / decode facts needed for the structural
finite-stage witness.
-/

namespace RHFormalization

noncomputable section

/-- Encode a prime-power pair as a Nat. -/
def ppCode (q : PrimePowerPair) : ℕ :=
  Nat.pair q.1 q.2

/-- Decode a Nat into a candidate prime-power pair. -/
def ppDecode (n : ℕ) : PrimePowerPair :=
  Nat.unpair n

/-- Decoding after encoding recovers the original prime-power pair. -/
theorem ppDecode_ppCode (q : PrimePowerPair) :
    ppDecode (ppCode q) = q := by
  rcases q with ⟨p, m⟩
  simp [ppDecode, ppCode, Nat.unpair_pair]

/-- Encoding after decoding recovers the original Nat code. -/
theorem ppCode_ppDecode (n : ℕ) :
    ppCode (ppDecode n) = n := by
  simp [ppDecode, ppCode, Nat.pair_unpair]

/-- The prime-power-pair encoder is injective. -/
theorem ppCode_injective :
    Function.Injective ppCode := by
  intro q r h
  calc
    q = ppDecode (ppCode q) := by
      simpa using (ppDecode_ppCode q).symm
    _ = ppDecode (ppCode r) := by
      rw [h]
    _ = r := ppDecode_ppCode r

/-- The Nat decoder is injective because it is inverse to `ppCode`. -/
theorem ppDecode_injective :
    Function.Injective ppDecode := by
  intro m n h
  calc
    m = ppCode (ppDecode m) := by
      simpa using (ppCode_ppDecode m).symm
    _ = ppCode (ppDecode n) := by
      rw [h]
    _ = n := ppCode_ppDecode n

end

end RHFormalization
