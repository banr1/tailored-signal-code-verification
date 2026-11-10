/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Decodes
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.RoundLemmas
import LibsignalBinary.Proofs.E2E.InMem.SipHashModel.Lemmas
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Correctness of 1-Byte `SipHasher13::write`

Proves `sipWriteU8_ok`: `<Hasher<Sip13Rounds> as Hasher>::write` on a 1-byte slice when
`1 ≤ h.ntail ≤ 6` appends the byte into `tail` without compressing, matching `SipHasher13.writeU8`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

namespace WriteU8

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem ofNat64_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

private theorem sipHasher13At_writeU8 (a : BitVec 64) (hasher : SipHasher13) (b : BitVec 8)
    (hnt1 : 1 ≤ hasher.ntail) (hnt6 : hasher.ntail ≤ 6) (hlen : hasher.length + 1 < 2 ^ 64) :
    sipHasher13At a (hasher.writeU8 (UInt8.ofBitVec b)) =
      sipStateAt a hasher.state ∗
      ((a + 0x20#64) ↦₆₄ hasher.k0.toBitVec) ∗
      ((a + 0x28#64) ↦₆₄ hasher.k1.toBitVec) ∗
      ((a + 0x30#64) ↦₆₄ (BitVec.ofNat 64 hasher.length + 1#64)) ∗
      ((a + 0x38#64) ↦₆₄
        (hasher.tail.toBitVec |||
          ((b.zeroExtend 64) <<< (BitVec.ofNat 64 (8 * hasher.ntail)).umod 64#64))) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (hasher.ntail + 1)) := by
  rw [SipHasher13.writeU8_of_ntail_between hasher (UInt8.ofBitVec b) hnt1 (by omega)]
  unfold sipHasher13At
  have hpure : (hasher.length + 1 < 2 ^ 64 ∧ hasher.ntail + 1 < 8) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hlen, by omega⟩⟩
  simp only [hpure, pure_true, emp_sepConj, toBitVec_or64, toBitVec_shl64,
    toBitVec_toUInt64_ofBitVec8, ofNat64_add_one]
  rfl

end WriteU8

open WriteU8

attribute [local irreducible] Program.fnOff

/-- `SipHasher13::write` on a 1-byte slice with `1 ≤ ntail ≤ 6` satisfies `sipWriteU8Spec`. -/
theorem sipWriteU8_ok (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr sipWriteName)
      sipWriteU8Spec := by
  simp only [sipWriteU8Spec]
  have hfn : libsignalSessionCode.fnOff sipWriteName = num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write") :=
    (ls_lemma% fnOff "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")) 228
  clear hfn
  dsimp only [RebasedProg, sipWriteName, BitVec.ofNat_eq_ofNat] at ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr
    "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨hAddr, bPtr, hasher, byteVal⟩ := x
  dsimp only at *
  rw [sipHasher13At_writeU8 hAddr hasher byteVal h_4 h_5 h]
  unfold sipHasher13At sipStateAt
  have hnt_cases :
      hasher.ntail = 1 ∨ hasher.ntail = 2 ∨ hasher.ntail = 3 ∨
      hasher.ntail = 4 ∨ hasher.ntail = 5 ∨ hasher.ntail = 6 := by omega
  rcases hnt_cases with hnt | hnt | hnt | hnt | hnt | hnt <;> {
    rw [hnt]
    wp_steps
    wp_done
  }

end CryptoVerification.E2E.InMem.SipHashBin
