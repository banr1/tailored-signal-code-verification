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
# Correctness of 36-Byte `SipHasher13::write`

Proves `sipWrite36_ok`: `<Hasher<Sip13Rounds> as Hasher>::write` on a 36-byte slice with
`h.ntail = 0` processes four 8-byte little-endian blocks and buffers the 4-byte tail,
matching `SipHasher13.write`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

namespace Write36

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem ofNat64_add_36 (n : Nat) :
    BitVec.ofNat 64 n + 36#64 = BitVec.ofNat 64 (n + 36) := by
  rw [← BitVec.ofNat_add]

private theorem pointsToBytes_drop_split8 (a : BitVec 64) (msg : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ msg.length) :
    ((a + BitVec.ofNat 64 off) ↦ₛ msg.drop off) =
      ((a + BitVec.ofNat 64 off) ↦₆₄ (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) off).toBitVec) ∗
      ((a + BitVec.ofNat 64 (off + 8)) ↦ₛ msg.drop (off + 8)) := by
  have hle : 8 ≤ (msg.drop off).length := by simp [List.length_drop]; omega
  rw [pointsToBytes_take_drop (a + BitVec.ofNat 64 off) 8 (msg.drop off) hle,
      List.drop_drop, pointsToBytes_take8_eq_pointsTo64 (a + BitVec.ofNat 64 off) msg off h,
      toBitVec_loadU64Le msg off, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem pointsToBytes_36_split (a : BitVec 64) (msg : List (BitVec 8))
    (hlen : msg.length = 36) :
    (a ↦ₛ msg) =
      (a ↦₆₄ (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 0).toBitVec) ∗
      ((a + 8#64) ↦₆₄ (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 8).toBitVec) ∗
      ((a + 16#64) ↦₆₄ (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 16).toBitVec) ∗
      ((a + 24#64) ↦₆₄ (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 24).toBitVec) ∗
      ((a + 32#64) ↦₃₂
        pack32 (msg.getD 32 0#8) (msg.getD 33 0#8) (msg.getD 34 0#8) (msg.getD 35 0#8)) := by
  have h0 : (a ↦ₛ msg) = ((a + BitVec.ofNat 64 0) ↦ₛ msg.drop 0) := by simp
  rw [h0,
      pointsToBytes_drop_split8 a msg 0 (by omega),
      pointsToBytes_drop_split8 a msg 8 (by omega),
      pointsToBytes_drop_split8 a msg 16 (by omega),
      pointsToBytes_drop_split8 a msg 24 (by omega)]
  have hdrop32 : msg.drop 32 = (msg.drop 32).take 4 := by
    symm
    apply List.take_of_length_le
    simp [List.length_drop, hlen]
  rw [hdrop32, pointsToBytes_take4_eq_pointsTo32 (a + BitVec.ofNat 64 32) msg 32 (by omega)]
  simp only [BitVec.add_zero]

attribute [local irreducible] compressBv in
private theorem sipHasher13At_write36 (a : BitVec 64) (hasher : SipHasher13) (msg : List (BitVec 8))
    (hlen36 : msg.length = 36) (hnt0 : hasher.ntail = 0) (hlen : hasher.length + 36 < 2 ^ 64) :
    sipHasher13At a (hasher.write (msg.map UInt8.ofBitVec)) =
      let m0 := (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 0).toBitVec
      let m1 := (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 8).toBitVec
      let m2 := (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 16).toBitVec
      let m3 := (SipHashModel.loadU64Le (msg.map UInt8.ofBitVec) 24).toBitVec
      let tail32 := pack32 (msg.getD 32 0#8) (msg.getD 33 0#8) (msg.getD 34 0#8) (msg.getD 35 0#8)
      let c1 := compressBv hasher.state.v0.toBitVec hasher.state.v1.toBitVec
        hasher.state.v2.toBitVec (hasher.state.v3.toBitVec ^^^ m0)
      let c2 := compressBv (c1.1 ^^^ m0) c1.2.1 c1.2.2.1 (c1.2.2.2 ^^^ m1)
      let c3 := compressBv (c2.1 ^^^ m1) c2.2.1 c2.2.2.1 (c2.2.2.2 ^^^ m2)
      let c4 := compressBv (c3.1 ^^^ m2) c3.2.1 c3.2.2.1 (c3.2.2.2 ^^^ m3)
      (a ↦₆₄ (c4.1 ^^^ m3)) ∗ ((a + 8#64) ↦₆₄ c4.2.2.1) ∗
      ((a + 16#64) ↦₆₄ c4.2.1) ∗ ((a + 24#64) ↦₆₄ c4.2.2.2) ∗
      ((a + 0x20#64) ↦₆₄ hasher.k0.toBitVec) ∗
      ((a + 0x28#64) ↦₆₄ hasher.k1.toBitVec) ∗
      ((a + 0x30#64) ↦₆₄ (BitVec.ofNat 64 hasher.length + 36#64)) ∗
      ((a + 0x38#64) ↦₆₄ tail32.zeroExtend 64) ∗
      ((a + 0x40#64) ↦₆₄ 4#64) := by
  rw [SipHasher13.write_of_ntail_zero hasher (msg.map UInt8.ofBitVec) hnt0]
  have hmap_len : (msg.map UInt8.ofBitVec).length = 36 := by simp [hlen36]
  rw [hmap_len, eq_stateOfBv hasher.state]
  unfold sipHasher13At
  have hpure : (hasher.length + 36 < 2 ^ 64 ∧ 36 % 8 < 8) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hlen, by decide⟩⟩
  simp only [hpure, pure_true, emp_sepConj, Nat.reduceMod, Nat.reduceSub,
    SipHasher13.writeBlocks, Nat.zero_add, Nat.reduceAdd,
    compressBlock_stateOfBv, sipStateAt_stateOfBv,
    toBitVec_u8to64Le_4, ofNat64_add_36, sepConj_assoc]
  rfl

end Write36

open Write36

attribute [local irreducible] Program.fnOff

set_option maxHeartbeats 1600000 in
/-- `SipHasher13::write` on a 36-byte slice with `ntail = 0` satisfies `sipWrite36Spec`. -/
theorem sipWrite36_ok (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr sipWriteName)
      sipWrite36Spec := by
  simp only [sipWrite36Spec]
  have hfn : libsignalSessionCode.fnOff sipWriteName = num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write") :=
    (ls_lemma% fnOff "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")) 488
  clear hfn
  dsimp only [RebasedProg, sipWriteName, BitVec.ofNat_eq_ofNat] at ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr
    "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write" = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨hAddr, msgPtr, hasher, msg⟩ := x
  dsimp only at *
  rw [sipHasher13At_write36 hAddr hasher msg h_4 h_5 h,
      pointsToBytes_36_split msgPtr msg h_4]
  unfold sipHasher13At sipStateAt
  rw [h_5]
  wp_steps
  dsimp only [compressBv]
  wp_done

end CryptoVerification.E2E.InMem.SipHashBin
