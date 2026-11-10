/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.ResponderWireCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromHooks
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import ProofLib.SepLogic.WPp

/-!
# Base Definitions and Helpers for `PreKeySignalMessage::try_from` (`0x29b30`)

Defines `PreKeyTryFromArgs`, `preKeyResultAt`, and `preKeyTryFromSpec` (plus their
`[LibsignalPlacement]` counterparts for Block `111`), protobuf suffix decompositions for the 8 wire
fields of `PreKeySignalMessage`, and `<IdentityKey as TryFrom<&[u8]>>::try_from` (`0x2c530`,
Block `116`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoVerification
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre_wire (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_setPC_pre_wire (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre_wire (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_setPC_pre_wire (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre_wire (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_setPC_pre_wire (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre_wire (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_setPC_pre_wire (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl


/-! ## Symbol Names and Stack Budget -/

@[simp, arm64_norm]
abbrev preKeyTryFromName : String :=
  "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"

@[simp, arm64_norm]
abbrev identityKeyTryFromSliceName : String :=
  "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from"

/-- Callee stack budget for `PreKeySignalMessage::try_from` (`0x29b30`), paired with its 608-byte
(`96 + 512`) local frame in `preKeyTryFromStack`. -/
abbrev preKeyTryFromSubStack : Nat := smallRootStack

abbrev preKeyTryFromStack : Nat := 608 + preKeyTryFromSubStack

/-! ## Negative-Immediate and Bit-Extraction Lemmas -/

theorem bv_add_neg_8 (x : BitVec 64) : x + 18446744073709551608#64 = x - 8#64 := (BitVec.sub_eq_add_neg x 8#64).symm
theorem bv_add_neg_16 (x : BitVec 64) : x + 18446744073709551600#64 = x - 16#64 := (BitVec.sub_eq_add_neg x 16#64).symm
theorem bv_add_neg_24 (x : BitVec 64) : x + 18446744073709551592#64 = x - 24#64 := (BitVec.sub_eq_add_neg x 24#64).symm
theorem bv_add_neg_32 (x : BitVec 64) : x + 18446744073709551584#64 = x - 32#64 := (BitVec.sub_eq_add_neg x 32#64).symm
theorem bv_add_neg_40 (x : BitVec 64) : x + 18446744073709551576#64 = x - 40#64 := (BitVec.sub_eq_add_neg x 40#64).symm
theorem bv_add_neg_48 (x : BitVec 64) : x + 18446744073709551568#64 = x - 48#64 := (BitVec.sub_eq_add_neg x 48#64).symm
theorem bv_add_neg_55 (x : BitVec 64) : x + 18446744073709551561#64 = x - 55#64 := (BitVec.sub_eq_add_neg x 55#64).symm
theorem bv_add_neg_56 (x : BitVec 64) : x + 18446744073709551560#64 = x - 56#64 := (BitVec.sub_eq_add_neg x 56#64).symm
theorem bv_add_neg_64 (x : BitVec 64) : x + 18446744073709551552#64 = x - 64#64 := (BitVec.sub_eq_add_neg x 64#64).symm
theorem bv_add_neg_72 (x : BitVec 64) : x + 18446744073709551544#64 = x - 72#64 := (BitVec.sub_eq_add_neg x 72#64).symm
theorem bv_add_neg_80 (x : BitVec 64) : x + 18446744073709551536#64 = x - 80#64 := (BitVec.sub_eq_add_neg x 80#64).symm
theorem bv_add_neg_87 (x : BitVec 64) : x + 18446744073709551529#64 = x - 87#64 := (BitVec.sub_eq_add_neg x 87#64).symm
theorem bv_add_neg_88 (x : BitVec 64) : x + 18446744073709551528#64 = x - 88#64 := (BitVec.sub_eq_add_neg x 88#64).symm
theorem bv_add_neg_96 (x : BitVec 64) : x + 18446744073709551520#64 = x - 96#64 := (BitVec.sub_eq_add_neg x 96#64).symm
theorem bv_add_neg_104 (x : BitVec 64) : x + 18446744073709551512#64 = x - 104#64 := (BitVec.sub_eq_add_neg x 104#64).symm
theorem bv_add_neg_112 (x : BitVec 64) : x + 18446744073709551504#64 = x - 112#64 := (BitVec.sub_eq_add_neg x 112#64).symm
theorem bv_add_neg_128 (x : BitVec 64) : x + 18446744073709551488#64 = x - 128#64 := (BitVec.sub_eq_add_neg x 128#64).symm
theorem bv_add_neg_136 (x : BitVec 64) : x + 18446744073709551480#64 = x - 136#64 := (BitVec.sub_eq_add_neg x 136#64).symm
theorem bv_add_neg_152 (x : BitVec 64) : x + 18446744073709551464#64 = x - 152#64 := (BitVec.sub_eq_add_neg x 152#64).symm
theorem bv_add_neg_160 (x : BitVec 64) : x + 18446744073709551456#64 = x - 160#64 := (BitVec.sub_eq_add_neg x 160#64).symm
theorem bv_add_neg_168 (x : BitVec 64) : x + 18446744073709551448#64 = x - 168#64 := (BitVec.sub_eq_add_neg x 168#64).symm
theorem bv_add_neg_176 (x : BitVec 64) : x + 18446744073709551440#64 = x - 176#64 := (BitVec.sub_eq_add_neg x 176#64).symm
theorem bv_add_neg_184 (x : BitVec 64) : x + 18446744073709551432#64 = x - 184#64 := (BitVec.sub_eq_add_neg x 184#64).symm
theorem bv_add_neg_186 (x : BitVec 64) : x + 18446744073709551430#64 = x - 186#64 := (BitVec.sub_eq_add_neg x 186#64).symm
theorem bv_add_neg_191 (x : BitVec 64) : x + 18446744073709551425#64 = x - 191#64 := (BitVec.sub_eq_add_neg x 191#64).symm
theorem bv_add_neg_192 (x : BitVec 64) : x + 18446744073709551424#64 = x - 192#64 := (BitVec.sub_eq_add_neg x 192#64).symm
theorem bv_add_neg_196 (x : BitVec 64) : x + 18446744073709551420#64 = x - 196#64 := (BitVec.sub_eq_add_neg x 196#64).symm
theorem bv_add_neg_200 (x : BitVec 64) : x + 18446744073709551416#64 = x - 200#64 := (BitVec.sub_eq_add_neg x 200#64).symm
theorem bv_add_neg_216 (x : BitVec 64) : x + 18446744073709551400#64 = x - 216#64 := (BitVec.sub_eq_add_neg x 216#64).symm
theorem bv_add_neg_512 (x : BitVec 64) : x + 18446744073709551104#64 = x - 512#64 := (BitVec.sub_eq_add_neg x 512#64).symm

theorem bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
theorem bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

/-- Masking `w` by `0xffffffff00000000#64` and ORing `BitVec.zeroExtend 64 v` replaces the low
32 bits of `w` with `v`. -/
private theorem mask32_or_zext32_eq (w : BitVec 64) (v : BitVec 32) :
    (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 32 32 w ++ v := by
  have hmask : (18446744069414584320#64 : BitVec 64) = 0xffffffff#32 ++ 0#32 := rfl
  rw [hmask]; bv_bits

private theorem extractLsb'_append_lo {n m k len : Nat} (hi : BitVec n) (lo : BitVec m)
    (hk : k + len ≤ m) :
    BitVec.extractLsb' k len (hi ++ lo) = BitVec.extractLsb' k len lo := by
  ext i hlt
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  have hltm : k + i < m := by omega
  simp [hltm]

private theorem extractLsb'_append_hi {n m k len : Nat} (hi : BitVec n) (lo : BitVec m)
    (hk : m ≤ k) :
    BitVec.extractLsb' k len (hi ++ lo) = BitVec.extractLsb' (k - m) len hi := by
  ext i hlt
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  have hge : ¬ (k + i < m) := by omega
  have hsub : k + i - m = k - m + i := by omega
  simp [hge, hsub]

private theorem extractLsb'_self (b : BitVec 8) : BitVec.extractLsb' 0 8 b = b := by
  ext i hi; simp

private theorem extract8_mask32_hi (w : BitVec 64) (v : BitVec 32) (k : Nat)
    (hk : 32 ≤ k) (hk8 : k + 8 ≤ 64) :
    BitVec.extractLsb' k 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' k 8 w := by
  rw [mask32_or_zext32_eq, extractLsb'_append_hi _ _ hk]
  ext i hi
  have h2 : k - 32 + i < 32 := by omega
  have h3 : 32 + (k - 32 + i) = k + i := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem, h2, h3]

theorem extract8_mask32_0 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = a := by
  rw [mask32_or_zext32_eq, extractLsb'_append_lo _ _ (by decide),
    extractLsb'_append_lo _ _ (by decide), extractLsb'_self]
theorem extract8_mask32_8 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = b := by
  rw [mask32_or_zext32_eq, extractLsb'_append_lo _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_lo _ _ (by decide),
    extractLsb'_self]
theorem extract8_mask32_16 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = c := by
  rw [mask32_or_zext32_eq, extractLsb'_append_lo _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_lo _ _ (by decide), extractLsb'_self]
theorem extract8_mask32_24 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8
      (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = d := by
  rw [mask32_or_zext32_eq, extractLsb'_append_lo _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_self]
theorem extract8_mask32_32 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 32 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 32 8 w := extract8_mask32_hi w v 32 (by decide) (by decide)
theorem extract8_mask32_40 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 40 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 40 8 w := extract8_mask32_hi w v 40 (by decide) (by decide)
theorem extract8_mask32_48 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 48 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 48 8 w := extract8_mask32_hi w v 48 (by decide) (by decide)
theorem extract8_mask32_56 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 56 8 (w &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 56 8 w := extract8_mask32_hi w v 56 (by decide) (by decide)

theorem extract8_concat8_0 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 0 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b0 := by
  rw [extractLsb'_append_lo _ _ (by decide), extractLsb'_self]
theorem extract8_concat8_8 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 8 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b1 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_lo _ _ (by decide),
    extractLsb'_self]
theorem extract8_concat8_16 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 16 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b2 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_lo _ _ (by decide), extractLsb'_self]
theorem extract8_concat8_24 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 24 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b3 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_lo _ _ (by decide),
    extractLsb'_self]
theorem extract8_concat8_32 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 32 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b4 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_lo _ _ (by decide), extractLsb'_self]
theorem extract8_concat8_40 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 40 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b5 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_lo _ _ (by decide),
    extractLsb'_self]
theorem extract8_concat8_48 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 48 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b6 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_lo _ _ (by decide), extractLsb'_self]
theorem extract8_concat8_56 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 56 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b7 := by
  rw [extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_append_hi _ _ (by decide),
    extractLsb'_append_hi _ _ (by decide), extractLsb'_self]

attribute [local arm64_norm, local wp_norm]
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## `<IdentityKey as TryFrom<&[u8]>>::try_from` (`0x2c530`) -/

def bytes32At (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
  ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
  ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15) ∗
  ((a + 16#64) ↦₈ b16) ∗ ((a + 17#64) ↦₈ b17) ∗ ((a + 18#64) ↦₈ b18) ∗ ((a + 19#64) ↦₈ b19) ∗
  ((a + 20#64) ↦₈ b20) ∗ ((a + 21#64) ↦₈ b21) ∗ ((a + 22#64) ↦₈ b22) ∗ ((a + 23#64) ↦₈ b23) ∗
  ((a + 24#64) ↦₈ b24) ∗ ((a + 25#64) ↦₈ b25) ∗ ((a + 26#64) ↦₈ b26) ∗ ((a + 27#64) ↦₈ b27) ∗
  ((a + 28#64) ↦₈ b28) ∗ ((a + 29#64) ↦₈ b29) ∗ ((a + 30#64) ↦₈ b30) ∗ ((a + 31#64) ↦₈ b31)

theorem exists_bytes32_of_vector32 (v : List.Vector (BitVec 8) 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
       b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ v.toList) =
        bytes32At a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
    fun a => ?_⟩
  change (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]) = _
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, bytes32At]

theorem pointsTo64_eq_extract_bytes8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ w.extractLsb' 8 8) ∗
      ((a + 2#64) ↦₈ w.extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ w.extractLsb' 24 8) ∗
      ((a + 4#64) ↦₈ w.extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ w.extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ w.extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hw : w = w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++
      w.extractLsb' 32 8 ++ w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by
    have hext (s₂ s₁ n₂ n₁ : Nat) (h : s₂ = s₁ + n₁) :
        w.extractLsb' s₂ n₂ ++ w.extractLsb' s₁ n₁ = w.extractLsb' s₁ (n₂ + n₁) := by
      subst h
      ext i hi
      simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
      split
      · rfl
      · congr 1; omega
    rw [hext 56 48 8 8 rfl, hext 48 40 16 8 rfl, hext 40 32 24 8 rfl,
      hext 32 24 32 8 rfl, hext 24 16 40 8 rfl, hext 16 8 48 8 rfl,
      hext 8 0 56 8 rfl]
    ext i hi; simp
  conv => lhs; rw [hw]
  exact pointsTo64_eq_bytes8 a _ _ _ _ _ _ _ _

theorem memRegion_8_bytes (a : BitVec 64) :
    memRegion a 8 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (a + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (a + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (a + 3#64) ↦₈ b3) ∗
      (∃∗ b4 : BitVec 8, (a + 4#64) ↦₈ b4) ∗
      (∃∗ b5 : BitVec 8, (a + 5#64) ↦₈ b5) ∗
      (∃∗ b6 : BitVec 8, (a + 6#64) ↦₈ b6) ∗
      (∃∗ b7 : BitVec 8, (a + 7#64) ↦₈ b7) := by
  rw [memRegion_split a 1 7 (by decide),
    memRegion_split (a + 1#64) 1 6 (by decide),
    memRegion_split (a + 1#64 + 1#64) 1 5 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64) 1 4 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64) 1 3 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [ProofLib.memRegion_one, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_7_bytes (a : BitVec 64) :
    memRegion a 7 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (a + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (a + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (a + 3#64) ↦₈ b3) ∗
      (∃∗ b4 : BitVec 8, (a + 4#64) ↦₈ b4) ∗
      (∃∗ b5 : BitVec 8, (a + 5#64) ↦₈ b5) ∗
      (∃∗ b6 : BitVec 8, (a + 6#64) ↦₈ b6) := by
  rw [memRegion_split a 1 6 (by decide),
    memRegion_split (a + 1#64) 1 5 (by decide),
    memRegion_split (a + 1#64 + 1#64) 1 4 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64) 1 3 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [ProofLib.memRegion_one, BitVec.add_assoc, BitVec.reduceAdd]

def memRegion_8_bytes_mr_rhs (a : BitVec 64) : SepProp :=
  memRegion a 1 ∗
  memRegion (a + 1#64) 1 ∗
  memRegion (a + 2#64) 1 ∗
  memRegion (a + 3#64) 1 ∗
  memRegion (a + 4#64) 1 ∗
  memRegion (a + 5#64) 1 ∗
  memRegion (a + 6#64) 1 ∗
  memRegion (a + 7#64) 1

theorem memRegion_8_bytes_mr (a : BitVec 64) :
    memRegion a 8 = memRegion_8_bytes_mr_rhs a := by
  rw [memRegion_8_bytes a]
  simp only [← ProofLib.memRegion_one, memRegion_8_bytes_mr_rhs]

theorem memRegion_40_words (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

private theorem cells_12_identityKey_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      memRegion (sp - 48#64) 8 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    memRegion_split (sp - 96#64) 8 88 (by decide),
    memRegion_split (sp - 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64)]

private theorem memRegion_40_identityKey_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗
      memRegion_8_bytes_mr_rhs (sp - 87#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 79#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 71#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 63#64) ∗
      memRegion (sp - 55#64) 7 := by
  rw [memRegion_split (sp - 88#64) 1 39 (by decide),
    memRegion_split (sp - 88#64 + 1#64) 8 31 (by decide),
    memRegion_split (sp - 88#64 + 1#64 + 8#64) 8 23 (by decide),
    memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64) 8 15 (by decide),
    memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64 + 8#64) 8 7 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  rw [memRegion_8_bytes_mr (sp - 87#64),
      memRegion_8_bytes_mr (sp - 79#64),
      memRegion_8_bytes_mr (sp - 71#64),
      memRegion_8_bytes_mr (sp - 63#64)]

private def pkTryFromOk40Spec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ logOff img
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ logOff img

private theorem pkTryFromOk40_ok_at {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyTryFromSliceName +
        BitVec.ofNat 64 75180)
      (pkTryFromOk40Spec img) := by
  have hk : libsignalSessionCode.fnOff identityKeyTryFromSliceName + 75180 =
      libsignalSessionCode.fnOff pkTryFromName := by
    simp only [libsignalSessionCode_fnOff_0x2c614, libsignalSessionCode_fnOff_0x3ebc0]
  refine subroutine_ok_map
    (pk_try_from_ok_at img C ctl abs himg identityKeyTryFromSliceName 75180 hk) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOk40Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOk40Spec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

def identityKeyTryFromSliceOkSpec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, outPtr) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = outPtr ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion outPtr 40 ∗ logOff img ∗
      stackAt s.sp 96
  post := fun (p, bs, pk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 8#64) ↦ₛ pk.bytes.toList) ∗
      logOff img ∗
      stackAt s0.sp 96

set_option maxHeartbeats 3200000 in
private theorem identityKeyTryFromSlice_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceOkSpec img) := by
  unfold identityKeyTryFromSliceOkSpec
  have hpk := pkTryFromOk40_ok_at (C := C) (ctl := ctl) (abs := abs) himg
  simp only [pkTryFromOk40Spec] at hpk
  have hfn : libsignalSessionCode.fnOff identityKeyTryFromSliceName = 0x2c614 :=
    libsignalSessionCode_fnOff_0x2c614
  responder_wire_fetches_from img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x2c614 0 264
  clear hfn
  dsimp only [tripleRatchetProgAt, BitVec.ofNat_eq_ofNat] at hpk ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr identityKeyTryFromSliceName = entry
  wp_init x s0
  examples_hide_fetches
  rcases x with ⟨p, bs, pk, outPtr⟩
  dsimp only at *
  subst h_1 h_3
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk_bytes⟩ := exists_bytes32_of_vector32 pk.bytes
  have hstk_eq : stackAt s0.sp 96 = cells (s0.sp - 96#64) 12 := by
    simp only [stackAt]
    exact ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)
  rw [hstk_eq]
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  wp_pull_exists
  wp_steps
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, pk, s0.sp - 88#64)
  rw [memRegion_40_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 48#64),
      memRegion_8_bytes (s0.sp - 40#64),
      memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  rw [hpk_bytes (s0.sp - 87#64),
      hpk_bytes (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 16#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 24#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 32#64),
      cells_12_identityKey_pre s0.sp,
      memRegion_40_identityKey_post s0.sp,
      memRegion_8_bytes_mr (s0.sp - 48#64),
      memRegion_8_bytes_mr (s0.sp - 40#64),
      memRegion_8_bytes_mr (s0.sp - 8#64)]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

/-! ## `PreKeyTryFromArgs` and `preKeyTryFromSpec` -/

/-- Arguments of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (`0x29b30`), matching
`PreKeyMessageFields` in `Computational/Specifications/LibsignalE2E/PqxdhCorrect.lean`. -/
structure PreKeyTryFromArgs where
  /-- Input slice pointer (`x0`). -/
  ptr : BitVec 64
  /-- Output `sret` pointer (`x8`, 248 bytes). -/
  sret : BitVec 64
  /-- Field 5: `registration_id` (`u32`). -/
  regId : BitVec 32
  /-- Field 1: `pre_key_id` (`Option<u32>`). -/
  opkId : Option (BitVec 32)
  /-- Field 6: `signed_pre_key_id` (`u32`). -/
  spkId : BitVec 32
  /-- Field 7: `kyber_pre_key_id` (`u32`). -/
  kpkId : BitVec 32
  /-- Field 8 payload: 1568-byte Kyber1024 ciphertext (serialized behind `0x08`). -/
  kyberCt : List.Vector (BitVec 8) 1568
  /-- Field 2 payload: 32-byte X25519 base public key (serialized behind `0x05`). -/
  baseKey : List.Vector (BitVec 8) 32
  /-- Field 3 payload: 32-byte X25519 identity public key (serialized behind `0x05`). -/
  idPub : List.Vector (BitVec 8) 32
  /-- Field 4 payload: serialized inner `SignalMessage`. -/
  inner : List (BitVec 8)

namespace PreKeyTryFromArgs

/-- Serialized 1569-byte Kyber1024 ciphertext (`0x08 ‖ kyberCt`). -/
def kyberBytes (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  0x08#8 :: x.kyberCt.toList

/-- Serialized 33-byte base public key (`0x05 ‖ baseKey`). -/
def bkBytes (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  0x05#8 :: x.baseKey.toList

/-- Serialized 33-byte identity public key (`0x05 ‖ idPub`). -/
def ikBytes (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  0x05#8 :: x.idPub.toList

@[simp] theorem kyberBytes_length (x : PreKeyTryFromArgs) : x.kyberBytes.length = 1569 := by
  simp [kyberBytes]

@[simp] theorem bkBytes_length (x : PreKeyTryFromArgs) : x.bkBytes.length = 33 := by
  simp [bkBytes]

@[simp] theorem ikBytes_length (x : PreKeyTryFromArgs) : x.ikBytes.length = 33 := by
  simp [ikBytes]

def protoMsg (x : PreKeyTryFromArgs) : ProtoPreKeySignalMessage :=
  { registrationId := some x.regId
    preKeyId := x.opkId
    signedPreKeyId := some x.spkId
    kyberPreKeyId := some x.kpkId
    kyberCiphertext := some x.kyberBytes
    baseKey := some x.bkBytes
    identityKey := some x.ikBytes
    message := some x.inner }

def protoBytes (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  x.protoMsg.encode

/-- Full wire bytes `versionByte 4#8 :: x.protoBytes`. -/
def bytes (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  versionByte 4#8 :: x.protoBytes

/-- Model `PreKeySignalMessage` produced when
`SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg`. -/
def toModel (x : PreKeyTryFromArgs) (innerMsg : SignalMessage) : PreKeySignalMessage :=
  { messageVersion := 4#8
    registrationId := x.regId
    preKeyId := x.opkId
    signedPreKeyId := x.spkId
    kyberPayload := some { preKeyId := x.kpkId, ciphertext := x.kyberBytes }
    baseKey := ⟨x.baseKey⟩
    identityKey := ⟨⟨x.idPub⟩⟩
    message := innerMsg
    serialized := x.bytes }

end PreKeyTryFromArgs

/-- Result layout at `sret` (248 bytes) after `PreKeySignalMessage::try_from` (`0x29b30`). -/
def preKeyResultAt (A : RustAlloc) (sret : BitVec 64) (x : PreKeyTryFromArgs) : SepProp :=
  match SignalMessage.tryFrom protoSignalCodec x.inner with
  | .ok innerMsg =>
      ∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g sret (x.toModel innerMsg)
  | .error e =>
      (sret ↦₆₄ errTag) ∗
      speAt A [] (sret + 8#64) e ∗
      memRegion (sret + 56#64) 192

/-- Specification of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (`0x29b30`, 675 insns). -/
def preKeyTryFromSpec (A : RustAlloc) (img : Obj.Image) : Spec PreKeyTryFromArgs :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptr ∧
          (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧
          s.readReg64 .x8 = x.sret⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗
        memRegion x.sret 248 ∗
        logOff img ∗
        stackAt s.sp preKeyTryFromStack ∗
        A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        preKeyResultAt A x.sret x ∗
        (x.ptr ↦ₛ x.bytes) ∗
        logOff img ∗
        stackAt s0.sp preKeyTryFromStack ∗
        A.pool
      onPanic := fun _ s0 sf =>
        ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Callee Offset Wrappers from `preKeyTryFromName` -/

theorem int32Merge_ok_at_prekey {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Int32MergeOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyTryFromName + 18446744073709391792#64)
      (int32MergeSpec A) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0x2bc4 (by decide)]
  exact h

theorem bytesMerge_ok_at_prekey {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : BytesMergeOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 18446744073709390708#64)
      (bytesMergeSpec A img) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0x2788 (by decide)]
  exact h

theorem dropSpe_ok_at_prekey {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : CryptoVerification.LibsignalTripleRatchet.DropSpeOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 18446744073709389828#64)
      ((dropSpeSpec A).inImage img) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0x2418 (by decide)]
  exact h

def deserializeOk33Spec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (ptr, bs, pk, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      PublicKey.deserialize bs = .ok pk⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    logOff img
  post := fun (ptr, bs, pk, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    logOff img

theorem deserializeFull_ok_at_tripleRatchet {C : Crypto} {b : BitVec 64} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = 0x3dc34) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (deserializeFullSpec b) := by
  rw [← Program.fnAddr_rel hfn libsignalSessionCode_fnOff_0x3dc34 hk]
  exact deserializeFull_ok b (Rust.withPanics (tripleRatchetExterns C ctl abs))

def IntoBoxedSliceOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr intoBoxedSliceName)
    (intoBoxedSliceSpec A)

def TryCloneFromRefOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr tryCloneFromRefName)
    (tryCloneFromRefSpec A)

theorem panic_at_handle_alloc_error2 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_alloc_error_ext b (tripleRatchetExterns C ctl abs) name k hk

theorem deserialize_ok_at_prekey {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 81952#64)
      (deserializeOk33Spec img) := by
  have hfull := deserializeFull_ok_at_tripleRatchet (C := C) (b := img.base) (ctl := ctl)
    (abs := abs) libsignalSessionCode_fnOff_0x29c14 (k := 81952) (by decide)
  refine subroutine_ok_map hfull ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeOk33Spec, logOff, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen, hdes⟩, hmem⟩
  refine ⟨(ptr, bs, sret), R, ?_, fun sf hpost => ?_⟩
  · simp only [deserializeFullSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlen, ProofLib.ObjectLoad.base_aligned_of_loads himg⟩, hmem⟩
  · simp only [deserializeFullSpec, hdes, deserializeResult33At,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [deserializeOk33Spec, logOff, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

theorem intoBoxedSlice_ok_at_prekey {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : IntoBoxedSliceOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyTryFromName + 18446744073709491136#64)
      (intoBoxedSliceSpec A) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0x1afd4 (by decide)]
  exact h

theorem identityKeyTryFrom_ok_at_prekey {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 10752#64)
      (identityKeyTryFromSliceOkSpec img) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0x2c614 (by decide)]
  exact identityKeyTryFromSlice_ok himg

theorem signalTryFrom_ok_at_prekey {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryFromName) (tryFromSpec A img)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyTryFromName + 18446744073709534472#64)
      (tryFromSpec A img) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0x2591c (by decide)]
  exact h

theorem tryCloneFromRef_ok_at_prekey {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : TryCloneFromRefOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyTryFromName + 18446744073709433996#64)
      (tryCloneFromRefSpec A) := by
  rw [fnAddr_sub_rel libsignalSessionCode_fnOff_0x29c14
    libsignalSessionCode_fnOff_0xd0a0 (by decide)]
  exact h

theorem dealloc_ok_at_prekey {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyTryFromName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x29c14))
      (rustDeallocSpec A) :=
  dealloc_ok_at_norm hA (name := preKeyTryFromName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x29c14))

theorem panic_at_prekey_handle_alloc_error {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyTryFromName + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x29c14)) =
      some Rust.panicked :=
  panic_at_handle_alloc_error2 (name := preKeyTryFromName) (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x29c14))

/-! ## Protobuf Field Suffix Decomposition and Cursor Lemmas -/

def psmField1 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.uint32Field 1 x.opkId

def psmField2 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.bytesField 2 (some x.bkBytes)

def psmField3 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.bytesField 3 (some x.ikBytes)

def psmField4 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.bytesField 4 (some x.inner)

def psmField5 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.uint32Field 5 (some x.regId)

def psmField6 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.uint32Field 6 (some x.spkId)

def psmField7 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.uint32Field 7 (some x.kpkId)

def psmField8 (x : PreKeyTryFromArgs) : List (BitVec 8) :=
  Prost.bytesField 8 (some x.kyberBytes)

def psmRem8 (_ : PreKeyTryFromArgs) : List (BitVec 8) := []
def psmRem7 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField8 x ++ psmRem8 x
def psmRem6 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField7 x ++ psmRem7 x
def psmRem5 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField6 x ++ psmRem6 x
def psmRem4 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField5 x ++ psmRem5 x
def psmRem3 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField4 x ++ psmRem4 x
def psmRem2 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField3 x ++ psmRem3 x
def psmRem1 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField2 x ++ psmRem2 x
def psmRem0 (x : PreKeyTryFromArgs) : List (BitVec 8) := psmField1 x ++ psmRem1 x

theorem protoBytes_eq_psmRem0 (x : PreKeyTryFromArgs) :
    x.protoBytes = psmRem0 x := by
  simp [PreKeyTryFromArgs.protoBytes, PreKeyTryFromArgs.protoMsg,
    ProtoPreKeySignalMessage.encode,
    psmRem0, psmRem1, psmRem2, psmRem3, psmRem4, psmRem5, psmRem6, psmRem7, psmRem8,
    psmField1, psmField2, psmField3, psmField4, psmField5, psmField6, psmField7, psmField8,
    List.append_assoc]

theorem encodeVarint_1569 : encodeVarint 1569#64 = [0xa1#8, 0x0c#8] := by decide

theorem psmField1_some (x : PreKeyTryFromArgs) (v : BitVec 32) (h : x.opkId = some v) :
    psmField1 x = 0x08#8 :: encodeVarint (v.zeroExtend 64) := by
  rw [psmField1, h, prost_uint32Field_some, prost_key_1_0, List.singleton_append]

theorem psmField2_eq (x : PreKeyTryFromArgs) :
    psmField2 x = 0x12#8 :: (encodeVarint 33#64 ++ x.bkBytes) := by
  rw [psmField2, prost_bytesField_some 2 x.bkBytes (by simp), prost_key_2_2,
    PreKeyTryFromArgs.bkBytes_length, List.append_assoc, List.singleton_append]

theorem psmField3_eq (x : PreKeyTryFromArgs) :
    psmField3 x = 0x1a#8 :: (encodeVarint 33#64 ++ x.ikBytes) := by
  rw [psmField3, prost_bytesField_some 3 x.ikBytes (by simp), prost_key_3_2,
    PreKeyTryFromArgs.ikBytes_length, List.append_assoc, List.singleton_append]

theorem psmField4_eq (x : PreKeyTryFromArgs) (hlen : x.inner.length < 2 ^ 64) :
    psmField4 x = 0x22#8 :: (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner) := by
  rw [psmField4, prost_bytesField_some 4 x.inner hlen, prost_key_4_2,
    List.append_assoc, List.singleton_append]

theorem psmField5_eq (x : PreKeyTryFromArgs) :
    psmField5 x = 0x28#8 :: encodeVarint (x.regId.zeroExtend 64) := by
  rw [psmField5, prost_uint32Field_some, prost_key_5_0, List.singleton_append]

theorem psmField6_eq (x : PreKeyTryFromArgs) :
    psmField6 x = 0x30#8 :: encodeVarint (x.spkId.zeroExtend 64) := by
  rw [psmField6, prost_uint32Field_some, prost_key_6_0, List.singleton_append]

theorem psmField7_eq (x : PreKeyTryFromArgs) :
    psmField7 x = 0x38#8 :: encodeVarint (x.kpkId.zeroExtend 64) := by
  rw [psmField7, prost_uint32Field_some, prost_key_7_0, List.singleton_append]

theorem psmField8_eq (x : PreKeyTryFromArgs) :
    psmField8 x = 0x42#8 :: (encodeVarint 1569#64 ++ x.kyberBytes) := by
  rw [psmField8, prost_bytesField_some 8 x.kyberBytes (by simp), prost_key_8_2,
    PreKeyTryFromArgs.kyberBytes_length, List.append_assoc, List.singleton_append]

theorem cons_sliceCursorAfter_append (slot p : BitVec 64) (b : BitVec 8)
    (field rest : List (BitVec 8)) :
    (p ↦₈ b) ∗ sliceCursorAfter slot (p + 1#64) (field ++ rest) rest =
      (p ↦ₛ (b :: field)) ∗
        sliceCursorAt slot (p + BitVec.ofNat 64 (b :: field).length) rest := by
  unfold sliceCursorAfter sliceCursorAt
  have hsub : (field ++ rest).length - rest.length = field.length := by simp
  have hlen : p + 1#64 + BitVec.ofNat 64 field.length =
      p + BitVec.ofNat 64 (b :: field).length := by
    simp only [List.length_cons, BitVec.ofNat_add]
    bv_omega
  rw [hsub, pointsToBytes_append, hlen, pointsToBytes_cons]
  ac_rfl

theorem psmRem_lengths_lt (x : PreKeyTryFromArgs) (h : x.bytes.length < 2 ^ 32) :
    x.protoBytes.length < 2 ^ 32 ∧
    (psmRem0 x).length < 2 ^ 32 ∧
    (psmRem1 x).length < 2 ^ 32 ∧
    (psmRem2 x).length < 2 ^ 32 ∧
    (psmRem3 x).length < 2 ^ 32 ∧
    (psmRem4 x).length < 2 ^ 32 ∧
    (psmRem5 x).length < 2 ^ 32 ∧
    (psmRem6 x).length < 2 ^ 32 ∧
    (psmRem7 x).length < 2 ^ 32 ∧
    x.inner.length < 2 ^ 32 := by
  have h0 : x.bytes.length = x.protoBytes.length + 1 := by simp [PreKeyTryFromArgs.bytes]
  have hp : x.protoBytes.length = (psmRem0 x).length := by rw [protoBytes_eq_psmRem0]
  have hr0 : (psmRem0 x).length = (psmField1 x).length + (psmRem1 x).length := by simp [psmRem0]
  have hr1 : (psmRem1 x).length = (psmField2 x).length + (psmRem2 x).length := by simp [psmRem1]
  have hr2 : (psmRem2 x).length = (psmField3 x).length + (psmRem3 x).length := by simp [psmRem2]
  have hr3 : (psmRem3 x).length = (psmField4 x).length + (psmRem4 x).length := by simp [psmRem3]
  have hr4 : (psmRem4 x).length = (psmField5 x).length + (psmRem5 x).length := by simp [psmRem4]
  have hr5 : (psmRem5 x).length = (psmField6 x).length + (psmRem6 x).length := by simp [psmRem5]
  have hr6 : (psmRem6 x).length = (psmField7 x).length + (psmRem7 x).length := by simp [psmRem6]
  have hf4 : x.inner.length ≤ (psmField4 x).length := by
    simp [psmField4, Prost.bytesField]; omega
  omega

theorem cons_sliceCursorAfter_split (slot ptr : BitVec 64) (b0 : BitVec 8)
    (body rest : List (BitVec 8)) :
    (ptr ↦₈ b0) ∗ sliceCursorAfter slot (ptr + 1#64) (body ++ rest) rest =
      (ptr ↦ₛ (b0 :: body)) ∗
        sliceCursorAt slot (ptr + BitVec.ofNat 64 (b0 :: body).length) rest := by
  unfold sliceCursorAfter sliceCursorAt
  have hsub : (body ++ rest).length - rest.length = body.length := by simp
  have hlen : BitVec.ofNat 64 (b0 :: body).length = 1#64 + BitVec.ofNat 64 body.length := by
    simp only [List.length_cons, Nat.add_comm _ 1, BitVec.ofNat_add]
  have had : ptr + 1#64 + BitVec.ofNat 64 body.length =
      ptr + BitVec.ofNat 64 (b0 :: body).length := by
    rw [hlen, BitVec.add_assoc]
  rw [hsub, pointsToBytes_append, pointsToBytes_cons, had]
  ac_rfl

def opkTag (x : PreKeyTryFromArgs) : BitVec 32 :=
  match x.opkId with
  | none => 0#32
  | some _ => 1#32

theorem opkTag_and_one (x : PreKeyTryFromArgs) :
    opkTag x &&& 1#32 = opkTag x := by
  unfold opkTag
  cases h : x.opkId <;> simp

theorem pointsTo32_pair_entails_optU32At (a : BitVec 64) (x : PreKeyTryFromArgs)
    (opkVal : BitVec 32) (h : ∀ v, x.opkId = some v → opkVal = v) :
    (a ↦₃₂ opkTag x) ∗ ((a + 4#64) ↦₃₂ opkVal) ⊢
      CryptoVerification.LibsignalPublicApiRepr.optU32At a x.opkId := by
  cases hopk : x.opkId with
  | none =>
    simp only [opkTag, hopk, CryptoVerification.LibsignalPublicApiRepr.optU32At]
    exact sepConj_mono_right (pointsTo32_entails_memRegion (a + 4#64) opkVal)
  | some v =>
    have hv := h v hopk
    subst hv
    simp only [opkTag, hopk, CryptoVerification.LibsignalPublicApiRepr.optU32At]
    exact Entails.refl _

/-! ## Placed Specifications and Callees -/

def pkTryFromOk40PlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ lsLogOff
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ lsLogOff

theorem pkTryFromOk40_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (lsmpl.base 211)
      pkTryFromOk40PlacedSpec := by
  refine subroutine_ok_map (pkTryFrom_placed_ok H) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOk40PlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOk40PlacedSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

def identityKeyTryFromSliceOkPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, outPtr) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = outPtr ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion outPtr 40 ∗ lsLogOff ∗
      stackAt s.sp 96
  post := fun (p, bs, pk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 8#64) ↦ₛ pk.bytes.toList) ∗
      lsLogOff ∗
      stackAt s0.sp 96

set_option maxHeartbeats 3200000 in
theorem identityKeyTryFromSlice_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_116).rebase (blkPl_116).base H)
      (blkPl_116).base
      (withLsCodeLoaded lsmpl identityKeyTryFromSliceOkPlacedSpec) := by
  unfold identityKeyTryFromSliceOkPlacedSpec
  have hpk := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_116).rebase (blkPl_116).base H)
    (entry := lsmpl.base 211)
    (pkTryFromOk40_placed_ok H)
  simp only [withLsCl, pkTryFromOk40PlacedSpec] at hpk
  wp_init x s0
  rcases x with ⟨p, bs, pk, outPtr⟩
  dsimp only at *
  subst h_2 h_4
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk_bytes⟩ := exists_bytes32_of_vector32 pk.bytes
  have hstk_eq : stackAt s0.sp 96 = cells (s0.sp - 96#64) 12 := by
    simp only [stackAt]
    exact ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)
  rw [hstk_eq]
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 211)
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, pk, s0.sp - 88#64)
  rw [memRegion_40_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 48#64),
      memRegion_8_bytes (s0.sp - 40#64),
      memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  rw [hpk_bytes (s0.sp - 87#64),
      hpk_bytes (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 16#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 24#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 32#64),
      cells_12_identityKey_pre s0.sp,
      memRegion_40_identityKey_post s0.sp,
      memRegion_8_bytes_mr (s0.sp - 48#64),
      memRegion_8_bytes_mr (s0.sp - 40#64),
      memRegion_8_bytes_mr (s0.sp - 8#64)]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

def deserializeOk33PlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (ptr, bs, pk, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      PublicKey.deserialize bs = .ok pk⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    lsLogOff
  post := fun (ptr, bs, pk, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    lsLogOff

private theorem memRegion_33_eq (sret : BitVec 64) :
    memRegion sret 33 =
      ∃∗ tag0 : BitVec 8, ∃∗ out32 : List (BitVec 8),
        ⌜out32.length = 32⌝ ∗ (sret ↦₈ tag0) ∗ ((sret + 1#64) ↦ₛ out32) := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 1) (k := 32)
      (b' := sret + 1#64) rfl (by rfl) (by decide),
    memRegion_one,
    memRegion_eq_exists_bytes (sret + 1#64) 32 (by decide)]
  rw [sepExists_sepConj_left]
  apply congrArg sepExists; funext tag0
  rw [sepExists_sepConj_right]
  apply congrArg sepExists; funext out32
  rw [← sepConj_assoc, sepConj_comm (sret ↦₈ tag0), sepConj_assoc]

theorem deserialize_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok
      ((CryptoVerification.blkPC_201).rebase (CryptoVerification.blkPl_201).base H)
      (lsmpl.base 201)
      deserializeOk33PlacedSpec := by
  refine subroutine_ok_map
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeOk33PlacedSpec, memRegion_33_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hpre
  rcases hpre with ⟨tag0, out32, hpre⟩
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt, hdeser⟩, hpre⟩
  rw [sepConj_pure_left_comm (ptr ↦ₛ bs), satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hout32, hpre⟩
  refine ⟨(ptr, bs, pk, sret, tag0, out32), R, ?_, ?_⟩
  · dsimp only [CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt, hdeser, hout32⟩, hpre⟩
  · intro sf hpost
    exact hpost

def preKeyTryFromPlacedSpec (A : RustAlloc) [LibsignalPlacement] : Spec PreKeyTryFromArgs :=
  withLsCodeLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptr ∧
          (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧
          s.readReg64 .x8 = x.sret⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗
        memRegion x.sret 248 ∗
        lsLogOff ∗
        stackAt s.sp preKeyTryFromStack ∗
        A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        preKeyResultAt A x.sret x ∗
        (x.ptr ↦ₛ x.bytes) ∗
        lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗
        A.pool
      onPanic := fun _ s0 sf =>
        ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

end CryptoVerification.E2E.Pqxdh.ResponderWire
