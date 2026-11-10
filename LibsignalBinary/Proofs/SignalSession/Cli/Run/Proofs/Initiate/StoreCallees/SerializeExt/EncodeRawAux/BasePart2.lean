/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.BasePart1
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::encode_raw`: Receiver-Chain Call Wrapper and Proto3 Field Rewrites
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
open ProofLib.ProgramReflection
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Execute a `bl encode::<Chain>` call inside `encode_raw` on `chainAt` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_encodeChain {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : OkAtX img ext encodeChainName (encodeChainSpecX A))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  refine encraw_call_protoEncodeChain hEC tag sp0 a v cap ptr ret_pc gc bs htag hlen_lt
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
  have hPostEq :
      ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' hpcm hrunm hspm htrm hcsm

/-! ## 9. Callee-saved tracking, branch condition lemmas, and proto3 field rewrites -/

@[scoped arm64_norm]
theorem and_self_true : (True ∧ True) = True := and_self True

def EncRawUpperSaved (s0 s : State) : Prop :=
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  (s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)

theorem EncRawUpperSaved.refl (s : State) : EncRawUpperSaved s s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem EncRawUpperSaved.trans {s0 s1 s2 : State}
    (h1 : EncRawUpperSaved s0 s1) (h2 : EncRawUpperSaved s1 s2) :
    EncRawUpperSaved s0 s2 := by
  reg_chain

theorem EncRawUpperSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) : EncRawUpperSaved s1 s2 := by
  reg_chain

theorem sp_sub_80_spAligned {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 80#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem bv32_beq_zero_false {w : BitVec 32} (hne : w ≠ 0#32) :
    (w == 0#32) = false :=
  beq_eq_false_iff_ne.mpr hne

theorem bv64_beq_zero_false {w : BitVec 64} (hne : w ≠ 0#64) :
    (w == 0#64) = false :=
  beq_eq_false_iff_ne.mpr hne

theorem ofNat64_len_beq_zero_false {bs : List (BitVec 8)} (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change bs.length = 0 at h1
  omega

theorem cap_sub_len_ult_false {cap : BitVec 64} {len add : Nat}
    (hle : len + add ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap - BitVec.ofNat 64 len) (BitVec.ofNat 64 add) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

theorem cap_sub_len_ult_true {cap : BitVec 64} {len add : Nat}
    (hlen_le : len ≤ cap.toNat) (hlt : cap.toNat < len + add)
    (hcap : cap.toNat < 2 ^ 63) (hadd : add < 2 ^ 63) :
    BitVec.ult (cap - BitVec.ofNat 64 len) (BitVec.ofNat 64 add) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

theorem bv_len_add_slice_er (bs payload : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length =
      BitVec.ofNat 64 (bs ++ payload).length := by
  simp only [List.length_append, BitVec.ofNat_add]

theorem uint32Field_zero (tag : Nat) : uint32Field tag 0#32 = [] := rfl

theorem uint32Field_ne_zero {tag : Nat} {v : BitVec 32} {k : BitVec 8}
    (hne : v ≠ 0#32) (hk : encodeKey tag .varint = [k] := by decide) :
    uint32Field tag v = [k] ++ encodeVarint (BitVec.zeroExtend 64 v) := by
  have hne' : v ≠ 0 := hne
  simp only [uint32Field, hne', ↓reduceIte, hk]

theorem uint64Field_zero (tag : Nat) : uint64Field tag 0#64 = [] := rfl

theorem uint64Field_ne_zero {tag : Nat} {v : BitVec 64} {k : BitVec 8}
    (hne : v ≠ 0#64) (hk : encodeKey tag .varint = [k] := by decide) :
    uint64Field tag v = [k] ++ encodeVarint v := by
  have hne' : v ≠ 0 := hne
  simp only [uint64Field, hne', ↓reduceIte, hk]

theorem int32Field_zero (tag : Nat) : int32Field tag 0#32 = [] := rfl

theorem int32Field_ne_zero {tag : Nat} {v : BitVec 32} {k : BitVec 8}
    (hne : v ≠ 0#32) (hk : encodeKey tag .varint = [k] := by decide) :
    int32Field tag v = [k] ++ encodeVarint (BitVec.signExtend 64 v) := by
  have hne' : v ≠ 0 := hne
  simp only [int32Field, hne', ↓reduceIte, hk]

theorem optUint32Field_none (tag : Nat) : optUint32Field tag none = [] := rfl

theorem optUint32Field_some {tag : Nat} (v : BitVec 32) {k : BitVec 8}
    (hk : encodeKey tag .varint = [k] := by decide) :
    optUint32Field tag (some v) = [k] ++ encodeVarint (BitVec.zeroExtend 64 v) := by
  simp only [optUint32Field, hk]

theorem bytesField_nil (tag : Nat) : bytesField tag [] = [] := rfl

theorem bytesField_ne_nil {tag : Nat} {bs : List (BitVec 8)} {k : BitVec 8}
    (hne : bs ≠ []) (hk : encodeKey tag .lengthDelimited = [k] := by decide) :
    bytesField tag bs = [k] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  simp only [bytesField, hne, ↓reduceIte, lenField, hk]

theorem bytesField_ne_nil_length {tag : Nat} {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hk : (encodeKey tag .lengthDelimited).length = 1 := by decide) :
    (bytesField tag bs).length = 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hk]

theorem uint32Field_ne_zero_length {tag : Nat} {v : BitVec 32}
    (hne : v ≠ 0#32) (hk : (encodeKey tag .varint).length = 1 := by decide) :
    (uint32Field tag v).length = 1 + (encodeVarint (BitVec.zeroExtend 64 v)).length := by
  have hne' : v ≠ 0 := hne
  simp only [uint32Field, hne', ↓reduceIte, List.length_append, hk]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
