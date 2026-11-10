/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `encode::<Chain, Vec<u8>>`: Prologue, Length Header, and `sender_ratchet_key` Helpers
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf sepWPp_extract_vecU8Buf_le vecU8Buf_eq_open_one vecU8Buf_snoc_eq
open CryptoVerification.E2E.Record
open EncodeVarintNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ### Pure helpers for Seg 0, Seg 1, Seg 2 -/

theorem encChain_tag_orr_eq {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    ((2#32 ||| ((BitVec.ofNat 64 tag).truncate 32 <<< (3 : Nat))).zeroExtend 64) =
      BitVec.ofNat 64 (tag * 8 + 2) := by
  rcases htag with rfl | rfl <;> decide

theorem encChain_encodeKey_eq {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) = encodeKey tag .lengthDelimited := by
  rcases htag with rfl | rfl <;> decide +kernel

theorem encChain_encodeKey_len {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    (encodeKey tag .lengthDelimited).length = 1 := by
  rcases htag with rfl | rfl <;> decide +kernel

theorem encChainMem_len_lt {x : EncodeChainGhost}
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (encChainMem x.gc).length < 2 ^ 32 := by
  simp only [lenField, List.length_append] at hlen
  omega

theorem bytesField_len_le_encChainMem_srk (gc : ChainGhost × ReceiverChain) :
    (bytesField 1 gc.1.srk.bytes).length ≤ (encChainMem gc).length := by
  simp only [encChainMem, List.length_append]
  omega

theorem bytesField_len_le_encChainMem_priv (gc : ChainGhost × ReceiverChain) :
    (bytesField 1 gc.1.srk.bytes).length + (bytesField 2 gc.1.priv.bytes).length ≤
      (encChainMem gc).length := by
  simp only [encChainMem, List.length_append]
  omega

theorem bytesField_nonempty_eq (tag : Nat) (tagByte : BitVec 8) (bs : List (BitVec 8))
    (hne : bs ≠ [])
    (htag : [tagByte] = encodeKey tag .lengthDelimited) :
    [tagByte] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs = bytesField tag bs := by
  simp only [bytesField, hne, ↓reduceIte, lenField, htag, List.append_assoc]

/-! ### Callee Helper for `Chain::encoded_len` -/

theorem step_encChain_chainLen (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hchain : OkAtX img ext chainLenName (chainLenSpec A))
    (sp0 ret_pc : BitVec 64)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = x.a)
    (hlen : (encChainMem x.gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [chainLen_fnAddr_eq] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpX.call (x := ChainLenGhost.mk x.a x.gc)
    (F := memRegion (sp0 - 96#64 - 33120#64) 33040 ∗ F)
    hchain hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_chainLen (sp0 - 96#64)] at hm
    simp only [chainLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [chainLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [chainLenSpec, hsp, sepConj_assoc]
    refine SepWPpX.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    have hGoalEq :
        (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          memRegion (sp0 - 96#64 - 33120#64) 33040 ∗ F) =
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_chainLen (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

/-! ### Segment 0 basic-block helpers (`+0x000..+0x040`) -/

@[local arm64_norm]
theorem bv_add_neg96 (sp0 : BitVec 64) :
    sp0 + bv% (2 ^ 64 - 96) = sp0 - 96#64 := by bv_omega

/-- Steps the prologue, field-key setup, and `encode_varint` call (`+0x000..+0x030`). -/
theorem step_encChain_prologue (img : Obj.Image) (ext : String → Option (State → State))
    (tag : Nat) (a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (htag : tag = 6 ∨ tag = 7)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
      ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
      ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
      ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
      ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 52#64 →
      sm.readReg64 .x0 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm (encChainSavedRegs sp0 s ∗ F) Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 0 48
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  have horr := encChain_tag_orr_eq htag
  apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  have hSavedEq :
      (((sp0 - 96#64) ↦₆₄ s.readReg64 (Reg.gpr 29#5)) ∗
        ((sp0 - 88#64) ↦₆₄ s.readReg64 (Reg.gpr 30#5)) ∗
        ((sp0 - 80#64) ↦₆₄ s.readReg64 (Reg.gpr 28#5)) ∗
        ((sp0 - 72#64) ↦₆₄ s.readReg64 (Reg.gpr 27#5)) ∗
        ((sp0 - 64#64) ↦₆₄ s.readReg64 (Reg.gpr 26#5)) ∗
        ((sp0 - 56#64) ↦₆₄ s.readReg64 (Reg.gpr 25#5)) ∗
        ((sp0 - 48#64) ↦₆₄ s.readReg64 (Reg.gpr 24#5)) ∗
        ((sp0 - 40#64) ↦₆₄ s.readReg64 (Reg.gpr 23#5)) ∗
        ((sp0 - 32#64) ↦₆₄ s.readReg64 (Reg.gpr 22#5)) ∗
        ((sp0 - 24#64) ↦₆₄ s.readReg64 (Reg.gpr 21#5)) ∗
        ((sp0 - 16#64) ↦₆₄ s.readReg64 (Reg.gpr 20#5)) ∗
        ((sp0 - 8#64) ↦₆₄ s.readReg64 (Reg.gpr 19#5))) ∗ F =
      encChainSavedRegs sp0 s ∗ F := rfl
  rw [hSavedEq]
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rcases htag with rfl | rfl <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

/-- Steps `+0x034..+0x038` up to `bl Chain::encoded_len`. -/
theorem step_encChain_to_chainLen (img : Obj.Image) (ext : String → Option (State → State))
    (a v : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 52#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 60#64 →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm P Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 52 56
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

/-- Steps `+0x03c..+0x040` up to `bl encode_varint`. -/
theorem step_encChain_to_lenVarint (img : Obj.Image) (ext : String → Option (State → State))
    (a v lenVal : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 60#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = lenVal)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 68#64 →
      sm.readReg64 .x0 = lenVal →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm P Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 60 64
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

/-! ### Combined Segment 0 (`+0x000 → +0x044`, offsets `0..68`) -/

theorem step_encChain_seg0 (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hchain : OkAtX img ext chainLenName (chainLenSpec A))
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 : State} {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        (vecU8At A x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A x.gc x.a ∗ A.pool ∗
          stackAt (s0.sp - 96#64) encChainSubStack ∗
          encChainSavedRegs s0.sp s0)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s0
      ((encodeChainSpecX A).pre x s0) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  dsimp only [encodeChainSpecX]
  refine SepWPpX.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen⟩ => ?_
  rw [stackAt_encodeChainStackX_split s0.sp]
  simp only [sepExists_sepConj_right]
  refine SepWPpX.exists_elim fun w96 => SepWPpX.exists_elim fun w88 =>
    SepWPpX.exists_elim fun w80 => SepWPpX.exists_elim fun w72 =>
    SepWPpX.exists_elim fun w64 => SepWPpX.exists_elim fun w56 =>
    SepWPpX.exists_elim fun w48 => SepWPpX.exists_elim fun w40 =>
    SepWPpX.exists_elim fun w32 => SepWPpX.exists_elim fun w24 =>
    SepWPpX.exists_elim fun w16 => SepWPpX.exists_elim fun w8 => ?_
  refine step_encChain_prologue img ext x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗
      A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack)
    hpc hrun rfl halign hx0 hx1 hx2 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  refine step_encChain_encodeVarint img A ext hEV
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 52#64) x.bs
    (by simp only [lenField, List.length_append] at hlen; omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by ac_rfl) ?_
  intro s2 cap0 ptr0 hpc2 hrun2 hsp2 htr2 hcs2
  refine step_encChain_to_chainLen img ext x.a x.v
    hpc2 hrun2 (by reg_chain) (by reg_chain) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  refine step_encChain_chainLen img A ext hchain s0.sp
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 60#64)
    (x := x)
    (F := vecU8At A x.v cap0 ptr0 (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      A.pool ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3 (encChainMem_len_lt hlen)
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hcs4 hx0_4
  rw [encChain_encodeKey_eq htag]
  refine step_encChain_to_lenVarint img ext x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hx0_4 (by reg_chain) (by reg_chain) ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  refine step_encChain_encodeVarint img A ext hEV
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v cap0 ptr0 s0.sp
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited)
    (by
      have := encChain_encodeKey_len htag
      simp only [lenField, List.length_append] at hlen ⊢
      omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc5 hrun5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs6
  have hGoalEq :
      ((vecU8At A x.v cap1 ptr1
        ((x.bs ++ encodeKey x.tag .lengthDelimited) ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack) ∗
        protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0) =
      (vecU8At A x.v cap1 ptr1
        (x.bs ++ encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        protoChainAt A x.gc x.a ∗ A.pool ∗
        stackAt (s0.sp - 96#64) encChainSubStack ∗
        encChainSavedRegs s0.sp s0) := by ac_rfl
  rw [hGoalEq]
  exact hnext s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 (by reg_chain) (by reg_chain) hlen

/-! ### Additional pure helpers for `bytesField` segments -/

theorem bytes_len_le_bytesField (tag : Nat) (bs : List (BitVec 8)) :
    bs.length ≤ (bytesField tag bs).length := by
  by_cases h : bs = []
  · subst h; simp [bytesField]
  · simp only [bytesField, h, ↓reduceIte, lenField, List.length_append]
    omega

theorem bv_ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1
  omega

theorem bv_len_add_slice (bs sliceBs : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 sliceBs.length =
      BitVec.ofNat 64 (bs ++ sliceBs).length := by
  simp only [List.length_append, BitVec.ofNat_add]

/-! ### Segment 1 (`+0x044 → +0x0b0`, offsets `68..176`, cold `1676..1744`): `sender_ratchet_key` -/

theorem step_encChain_seg1_tag (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 128#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 68 124
  encChain_fetches_range img.base (Rust.withPanics ext) 1676 1700
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x0a#8 hlt]
    refine step_encChain_encodeVarint img A ext hEV
      (BitVec.ofNat 64 srkBs.length) v curCap curPtr sp0 (entry + bv% (128)) (curBs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 img A ext hDR v curCap curPtr sp0 (entry + bv% (1696))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x0a#8 hnew_gt]
    refine step_encChain_encodeVarint img A ext hEV
      (BitVec.ofNat 64 srkBs.length) v newCap p' sp0 (entry + bv% (128)) (curBs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem ule_of_ult_false {x y : BitVec 64} (h : y.ult x = false) : x.ule y = true := by
  simp only [BitVec.ult, BitVec.ule, decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
  omega

theorem step_encChain_seg1_copy (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 srkBs.length)
    (hx22 : s.readReg64 .x22 = srkPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 128 172
  encChain_fetches_range img.base (Rust.withPanics ext) 1704 1744
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle2 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hsrk_le => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  by_cases hfit : bsMid.length + srkBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hfit
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy img A ext hA cap2 ptr2 srkPtr sp0 (entry + bv% (168))
      bsMid srkBs hsrk_pos hfit hsrk_lt
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpX.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A cap2 ptr2 (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs)) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < srkBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).1.mpr hrem
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice img A ext hDR v cap2 ptr2 sp0 (entry + bv% (1728))
      bsMid srkBs.length hle2 hrem hmid_lt hsrk_lt
      (x := x)
      (F := vecU8Buf A srkCap srkPtr srkBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy img A ext hA newCap p' srkPtr sp0 (entry + bv% (168))
      bsMid srkBs hsrk_pos hnew_ge hsrk_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpX.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A newCap p' (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs)) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
