/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseX
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>` Segments 0 and 1: Prologue and `sender_ratchet_key` (`+0` → `+176`)

Verifies Segment 0 (prologue, outer tag, `Chain::encoded_len`, and length varint, `+0 → +68`) and
Segment 1 (`sender_ratchet_key`, `+68 → +176`, cold `1676..1744`) of
`prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`, Block `12`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg96

theorem L1_EncodeChainPrologueXA : True := trivial

/-! ### Callee helper for `Chain::encoded_len` (`entry + 140784#64`) -/

theorem step_encChain_chainLen_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hchain : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainLenName)
      (chainLenSpec A))
    (sp0 ret_pc : BitVec 64)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = x.a)
    (hlen : (encChainMem x.gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [chainLen_fnAddr_eq_x] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpIn.call (x := ChainLenGhost.mk x.a x.gc)
    (F := encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F)
    hchain hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_chainLenX (sp0 - 96#64)] at hm
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
    refine SepWPpIn.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    have hGoalEq :
        (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F) =
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_chainLenX (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

/-! ### Segment 0 basic-block helpers (`+0x000..+0x040`) -/

/-- Prologue, key setup, and `bl encode_varint` (`+0x000..+0x030`). -/
theorem step_encChain_prologue_x (ext : String → Option (State → State)) {img : Obj.Image}
    (tag : Nat) (a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (htag : tag = 6 ∨ tag = 7)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName)
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
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr encodeChainName + 52#64 →
      sm.readReg64 .x0 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm (encChainSavedRegs sp0 s ∗ F) Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 0 48
  generalize_entry (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  have horr := encChain_tag_orr_eq htag
  apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
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

theorem step_encChain_to_chainLen_x (ext : String → Option (State → State)) {img : Obj.Image}
    (a v : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 52#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr encodeChainName + 60#64 →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm P Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 52 56
  generalize_entry (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
  wp_step
  wp_step
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_to_lenVarint_x (ext : String → Option (State → State)) {img : Obj.Image}
    (a v lenVal : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 60#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = lenVal)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr encodeChainName + 68#64 →
      sm.readReg64 .x0 = lenVal →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm P Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 60 64
  generalize_entry (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
  wp_step
  wp_step
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

/-! ### Combined Segment 0 (`+0x000 → +0x044`, offsets `0..68`) -/

theorem step_encChain_seg0_x (A : RustAlloc) (ext : String → Option (State → State)) {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (hchain : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainLenName)
      (chainLenSpec A))
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 : State} {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr encodeChainName)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        (vecU8At A x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A x.gc x.a ∗ A.pool ∗
          stackAt (s0.sp - 96#64) encChainSubStackX ∗
          encChainSavedRegs s0.sp s0)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s0
      ((encodeChainSpecX A).pre x s0) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  dsimp only [encodeChainSpecX]
  refine SepWPpIn.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen⟩ => ?_
  rw [stackAt_encodeChainStackX_split s0.sp]
  simp only [sepExists_sepConj_right]
  refine SepWPpIn.exists_elim fun w96 => SepWPpIn.exists_elim fun w88 =>
    SepWPpIn.exists_elim fun w80 => SepWPpIn.exists_elim fun w72 =>
    SepWPpIn.exists_elim fun w64 => SepWPpIn.exists_elim fun w56 =>
    SepWPpIn.exists_elim fun w48 => SepWPpIn.exists_elim fun w40 =>
    SepWPpIn.exists_elim fun w32 => SepWPpIn.exists_elim fun w24 =>
    SepWPpIn.exists_elim fun w16 => SepWPpIn.exists_elim fun w8 => ?_
  refine step_encChain_prologue_x ext x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗
      A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStackX)
    hpc hrun rfl halign hx0 hx1 hx2 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  refine step_encChain_encodeVarint_x A ext hEV
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((SP2Ext img.base ext).fnAddr encodeChainName + 52#64) x.bs
    (by simp only [lenField, List.length_append] at hlen; omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by ac_rfl) ?_
  intro s2 cap0 ptr0 hpc2 hrun2 hsp2 htr2 hcs2
  have hx19_2 : s2.readReg64 .x19 = x.v := hcs2.1.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = x.a := hcs2.2.1.trans hx20_1
  refine step_encChain_to_chainLen_x ext x.a x.v
    hpc2 hrun2 hx19_2 hx20_2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  refine step_encChain_chainLen_x A ext hchain s0.sp
    ((SP2Ext img.base ext).fnAddr encodeChainName + 60#64)
    (x := x)
    (F := vecU8At A x.v cap0 ptr0 (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      A.pool ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3 (encChainMem_len_lt hlen)
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hcs4 hx0_4
  have hx19_4 : s4.readReg64 .x19 = x.v := hcs4.1.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = x.a := hcs4.2.1.trans hx20_3
  rw [encChain_encodeKey_eq htag]
  refine step_encChain_to_lenVarint_x ext x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hx0_4 hx19_4 hx20_4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  refine step_encChain_encodeVarint_x A ext hEV
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v cap0 ptr0 s0.sp
    ((SP2Ext img.base ext).fnAddr encodeChainName + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited)
    (by
      have := encChain_encodeKey_len htag
      simp only [lenField, List.length_append] at hlen ⊢
      omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc5 hrun5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs6
  have hx19_6 : s6.readReg64 .x19 = x.v := hcs6.1.trans hx19_5
  have hx20_6 : s6.readReg64 .x20 = x.a := hcs6.2.1.trans hx20_5
  have hGoalEq :
      ((vecU8At A x.v cap1 ptr1
        ((x.bs ++ encodeKey x.tag .lengthDelimited) ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStackX) ∗
        protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0) =
      (vecU8At A x.v cap1 ptr1
        (x.bs ++ encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        protoChainAt A x.gc x.a ∗ A.pool ∗
        stackAt (s0.sp - 96#64) encChainSubStackX ∗
        encChainSavedRegs s0.sp s0) := by ac_rfl
  rw [hGoalEq]
  exact hnext s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hlen

/-! ### Segment 1 (`+0x044 → +0x0b0`, offsets `68..176`, cold `1676..1744`): `sender_ratchet_key` -/

theorem sepWPpIn_extract_vecU8Buf_bounds_prost {img : Obj.Image} {A : RustAlloc} {cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hP : P = Prost.vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym R hm hL
  have hhm : s.mem ⊨ Prost.vecU8Buf A cap ptr bs ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  obtain ⟨h1, h2, h3⟩ := Prost.vecU8Buf_bounds hhm
  exact h h1 h2 h3 hF hsym R hm hL

theorem step_encChain_seg1_tag_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 128#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 68 124
  encChain_fetches_range img.base (Rust.withPanics ext) 1676 1700
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by ac_rfl) fun hle _ _ => ?_
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x0a#8 hlt]
    refine step_encChain_encodeVarint_x A ext hEV
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
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_x A ext hDR v curCap curPtr sp0 (entry + bv% (1696))
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
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x0a#8 hnew_gt]
    refine step_encChain_encodeVarint_x A ext hEV
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
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg1_copy_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hC : SerContractsX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 128#64)
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
      Prost.vecU8Buf A cap2 ptr2 bsMid ∗
      Prost.vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ srkBs) ∗
          Prost.vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 128 172
  encChain_fetches_range img.base (Rust.withPanics ext) 1704 1744
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by ac_rfl) fun hle2 _ _ => ?_
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by ac_rfl) fun hsrk_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  by_cases hfit : bsMid.length + srkBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hfit
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy_x A ext hC cap2 ptr2 srkPtr sp0 (entry + bv% (168))
      bsMid srkBs hsrk_pos hfit (by omega)
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ F)
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
    apply SepWPpIn.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((Prost.vecU8Buf A cap2 ptr2 (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ srkBs) ∗
          Prost.vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < srkBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).1.mpr hrem
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice_x A ext hDR v cap2 ptr2 sp0 (entry + bv% (1728))
      bsMid srkBs.length hle2 hrem (by omega) (by omega)
      (x := x)
      (F := Prost.vecU8Buf A srkCap srkPtr srkBs ∗ F)
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
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy_x A ext hC newCap p' srkPtr sp0 (entry + bv% (168))
      bsMid srkBs hsrk_pos hnew_ge (by omega)
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ F)
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
    apply SepWPpIn.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((Prost.vecU8Buf A newCap p' (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ srkBs) ∗
          Prost.vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

/-- Combined Segment 1 (`+0x044 → +0x0b0`, offsets `68..176`): appends `bytesField 1 srk.bytes`. -/
theorem step_encChain_seg1_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hC : SerContractsX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A srk a ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : srk.bytes = []
  · encChain_fetches_range img.base (Rust.withPanics ext) 68 72
    generalize_entry (SP2Ext img.base ext).fnAddr encodeChainName = entry
    examples_hide_fetches
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length + srk.bytes.length =
        (bytesField 1 srk.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag_x A ext hEV hDR
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes
      hsrk_pos (by omega) (by omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ Prost.vecU8Buf A srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy_x A ext hC hDR
      v a cap2 ptr2 srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      hsrk_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes) ∗
          Prost.vecU8Buf A srk.cap srk.ptr srk.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗
          (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `12`, Segments 0 and 1) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_encChain_chainLen_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (sp0 ret_pc : BitVec 64)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 88)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = x.a)
    (hlen : (encChainMem x.gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hchain' : subroutine_ok (lsProg_12 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hchain
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpLsCl.call_withLsCodeLoaded (x := ChainLenGhost.mk x.a x.gc)
    (F := encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F)
    hchain' hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_chainLenX (sp0 - 96#64)] at hm
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
    refine SepWPpLsCl.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    have hGoalEq :
        (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F) =
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_chainLenX (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

theorem step_encChain_prologue_placed_x [LibsignalPlacement]
    (H : LibsignalHooks)
    (tag : Nat) (a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (htag : tag = 6 ∨ tag = 7)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base)
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
      sm.pc = lsmpl.base 10 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 52#64 →
      sm.readReg64 .x0 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm (encChainSavedRegs sp0 s ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_prologue_placed H tag a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8
    htag hpc hrun hcl hsp halign hx0 hx1 hx2 hP
    fun sm hpcm hrunm hclm hspm htrm hlrm hx0m hx1m hx19m hx20m =>
      hnext sm hpcm hrunm hspm htrm hlrm hx0m hx1m hx19m hx20m hclm

theorem step_encChain_to_chainLen_placed_x [LibsignalPlacement]
    (H : LibsignalHooks) (a v : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 52#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 88 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 60#64 →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_to_chainLen_placed H a v hpc hrun hcl hx19 hx20
    fun sm hpcm hrunm hclm hspm htrm hlrm hx0m hx19m hx20m =>
      hnext sm hpcm hrunm hspm htrm hlrm hx0m hx19m hx20m hclm

theorem step_encChain_to_lenVarint_placed_x [LibsignalPlacement]
    (H : LibsignalHooks) (a v lenVal : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 60#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = lenVal)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 10 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 68#64 →
      sm.readReg64 .x0 = lenVal →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp :=
  fun hcl => step_encChain_to_lenVarint_placed H a v lenVal hpc hrun hcl hx0 hx19 hx20
    fun sm hpcm hrunm hclm hspm htrm hlrm hx0m hx1m hx19m hx20m =>
      hnext sm hpcm hrunm hspm htrm hlrm hx0m hx1m hx19m hx20m hclm

theorem step_encChain_seg0_placed_x [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base (withLsCodeLoaded lsmpl (chainLenSpec A)))
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 : State} {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_12).base)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_12).base + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        (vecU8At A x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A x.gc x.a ∗ A.pool ∗
          stackAt (s0.sp - 96#64) encChainSubStackX ∗
          encChainSavedRegs s0.sp s0)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s0
      ((encodeChainSpecX A).pre x s0) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  dsimp only [encodeChainSpecX]
  refine SepWPpLsCl.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen⟩ => ?_
  rw [stackAt_encodeChainStackX_split s0.sp]
  simp only [sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun w96 => SepWPpLsCl.exists_elim fun w88 =>
    SepWPpLsCl.exists_elim fun w80 => SepWPpLsCl.exists_elim fun w72 =>
    SepWPpLsCl.exists_elim fun w64 => SepWPpLsCl.exists_elim fun w56 =>
    SepWPpLsCl.exists_elim fun w48 => SepWPpLsCl.exists_elim fun w40 =>
    SepWPpLsCl.exists_elim fun w32 => SepWPpLsCl.exists_elim fun w24 =>
    SepWPpLsCl.exists_elim fun w16 => SepWPpLsCl.exists_elim fun w8 => ?_
  refine step_encChain_prologue_placed_x H x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗
      A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStackX)
    hpc hrun rfl halign hx0 hx1 hx2 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  refine step_encChain_encodeVarint_placed_x A H hEV
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((blkPl_12).base + 52#64) x.bs
    (by simp only [lenField, List.length_append] at hlen; omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by ac_rfl) ?_
  intro s2 cap0 ptr0 hpc2 hrun2 hsp2 htr2 hcs2
  have hx19_2 : s2.readReg64 .x19 = x.v := hcs2.1.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = x.a := hcs2.2.1.trans hx20_1
  refine step_encChain_to_chainLen_placed_x H x.a x.v
    hpc2 hrun2 hx19_2 hx20_2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  refine step_encChain_chainLen_placed_x A H hchain s0.sp
    ((blkPl_12).base + 60#64)
    (x := x)
    (F := vecU8At A x.v cap0 ptr0 (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      A.pool ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3 (encChainMem_len_lt hlen)
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hcs4 hx0_4
  have hx19_4 : s4.readReg64 .x19 = x.v := hcs4.1.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = x.a := hcs4.2.1.trans hx20_3
  rw [encChain_encodeKey_eq htag]
  refine step_encChain_to_lenVarint_placed_x H x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hx0_4 hx19_4 hx20_4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  refine step_encChain_encodeVarint_placed_x A H hEV
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v cap0 ptr0 s0.sp
    ((blkPl_12).base + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited)
    (by
      have := encChain_encodeKey_len htag
      simp only [lenField, List.length_append] at hlen ⊢
      omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc5 hrun5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs6
  have hx19_6 : s6.readReg64 .x19 = x.v := hcs6.1.trans hx19_5
  have hx20_6 : s6.readReg64 .x20 = x.a := hcs6.2.1.trans hx20_5
  have hGoalEq :
      ((vecU8At A x.v cap1 ptr1
        ((x.bs ++ encodeKey x.tag .lengthDelimited) ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStackX) ∗
        protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0) =
      (vecU8At A x.v cap1 ptr1
        (x.bs ++ encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        protoChainAt A x.gc x.a ∗ A.pool ∗
        stackAt (s0.sp - 96#64) encChainSubStackX ∗
        encChainSavedRegs s0.sp s0) := by ac_rfl
  rw [hGoalEq]
  exact hnext s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hlen

theorem step_encChain_seg1_tag_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_12).base + 128#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by ac_rfl) fun hle _ _ => ?_
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x0a#8 hlt]
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 srkBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (128)) (curBs ++ [0x0a#8])
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
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_placed_x A H hDR v curCap curPtr sp0 ((blkPl_12).base + bv% (1696))
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
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x0a#8 hnew_gt]
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 srkBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (128)) (curBs ++ [0x0a#8])
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
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg1_copy_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hDR : DoReservePlacedOkX A H)
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 128#64)
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
      Prost.vecU8Buf A cap2 ptr2 bsMid ∗
      Prost.vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ srkBs) ∗
          Prost.vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by ac_rfl) fun hle2 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by ac_rfl) fun hsrk_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  by_cases hfit : bsMid.length + srkBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hfit
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy_placed_x A H hC cap2 ptr2 srkPtr sp0 ((blkPl_12).base + bv% (168))
      bsMid srkBs hsrk_pos hfit (by omega)
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ F)
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
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((Prost.vecU8Buf A cap2 ptr2 (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ srkBs) ∗
          Prost.vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < srkBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).1.mpr hrem
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice_placed_x A H hDR v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1728))
      bsMid srkBs.length hle2 hrem (by omega) (by omega)
      (x := x)
      (F := Prost.vecU8Buf A srkCap srkPtr srkBs ∗ F)
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
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy_placed_x A H hC newCap p' srkPtr sp0 ((blkPl_12).base + bv% (168))
      bsMid srkBs hsrk_pos hnew_ge (by omega)
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ F)
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
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((Prost.vecU8Buf A newCap p' (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ srkBs) ∗
          Prost.vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg1_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A srk a ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : srk.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length + srk.bytes.length =
        (bytesField 1 srk.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag_placed_x A H hEV hDR
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes
      hsrk_pos (by omega) (by omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ Prost.vecU8Buf A srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy_placed_x A H hC hDR
      v a cap2 ptr2 srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      hsrk_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes) ∗
          Prost.vecU8Buf A srk.cap srk.ptr srk.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗
          (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2

end Placed

end CryptoVerification.E2E.Record.Serialization
