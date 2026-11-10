/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBody
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXA
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>` `MessageKey` Loop Body (`+680` → `+668`)

Verifies one iteration of the `message_keys` encoding loop (`+680` → `+668`) inside
`prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`, Block `12`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open EncodeVarintNorm
open Proofs.libsignal.Hooks2
open scoped BigOperators

set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_EncodeChainMessageKeyLoopBody : True := trivial

theorem sepWPpIn_extract_messageKey_seed_ne_nil_x {img : Obj.Image} {prog : Program} {A : RustAlloc}
    {gk : MessageKeyGhost × MessageKeyGenerator} {cur : BitVec 64}
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = messageKeyAt A gk cur ∗ F)
    (h : gk.2.seed ≠ [] → SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s P Q Qp := fun hF hsym =>
  sepWPp_extract_messageKey_seed_ne_nil hP fun hne => h hne hF hsym

/-! ### Callee wrapper for `MessageKey::encoded_len` (`0x2d6bc`) -/

theorem step_encChain_msgKeyLen_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hmk : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr msgKeyLenName)
      (msgKeyLenSpec A))
    (cur sp0 ret_pc : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = cur)
    (hP : P = (messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey gk.2).length →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [msgKeyLen_fnAddr_eq_encChain_x] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpIn.call (x := MsgKeyLenGhost.mk cur gk)
    (F := encChainSubRestX (sp0 - 96#64) msgKeyLenStack ∗ F)
    hmk hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_msgKeyLenX (sp0 - 96#64)] at hm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [msgKeyLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc]
    refine SepWPpIn.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPpIn.congr_pre ?_ (hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m)
    rw [stackAt_sub_to_msgKeyLenX (sp0 - 96#64)]
    ac_rfl

/-! ### Tag `0x22#8`, `MessageKey::encoded_len`, and length varint (`+680 → +728`, cold `1244..1272`) -/

theorem step_encChain_mk_tag_len_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hmk : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr msgKeyLenName)
      (msgKeyLenSpec A))
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v cur endPtr curCap curPtr sp0 : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    (curBs : List (BitVec 8))
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 728#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap1 ptr1
          ((curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 680 728
  encChain_fetches_range img.base (Rust.withPanics ext) 1244 1272
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hcur_snoc_lt : (curBs ++ [0x22#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x22#8 hlt]
    refine step_encChain_msgKeyLen_x A ext hmk cur sp0 (entry + bv% (720)) gk
      (x := x)
      (F := vecU8At A v curCap curPtr (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_x A ext hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v curCap curPtr sp0 (entry + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine SepWPpIn.congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hregs2)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_x A ext hDR v curCap curPtr sp0 (entry + bv% (1264))
      curBs hcap_eq (by omega)
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x22#8 hnew_gt]
    refine step_encChain_msgKeyLen_x A ext hmk cur sp0 (entry + bv% (720)) gk
      (x := x)
      (F := vecU8At A v newCap p' (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_x A ext hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v newCap p' sp0 (entry + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine SepWPpIn.congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hregs2)

/-! ### `uint32Field 1 gk.2.counter` encoding (`+728 → +776`, cold `1272..1308`) -/

theorem step_encChain_mk_counter_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v cur endPtr cap1 ptr1 sp0 : BitVec 64) (cnt : BitVec 32) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      ((cur + 96#64) ↦₃₂ cnt) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 776#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ uint32Field 1 cnt) ∗
          ((cur + 96#64) ↦₃₂ cnt) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 728 776
  encChain_fetches_range img.base (Rust.withPanics ext) 1272 1308
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  by_cases hcnt : cnt = 0#32
  · have hcnt_beq : (cnt == 0#32) = true := by simp [hcnt]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (776))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hu0 : bs1 ++ uint32Field 1 cnt = bs1 := by simp [hcnt, uint32Field1_zero_eq]
    rw [← hu0]
    exact hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩
  · have hcnt_beq : (cnt == 0#32) = false := beq_eq_false_iff_ne.mpr hcnt
    have hu_eq : (bs1 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 cnt) =
        bs1 ++ uint32Field 1 cnt := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hcnt]
    have hcur_snoc_lt : (bs1 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A v cap1 ptr1 bs1]
    refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := (v ↦₆₄ cap1) ∗ ((v + 8#64) ↦₆₄ ptr1) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        ((cur + 96#64) ↦₃₂ cnt) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by ac_rfl) fun hle _ _ => ?_
    by_cases hlt : bs1.length < cap1.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A cap1 ptr1 bs1 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpIn.exists_elim fun y => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A cap1 ptr1 bs1 0x08#8 hlt]
      refine step_encChain_encodeVarint_x A ext hEV
        (BitVec.zeroExtend 64 cnt) v cap1 ptr1 sp0 (entry + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine SepWPpIn.congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hregsm)
    · have hcap_eq : cap1.toNat = bs1.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine step_encChain_reserve1_x A ext hDR v cap1 ptr1 sp0 (entry + bv% (1296))
        bs1 hcap_eq (by omega)
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
      have hregsr : MkLoopRegs sr v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
      have hx19r : sr.readReg64 .x19 = v := hregsr.1
      have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
      have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
      have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
      have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
      have hx21r : sr.readReg64 .x21 = BitVec.zeroExtend 64 cnt :=
        hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A newCap p' bs1 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpIn.exists_elim fun y => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A newCap p' bs1 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint_x A ext hEV
        (BitVec.zeroExtend 64 cnt) v newCap p' sp0 (entry + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine SepWPpIn.congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hregsm)

/-! ### Empty fields `2..4` skip and seed tag `0x2a#8` + varint (`+776 → +1148`, cold `1620..1648`) -/

theorem step_encChain_mk_seed_tag_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v cur endPtr cap2 ptr2 seedPtr sp0 : BitVec 64) (bs2 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hbs2_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 776#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 1148#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length →
      sm.readReg64 .x22 = seedPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap3 ptr3
          ((bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 seedBs.length)) ∗
          ((cur + 16#64) ↦₆₄ 0#64) ∗
          ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗
          ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 776 784
  encChain_fetches_range img.base (Rust.withPanics ext) 880 888
  encChain_fetches_range img.base (Rust.withPanics ext) 984 992
  encChain_fetches_range img.base (Rust.withPanics ext) 1088 1148
  encChain_fetches_range img.base (Rust.withPanics ext) 1620 1648
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hseed_nz := bv_len_beq_zero_false hseed_pos hseed_lt
  have hbs2_snoc_lt : (bs2 ++ [0x2a#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hbs2_lt
  rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2]
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  by_cases hlt : bs2.length < cap2.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x2a#8 hlt]
    refine step_encChain_encodeVarint_x A ext hEV
      (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 sp0 (entry + bv% (1148)) (bs2 ++ [0x2a#8])
      hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine SepWPpIn.congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hregsm hx21m hx22m)
  · have hcap_eq : cap2.toNat = bs2.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_x A ext hDR v cap2 ptr2 sp0 (entry + bv% (1640))
      bs2 hcap_eq (by omega)
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A newCap p' bs2 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' bs2 0x2a#8 hnew_gt]
    refine step_encChain_encodeVarint_x A ext hEV
      (BitVec.ofNat 64 seedBs.length) v newCap p' sp0 (entry + bv% (1148)) (bs2 ++ [0x2a#8])
      hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine SepWPpIn.congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hregsm hx21m hx22m)

/-! ### Seed reserve and `memcpy` (`+1148 → +668`, cold `1168..1208`) -/

theorem step_encChain_mk_seed_copy_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hC : SerContractsX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v cur endPtr cap3 ptr3 seedCap seedPtr sp0 : BitVec 64)
    (bs3 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hsum_lt : bs3.length + seedBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 1148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 seedBs.length)
    (hx22 : s.readReg64 .x22 = seedPtr)
    (hP : P = (vecU8At A v cap3 ptr3 bs3 ∗
      Prost.vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap4 ptr4 (bs3 ++ seedBs) ∗
          Prost.vecU8Buf A seedCap seedPtr seedBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 1148 1212
  encChain_fetches_range img.base (Rust.withPanics ext) 640 668
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hbs3_lt : bs3.length < 2 ^ 32 := by omega
  have hlen_add := bv_len_add_slice bs3 seedBs
  rw [vecU8At_eq_cells_buf A v cap3 ptr3 bs3]
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      Prost.vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := seedCap) (ptr := seedPtr) (bs := seedBs)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      Prost.vecU8Buf A cap3 ptr3 bs3 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hseed_le _ _ => ?_
  by_cases hfit : bs3.length + seedBs.length ≤ cap3.toNat
  · have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = false :=
      (spare_ult_iff hle hbs3_lt hseed_lt).2.mpr hfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = true :=
      ule_of_ult_false hult
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy_x A ext hC cap3 ptr3 seedPtr sp0 (entry + bv% (660))
      bs3 seedBs hseed_pos hfit hseed_lt
      (x := x)
      (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpIn.of_sepWP (mid := entry + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.congr_pre ?_
      (hnext _ cap3 ptr3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl
  · have hnfit : cap3.toNat - bs3.length < seedBs.length := by omega
    have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = true :=
      (spare_ult_iff hle hbs3_lt hseed_lt).1.mpr hnfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = false :=
      ule_false_of_ult_true hult
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice_x A ext hDR v cap3 ptr3 sp0 (entry + bv% (1192))
      bs3 seedBs.length hle hnfit hbs3_lt hseed_lt
      (x := x) (F := Prost.vecU8Buf A seedCap seedPtr seedBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_fit hult_false
    have hule_true := ule_of_ult_false hult_false
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy_x A ext hC newCap p' seedPtr sp0 (entry + bv% (660))
      bs3 seedBs hseed_pos hnew_fit hseed_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregsr.1], by simp only [arm64_norm, hregsr.2.1],
         by simp only [arm64_norm, hregsr.2.2.1], by simp only [arm64_norm, hregsr.2.2.2.1],
         by simp only [arm64_norm, hregsr.2.2.2.2]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpIn.of_sepWP (mid := entry + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl

/-! ### Combined per-element `MessageKey` loop body (`+680 → +668`) -/

theorem step_encChain_mk_elem_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hC : SerContractsX img A ext)
    (hmk : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr msgKeyLenName)
      (msgKeyLenSpec A))
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (curBs : List (BitVec 8))
    (hbound : curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v capOut ptrOut (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPpIn_extract_messageKey_seed_ne_nil_x (A := A) (gk := gk) (cur := cur)
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hseed => ?_
  have hseed_pos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hseed
  have hparts := lenField4_encMessageKey_len_parts gk.2 hseed
  have hcur_lt : curBs.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_tag_len_x A ext hmk hEV hDR
    v cur endPtr curCap curPtr sp0 gk curBs hcur_lt
    (x := x) (F := F) hpc hrun hsp halign htr hregs
    (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hregs1
  set bs1 := (curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hbs1_len : bs1.length =
      curBs.length + 1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length := by
    simp only [bs1, List.length_append, List.length_singleton]
  have hbs1_lt : bs1.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_counter_x A ext hEV hDR
    v cur endPtr cap1 ptr1 sp0 gk.2.counter bs1 hbs1_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      Prost.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc1 hrun1 hsp1 halign htr1 hregs1
    (by rw [messageKeyAt_eq_cells A gk cur]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hregs2
  set bs2 := bs1 ++ uint32Field 1 gk.2.counter
  have hbs2_len : bs2.length = bs1.length + (uint32Field 1 gk.2.counter).length := by
    simp only [bs2, List.length_append]
  have hbs2_lt : bs2.length + 1 < 2 ^ 32 := by omega
  have hseed_lt : gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_tag_x A ext hEV hDR
    v cur endPtr cap2 ptr2 gk.1.seed.ptr sp0 bs2 gk.2.seed hseed_pos hseed_lt hbs2_lt
    (x := x)
    (F := ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      Prost.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc2 hrun2 hsp2 halign htr2 hregs2 (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hregs3 hx21_3 hx22_3
  set bs3 := (bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 gk.2.seed.length)
  have hbs3_len : bs3.length =
      bs2.length + 1 + (encodeVarint (BitVec.ofNat 64 gk.2.seed.length)).length := by
    simp only [bs3, List.length_append, List.length_singleton]
  have hsum_lt : bs3.length + gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_copy_x A ext hC hDR
    v cur endPtr cap3 ptr3 gk.1.seed.cap gk.1.seed.ptr sp0 bs3 gk.2.seed
    hseed_pos hseed_lt hsum_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A gk cur ∗ F)
    hpc3 hrun3 hsp3 halign htr3 hregs3 hx21_3 hx22_3 (by ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hregs4
  have hbs4_eq : bs3 ++ gk.2.seed = curBs ++ lenField 4 (encMessageKey gk.2) := by
    rw [← lenField4_encMessageKey_eq gk.2 hseed]
    simp [bs3, bs2, bs1, List.append_assoc]
  refine SepWPpIn.congr_pre ?_ (hnext s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hregs4)
  rw [hbs4_eq, messageKeyAt_eq_cells A gk cur]
  ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `12`, `MessageKey` loop body) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

theorem sepWPpLsCl_extract_messageKey_seed_ne_nil_x {pl : Obj.MultiPlacement} {prog : Program}
    {A : RustAlloc} {gk : MessageKeyGhost × MessageKeyGenerator} {cur : BitVec 64}
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = messageKeyAt A gk cur ∗ F)
    (h : gk.2.seed ≠ [] → SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  fun hcl => sepWPp_extract_messageKey_seed_ne_nil hP fun hne => h hne hcl

theorem step_encChain_msgKeyLen_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (cur sp0 ret_pc : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 118)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = cur)
    (hP : P = (messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey gk.2).length →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hmk' : subroutine_ok (lsProg_12 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hmk
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpLsCl.call_withLsCodeLoaded (x := MsgKeyLenGhost.mk cur gk)
    (F := encChainSubRestX (sp0 - 96#64) msgKeyLenStack ∗ F)
    hmk' hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_msgKeyLenX (sp0 - 96#64)] at hm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [msgKeyLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPpLsCl.congr_pre ?_ (hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m)
    rw [stackAt_sub_to_msgKeyLenX (sp0 - 96#64)]
    ac_rfl

theorem step_encChain_mk_tag_len_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v cur endPtr curCap curPtr sp0 : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    (curBs : List (BitVec 8))
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_12).base + 728#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap1 ptr1
          ((curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hcur_snoc_lt : (curBs ++ [0x22#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 118)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x22#8 hlt]
    refine step_encChain_msgKeyLen_placed_x A H hmk cur sp0 ((blkPl_12).base + bv% (720)) gk
      (x := x)
      (F := vecU8At A v curCap curPtr (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v curCap curPtr sp0 ((blkPl_12).base + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine SepWPpLsCl.congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hregs2)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_placed_x A H hDR v curCap curPtr sp0 ((blkPl_12).base + bv% (1264))
      curBs hcap_eq (by omega)
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 118)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x22#8 hnew_gt]
    refine step_encChain_msgKeyLen_placed_x A H hmk cur sp0 ((blkPl_12).base + bv% (720)) gk
      (x := x)
      (F := vecU8At A v newCap p' (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v newCap p' sp0 ((blkPl_12).base + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine SepWPpLsCl.congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hregs2)

theorem step_encChain_mk_counter_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v cur endPtr cap1 ptr1 sp0 : BitVec 64) (cnt : BitVec 32) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      ((cur + 96#64) ↦₃₂ cnt) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_12).base + 776#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ uint32Field 1 cnt) ∗
          ((cur + 96#64) ↦₃₂ cnt) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  by_cases hcnt : cnt = 0#32
  · have hcnt_beq : (cnt == 0#32) = true := by simp [hcnt]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (776))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hu0 : bs1 ++ uint32Field 1 cnt = bs1 := by simp [hcnt, uint32Field1_zero_eq]
    rw [← hu0]
    exact hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩
  · have hcnt_beq : (cnt == 0#32) = false := beq_eq_false_iff_ne.mpr hcnt
    have hu_eq : (bs1 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 cnt) =
        bs1 ++ uint32Field 1 cnt := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hcnt]
    have hcur_snoc_lt : (bs1 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A v cap1 ptr1 bs1]
    refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := (v ↦₆₄ cap1) ∗ ((v + 8#64) ↦₆₄ ptr1) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        ((cur + 96#64) ↦₃₂ cnt) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by ac_rfl) fun hle _ _ => ?_
    by_cases hlt : bs1.length < cap1.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A cap1 ptr1 bs1 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpLsCl.exists_elim fun y => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A cap1 ptr1 bs1 0x08#8 hlt]
      refine step_encChain_encodeVarint_placed_x A H hEV
        (BitVec.zeroExtend 64 cnt) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine SepWPpLsCl.congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hregsm)
    · have hcap_eq : cap1.toNat = bs1.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine step_encChain_reserve1_placed_x A H hDR v cap1 ptr1 sp0 ((blkPl_12).base + bv% (1296))
        bs1 hcap_eq (by omega)
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
      have hregsr : MkLoopRegs sr v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
      have hx19r : sr.readReg64 .x19 = v := hregsr.1
      have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
      have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
      have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
      have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
      have hx21r : sr.readReg64 .x21 = BitVec.zeroExtend 64 cnt :=
        hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A newCap p' bs1 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpLsCl.exists_elim fun y => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A newCap p' bs1 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint_placed_x A H hEV
        (BitVec.zeroExtend 64 cnt) v newCap p' sp0 ((blkPl_12).base + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine SepWPpLsCl.congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hregsm)

theorem step_encChain_mk_seed_tag_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v cur endPtr cap2 ptr2 seedPtr sp0 : BitVec 64) (bs2 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hbs2_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 776#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_12).base + 1148#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length →
      sm.readReg64 .x22 = seedPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3
          ((bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 seedBs.length)) ∗
          ((cur + 16#64) ↦₆₄ 0#64) ∗
          ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗
          ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hseed_nz := bv_len_beq_zero_false hseed_pos hseed_lt
  have hbs2_snoc_lt : (bs2 ++ [0x2a#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hbs2_lt
  rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2]
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  by_cases hlt : bs2.length < cap2.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x2a#8 hlt]
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1148)) (bs2 ++ [0x2a#8])
      hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine SepWPpLsCl.congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hregsm hx21m hx22m)
  · have hcap_eq : cap2.toNat = bs2.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_placed_x A H hDR v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1640))
      bs2 hcap_eq (by omega)
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A newCap p' bs2 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' bs2 0x2a#8 hnew_gt]
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 seedBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (1148)) (bs2 ++ [0x2a#8])
      hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine SepWPpLsCl.congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hregsm hx21m hx22m)

theorem step_encChain_mk_seed_copy_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hDR : DoReservePlacedOkX A H)
    (v cur endPtr cap3 ptr3 seedCap seedPtr sp0 : BitVec 64)
    (bs3 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hsum_lt : bs3.length + seedBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 1148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 seedBs.length)
    (hx22 : s.readReg64 .x22 = seedPtr)
    (hP : P = (vecU8At A v cap3 ptr3 bs3 ∗
      Prost.vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap4 ptr4 (bs3 ++ seedBs) ∗
          Prost.vecU8Buf A seedCap seedPtr seedBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hbs3_lt : bs3.length < 2 ^ 32 := by omega
  have hlen_add := bv_len_add_slice bs3 seedBs
  rw [vecU8At_eq_cells_buf A v cap3 ptr3 bs3]
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      Prost.vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := seedCap) (ptr := seedPtr) (bs := seedBs)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      Prost.vecU8Buf A cap3 ptr3 bs3 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hseed_le _ _ => ?_
  by_cases hfit : bs3.length + seedBs.length ≤ cap3.toNat
  · have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = false :=
      (spare_ult_iff hle hbs3_lt hseed_lt).2.mpr hfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = true :=
      ule_of_ult_false hult
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy_placed_x A H hC cap3 ptr3 seedPtr sp0 ((blkPl_12).base + bv% (660))
      bs3 seedBs hseed_pos hfit hseed_lt
      (x := x)
      (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ cap3 ptr3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl
  · have hnfit : cap3.toNat - bs3.length < seedBs.length := by omega
    have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = true :=
      (spare_ult_iff hle hbs3_lt hseed_lt).1.mpr hnfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = false :=
      ule_false_of_ult_true hult
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice_placed_x A H hDR v cap3 ptr3 sp0 ((blkPl_12).base + bv% (1192))
      bs3 seedBs.length hle hnfit hbs3_lt hseed_lt
      (x := x) (F := Prost.vecU8Buf A seedCap seedPtr seedBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_fit hult_false
    have hule_true := ule_of_ult_false hult_false
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy_placed_x A H hC newCap p' seedPtr sp0 ((blkPl_12).base + bv% (660))
      bs3 seedBs hseed_pos hnew_fit hseed_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregsr.1], by simp only [arm64_norm, hregsr.2.1],
         by simp only [arm64_norm, hregsr.2.2.1], by simp only [arm64_norm, hregsr.2.2.2.1],
         by simp only [arm64_norm, hregsr.2.2.2.2]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl

theorem step_encChain_mk_elem_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (curBs : List (BitVec 8))
    (hbound : curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64),
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v capOut ptrOut (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPpLsCl_extract_messageKey_seed_ne_nil_x (A := A) (gk := gk) (cur := cur)
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hseed => ?_
  have hseed_pos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hseed
  have hparts := lenField4_encMessageKey_len_parts gk.2 hseed
  have hcur_lt : curBs.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_tag_len_placed_x A H hmk hEV hDR
    v cur endPtr curCap curPtr sp0 gk curBs hcur_lt
    (x := x) (F := F) hpc hrun hsp halign htr hregs
    (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hregs1
  set bs1 := (curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hbs1_len : bs1.length =
      curBs.length + 1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length := by
    simp only [bs1, List.length_append, List.length_singleton]
  have hbs1_lt : bs1.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_counter_placed_x A H hEV hDR
    v cur endPtr cap1 ptr1 sp0 gk.2.counter bs1 hbs1_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      Prost.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc1 hrun1 hsp1 halign htr1 hregs1
    (by rw [messageKeyAt_eq_cells A gk cur]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hregs2
  set bs2 := bs1 ++ uint32Field 1 gk.2.counter
  have hbs2_len : bs2.length = bs1.length + (uint32Field 1 gk.2.counter).length := by
    simp only [bs2, List.length_append]
  have hbs2_lt : bs2.length + 1 < 2 ^ 32 := by omega
  have hseed_lt : gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_tag_placed_x A H hEV hDR
    v cur endPtr cap2 ptr2 gk.1.seed.ptr sp0 bs2 gk.2.seed hseed_pos hseed_lt hbs2_lt
    (x := x)
    (F := ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      Prost.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc2 hrun2 hsp2 halign htr2 hregs2 (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hregs3 hx21_3 hx22_3
  set bs3 := (bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 gk.2.seed.length)
  have hbs3_len : bs3.length =
      bs2.length + 1 + (encodeVarint (BitVec.ofNat 64 gk.2.seed.length)).length := by
    simp only [bs3, List.length_append, List.length_singleton]
  have hsum_lt : bs3.length + gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_copy_placed_x A H hC hDR
    v cur endPtr cap3 ptr3 gk.1.seed.cap gk.1.seed.ptr sp0 bs3 gk.2.seed
    hseed_pos hseed_lt hsum_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A gk cur ∗ F)
    hpc3 hrun3 hsp3 halign htr3 hregs3 hx21_3 hx22_3 (by ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hregs4
  have hbs4_eq : bs3 ++ gk.2.seed = curBs ++ lenField 4 (encMessageKey gk.2) := by
    rw [← lenField4_encMessageKey_eq gk.2 hseed]
    simp [bs3, bs2, bs1, List.append_assoc]
  refine SepWPpLsCl.congr_pre ?_ (hnext s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hregs4)
  rw [hbs4_eq, messageKeyAt_eq_cells A gk cur]
  ac_rfl

end Placed

end CryptoVerification.E2E.Record.Serialization
