/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `message::merge<Chain>` Tag 4 (`message_keys`) Leaf Proof

Proves `chainMessageKeysG_ok` (tag 4 `message_keys` in `prost::encoding::message::merge<Chain>`),
together with X-stack (`_atW`, `_atWA`) and relocatable `[LibsignalPlacement]` (`lsProg_11 H`,
Block `11`) variants.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk Int32MergeOk)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open Proofs.libsignal Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

private theorem calleeSavedVRegs_setPC_pre_keys (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
private theorem calleeSavedVRegs_setMem_setPC_pre_keys (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl
private theorem sp_setPC_pre_keys (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
private theorem sp_setMem_setPC_pre_keys (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
private theorem readReg64_setPC_pre_keys (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
private theorem readReg64_setMem_setPC_pre_keys (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
private theorem readReg32_setPC_pre_keys (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
private theorem readReg32_setMem_setPC_pre_keys (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
private theorem readReg_setPC_pre_keys (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
private theorem readReg_setMem_setPC_pre_keys (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

attribute [local arm64_norm ↓, local wp_norm ↓]
  calleeSavedVRegs_setPC_pre_keys calleeSavedVRegs_setMem_setPC_pre_keys
  sp_setPC_pre_keys sp_setMem_setPC_pre_keys
  readReg64_setPC_pre_keys readReg64_setMem_setPC_pre_keys
  readReg32_setPC_pre_keys readReg32_setMem_setPC_pre_keys
  readReg_setPC_pre_keys readReg_setMem_setPC_pre_keys

private abbrev int32MergeRelOff : BitVec 64 :=
  bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
    (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))

private abbrev bytesMergeRelOff : BitVec 64 :=
  bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
    (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))

private abbrev growOneChainRelOff : BitVec 64 :=
  bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" -
    ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")

private theorem call_frame_inImage_keys_ext {α : Type} {img : Obj.Image} {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} {x : α} {φ : Prop} {P T F : SepProp} {s : State}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_frame_frozen (x := x) hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic hnext ?_
  intro sf R' _ hm
  rw [hoom] at hm
  exact (not_satisfies_false_sepConj hm).elim

private theorem growOne_inImage_pre_eq_extWA_keys (img : Obj.Image) (A : RustAlloc)
    (a cap ptr sp : BitVec 64) (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) :
    ((Stage1X.growOneChainSpecX A).inImage img).pre (a + 0x30#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = a + 0x30#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗ stackAt sp Stage1X.growOneChainStackX) := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  rw [growOne_inImage_pre_eq_extWA img A (a + 0x30#64) cap ptr sp bs s hsp, e38]

theorem growOne_inImage_pre_eq_extW_keys (img : Obj.Image) (a cap ptr sp : BitVec 64) (bs : List (BitVec 8)) (s : State)
    (hsp : s.sp = sp) (hbs : bs.length = cap.toNat * 104) :
    ((Stage1X.growOneChainSpecX A0).inImage img).pre (a + 0x30#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = a + 0x30#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ (ptr ↦ₛ bs) ∗ stackAt sp Stage1X.growOneChainStackX) := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  rw [growOne_inImage_pre_eq_extW img (a + 0x30#64) cap ptr sp bs s hsp hbs, e38]

private theorem growOne_post_elim_sp_extWA_keys (img : Obj.Image) (A : RustAlloc)
    (a cap ptr sp : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp) (hfull : n = cap.toNat)
    (hbs : bs.length = n * 104) (hbound : n ≤ maxMessageKeys) :
    ((Stage1X.growOneChainSpecX A).inImage img).post (a + 0x30#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
        A.pool ∗ stackAt sp Stage1X.growOneChainStackX := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
  simpa only [e38] using growOne_post_elim_sp_extWA img A (a + 0x30#64) cap ptr sp bs n s_pre sf hsp hfull hbs hmax_lt

theorem growOne_post_elim_sp_extW_keys (img : Obj.Image) (a cap ptr sp : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp) (hfull : n = cap.toNat)
    (hbs : bs.length = n * 104) (hbound : n ≤ maxMessageKeys) :
    ((Stage1X.growOneChainSpecX A0).inImage img).post (a + 0x30#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ p') ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗ stackAt sp Stage1X.growOneChainStackX := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
  simpa only [e38] using growOne_post_elim_sp_extW img (a + 0x30#64) cap ptr sp bs n s_pre sf hsp hfull hbs hmax_lt

private theorem emptyVec_entails_vecU8A_keys (A : RustAlloc) (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A addr [] := by
  rw [emptyVec_eq_vecU8At_seedChain]
  change vecU8At A addr 0#64 1#64 [] ⊢ vecU8 A addr []
  unfold vecU8
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 (Entails.refl _))

private theorem msgKey_default_of_cellsA (A : RustAlloc) (sp0 : BitVec 64) :
    ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
      ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
      ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) ⊢
    vecU8 A (sp0 - 248#64) [] ∗ vecU8 A (sp0 - 224#64) [] ∗ vecU8 A (sp0 - 200#64) [] ∗ vecU8 A (sp0 - 176#64) [] := by
  have v0 := emptyVec_entails_vecU8A_keys A (sp0 - 248#64); have v1 := emptyVec_entails_vecU8A_keys A (sp0 - 224#64)
  have v2 := emptyVec_entails_vecU8A_keys A (sp0 - 200#64); have v3 := emptyVec_entails_vecU8A_keys A (sp0 - 176#64)
  have e0a : (sp0 - 248#64) + 8#64 = sp0 - 240#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e0b : (sp0 - 248#64) + 16#64 = sp0 - 232#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1a : (sp0 - 224#64) + 8#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1b : (sp0 - 224#64) + 16#64 = sp0 - 208#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2a : (sp0 - 200#64) + 8#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2b : (sp0 - 200#64) + 16#64 = sp0 - 184#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3a : (sp0 - 176#64) + 8#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3b : (sp0 - 176#64) + 16#64 = sp0 - 160#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e0a, e0b] at v0; rw [e1a, e1b] at v1; rw [e2a, e2b] at v2; rw [e3a, e3b] at v3
  have hgrp :
      ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
        ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
        ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) =
      (((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64)) ∗
       (((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64)))) := by ac_rfl
  rw [hgrp]; exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 v3))

private theorem prostMsgKeyAt_foldA (A : RustAlloc) (sp0 : BitVec 64) (mk : MessageKeyGenerator) :
    vecU8 A (sp0 - 248#64) [] ∗ vecU8 A (sp0 - 224#64) [] ∗ vecU8 A (sp0 - 200#64) [] ∗
      vecU8 A (sp0 - 176#64) mk.seed ∗ ((sp0 - 152#64) ↦₃₂ mk.counter) ∗
      memRegion (sp0 - 148#64) 4 = prostMsgKeyAt A mk (sp0 - 248#64) := by
  unfold prostMsgKeyAt
  have e1 : (sp0 - 248#64) + 24#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 248#64) + 48#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 248#64) + 72#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 248#64) + 96#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 248#64) + 100#64 = sp0 - 148#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e1, e2, e3, e4, e5]

private theorem vecOf_keys_openA (A : RustAlloc) (a : BitVec 64) (keys : List MessageKeyGenerator) :
    vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) keys ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 ptr keys ∗
           memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e38, e40, h0]
  by_cases hcap : cap = 0#64 <;> simp only [hcap, ↓reduceIte] <;> exact Entails.of_eq (by ac_rfl)

private theorem vecBuf_keys_full_openA (A : RustAlloc) (cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (hfull : keys.length = cap.toNat) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 ptr keys ∗
       memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun mk b' => prostMsgKeyAt A mk b') 104 b keys⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0; have hks : keys = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hks; simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_); rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp, arrayAt_nil]; exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - keys.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (arrayAt_prostMsgKeyAt_move_bytes A keys ptr)) ?_
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro H
    rw [← sepConj_assoc, sepConj_comm (A.live _ _ _), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    rw [← hbs_cap]; exact Entails.pure_right ⟨rfl, hmov⟩ (Entails.of_eq (by ac_rfl))

private theorem vecBuf_keys_not_full_openA (A : RustAlloc) (cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (hlt : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 ptr keys ∗
       memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 ptr keys ∗
        memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  have hmr := memRegion_spare_split_of_lt cap ptr keys.length hlt hcap_lt
  simp only [hcap0, ↓reduceIte] at hmr ⊢
  rw [hmr]

private theorem vecOf_keys_push_foldA (A : RustAlloc) (a cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr keys ∗
      prostMsgKeyAt A mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) ⊢
    vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) (keys ++ [mk]) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hcap_le
  have hlen : (keys ++ [mk]).length = keys.length + 1 := by simp
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hif : (if cap = 0 then emp else A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr (keys ++ [mk]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys ++ [mk]).length * 104)) ((cap.toNat - (keys ++ [mk]).length) * 104)) =
      A.live ptr (cap.toNat * 104) 8 ∗
      (arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr keys ∗
        prostMsgKeyAt A mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) := by
    rw [hlen, arrayAt_concat]; change (if cap = 0#64 then emp else _) = _; simp [hne0]
  rw [e38, e40, hif, hlen]
  have hgrp : (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1))) ∗
      (⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
          (arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr keys ∗
            prostMsgKeyAt A mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104))) =
      ⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr keys ∗
        prostMsgKeyAt A mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104)) := by ac_rfl
  rw [hgrp]; exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr⟩ (Entails.refl _)

theorem step_tag4a_extWA (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (mk_body rest tail : List (BitVec 8))
    (hmk_lt : mk_body.length < 128) (htail_le : tail.length ≤ rest.length)
    (hlen_lt : (2 + (mk_body.length + rest.length)) < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A (sp0 - 248#64) [] ∗ vecU8 A (sp0 - 224#64) [] ∗
          vecU8 A (sp0 - 200#64) [] ∗ vecU8 A (sp0 - 176#64) [] ∗
          ((sp0 - 152#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 148#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 mk_body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (mk_body ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 248#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q Qp := by
  have hsp_align_bv : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hlen_gt : tail.length < (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x22#8 (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest))
  have hrem1_lt : (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain62 hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hmk_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hmk_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 mk_body.length) (mk_body ++ rest)
  have hlen_mk_append : (mk_body ++ rest).length = mk_body.length + rest.length := List.length_append
  have hult_mk_sub := ult_ofNat_add_right_false_seedChain (m := mk_body.length) (k := rest.length) (by omega)
  have hsub_mk_rest := bv_ofNat_add_sub_left_seedChain mk_body.length rest.length
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x120 0x144
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x188 0x1ac
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x1d8 0x300
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (768)) hF hsym ?_
  conv => arg 4; rw [memRegion104_sp248_split sp0, memRegion80_sp248_eq_cells10 sp0]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons, pointsToBytes_cons]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c0
  apply SepWP.exists_elim; intro c1
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c4
  apply SepWP.exists_elim; intro c5
  apply SepWP.exists_elim; intro c6
  apply SepWP.exists_elim; intro c7
  apply SepWP.exists_elim; intro c8
  apply SepWP.exists_elim; intro c9
  apply SepWP.exists_elim; intro c10
  apply SepWP.exists_elim; intro c11
  apply SepWP.exists_elim; intro wc
  iterate 48 wp_step
  apply SepWP.fold (msgKey_default_of_cellsA A sp0) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ rfl (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) hF1 hsym1 (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hvregs]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hx29]))
  unfold Prost.sliceCursorAt
  rw [← hlen_mk_append, ← mk_hdr_pointsTo_combine_seedChain ptr mk_body.length]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4a_extW (img : Obj.Image) {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (mk_body rest tail : List (BitVec 8))
    (hmk_lt : mk_body.length < 128) (htail_le : tail.length ≤ rest.length)
    (hlen_lt : (2 + (mk_body.length + rest.length)) < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗
          vecU8 A0 (sp0 - 200#64) [] ∗ vecU8 A0 (sp0 - 176#64) [] ∗
          ((sp0 - 152#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 148#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 mk_body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (mk_body ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 248#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q Qp :=
  step_tag4a_extWA img a bufRef slot ptr sp0 mk_body rest tail hmk_lt htail_le hlen_lt
    hpc hrun hsp hsp_align hF hsym htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx29 hnext

theorem step_tag4b_extWA (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (hIM : Prost.X.Int32MergeOkW img A ext)
    (a bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest tail : List (BitVec 8))
    (hlen_lt : (pbVarint 1 i.toNat ++ rest_mk ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → img.FrozenLoaded sm →
      sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest_mk ++ rest) ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0; have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil, BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (by ac_rfl))
      (hnext s0 hpc hrun hsp hF hsym htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 hx29)
  · have hi_pos : i.toNat ≠ 0 := by intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest_mk ++ rest) = 0x08#8 :: rem1 := by rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : rest.length < (0x08#8 :: rem1).length := by simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = (SP2Ext img.base ext).fnAddr chainMergeName + int32MergeRelOff →
        s1.status = .Running → s1.sp = sp0 - 256#64 → img.FrozenLoaded s1 →
        s1.symtab = img.symtab → s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x424#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 → s1.readReg64 .x1 = sp0 - 152#64 →
        s1.readReg64 .x2 = bufRef → s1.readReg64 .x19 = bufRef → s1.readReg64 .x20 = a →
        s1.readReg64 .x21 = 98#64 → s1.readReg64 .x22 = 97#64 →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length → s1.readReg64 .x25 = sp0 - 248#64 →
        s1.readReg64 .x26 = 1#64 → s1.readReg64 .x28 = BitVec.ofNat 64 rest.length →
        s1.readReg64 .x29 = sp0 - 0x60#64 →
        SepWPp (SP2Ext img.base ext) ret s1
          ((((sp0 - 152#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot (ptr + 1#64) rem1 ∗
            A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      chainMerge_fetches_range img.base (Rust.withPanics ext) 0x300 0x324
      chainMerge_fetches_range img.base (Rust.withPanics ext) 0x368 0x38c
      chainMerge_fetches_range img.base (Rust.withPanics ext) 0x3c0 0x3c4
      chainMerge_fetches_range img.base (Rust.withPanics ext) 0x418 0x420
      dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext1 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
      have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
      have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + int32MergeRelOff) hF hsym ?_
      conv => arg 4; rw [hcons_eq]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons]; simp only [sepConj_assoc]
      iterate 25 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
        (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm]) (by simp only [h24, arm64_norm])
        (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm]) (by simp only [h28, arm64_norm])
        (by simp only [h29, arm64_norm]))
      unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_atWA img hIM (sp0 - 152#64) bufRef slot (ptr + 1#64) sp0
        ((SP2Ext img.base ext).fnAddr chainMergeName + 0x424#64)
        0#32 i (rest_mk ++ rest) hrem1_lt (x := dummyChainMergeGhost) (R := R)
        hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
      chainMerge_fetches_range img.base (Rust.withPanics ext) 0x424 0x42c
      dsimp only [SP2Ext, contractProg, chainMergeName] at hpc2 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (768)) hF2 hsym2 ?_
      iterate 3 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hF3 hsym3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hcs2.2.2.1.trans hx21_1
      have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hcs2.2.2.2.1.trans hx22_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
      have h28_2 : s2.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
      have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
        (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
        (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
        (by simp only [h26_2, arm64_norm]) (by simp only [h28_2, arm64_norm])
        (by simp only [h29_2, arm64_norm]))
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos, ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4b_extW (img : Obj.Image) {ext : String → Option (State → State)}
    (hIM : Prost.X.Int32MergeOkW img A0 ext)
    (a bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest tail : List (BitVec 8))
    (hlen_lt : (pbVarint 1 i.toNat ++ rest_mk ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → img.FrozenLoaded sm →
      sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest_mk ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  refine SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hp, emp_sepConj]))
    (step_tag4b_extWA img hIM a bufRef slot ptr sp0 i rest_mk rest tail hlen_lt (x := x) (R := R)
      hpc hrun hsp halign hF hsym htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 hx29
      (fun sm h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
        SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hp, emp_sepConj]))
          (hnext sm h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)))

theorem step_tag4c_extWA (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A ext)
    (a bufRef slot ptr sp0 : BitVec 64) (k rest tail : List (BitVec 8))
    (hk_lt : k.length < 128) (hlen_lt : (pbBytes 5 k ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → img.FrozenLoaded sm →
      sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A (sp0 - 176#64) k ∗ (ptr ↦ₛ pbBytes 5 k) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 k).length) rest ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ vecU8 A (sp0 - 176#64) [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 k ++ rest) ∗
        A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 5 k = 0x2a#8 :: BitVec.ofNat 8 k.length :: k := pbBytes_lt128_eq_seedChain 5 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ rest
  have hcons_eq : pbBytes 5 k ++ rest = 0x2a#8 :: rem1 := by rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x2a#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bytesMergeRelOff →
      s1.status = .Running → s1.sp = sp0 - 256#64 → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x3b4#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = sp0 - 176#64 →
      s1.readReg64 .x2 = bufRef → s1.readReg64 .x19 = bufRef → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = 98#64 → s1.readReg64 .x22 = 97#64 →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length → s1.readReg64 .x25 = sp0 - 248#64 →
      s1.readReg64 .x26 = 1#64 → s1.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s1.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret s1
        ((vecU8 A (sp0 - 176#64) [] ∗ (bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x2a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x300 0x324
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x368 0x3b0
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
    have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bytesMergeRelOff) hF hsym ?_
    conv => arg 4; rw [hcons_eq]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons]; simp only [sepConj_assoc]
    iterate 29 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
      (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm]) (by simp only [h24, arm64_norm])
      (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm]) (by simp only [h28, arm64_norm])
      (by simp only [h29, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ rest).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_atWA img hBM (sp0 - 176#64) bufRef slot (ptr + 1#64) sp0
      ((SP2Ext img.base ext).fnAddr chainMergeName + 0x3b4#64)
      [] k rest hk_lt hrem1_lt (x := dummyChainMergeGhost) (R := R)
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x3b4 0x3bc
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (768)) hF2 hsym2 ?_
    iterate 3 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hF3 hsym3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hcs2.2.2.1.trans hx21_1
    have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hcs2.2.2.2.1.trans hx22_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have h28_2 : s2.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
      (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
      (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]) (by simp only [h28_2, arm64_norm])
      (by simp only [h29_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 5 (by decide) ptr k hk_lt, ← pbBytes_pointsTo_combine_seedChain 5 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4c_extW (img : Obj.Image) {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A0 ext)
    (a bufRef slot ptr sp0 : BitVec 64) (k rest tail : List (BitVec 8))
    (hk_lt : k.length < 128) (hlen_lt : (pbBytes 5 k ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → img.FrozenLoaded sm →
      sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 176#64) k ∗ (ptr ↦ₛ pbBytes 5 k) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 k).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 176#64) [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 k ++ rest) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  refine SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hp, emp_sepConj]))
    (step_tag4c_extWA img hBM a bufRef slot ptr sp0 k rest tail hk_lt hlen_lt (x := x) (R := R)
      hpc hrun hsp halign hF hsym htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 hx29
      (fun sm h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
        SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hp, emp_sepConj]))
          (hnext sm h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)))

theorem step_tag4d_extWA (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (hG : Stage1X.GrowOneChainOkX img A ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret val24 : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = val24)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x5c8#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x23 = BitVec.ofNat 64 keys.length →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          A.live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) keys ∗
        A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R)) := by
  have hG' := growOneChain_ok_sub_seedChain_extW hG; clear hG
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false := bne_self_eq_false _
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x300 0x30c
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x5b4 0x5c4
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x61c 0x624
  dsimp only [SP2Ext, contractProg, chainMergeName] at hG' hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = val24 := hx24; have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26; have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  apply SepWPp.fold (vecOf_keys_openA A a keys) (by sep_frame)
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    apply SepWPp.fold (vecBuf_keys_full_openA A cap ptr keys hfull) (by sep_frame)
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_cap, hmov⟩
    have hbs_len : bs.length = keys.length * 104 := by rw [hbs_cap, hfull]
    conv => arg 4; rw [stackAt_sub_to_growOne_seedChainW (sp0 - 256#64)]
    have hmax_le : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + growOneChainRelOff) hF hsym ?_
    conv => arg 4; unfold Prost.sliceCursorAt
    iterate 11 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine call_frame_inImage_keys_ext (x := (a + 0x30#64, cap, ptr, bs))
      (ret_pc := entry + bv% (1572)) hF1 hsym1 hG'
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) (by simp only [arm64_norm])
      (growOne_inImage_pre_eq_extWA_keys img A a cap ptr (sp0 - 256#64) bs _ (by simp only [hsp, arm64_norm]))
      ⟨⟨hbs_cap, by simp only [arm64_norm], hptr, hmax_le⟩, hF1, hsym1⟩ (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [htr, arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hFm hsymm
    have ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, _, h28_2, h29_2, hvregs_m⟩ := hcsm
    simp only [h19, h20, h21, h22, h24, h25, h26, h28, h29, hsp, arm64_norm] at h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h28_2 h29_2 hspm
    have hvregs_m' : calleeSavedVRegs sm = calleeSavedVRegs s_init := by
      simpa only [hvregs, arm64_norm] using hvregs_m
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm.trans hsp.symm) hsp_align
    refine SepWPp.fold (growOne_post_elim_sp_extWA_keys img A a cap ptr (sp0 - 256#64) bs keys.length _ sm
      (by simp only [hsp, arm64_norm]) hfull hbs_len hbound) rfl ?_
    conv => arg 4; simp only [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s_init.trace := by simpa only [htr, arm64_norm] using htr_m
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro ptr'
    apply SepWPp.pure_left; rintro ⟨hcap'_le, hcap'_lt, hptr'⟩
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_seedChainW (sp0 - 256#64)).symm) (by sep_frame)
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1480)) hFm hsymm ?_
    wp_step; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm]) ?_; intro hF2 hsym2
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap' ptr' hcap'_le hcap'_lt hptr'
      (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm])
      (by simp only [hspm, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align_m)
      hF2 hsym2 (by simp only [htr_m', arm64_norm]) (by simp only [hvregs_m', arm64_norm])
      (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm]) (by simp only [h21_2, arm64_norm])
      (by simp only [h22_2, arm64_norm]) (by simp only [h23_2, hfull, BitVec.ofNat_toNat, arm64_norm])
      (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]) (by simp only [h29_2, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
    conv => arg 4; rw [vecBuf_keys_not_full_openA A cap ptr keys hcap_le' hcap_lt]
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1480)) hF hsym ?_
    conv => arg 4; unfold Prost.sliceCursorAt
    iterate 9 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap ptr hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
      hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [h19, arm64_norm])
      (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm])
      (by simp only [h22, arm64_norm]) (by simp only [arm64_norm])
      (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm])
      (by simp only [h26, arm64_norm]) (by simp only [h29, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4d_extW (img : Obj.Image) {ext : String → Option (State → State)}
    (hG : Stage1X.GrowOneChainOkX img A0 ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret val24 : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = val24)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x5c8#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x23 = BitVec.ofNat 64 keys.length →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) keys ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  refine SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hp, emp_sepConj]))
    (step_tag4d_extWA img hG a bufRef slot ptr_rest sp0 keys rest hbound (x := x) (R := R)
      hpc hrun hsp hsp_align hF hsym htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 hx29
      (fun sm cap' ptr' hc1 hc2 hp' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 => by
        have hl : A0.live ptr' (cap'.toNat * 104) 8 = emp := rfl
        exact SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hl, hp, emp_sepConj, emp_sepConj]))
          (hnext sm cap' ptr' hc1 hc2 hp' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17)))

theorem step_tag4e_extWA (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (a cap' ptr' sp0 : BitVec 64) (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    {ret val19 val24 : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x5c8#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init) (hx19 : s0.readReg64 .x19 = val19)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 keys.length)
    (hx24 : s0.readReg64 .x24 = val24) (hx25 : s0.readReg64 .x25 = sp0 - 248#64)
    (hx26 : s0.readReg64 .x26 = 1#64) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s_init.trace → calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = val19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 248#64) 104) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A mk (sp0 - 248#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length; have hadd1 := ofNat_add_one_eq keys.length
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x5c8 0x618
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x260 0x260
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = val19 := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20; have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 keys.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = val24 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF hsym ?_
  apply SepWP.fold (prostMsgKeyAt_move_chunks104 A (sp0 - 248#64) mk) (by sep_frame)
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0; apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2; apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4; apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro H
  apply SepWP.pure_elim; intro hmov
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)))) (by sep_frame)
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) d0 d1 d2 d3 d4 d5 dw6]
  iterate 22 wp_step
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6]
  apply SepWP.fold (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104))) (by sep_frame)
  apply SepWP.fold (chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  apply SepWP.fold (vecOf_keys_push_foldA A a cap' ptr' keys mk hcap_le hcap_lt hptr) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm])
    (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm])
    (by simp only [h29, arm64_norm]))
  exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4e_extW (img : Obj.Image) {ext : String → Option (State → State)}
    (a cap' ptr' sp0 : BitVec 64) (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    {ret val19 val24 : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x5c8#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init) (hx19 : s0.readReg64 .x19 = val19)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 keys.length)
    (hx24 : s0.readReg64 .x24 = val24) (hx25 : s0.readReg64 .x25 = sp0 - 248#64)
    (hx26 : s0.readReg64 .x26 = 1#64) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s_init.trace → calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = val19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 248#64) 104) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A0 mk (sp0 - 248#64)) ∗ F) Q Qp := by
  have hl : A0.live ptr' (cap'.toNat * 104) 8 = emp := rfl
  refine SepWPp.mono_pre_seedChain (Entails.of_eq (by rw [hl, emp_sepConj]))
    (step_tag4e_extWA img a cap' ptr' sp0 keys mk hcap_le hcap_lt hptr
      hpc hrun hsp hsp_align hF hsym htr hvregs hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx29 hnext)

theorem chainMessageKeysG_ok_atWA (img : Obj.Image) (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtWA img A ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 4)
    (hs : ChainLoopGAtWA img A ext x R s0 k s) :
    ChainStepGAtWA img A ext x R s0 s (ChainLoopGAtWA img A ext x R s0 (k + 1)) := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hsp_align, hx29, hx19, hx20, hx24,
    hx21, hx22, hx25, hx26, hOk, hlen_pay, hmem⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hOk.2.2.2.1 mk hmk_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  have halign : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sp_sub_256 hsp hsp_align
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let v1 : List (BitVec 8) := pbVarint 1 mk.counter.toNat
  let v2 : List (BitVec 8) := pbBytes 5 mk.seed
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    rw [chainG_payload_split x.c k x.tail, drop_fields_flatMap_enc_of_key hk hfl x.tail,
      lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
  have hcur_open : Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      ((x.c.fields.drop k).flatMap ChainField.enc ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗ Prost.sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest) := by
      rw [drop_fields_flatMap_enc_of_key hk hfl x.tail, lenField_4_encMessageKey_eq hseed,
        encMessageKey_eq_pb hseed]; rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : (v1 ++ v2).length < 128 := by
    rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + ((v1 ++ v2).length + rest.length) < 2 ^ 62 := by
    have h := hlen_pay; rw [hpay_eq] at h; simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (v1 ++ v2 ++ rest).length < 2 ^ 62 := by simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (v2 ++ rest).length < 2 ^ 62 := by simp only [List.length_append] at hlen_a ⊢; omega
  have hk_lt : mk.seed.length < 128 := by omega
  have hmem' : s.mem ⊨
      (prostChainGAt A x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
          (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
        A.pool ∗ stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0) ∗ R :=
    Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  refine segStepG_of_sepWPp (ret := (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64) hmem' ?_
  conv => arg 4; rw [prostChainGAt_eq_keys_sep_rest A x.a (chainGAfter x.c k),
    chainMergeSavedRegs_eq_split s0.sp s0, hcur_open]
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 := hpc
  refine SepWPp.focus_pre
    (step_tag4a_extWA (A := A) img x.a x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length) s0.sp
      (v1 ++ v2) rest x.tail hmk_lt htail_le hlen_a hpc' hrun hsp hsp_align hF hsym htr hvregs
      hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx29 ?_)
  intro s1 hpc1 hrun1 hsp1 hsp_align1 hF1 hsym1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
  conv => arg 4; rw [List.append_assoc v1 v2 rest]
  refine SepWPp.focus_pre
    (step_tag4b_extWA img hC.2.1 x.a x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64)
      s0.sp mk.counter v2 rest x.tail hlen_b hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hvregs1
      hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2
  refine SepWPp.focus_pre
    (step_tag4c_extWA img hC.2.2.1 x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) s0.sp
      mk.seed rest x.tail hk_lt hlen_c hpc2 hrun2 hsp2 halign hF2 hsym2 htr2 hvregs2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 ?_)
  intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3
  have hsp_align3 : s3.spAligned = true := spAligned_of_sp_eq (hsp3.trans hsp.symm) hsp_align
  apply SepWPp.fold (Entails.of_eq (prostMsgKeyAt_foldA A s0.sp mk)) (by sep_frame)
  refine SepWPp.focus_pre
    (step_tag4d_extWA img hC.2.2.2 x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length)
      s0.sp (chainGAfter x.c k).keys rest hbound
      hpc3 hrun3 hsp3 hsp_align3 hF3 hsym3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3
      hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 ?_)
  intro s4 cap' ptr' hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hF4 hsym4 htr4 hvregs4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
  refine SepWPp.focus_pre
    (step_tag4e_extWA (A := A) img x.a cap' ptr' s0.sp (chainGAfter x.c k).keys mk
      hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hF4 hsym4 htr4 hvregs4
      hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 ?_)
  intro s5 hpc5 hrun5 hsp5 hsp_align5 hF5 hsym5 htr5 hvregs5 hx19_5 hx20_5 hx21_5 hx22_5 hx24_5 hx25_5 hx26_5 hx29_5
  refine SepWPp.of_sepWP_ret (SepWP.done hpc5 hrun5 ?_)
  intro hmf5
  refine ⟨hpc5, hrun5, htr5, hvregs5, hsym5, hF5, hsp5, hsp_align5, hx29_5,
    hx19_5, hx20_5, hx24_5, hx21_5, hx22_5, hx25_5, hx26_5,
    hOk, hlen_pay, ?_⟩
  rw [chainGAfter_succ_of_key hk hfl,
    prostChainGAt_eq_keys_sep_rest A x.a { chainGAfter x.c k with keys := (chainGAfter x.c k).keys ++ [mk] },
    prostChainGRest_update_keys,
    chainMergeSavedRegs_eq_split s0.sp s0,
    ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx v1 v2 rest hpay_eq]
  exact Satisfies.mono (by sep_frame) hmf5

theorem chainMessageKeysG_ok_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtW img ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 4)
    (hs : ChainLoopGAtW img ext x R s0 k s) :
    ChainStepGAtW img ext x R s0 s (ChainLoopGAtW img ext x R s0 (k + 1)) := by
  have hp : A0.pool = emp := rfl
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hmem⟩
  rw [← emp_sepConj (stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ _), ← hp] at hmem
  intro hL
  obtain ⟨sf, hsteps, hex⟩ := chainMessageKeysG_ok_atWA img A0 hC x R s0 k s hk htag
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hmem⟩ hL
  refine ⟨sf, hsteps, hex.imp ?_ id⟩
  rintro ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, gmem⟩
  rw [hp, emp_sepConj] at gmem
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, gmem⟩

/-! ## Relocatable `[LibsignalPlacement]` Proof of `message::merge<Chain>` Tag 4 (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_ChainMessageKeysGExt_Placed : True := trivial

private theorem of_sepWP_lscro [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ (hcrl' : LibsignalCodeRoLoaded lsmpl _) hkf => hcrl'.of_keepsFrozen hkf)
    hcrl h

private theorem call_frame_lscro_keys [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} {x : α} {φ : Prop} {P T F : SepProp} {s : State}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  let spec' : Spec α :=
    { LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec with
      post := fun x s0 sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x s0 sf }
  have hcall' : subroutine_ok prog entry spec' := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R' s0' hpc' hrun' hpre' hsp' hL' => ?_
    have hcrl0 : LibsignalCodeRoLoaded lsmpl s0'.mem := by
      dsimp only [spec', LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre'
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre'
      exact hpre'.1
    obtain ⟨sf, hsteps, hout, -⟩ :=
      hcall.no_fault_before_outcome x' R' s0' hpc' hrun' hpre' hsp' hL'
    have hcrlf : LibsignalCodeRoLoaded lsmpl sf.mem := hcrl0.of_keepsFrozen hsteps.keepsFrozen
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [spec']
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcrlf, hpost⟩
    · exact Or.inr hrest
  refine SepWPp.call (x := x) (F := F) hcall' hpc hrun hsp hlr ?_ hexit hpanic ?_ ?_
  · intro R hm
    dsimp only [spec', LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf hpcm hrunm hspm hcsm
    dsimp only [spec']
    rw [sepConj_assoc]
    exact SepWPp.pure_elim (hnext sf hpcm hrunm hspm hcsm)
  · intro sf R' _ hm
    dsimp only [spec', LibsignalTripleRatchet.withLsCodeRoLoaded] at hm
    rw [hoom] at hm
    exact (not_satisfies_false_sepConj hm).elim

theorem growOne_placed_pre_eq_extW_keys (a cap ptr sp : BitVec 64) (bs : List (BitVec 8)) (s : State)
    (hsp : s.sp = sp) (hbs : bs.length = cap.toNat * 104) :
    (Stage1X.growOneChainSpecX A0).pre (a + 0x30#64, cap, ptr, bs) s =
    ⌜bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = a + 0x30#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63⌝ ∗
    (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ (ptr ↦ₛ bs) ∗ stackAt sp Stage1X.growOneChainStackX) := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  rw [growOne_placed_pre_eq_extW (a + 0x30#64) cap ptr sp bs s hsp hbs, e38]

theorem growOne_placed_post_elim_sp_extW_keys (a cap ptr sp : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp) (hfull : n = cap.toNat)
    (hbs : bs.length = n * 104) (hbound : n ≤ maxMessageKeys) :
    (Stage1X.growOneChainSpecX A0).post (a + 0x30#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ p') ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗ stackAt sp Stage1X.growOneChainStackX := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
  simpa only [e38] using growOne_placed_post_elim_sp_extW (a + 0x30#64) cap ptr sp bs n s_pre sf hsp hfull hbs hmax_lt

theorem step_tag4a_placedW [LibsignalPlacement] {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64) (mk_body rest tail : List (BitVec 8))
    (hmk_lt : mk_body.length < 128) (htail_le : tail.length ≤ rest.length)
    (hlen_lt : (2 + (mk_body.length + rest.length)) < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      LibsignalCodeRoLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗
          vecU8 A0 (sp0 - 200#64) [] ∗ vecU8 A0 (sp0 - 176#64) [] ∗
          ((sp0 - 152#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 148#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 mk_body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (mk_body ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 248#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q Qp := by
  have hsp_align_bv : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hlen_gt : tail.length < (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x22#8 (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest))
  have hrem1_lt : (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain62 hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hmk_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hmk_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 mk_body.length) (mk_body ++ rest)
  have hlen_mk_append : (mk_body ++ rest).length = mk_body.length + rest.length := List.length_append
  have hult_mk_sub := ult_ofNat_add_right_false_seedChain (m := mk_body.length) (k := rest.length) (by omega)
  have hsub_mk_rest := bv_ofNat_add_sub_left_seedChain mk_body.length rest.length
  refine of_sepWP_lscro (mid := (blkPl_11).base + 0x300#64) hcrl ?_
  rw [memRegion104_sp248_split sp0, memRegion80_sp248_eq_cells10 sp0]
  unfold Prost.sliceCursorAt; rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c0
  apply SepWP.exists_elim; intro c1
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c4
  apply SepWP.exists_elim; intro c5
  apply SepWP.exists_elim; intro c6
  apply SepWP.exists_elim; intro c7
  apply SepWP.exists_elim; intro c8
  apply SepWP.exists_elim; intro c9
  apply SepWP.exists_elim; intro c10
  apply SepWP.exists_elim; intro c11
  apply SepWP.exists_elim; intro wc
  iterate 48 wp_step
  apply SepWP.fold (msgKey_default_of_cells sp0) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcrl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) hcrl1 (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hvregs]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hx29]))
  unfold Prost.sliceCursorAt
  rw [← hlen_mk_append, ← mk_hdr_pointsTo_combine_seedChain ptr mk_body.length]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4b_placedW [LibsignalPlacement] {H : LibsignalHooks}
    (hIM : Prost.X.Int32MergePlacedOkW A0 H)
    (a bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest tail : List (BitVec 8))
    (hlen_lt : (pbVarint 1 i.toNat ++ rest_mk ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest_mk ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0; have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil, BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (by ac_rfl))
      (hnext s0 hpc hrun hsp hcrl htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 hx29)
  · have hi_pos : i.toNat ≠ 0 := by intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest_mk ++ rest) = 0x08#8 :: rem1 := by rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : rest.length < (0x08#8 :: rem1).length := by simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = lsmpl.base 8 →
        s1.status = .Running → s1.sp = sp0 - 256#64 → LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (blkPl_11).base + 0x424#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 → s1.readReg64 .x1 = sp0 - 152#64 →
        s1.readReg64 .x2 = bufRef → s1.readReg64 .x19 = bufRef → s1.readReg64 .x20 = a →
        s1.readReg64 .x21 = 98#64 → s1.readReg64 .x22 = 97#64 →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length → s1.readReg64 .x25 = sp0 - 248#64 →
        s1.readReg64 .x26 = 1#64 → s1.readReg64 .x28 = BitVec.ofNat 64 rest.length →
        s1.readReg64 .x29 = sp0 - 0x60#64 →
        SepWPp (lsProg_11 H) ret s1
          ((((sp0 - 152#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
      have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
      have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
      refine of_sepWP_lscro (mid := lsmpl.base 8) hcrl ?_
      rw [hcons_eq]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons]; simp only [sepConj_assoc]
      iterate 25 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcrl1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
        (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm]) (by simp only [h24, arm64_norm])
        (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm]) (by simp only [h28, arm64_norm])
        (by simp only [h29, arm64_norm]))
      unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_placedW hIM (sp0 - 152#64) bufRef slot (ptr + 1#64) sp0
        ((blkPl_11).base + 0x424#64)
        0#32 i (rest_mk ++ rest) hrem1_lt (x := x) (R := R)
        hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine of_sepWP_lscro (mid := (blkPl_11).base + 0x300#64) hcrl2 ?_
      iterate 3 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hcrl3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hcs2.2.2.1.trans hx21_1
      have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hcs2.2.2.2.1.trans hx22_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
      have h28_2 : s2.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
      have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
        (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
        (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
        (by simp only [h26_2, arm64_norm]) (by simp only [h28_2, arm64_norm])
        (by simp only [h29_2, arm64_norm]))
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos, ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4c_placedW [LibsignalPlacement] {H : LibsignalHooks}
    (hBM : Prost.X.BytesMergePlacedOkW A0 H)
    (a bufRef slot ptr sp0 : BitVec 64) (k rest tail : List (BitVec 8))
    (hk_lt : k.length < 128) (hlen_lt : (pbBytes 5 k ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 176#64) k ∗ (ptr ↦ₛ pbBytes 5 k) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 k).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 176#64) [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 k ++ rest) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 5 k = 0x2a#8 :: BitVec.ofNat 8 k.length :: k := pbBytes_lt128_eq_seedChain 5 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ rest
  have hcons_eq : pbBytes 5 k ++ rest = 0x2a#8 :: rem1 := by rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x2a#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = lsmpl.base 7 →
      s1.status = .Running → s1.sp = sp0 - 256#64 → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (blkPl_11).base + 0x3b4#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = sp0 - 176#64 →
      s1.readReg64 .x2 = bufRef → s1.readReg64 .x19 = bufRef → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = 98#64 → s1.readReg64 .x22 = 97#64 →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length → s1.readReg64 .x25 = sp0 - 248#64 →
      s1.readReg64 .x26 = 1#64 → s1.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s1.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8 A0 (sp0 - 176#64) [] ∗ (bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x2a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
    have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
    refine of_sepWP_lscro (mid := lsmpl.base 7) hcrl ?_
    rw [hcons_eq]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons]; simp only [sepConj_assoc]
    iterate 29 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
      (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm]) (by simp only [h24, arm64_norm])
      (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm]) (by simp only [h28, arm64_norm])
      (by simp only [h29, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ rest).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_placedW hBM (sp0 - 176#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x3b4#64)
      [] k rest hk_lt hrem1_lt (x := x) (R := R)
      hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_lscro (mid := (blkPl_11).base + 0x300#64) hcrl2 ?_
    iterate 3 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hcrl3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hcs2.2.2.1.trans hx21_1
    have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hcs2.2.2.2.1.trans hx22_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have h28_2 : s2.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
      (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
      (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]) (by simp only [h28_2, arm64_norm])
      (by simp only [h29_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 5 (by decide) ptr k hk_lt, ← pbBytes_pointsTo_combine_seedChain 5 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4d_placedW [LibsignalPlacement] {H : LibsignalHooks}
    (hG : Stage1X.GrowOneChainPlacedOkX A0 H)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret val24 : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = val24)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = (blkPl_11).base + 0x5c8#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      LibsignalCodeRoLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x23 = BitVec.ofNat 64 keys.length →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) keys ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R)) := by
  have hG' := growOneChain_placed_ok_sub_seedChainW hG; clear hG
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false := bne_self_eq_false _
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = val24 := hx24; have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26; have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  apply SepWPp.fold (vecOf_keys_open a keys) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    rw [memRegion_spare_eq_emp_of_full cap ptr keys.length hfull, stackAt_sub_to_growOne_seedChainW (sp0 - 256#64)]
    simp only [emp_sepConj]
    apply SepWPp.fold (arrayAt_prostMsgKeyAt_move_bytes A0 keys ptr) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro Hmov
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hmax_le : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
    refine of_sepWP_lscro (mid := lsmpl.base 43) hcrl ?_
    unfold Prost.sliceCursorAt; iterate 11 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcrl1
    refine call_frame_lscro_keys (x := (a + 0x30#64, cap, ptr, bs))
      (ret_pc := (blkPl_11).base + 0x624#64) hcrl1 hG'
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) (by simp only [arm64_norm])
      (growOne_placed_pre_eq_extW_keys a cap ptr (sp0 - 256#64) bs _ (by simp only [hsp, arm64_norm]) hbs_cap)
      ⟨hbs_cap, by simp only [arm64_norm], hptr, hmax_le⟩ (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [htr, arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hcrlm
    have ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, _, h28_2, h29_2, hvregs_m⟩ := hcsm
    simp only [h19, h20, h21, h22, h24, h25, h26, h28, h29, hsp, arm64_norm] at h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h28_2 h29_2 hspm
    have hvregs_m' : calleeSavedVRegs sm = calleeSavedVRegs s_init := by
      simpa only [hvregs, arm64_norm] using hvregs_m
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm.trans hsp.symm) hsp_align
    refine SepWPp.fold (growOne_placed_post_elim_sp_extW_keys a cap ptr (sp0 - 256#64) bs keys.length _ sm
      (by simp only [hsp, arm64_norm]) hfull hbs_len hbound) rfl ?_
    simp only [sepConj_assoc]; apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s_init.trace := by simpa only [htr, arm64_norm] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro ptr'
    apply SepWPp.pure_left; rintro ⟨hcap'_le, hcap'_lt, hptr'⟩
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_seedChainW (sp0 - 256#64)).symm) (by sep_frame)
    refine of_sepWP_lscro (mid := (blkPl_11).base + 0x5c8#64) hcrlm ?_
    wp_step; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm]) ?_; intro hcrl2
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap' ptr' hcap'_le hcap'_lt hptr'
      (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm])
      (by simp only [hspm, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align_m)
      hcrl2 (by simp only [htr_m', arm64_norm]) (by simp only [hvregs_m', arm64_norm])
      (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm]) (by simp only [h21_2, arm64_norm])
      (by simp only [h22_2, arm64_norm]) (by simp only [h23_2, hfull, BitVec.ofNat_toNat, arm64_norm])
      (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]) (by simp only [h29_2, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
    rw [memRegion_spare_split_of_lt cap ptr keys.length hcap_le' hcap_lt]
    refine of_sepWP_lscro (mid := (blkPl_11).base + 0x5c8#64) hcrl ?_
    unfold Prost.sliceCursorAt; iterate 9 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap ptr hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
      hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [h19, arm64_norm])
      (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm])
      (by simp only [h22, arm64_norm]) (by simp only [arm64_norm])
      (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm])
      (by simp only [h26, arm64_norm]) (by simp only [h29, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4e_placedW [LibsignalPlacement] {H : LibsignalHooks}
    (a cap' ptr' sp0 : BitVec 64) (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    {ret val19 val24 : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x5c8#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init) (hx19 : s0.readReg64 .x19 = val19)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 keys.length)
    (hx24 : s0.readReg64 .x24 = val24) (hx25 : s0.readReg64 .x25 = sp0 - 248#64)
    (hx26 : s0.readReg64 .x26 = 1#64) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      LibsignalCodeRoLoaded lsmpl sm.mem → sm.trace = s_init.trace → calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = val19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (lsProg_11 H) ret sm
        ((vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 248#64) 104) ∗ F) Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A0 mk (sp0 - 248#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length; have hadd1 := ofNat_add_one_eq keys.length
  have h19 : s0.readReg64 (Reg.gpr 19#5) = val19 := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20; have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 keys.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = val24 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  refine of_sepWP_lscro (mid := (blkPl_11).base + 0x120#64) hcrl ?_
  apply SepWP.fold (prostMsgKeyAt_move_chunks104 A0 (sp0 - 248#64) mk) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0; apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2; apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4; apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro Hmov
  apply SepWP.pure_elim; intro hmov
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)))) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) d0 d1 d2 d3 d4 d5 dw6]
  iterate 22 wp_step
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6]
  apply SepWP.fold (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104))) (by sep_frame)
  apply SepWP.fold (chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  apply SepWP.fold (vecOf_keys_push_fold a cap' ptr' keys mk hcap_le hcap_lt hptr) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hcrl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
    hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm])
    (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm])
    (by simp only [h29, arm64_norm]))
  exact sep_ac_seedChain (by ac_rfl)

theorem chainMessageKeysG_placed_okW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hC : DeserializeCalleesPlacedW H) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 4)
    (hs : ChainLoopGPlacedW x R s0 k s) :
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1)) := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcrl, hsp, hsp_align, hx29, hx19, hx20, hx24,
    hx21, hx22, hx25, hx26, hOk, hlen_pay, hmem⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hOk.2.2.2.1 mk hmk_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  have halign : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sp_sub_256 hsp hsp_align
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let v1 : List (BitVec 8) := pbVarint 1 mk.counter.toNat
  let v2 : List (BitVec 8) := pbBytes 5 mk.seed
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    rw [chainG_payload_split x.c k x.tail, drop_fields_flatMap_enc_of_key hk hfl x.tail,
      lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
  have hcur_open : Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      ((x.c.fields.drop k).flatMap ChainField.enc ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗ Prost.sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest) := by
      rw [drop_fields_flatMap_enc_of_key hk hfl x.tail, lenField_4_encMessageKey_eq hseed,
        encMessageKey_eq_pb hseed]; rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : (v1 ++ v2).length < 128 := by
    rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + ((v1 ++ v2).length + rest.length) < 2 ^ 62 := by
    have h := hlen_pay; rw [hpay_eq] at h; simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (v1 ++ v2 ++ rest).length < 2 ^ 62 := by simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (v2 ++ rest).length < 2 ^ 62 := by simp only [List.length_append] at hlen_a ⊢; omega
  have hk_lt : mk.seed.length < 128 := by omega
  have hmem' : s.mem ⊨
      (prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
          (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
        stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0) ∗ R :=
    Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  refine segStepG_of_sepWPp (ret := (blkPl_11).base + 0x120#64) hmem' ?_
  rw [prostChainGAt_eq_keys_sep_rest A0 x.a (chainGAfter x.c k),
    chainMergeSavedRegs_eq_split s0.sp s0, hcur_open]
  have hpc' : s.pc = (blkPl_11).base + 0x120#64 := hpc
  refine SepWPp.focus_pre
    (step_tag4a_placedW x.a x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length) s0.sp
      (v1 ++ v2) rest x.tail hmk_lt htail_le hlen_a hpc' hrun hsp hsp_align hcrl htr hvregs
      hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx29 ?_)
  intro s1 hpc1 hrun1 hsp1 hsp_align1 hcrl1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
  rw [List.append_assoc v1 v2 rest]
  refine SepWPp.focus_pre
    (step_tag4b_placedW hC.2.1 x.a x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64)
      s0.sp mk.counter v2 rest x.tail hlen_b hpc1 hrun1 hsp1 halign hcrl1 htr1 hvregs1
      hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2
  refine SepWPp.focus_pre
    (step_tag4c_placedW hC.2.2.1 x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) s0.sp
      mk.seed rest x.tail hk_lt hlen_c hpc2 hrun2 hsp2 halign hcrl2 htr2 hvregs2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 ?_)
  intro s3 hpc3 hrun3 hsp3 hcrl3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3
  have hsp_align3 : s3.spAligned = true := spAligned_of_sp_eq (hsp3.trans hsp.symm) hsp_align
  apply SepWPp.fold (Entails.of_eq (prostMsgKeyAt_fold s0.sp mk)) (by sep_frame)
  refine SepWPp.focus_pre
    (step_tag4d_placedW hC.2.2.2 x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length)
      s0.sp (chainGAfter x.c k).keys rest hbound
      hpc3 hrun3 hsp3 hsp_align3 hcrl3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3
      hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 ?_)
  intro s4 cap' ptr' hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hcrl4 htr4 hvregs4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
  refine SepWPp.focus_pre
    (step_tag4e_placedW x.a cap' ptr' s0.sp (chainGAfter x.c k).keys mk
      hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hcrl4 htr4 hvregs4
      hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 ?_)
  intro s5 hpc5 hrun5 hsp5 hsp_align5 hcrl5 htr5 hvregs5 hx19_5 hx20_5 hx21_5 hx22_5 hx24_5 hx25_5 hx26_5 hx29_5
  refine SepWPp.of_sepWP_ret (SepWP.done hpc5 hrun5 ?_)
  intro hmf5
  refine ⟨hpc5, hrun5, htr5, hvregs5, hcrl5, hsp5, hsp_align5, hx29_5,
    hx19_5, hx20_5, hx24_5, hx21_5, hx22_5, hx25_5, hx26_5,
    hOk, hlen_pay, ?_⟩
  rw [chainGAfter_succ_of_key hk hfl,
    prostChainGAt_eq_keys_sep_rest A0 x.a { chainGAfter x.c k with keys := (chainGAfter x.c k).keys ++ [mk] },
    prostChainGRest_update_keys,
    chainMergeSavedRegs_eq_split s0.sp s0,
    ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx v1 v2 rest hpay_eq]
  exact Satisfies.mono (by sep_frame) hmf5

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
