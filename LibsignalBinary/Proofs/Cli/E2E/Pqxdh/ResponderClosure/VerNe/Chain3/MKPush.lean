/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.Cli.ShardFill.ChainMerge5Decode
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenReceiverChainsExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Push (`Chain3MkPushStmt`)

Verifies steps 4d + 4e (`+0x244 → +0x0a8`) of the tag-4 (`message_keys`) path: inner-loop exit when
`remaining == x25`, capacity check and conditional `grow_one<MessageKey>` call on `Vec<MessageKey>`
at `a + 0x30`, and 104-byte copy of the scratch `MessageKey` at `sp0 - 0xe8` to `ptr + len * 104`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg Arm64.calleeSavedVRegs_writeVReg128_ite Arm64.isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Alignment & `Vec<MessageKey>` helpers -/

set_option maxHeartbeats 400000 in
theorem c3mk_push_spAligned {s : State} {sp0 : BitVec 64} (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  exact sp_sub_240_aligned_receiverChains halign

private theorem c3mk_growOne_inImage_pre_eq (img : Obj.Image) (A : RustAlloc)
    (a cap ptr sp : BitVec 64) (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) :
    ((Stage1X.growOneChainSpecX A).inImage img).pre (a + 0x30#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = a + 0x30#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗ stackAt sp Stage1X.growOneChainStackX) := by
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  rw [growOne_inImage_pre_eq_extWA img A (a + 0x30#64) cap ptr sp bs s hsp, e38]

private theorem c3mk_growOne_post_elim_sp (img : Obj.Image) (A : RustAlloc)
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

private theorem c3mk_vecOf_keys_openA (A : RustAlloc) (a : BitVec 64) (keys : List MessageKeyGenerator) :
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

private theorem c3mk_vecBuf_keys_full_openA (A : RustAlloc) (cap ptr : BitVec 64)
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

private theorem c3mk_vecBuf_keys_not_full_openA (A : RustAlloc) (cap ptr : BitVec 64)
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

private theorem c3mk_vecOf_keys_push_foldA (A : RustAlloc) (a cap ptr : BitVec 64)
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

/-! ## 2. Step 4d (`+0x244 → +0x178`): inner exit and `grow_one` check -/

set_option maxHeartbeats 400000 in
theorem step_c3mk_push4d {A : RustAlloc} (img : Obj.Image) {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x244#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x178#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 → sm.spAligned = true →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace →
      Chain3MkRegs s sm →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = 104#64 →
      sm.readReg64 .x25 = BitVec.ofNat 64 keys.length →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          A.live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) keys ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R)) := by
  have hG' := c3_growOne_ok_sub hC
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false := bne_self_eq_false _
  chain3_fetches_range img.base (Rust.withPanics ext) 0x244 0x250
  chain3_fetches_range img.base (Rust.withPanics ext) 0x3fc 0x3fc
  chain3_fetches_range img.base (Rust.withPanics ext) 0x160 0x174
  dsimp only [SP2Ext, contractProg, chainMerge3Name, c3GrowOneName] at hG' hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  apply SepWPp.fold (c3mk_vecOf_keys_openA A a keys) (by sep_frame)
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    apply SepWPp.fold (c3mk_vecBuf_keys_full_openA A cap ptr keys hfull) (by sep_frame)
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_cap, hmov⟩
    have hbs_len : bs.length = keys.length * 104 := by rw [hbs_cap, hfull]
    conv => arg 4; rw [stackAt_c3Sub_to_growOne (sp0 - 0xf0#64)]
    have hmax_le : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
    conv => arg 4; unfold Prost.sliceCursorAt
    iterate 11 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine call_frame_inImage_receiverChains_ext (x := (a + 0x30#64, cap, ptr, bs))
      (ret_pc := entry + bv% (376)) hF1 hsym1 hG'
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) (by simp only [arm64_norm])
      (c3mk_growOne_inImage_pre_eq img A a cap ptr (sp0 - 0xf0#64) bs _ (by simp only [hsp, arm64_norm]))
      ⟨⟨hbs_cap, by simp only [arm64_norm], hptr, hmax_le⟩, hF1, hsym1⟩ (by sep_frame)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [htr, arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hFm hsymm
    have hregs_m : Chain3MkRegs s sm :=
      Chain3MkRegs.trans
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩
        (Chain3MkRegs.of_calleeSaved hcsm)
    have h20_m : sm.readReg64 .x20 = a := hregs_m.2.1.trans hx20
    have h24_m : sm.readReg64 .x24 = 104#64 := hregs_m.2.2.2.2.2.1.trans hx24
    have h25_m : sm.readReg64 .x25 = BitVec.ofNat 64 keys.length := by
      have h25_cs := hcsm.2.2.2.2.2.2.1
      simp only [arm64_norm] at h25_cs
      change sm.readReg64 (Reg.gpr 25#5) = _
      rw [h25_cs, hfull, BitVec.ofNat_toNat]; rfl
    have hspm' : sm.sp = sp0 - 0xf0#64 := by simpa only [hsp, arm64_norm] using hspm
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm'.trans hsp.symm) hsp_align
    refine SepWPp.fold (c3mk_growOne_post_elim_sp img A a cap ptr (sp0 - 0xf0#64) bs keys.length _ sm
      (by simp only [hsp, arm64_norm]) hfull hbs_len hbound) rfl ?_
    conv => arg 4; simp only [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [htr, arm64_norm] using htr_m
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro ptr'
    apply SepWPp.pure_left; rintro ⟨hcap'_le, hcap'_lt, hptr'⟩
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_c3Sub_to_growOne (sp0 - 0xf0#64)).symm) (by sep_frame)
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm cap' ptr' hcap'_le hcap'_lt hptr'
      hpcm hrunm hspm' hsp_align_m hFm hsymm htr_m' hregs_m h20_m h24_m h25_m)
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
    have hbne_cap : (BitVec.ofNat 64 keys.length != cap) = true := by
      rw [bne_iff_ne, ne_eq, ← beq_iff_eq, hbeq_cap]; decide
    conv => arg 4; rw [c3mk_vecBuf_keys_not_full_openA A cap ptr keys hcap_le' hcap_lt]
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (376)) hF hsym ?_
    conv => arg 4; unfold Prost.sliceCursorAt
    iterate 9 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap ptr hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
      hF1 hsym1 (by simp only [htr, arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm]⟩
      (by simp only [h20, arm64_norm])
      (by simp only [h24, arm64_norm])
      (by simp only [arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)

/-! ## 3. Step 4e (`+0x178 → +0x0a8`): 104-byte copy and length increment -/

set_option maxHeartbeats 400000 in
theorem step_c3mk_push4e {A : RustAlloc} (img : Obj.Image) {ext : String → Option (State → State)}
    (a cap' ptr' sp0 : BitVec 64) (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x178#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 keys.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 0xe8#64) 104) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A mk (sp0 - 0xe8#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length; have hadd1 := ofNat_add_one_eq keys.length
  chain3_fetches_range img.base (Rust.withPanics ext) 0x178 0x1c4
  chain3_fetches_range img.base (Rust.withPanics ext) 0x1f4 0x1f4
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 keys.length := hx25
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (168)) hF hsym ?_
  apply SepWP.fold (prostMsgKeyAt_move_chunks104 A (sp0 - 0xe8#64) mk) (by sep_frame)
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
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) d0 d1 d2 d3 d4 d5 dw6]
  iterate 21 wp_step
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains sp0 q0 q1 q2 q3 q4 q5 w6]
  apply SepWP.fold (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104))) (by sep_frame)
  apply SepWP.fold (chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 0xe8#64) q0 q1 q2 q3 q4 q5 w6) (by sep_frame)
  apply SepWP.fold (c3mk_vecOf_keys_push_foldA A a cap' ptr' keys mk hcap_le hcap_lt hptr) (by sep_frame)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 4. Main theorem: `chain3MkPush_ok_ext` and `chain3MkPush_ok` -/

set_option maxHeartbeats 400000 in
theorem chain3MkPush_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkPushStmtExt A img ext := by
  intro hC a bufRef slot ptr_rest sp0 keys mk rest x R s0 s F ret Q
    hbound hpc hrun hsp halign hF hsym htr hx19 hx20 hx24 hx25 hnext
  have hsp_align : s.spAligned = true := c3mk_push_spAligned hsp halign
  refine SepWPp.focus_pre
    (step_c3mk_push4d img hC a bufRef slot ptr_rest sp0 keys rest hbound
      hpc hrun hsp hsp_align hF hsym htr hx19 hx20 hx24 hx25 ?_)
  intro s4 cap' ptr' hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hF4 hsym4 htr4 hregs4 hx20_4 hx24_4 hx25_4
  refine SepWPp.focus_pre
    (step_c3mk_push4e img a cap' ptr' sp0 keys mk hcap'_le hcap'_lt hptr'
      hpc4 hrun4 hsp4 hsp_align4 hF4 hsym4 htr4 hx20_4 hx24_4 hx25_4 ?_)
  intro s5 hpc5 hrun5 hsp5 hF5 hsym5 htr5 hregs5
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 hsp5 hF5 hsym5 htr5 (hregs4.trans hregs5))
  exact sep_ac_seedChain (by ac_rfl)

theorem chain3MkPush_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkPushStmt img ext := by
  rw [← Chain3MkPushStmtExt_A0]
  exact chain3MkPush_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
