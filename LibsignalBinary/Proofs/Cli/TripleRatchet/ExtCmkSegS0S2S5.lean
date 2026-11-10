/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSeams
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplit
import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Core
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segments `S0`, `S2`, and `S5` for `consume_message_key`

Proves the entry dispatch (`S0`), too-far-in-future error return (`S2`), and store-loop panic
tails (`S5`) of `RatchetState::consume_message_key` on `SP2Ext img.base ext`.
-/

@[expose] public section

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

theorem L1_SegS0S2S5 : True := trivial

/-! ## Segment S0 -/

section S0X

open CryptoVerification.LibsignalSession.PrologueSplit

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_sub_lit ProofLib.bv_sub_add_lit

private theorem s0_past_wp_x (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry img) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret) (hlt : x.counter < x.ck.index) :
    SepWP (SP2Ext img.base ext) (cmkTakePC img) s0
      (prologueSplitActive img x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActive img x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTakeRegs x s0 sf) := by
  have hfn := cmkEntry_eq_sp2_fnAddr himg ext
  unfold cmkTakePC
  rw [hfn] at hpc ⊢
  prologueSplit_fetches_range img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") 57048 0 92
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have h_not_ule : ¬(BitVec.ule x.ck.index x.counter = true) := by
    simp [BitVec.ule_iff_toNat_le, BitVec.lt_def] at hlt ⊢; omega
  dsimp only [prologueSplitActive]
  wp_steps
  refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold CmkTakeRegs
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem s0_tooFar_wp_x (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry img) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx4 : (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType)
    (hx8 : s0.readReg64 .x8 = x.ret) (hle : x.ck.index ≤ x.counter) :
    SepWP (SP2Ext img.base ext) (cmkTooFarPC img) s0
      (prologueSplitActive img x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActive img x s0 v368 x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkTooFarRegs x s0 sf) := by
  have hfn := cmkEntry_eq_sp2_fnAddr himg ext
  unfold cmkTooFarPC
  rw [hfn] at hpc ⊢
  prologueSplit_fetches_range img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") 57048 0 76
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have h_ule : BitVec.ule x.ck.index x.counter = true := by
    simp [BitVec.ule_iff_toNat_le, BitVec.le_def] at hle ⊢; omega
  dsimp only [prologueSplitActive]
  wp_steps
  refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold CmkTooFarRegs
  refine ⟨hx2, hx4, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
private theorem s0_advance_wp_x (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (s0 : State)
    (v368 : BitVec 64) (v356 : BitVec 32)
    (v352 v344 : BitVec 64) (v332 : BitVec 32) (v328 : BitVec 64)
    (v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64)
    (hpc : s0.pc = cmkEntry img) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.self) (hx1 : s0.readReg64 .x1 = x.theirA)
    (hx2 : s0.readReg64 .x2 = x.ckA) (hx3 : (s0.readReg64 .x3).setWidth 32 = x.counter)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hmax : x.st.maxForwardJumps < 2 ^ 64)
    (hle : x.ck.index ≤ x.counter)
    (hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps) :
    let targetPC := if x.ck.index < x.counter then cmkLoopPC img else cmkEpiloguePC img
    SepWP (SP2Ext img.base ext) targetPC s0
      (prologueSplitActive img x s0 v368 v356 v352 v344 v332 v328
        v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8)
      (fun sf P_f =>
        P_f = prologueSplitActive img x s0 x.ret x.counter
          (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index ((x.counter - x.ck.index).zeroExtend 64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        CmkLoopRegs x x.ck s0 sf ∧
        (targetPC = cmkLoopPC img → sf.readReg64 .x19 = 1#64)) := by
  intro targetPC
  have hfn := cmkEntry_eq_sp2_fnAddr himg ext
  rw [hfn] at hpc
  prologueSplit_fetches_range img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") 57048 0 76
  prologueSplit_fetches_range img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") 57048 368 20
  prologueSplit_fetches_range img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") 57048 628 32
  prologueSplit_fetches_range img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") 57048 804 16
  have hadrp :
      (((SP2Ext img.base ext).fnAddr cmkName + 644#64) &&&
        0xfffffffffffff000#64) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) = logFilterAddr img := by
    have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, cmkName, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]
    simp only [logFilterAddr, BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  have hsp480 : (s0.sp - 480#64) &&& 15#64 = 0#64 := beq_iff_eq.mp (s0.spAligned_sub 480#64 hsp)
  have h_ule : BitVec.ule x.ck.index x.counter = true := by
    simp [BitVec.ule_iff_toNat_le, BitVec.le_def] at hle ⊢; omega
  have h_jump_ule :
      BitVec.ule (BitVec.zeroExtend 64 (x.counter - x.ck.index))
        (BitVec.ofNat 64 x.st.maxForwardJumps) = true := by
    have := (x.counter - x.ck.index).isLt
    rw [BitVec.ule_iff_toNat_le, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  dsimp only [targetPC]
  by_cases hck_lt : x.ck.index < x.counter
  · simp only [hck_lt, ↓reduceIte]
    unfold cmkLoopPC
    rw [hfn]
    generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
    have h_not_ck_ule : ¬(BitVec.ule x.counter x.ck.index = true) := by
      simp [BitVec.ule_iff_toNat_le, BitVec.lt_def] at hck_lt ⊢; omega
    dsimp only [prologueSplitActive]
    by_cases h25000 : BitVec.ule (x.counter - x.ck.index) 25000#32 = true
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hck_lt, ↓reduceIte]
    unfold cmkEpiloguePC cmkLoopPC
    rw [hfn]
    generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
    have h_loop_ne : entry + bv% (1244) ≠ entry + bv% (820) := by
      intro h
      have h2 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
      omega
    have h_ck_ule : BitVec.ule x.counter x.ck.index = true := by
      simp [BitVec.ule_iff_toNat_le, BitVec.le_def, BitVec.lt_def] at hle hck_lt ⊢; omega
    dsimp only [prologueSplitActive]
    by_cases h25000 : BitVec.ule (x.counter - x.ck.index) 25000#32 = true
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun h => absurd h h_loop_ne⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩
    · wp_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun h => absurd h h_loop_ne⟩
      unfold CmkLoopRegs
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem s0_past_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS0PastSpecX F A ext img := by
  intro himg x R s0 hpc hrun hsp hpre hlt
  have hpre' := (cmkSpecX_pre_iff x R s0).mp hpre
  obtain ⟨hfrozen, hsym, hx0, hx1, hx2, hx3, _, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    cmkPre_unpack hpre'
  have hwp := s0_past_wp_x ext img himg x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hlt
  refine reaches_pc_mono
    (reaches_pc_callInv ⟨hfrozen, hsym⟩ (SepWP.to_reaches_pc hwp hm)) ?_
  rintro sf hpc_sf hrun_sf
    ⟨⟨P_f, hm_sf, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf⟩, hfrozen_sf, hsym_sf⟩
  refine ⟨hpc_sf, ?_, hregs_sf, ?_⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hfrozen_sf, hsym_sf, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← sepConj_assoc] at hm_sf
    exact Satisfies.mono
      (sepConj_mono_left (prologueSplitActive_entails_preLoopHeap A img x s0 v368 x.counter
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328 hchains hpad hmax))
      hm_sf

theorem s0_tooFar_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS0TooFarSpecX F A ext img := by
  intro himg x R s0 hpc hrun hsp hpre hle
  have hpre' := (cmkSpecX_pre_iff x R s0).mp hpre
  obtain ⟨hfrozen, hsym, hx0, hx1, hx2, hx3, hx4, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    cmkPre_unpack hpre'
  have hwp := s0_tooFar_wp_x ext img himg x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx4 hx8 hle
  refine reaches_pc_mono
    (reaches_pc_callInv ⟨hfrozen, hsym⟩ (SepWP.to_reaches_pc hwp hm)) ?_
  rintro sf hpc_sf hrun_sf
    ⟨⟨P_f, hm_sf, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf⟩, hfrozen_sf, hsym_sf⟩
  refine ⟨hpc_sf, ?_, hregs_sf, ?_⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hfrozen_sf, hsym_sf, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← sepConj_assoc] at hm_sf
    exact Satisfies.mono
      (sepConj_mono_left (prologueSplitActive_entails_preLoopHeap A img x s0 v368 x.counter
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index v328 hchains hpad hmax))
      hm_sf

theorem s0_advance_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS0AdvanceEntrySpecX F A ext img := by
  intro himg x R s0 hpc hrun hsp hpre hle hj targetPC
  have hpre' := (cmkSpecX_pre_iff x R s0).mp hpre
  obtain ⟨hfrozen, hsym, hx0, hx1, hx2, hx3, _, hx8, hchains, hpad, hmax,
    v368, v356, v352, v344, v332, v328, v96, v88, v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, hm⟩ :=
    cmkPre_unpack hpre'
  have hwp := s0_advance_wp_x ext img himg x s0
    v368 v356 v352 v344 v332 v328 v96 v88 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8
    hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hmax hle hj
  refine reaches_pc_mono
    (reaches_pc_callInv ⟨hfrozen, hsym⟩ (SepWP.to_reaches_pc hwp hm)) ?_
  rintro sf hpc_sf hrun_sf
    ⟨⟨P_f, hm_sf, rfl, hsp_sf, hx29_sf, htr_sf, hvregs_sf, hregs_sf, hx19_sf⟩, hfrozen_sf, hsym_sf⟩
  refine ⟨hpc_sf, ?_, hregs_sf, hx19_sf, ?_⟩
  · refine ⟨hrun_sf, hsp_sf, hsp, ?_, hx29_sf, htr_sf, hfrozen_sf, hsym_sf, hvregs_sf⟩
    unfold State.spAligned
    rw [hsp_sf]
    exact s0.spAligned_sub 480#64 hsp
  · rw [← sepConj_assoc] at hm_sf
    exact Satisfies.mono
      (sepConj_mono_left (prologueSplitActive_entails_loopHeap A img x s0
        (s0.readReg64 .x5) (s0.readReg64 .x6) x.ck.index
        ((x.counter - x.ck.index).zeroExtend 64) hchains hpad hmax))
      hm_sf

end S0X

/-! ## Segment S2 -/

section S2X

open CryptoVerification.LibsignalSession.TooFarPath

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private def cmkPreLoopHeapX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 20000 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

private theorem cmkPreLoopHeap_sep_low_eq (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (s0 : State) (R : SepProp) :
    cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R) =
      cmkPreLoopHeapX A img x s0 ∗ R := by
  unfold cmkPreLoopHeap cmkPreLoopHeapX
  rw [← stackAt_7712_sep_low_eq_20000 s0.sp]
  ac_rfl

private def s2PostX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
  ratchetAt A x.self x.G x.st ∗
  consumeMessageKeyResultAt A x.ret (.error (.invalidMessage x.msgType .tooFarInFuture)) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ckA 36 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt s0.sp cmkStackX ∗
  A.pool

private def s2PostRawX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (s0 : State) (p : BitVec 64)
    (sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
  (((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 x.st.maxForwardJumps) ∗ ratchetRest A x.self x.G x.st) ∗
  (A.live p 36 1 ∗
   (p ↦₆₄ 0x206567617373656d#64) ∗ ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
   ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗ ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
   ((p + 32#64) ↦₃₂ 0x65727574#32) ∗
   (x.ret ↦₃₂ 2#32) ∗ memRegion (x.ret + 4#64) 4 ∗
   ((x.ret + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
   ((x.ret + 16#64) ↦₆₄ 36#64) ∗ ((x.ret + 24#64) ↦₆₄ p) ∗ ((x.ret + 32#64) ↦₆₄ 36#64) ∗
   ((x.ret + 40#64) ↦₈ msgTypeByte x.msgType) ∗ memRegion (x.ret + 41#64) 47) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  (memRegion (s0.sp - 20480#64) 3616 ∗
   stackAt (s0.sp - 480#64) extHookStack ∗
   memRegion (s0.sp - 480#64) 152 ∗
   ((s0.sp - 328#64) ↦₆₄ (x.counter - x.ck.index).zeroExtend 64) ∗
   memRegion (s0.sp - 320#64) 224 ∗
   cmkSavedRegs s0.sp s0) ∗
  A.pool

private theorem stackAt_cmkStackX_reassemble (sp0 : BitVec 64) (s0 : State) (v9 : BitVec 64) :
    (memRegion (sp0 - 20480#64) 3616 ∗
     stackAt (sp0 - 480#64) extHookStack ∗
     memRegion (sp0 - 480#64) 152 ∗
     ((sp0 - 328#64) ↦₆₄ v9) ∗
     memRegion (sp0 - 320#64) 224 ∗
     cmkSavedRegs sp0 s0) ⊢
    stackAt sp0 cmkStackX := by
  have h1 : memRegion (sp0 - 20480#64) 3616 ∗ stackAt (sp0 - 480#64) extHookStack =
      cmkLowStack sp0 ∗ (memRegion (sp0 - 8192#64) 3616 ∗ stackAt (sp0 - 480#64) allocHookStack) := by
    rw [← stackAt_20000_split_extHook sp0, ← stackAt_7712_sep_low_eq_20000 sp0,
        stackAt_7712_split sp0, sepConj_comm]
  have hreord :
      (memRegion (sp0 - 20480#64) 3616 ∗
       stackAt (sp0 - 480#64) extHookStack ∗
       memRegion (sp0 - 480#64) 152 ∗
       ((sp0 - 328#64) ↦₆₄ v9) ∗
       memRegion (sp0 - 320#64) 224 ∗
       cmkSavedRegs sp0 s0) =
      ((memRegion (sp0 - 8192#64) 3616 ∗
        stackAt (sp0 - 480#64) allocHookStack ∗
        memRegion (sp0 - 480#64) 152 ∗
        ((sp0 - 328#64) ↦₆₄ v9) ∗
        memRegion (sp0 - 320#64) 224 ∗
        cmkSavedRegs sp0 s0) ∗ cmkLowStack sp0) := by
    rw [← sepConj_assoc (memRegion (sp0 - 20480#64) 3616), h1]
    ac_rfl
  rw [hreord, stackAt_cmkStackX_eq_cmkStack_sep_low sp0]
  exact sepConj_mono_left (stackAt_cmkStack_reassemble sp0 s0 v9)

private theorem s2PostRawX_entails_s2PostX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (s0 : State) (p : BitVec 64) (hp : p ≠ 0) (sf : State) :
    s2PostRawX A img x s0 p sf ⊢ s2PostX A img x s0 sf := by
  unfold s2PostRawX s2PostX
  apply sepConj_mono_right
  refine sepConj_mono (ratchetAt_mfj_intro A x.self x.G x.st) ?_
  refine sepConj_mono (resultAt_tooFar_words_intro A x.ret p x.msgType hp) ?_
  apply sepConj_mono_right
  refine sepConj_mono (chainKeyBytes_entails_memRegion x.ckA x.ck) ?_
  apply sepConj_mono_right
  refine sepConj_mono (stackAt_cmkStackX_reassemble s0.sp s0 ((x.counter - x.ck.index).zeroExtend 64))
    (Entails.refl _)

private theorem s2PostX_entails_cmkSpecX {F : ShaCompress}
    {A : RustAlloc} {img : Obj.Image} {x : ConsumeMessageKeyGhost}
    (hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture))
    (hm2 : (x.model F).2 = x.st)
    (htouch : x.touched F = none)
    (s0 sf : State) :
    s2PostX A img x s0 sf ⊢ (cmkSpecX F A img).post x s0 sf := by
  unfold s2PostX cmkSpecX Spec.inImage
  dsimp only
  rw [hm1, hm2, htouch]
  apply Entails.pure_left
  intro htr
  apply Entails.pure_right ⟨by nofun, htr⟩
  apply sepConj_mono_left
  refine Entails.trans ?_ (Entails.sepExists_intro x.G)
  exact Entails.pure_right (RatchetGhost.AgreeExcept.refl x.G none) (Entails.refl _)

set_option maxHeartbeats 1200000 in
theorem s2_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS2SpecX F A ext img := by
  intro hA himg x R s0 s hle hjump hstate
  rcases hstate with
    ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hfrozen, hsymtab, hvregs⟩,
     ⟨hx2, hx4, hx9, hx20, hx22, hx23, hx26, hx27, hx28⟩, hmem⟩
  rw [cmkPreLoopHeap_sep_low_eq] at hmem
  have hmodel : x.model F = (.error (.invalidMessage x.msgType .tooFarInFuture), x.st) :=
    consumeMessageKey_tooFar F x.st x.their x.ck x.counter x.msgType hle hjump
  have hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture) := by rw [hmodel]
  have hm2 : (x.model F).2 = x.st := by rw [hmodel]
  have htouch : x.touched F = none := by unfold ConsumeMessageKeyGhost.touched; rw [hm1]
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hshim := shim_ok_at_x hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have halloc := alloc_ok_at_x hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  unfold Spec.inImage Proofs.libsignal.Stage1X.session2ShimSpecX at hshim
  unfold Spec.inImage Proofs.libsignal.Stage1X.rustAllocSpecWithStack at halloc
  tooFarPath_fetches_range img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 368 36
  tooFarPath_fetches_range img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 540 88
  tooFarPath_fetches_range img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 1916 32
  tooFarPath_fetches_range img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 2548 12
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hfn_addr : (SP2Ext img.base ext).fnAddr cmkName = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := by
    rw [Program.fnAddr_rebase, cmkName, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 368#64 := by
    rw [hpc, cmkTooFarPC, cmkEntry_eq himg, hfn_addr]
  clear hpc
  have hpc := hpc'
  clear hpc'
  have hadrp1 : ((((SP2Ext img.base ext).fnAddr cmkName + 388#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = logFilterAddr img := by
    rw [hfn_addr]; exact adrp_logFilter hb
  have hadrp2 : (((SP2Ext img.base ext).fnAddr cmkName + 564#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (ls_str% "message from too far into the future" - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) = img.base + bv% (ls_str% "message from too far into the future") := by
    rw [hfn_addr]; bv_arith
  clear hfn_addr
  have hro : img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.mp hfrozen).2.1
  have hmem_ro : s.mem ⊨ (((img.base + bv% (ls_str% "message from too far into the future")) ↦ᵣ tooFarInFutureStr) ∗ cmkPreLoopHeapX A img x s0) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_tooFarInFuture_intro himg hro hmem
  clear hmem
  refine reaches_outcome_of_sepWPp_post
    (Drop := ((img.base + bv% (ls_str% "message from too far into the future")) ↦₆₄ᵣ 0x206567617373656d#64) ∗
      ((img.base + bv% (ls_str% "message from too far into the future" + 8)) ↦₆₄ᵣ 0x6f6f74206d6f7266#64) ∗
      ((img.base + bv% (ls_str% "message from too far into the future" + 16)) ↦₆₄ᵣ 0x746e692072616620#64) ∗
      ((img.base + bv% (ls_str% "message from too far into the future" + 24)) ↦₆₄ᵣ 0x756620656874206f#64) ∗
      ((img.base + bv% (ls_str% "message from too far into the future" + 32)) ↦₃₂ᵣ 0x65727574#32))
    (Post := s2PostX A img x s0)
    hmem_ro (s2PostX_entails_cmkSpecX hm1 hm2 htouch s0) ?_
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s := ⟨hfrozen, hsymtab⟩
  clear hfn himg hro hA hmodel hm1 hm2 htouch hfrozen hsymtab hmem_ro
  unfold cmkPreLoopHeapX cmkSavedRegs
  rw [pointsToBytesRO_tooFarInFutureStr (img.base + bv% (ls_str% "message from too far into the future")),
      ratchetAt_split_mfj A x.self x.G x.st,
      memRegion_88_ret_split x.ret,
      stackAt_20000_split_extHook s0.sp,
      memRegion_384_tooFarPath_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r40 => SepWPp.exists_elim fun r32 =>
    SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r16 =>
    SepWPp.exists_elim fun r8 => SepWPp.exists_elim fun r0 =>
    SepWPp.exists_elim fun v9 => ?_
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  have hcs := cs_maxForwardJumps_eq_false hjump
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  apply _root_.ProofLib.SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) hinv0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply _root_.ProofLib.SepWPp.of_sepWP_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  rintro ⟨hF2, hsym2⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (556))
  wp_call halloc (36, 1)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  rw [sepConj_left_comm (stackAt _ extHookStack), sepConj_left_comm A.pool]
  by_cases hoom : sf_1.readReg64 .x0 = 0#64
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    have htr_oom :
        (Rust.panicked
          ((((sf_1.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 36#64).writeReg64
                (Reg.gpr 30#5) (entry + bv% (2560))).setPC
            (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")))).trace = s0.trace ++ [allocFailedEvent] := by
      simp only [Rust.panicked, wp_norm, arm64_norm, *]
    simpa only [sepConj_assoc] using
      allowPanic_panicked (CryptoVerification.LibsignalSession.TooFarPath.allocFailedIn_of_eq htr_oom) hm
  · have hoom' : sf_1.readReg64 .x0 ≠ 0 := hoom
    have hcbz_oom : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [hoom', ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrace_ok⟩ => ?_
    rw [memRegion_36_split (sf_1.readReg64 .x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p4 => SepWPp.exists_elim fun p3 =>
      SepWPp.exists_elim fun p2 => SepWPp.exists_elim fun p1 =>
      SepWPp.exists_elim fun p0 => ?_
    apply SepWPp.of_sepWP_ret
    apply SepWP.conseq_tooFarPathPost (s2PostRawX_entails_s2PostX A img x s0 (sf_1.readReg64 .x0) hoom')
    unfold s2PostRawX cmkSavedRegs
    wp_steps
    rw [hsp_sf, hsp]
    wp_done

end S2X

/-! ## Segment S5 -/

section S5X

open CryptoVerification.LibsignalSession.PanicPaths

open Lean Elab Tactic in
local elab "session_slice_fetches_x " b:term:max H:term:max hfn:ident
    off:term:max kstart:num len:num : tactic => do
  let offVal ← CryptoVerification.CodeLayout.evalNat off "session_slice_fetches_x"
  let offStx := Syntax.mkNumLit (toString offVal)
  evalTactic (← `(tactic| code_fetches_range libsignalSessionCode CryptoVerification.LibsignalSession.PanicPaths.libsignalSessionBin $b $H $hfn $offStx $kstart $len))

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private def cmkS5UsedX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State)
    (b0 : BitVec 8) (u1 u2 u3 : BitVec 64) : SepProp :=
  ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length) ∗
  arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) hmacStackX ∗
  ((s0.sp - 320#64) ↦₈ b0) ∗
  memRegion (s0.sp - 319#64) 7 ∗
  ((s0.sp - 312#64) ↦₆₄ u1) ∗
  ((s0.sp - 304#64) ↦₆₄ u2) ∗
  ((s0.sp - 296#64) ↦₆₄ u3) ∗
  memRegion (s0.sp - 224#64) 32 ∗
  A.pool

private theorem cmkLoopHeap_decompose_s5_x {A : RustAlloc} {img : Obj.Image} {x : ConsumeMessageKeyGhost}
    {Gc : RatchetGhost} {stc : RatchetState} {ckc : ChainKey} {s0 : State}
    {R : SepProp} {m : Memory}
    (h : m ⊨ cmkLoopHeap A img x Gc stc ckc s0 ∗ (cmkLowStack s0.sp ∗ R)) :
    ∃ (b0 : BitVec 8) (u1 u2 u3 : BitVec 64) (R_unused : SepProp),
      Gc.chains.length = stc.receiverChains.length ∧
      (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 ∧
      (m ⊨ cmkS5UsedX A img x Gc stc ckc s0 b0 u1 u2 u3 ∗ (R_unused ∗ R)) := by
  have h20000 : cmkLoopHeap A img x Gc stc ckc s0 ∗ (cmkLowStack s0.sp ∗ R) =
      (ratchetAt A x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 20000 ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) ∗ R := by
    unfold cmkLoopHeap
    rw [← stackAt_7712_sep_low_eq_20000 s0.sp]
    ac_rfl
  rw [h20000] at h
  unfold chainKeyBytes cmkLoopFrame at h
  rw [pointsToBytes_append, stackAt_20000_split_hmacX s0.sp, memRegion_frame_panicPaths s0.sp] at h
  have h' := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_panicPaths A x.self Gc stc))) h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at h'
  obtain ⟨b0, u1, u2, u3, ⟨hlen, hxs_lt⟩, hm⟩ := h'
  refine ⟨b0, u1, u2, u3,
    ((x.self ↦₆₄ Gc.chainsCap) ∗
      (if Gc.chainsCap = 0 then emp
       else A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
         memRegion (Gc.chainsPtr + BitVec.ofNat 64 ((Gc.chains.zip stc.receiverChains).length * 104))
           ((Gc.chainsCap.toNat - (Gc.chains.zip stc.receiverChains).length) * 104)) ∗
      ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
      ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
      ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
      ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
      ((x.ckA + BitVec.ofNat 64 (keyToBytes32 ckc.key).length) ↦ₛ leBytes 4 ckc.index.toNat) ∗
      memRegion x.ret 88 ∗
      memRegion (s0.sp - 20480#64) 1568 ∗
      memRegion (s0.sp - 480#64) 112 ∗ ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
      memRegion (s0.sp - 360#64) 4 ∗ ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
      memRegion (s0.sp - 352#64) 32 ∗ memRegion (s0.sp - 288#64) 64 ∗
      memRegion (s0.sp - 192#64) 96 ∗ cmkSavedRegs s0.sp s0),
    hlen, hxs_lt, ?_⟩
  unfold cmkS5UsedX
  convert hm using 1
  ac_rfl

private theorem call_hmac_x {prog : Program} {img : Obj.Image}
    {F : ShaCompress}
    {ret entry : BitVec 64} (ret_pc out ka : BitVec 64) (key : List (BitVec 8))
    (ia : BitVec 64) (inp : List (BitVec 8)) (sp0 : BitVec 64)
    {s : State} {P Fr : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry ((hmacSpecX F).inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = ka)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = ia)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hklen : key.length = 32) (hilen : inp.length = 1)
    (hframe : SepFrame (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 hmacStackX) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 hmacStackX ∗ Fr) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_wpp_frozen (x := (out, ka, key, ia, inp)) (F := Fr)
    hcall hF hsym hpc hrun hsp_align hlr
    (fun R hm => by
      simp only [Spec.inImage, hmacSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, by simp [hx2, hklen], hx3, by simp [hx4, hilen], hklen, hilen⟩, ?_⟩
      have hm' := hm
      rw [hframe.eq] at hm'
      exact Satisfies.of_eq hm')
    (fun sf code R' _ hex => by
      simp only [Spec.inImage, hmacSpecX] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ ⟨R', hpan⟩ => by
      simp only [Spec.inImage, hmacSpecX] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    (fun sm hpcm hrunm hspm hcsm hFm hsymm => by
      have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
      rw [hsp] at hspm
      simp only [Spec.inImage, hmacSpecX, hsp, sepConj_assoc]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (SepWPp.pure_elim fun htrm =>
          hnext sm hpcm hrunm hspm hsp_sm htrm hFm hsymm hcsm))
    (hoom := fun sf R' _ ho => by
      simp only [Spec.inImage, hmacSpecX] at ho
      exact (not_satisfies_false_sepConj ho).elim)

private theorem call_findIndex_none_x {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {ret entry : BitVec 64} (ret_pc p theirA sp0 : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) (their : PublicKey)
    {s : State} {P Fr : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry ((findIndexSpecX img A).inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length)
    (hx2 : s.readReg64 .x2 = theirA)
    (hlen : Gc.chains.length = stc.receiverChains.length)
    (hxs_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63)
    (hnone : stc.findReceiverChainIndex their = none)
    (hframe : SepFrame
      (arrayAt (chainAt A) 104 p (Gc.chains.zip stc.receiverChains) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt sp0 hmacStackX) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 →
      SepWPp prog ret sf P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := ProofLib.stackAt_split_bottom sp0 17408 1024 (by decide)
  change stackAt sp0 hmacStackX = memRegion (sp0 - 18432#64) 1024 ∗ stackAt sp0 findIndexStackX at h_stk
  have hx1' : (s.readReg64 .x1).toNat = (Gc.chains.zip stc.receiverChains).length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.call_wpp_frozen
    (x := (p, Gc.chains.zip stc.receiverChains, theirA, their))
    (F := memRegion (sp0 - 18432#64) 1024 ∗ Fr)
    hcall hF hsym hpc hrun hsp_align hlr
    (fun R hm => by
      simp only [Spec.inImage, findIndexSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1', hx2, hxs_lt⟩, ?_⟩
      have hm' := hm
      rw [hframe.eq, h_stk] at hm'
      exact Satisfies.of_eq hm')
    (fun sf code R' _ hex => by
      simp only [Spec.inImage, findIndexSpecX] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ ⟨R', hpan⟩ => by
      simp only [Spec.inImage, findIndexSpecX] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    (fun sm hpcm hrunm hspm hcsm hFm hsymm => by
      have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
      rw [hsp] at hspm
      have hmap : (Gc.chains.zip stc.receiverChains).map (·.2) = stc.receiverChains :=
        List.map_snd_zip (Nat.le_of_eq hlen.symm)
      simp only [Spec.inImage, findIndexSpecX, hsp, hmap,
        show List.findIdx? (fun c : ReceiverChain => c.senderRatchetKey == their) stc.receiverChains =
          stc.findReceiverChainIndex their from rfl,
        hnone, sepConj_assoc]
      apply SepWPp.pure_elim
      rintro ⟨htrm, hx0_sm⟩
      exact SepWPp.weaken_pre (Entails.of_eq (by rw [hframe.eq, h_stk]; ac_rfl))
        (hnext sm hpcm hrunm hspm hsp_sm htrm hFm hsymm hcsm hx0_sm))
    (hoom := fun sf R' _ ho => by
      simp only [Spec.inImage, findIndexSpecX] at ho
      exact (not_satisfies_false_sepConj ho).elim)

private theorem call_shim_x {prog : Program} {img : Obj.Image}
    {ret entry : BitVec 64} (ret_pc sp0 : BitVec 64)
    {s : State} {P Fr : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hframe : SepFrame (stackAt sp0 hmacStackX) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := ProofLib.stackAt_split_bottom sp0 16384 2048 (by decide)
  change stackAt sp0 hmacStackX = memRegion (sp0 - 18432#64) 2048 ∗ stackAt sp0 extHookStack at h_stk
  refine SepWPp.call_wpp_frozen (x := ()) (F := memRegion (sp0 - 18432#64) 2048 ∗ Fr)
    hcall hF hsym hpc hrun hsp_align hlr
    (fun R hm => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack,
        emp_sepConj, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF, hsym⟩, ?_⟩
      have hm' := hm
      rw [hframe.eq, h_stk] at hm'
      exact Satisfies.of_eq hm')
    (fun sf code R' _ hex => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ ⟨R', hpan⟩ => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    (fun sm hpcm hrunm hspm hcsm hFm hsymm => by
      have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
      rw [hsp] at hspm
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, Spec.withHookStack,
        hsp, sepConj_assoc]
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [hframe.eq, h_stk]; ac_rfl))
        (SepWPp.pure_elim fun htrm =>
          hnext sm hpcm hrunm hspm hsp_sm htrm hFm hsymm hcsm))
    (hoom := fun sf R' _ ho => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.session2ShimSpecX] at ho
      exact (not_satisfies_false_sepConj ho).elim)

private theorem call_alloc_32_x {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {ret entry : BitVec 64} (ret_pc sp0 : BitVec 64)
    {s : State} {P Fr : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A extHookStack).inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 32#64)
    (hx1 : s.readReg64 .x1 = 1#64)
    (hframe : SepFrame (A.pool ∗ stackAt sp0 hmacStackX) P Fr)
    (hfail : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true →
      sf.trace = s.trace ++ [allocFailedEvent] →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 →
      SepWPp prog ret sf P Q Qp)
    (hsucc : ∀ (sf : State) (a0 a1 a2 a3 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf → (sf.readReg64 .x0 == 0#64) = false →
      SepWPp prog ret sf
        ((sf.readReg64 .x0 ↦₆₄ a0) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ a1) ∗
         ((sf.readReg64 .x0 + 16#64) ↦₆₄ a2) ∗ ((sf.readReg64 .x0 + 24#64) ↦₆₄ a3) ∗
         A.live (sf.readReg64 .x0) 32 1 ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := ProofLib.stackAt_split_bottom sp0 16384 2048 (by decide)
  change stackAt sp0 hmacStackX = memRegion (sp0 - 18432#64) 2048 ∗ stackAt sp0 extHookStack at h_stk
  have hlayout : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine SepWPp.call_wpp_frozen (x := (32, 1)) (F := memRegion (sp0 - 18432#64) 2048 ∗ Fr)
    hcall hF hsym hpc hrun hsp_align hlr
    (fun R hm => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF, hsym⟩, ⟨by simp [hx0], by simp [hx1], hlayout⟩, ?_⟩
      have hm' := hm
      rw [hframe.eq, h_stk] at hm'
      exact Satisfies.of_eq hm')
    (fun sf code R' _ hex => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ ⟨R', hpan⟩ => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    (fun sm hpcm hrunm hspm hcsm hFm hsymm => by
      have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
      rw [hsp] at hspm
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack, hsp]
      by_cases hx0_z : sm.readReg64 .x0 = 0
      · simp only [hx0_z, ↓reduceIte]
        refine SepWPp.weaken_pre (Entails.of_eq (by rw [hframe.eq, h_stk]; ac_rfl))
          (SepWPp.pure_elim fun htrm =>
            hfail sm hpcm hrunm hspm hsp_sm htrm hFm hsymm hcsm hx0_z)
      · simp only [hx0_z, ↓reduceIte]
        have hc4 : memRegion (sm.readReg64 .x0) 32 =
            ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
              ((sm.readReg64 .x0) ↦₆₄ a0) ∗ ((sm.readReg64 .x0 + 8#64) ↦₆₄ a1) ∗
              ((sm.readReg64 .x0 + 16#64) ↦₆₄ a2) ∗ ((sm.readReg64 .x0 + 24#64) ↦₆₄ a3) := by
          have ha1 : sm.readReg64 .x0 + 8#64 + 8#64 = sm.readReg64 .x0 + 16#64 := by
            rw [BitVec.add_assoc]; rfl
          have ha2 : sm.readReg64 .x0 + 16#64 + 8#64 = sm.readReg64 .x0 + 24#64 := by
            rw [BitVec.add_assoc]; rfl
          rw [show (32 : Nat) = 8 * 4 from rfl, ProofLib.memRegion_cells _ 4 (by decide)]
          simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right, ha1, ha2]
        rw [hc4]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
          SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 => ?_
        simp only [sepConj_assoc]
        apply SepWPp.pure_elim
        rintro ⟨_, htrm⟩
        have hx0_beq : (sm.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_z
        exact SepWPp.weaken_pre (Entails.of_eq (by rw [hframe.eq, h_stk]; ac_rfl))
          (hsucc sm a0 a1 a2 a3 hpcm hrunm hspm hsp_sm htrm hFm hsymm hcsm hx0_beq))
    (hoom := fun sf R' _ ho => by
      simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at ho
      exact (not_satisfies_false_sepConj ho).elim)

set_option maxHeartbeats 800000 in
theorem s5_epiloguePanic_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS5EpiloguePanicSpecX F A ext img := by
  intro himg hfind hhmac x Gc stc ckc R s0 s hidx hcond hpan hstate
  obtain ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hF, hsym, _⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _, hmem⟩ := hstate
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeap_decompose_s5_x hmem
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hhmac' := hmac_ok_at_x hhmac hfn (k := num% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  have hfind' := find_index_ok_at_x hfind hfn (k := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  have hpan_ovf := panic_at_add_overflow_x (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hpan_exp := panic_at_expect_failed_x (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "core::option::expect_failed" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  session_slice_fetches_x img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 1244 76
  session_slice_fetches_x img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 2460 48
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1244#64 := by
    rw [hpc, cmkEpiloguePC, cmkEntry_eq_sp2_fnAddr himg ext]
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkSpecX_onPanic_eq, cmkSpec_onPanic_eq]
  unfold cmkS5UsedX
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  apply ProofLib.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hF1 hsym1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 2#8]
  refine call_hmac_x (entry + bv% (1276)) (s0.sp - 224#64) x.ckA (keyToBytes32 ckc.key)
    (s0.sp - 320#64) [2#8] (s0.sp - 480#64) hhmac'
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hF1 hsym1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length ckc.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hF2 hsym2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : s1.readReg64 .x28 = BitVec.zeroExtend 64 ckc.index := by
    simpa [CalleeSavedPreserved, hx28, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1
  by_cases hc : x.counter = BitVec.allOnes 32
  · have hckc_max : ckc.index = 0xffffffff#32 := hidx.trans hc
    rw [hckc_max] at hx28_1
    apply ProofLib.SepWPp.of_sepWP_frozen hF2 hsym2
      (mid := entry + bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro _ _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) hpan_ovf hpan
      (by simp [htr1, htrace, arm64_norm])
  · have hnone : stc.findReceiverChainIndex x.their = none := hcond.resolve_left hc
    have hz2 : (x.counter + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hc; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := x.counter.isLt
      rw [BitVec.toNat_add] at h1
      change (x.counter.toNat + 1) % 4294967296 = 0 at h1
      change x.counter.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 ckc.key) [2#8])
    rw [hw32 (s0.sp - 224#64)]
    refine SepWPp.fold_cell64_320 (by wp_sep_access) fun u0 => ?_
    apply ProofLib.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro hF3 hsym3
    refine call_findIndex_none_x (entry + bv% (1312)) Gc.chainsPtr x.theirA (s0.sp - 480#64)
      Gc stc x.their hfind'
      (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
      (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
      hF3 hsym3 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hF4 hsym4 _ hx0_2
    apply ProofLib.SepWPp.of_sepWP_frozen hF4 hsym4
      (mid := entry + bv% (ls_off% "core::option::expect_failed" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    intro _ _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) hpan_exp hpan
      (by simp [htr2, htr1, htrace, arm64_norm])

set_option maxHeartbeats 800000 in
theorem s5_noChainLoop_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS5NoChainLoopSpecX F A ext img := by
  intro hA himg hfind hhmac x R s0 s _ hnone hpan hstate
  obtain ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hF, hsym, _⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hloop_x19, hmem⟩ := hstate
  have hx19 : s.readReg64 .x19 = 1#64 := hloop_x19 rfl
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeap_decompose_s5_x hmem
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hhmac' := hmac_ok_at_x hhmac hfn (k := num% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  have hfind' := find_index_ok_at_x hfind hfn (k := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  have hshim' := shim_ok_at_x hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have halloc' := alloc_ok_at_x hA (name := cmkName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hpan_oom := panic_at_handle_error_x (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  have hpan_exp := panic_at_expect_failed_x (b := img.base) (ext := ext) hfn
    (k := num% (ls_off% "core::option::expect_failed" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm])
  session_slice_fetches_x img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 820 88
  session_slice_fetches_x img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 2420 24
  session_slice_fetches_x img.base (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) 2484 12
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 820#64 := by
    rw [hpc, cmkLoopPC, cmkEntry_eq_sp2_fnAddr himg ext]
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkSpecX_onPanic_eq, cmkSpec_onPanic_eq]
  unfold cmkS5UsedX
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  apply ProofLib.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hF1 hsym1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 1#8]
  refine call_hmac_x (entry + bv% (848)) (s0.sp - 224#64) x.ckA (keyToBytes32 x.ck.key)
    (s0.sp - 320#64) [1#8] (s0.sp - 480#64) hhmac'
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hF1 hsym1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length x.ck.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hF2 hsym2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  apply ProofLib.SepWPp.of_sepWP_frozen hF2 hsym2
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
  intro hF3 hsym3
  refine call_shim_x (entry + bv% (852)) (s0.sp - 480#64) hshim'
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
    hF3 hsym3 (by simp [arm64_norm]) (by wp_sep_access) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hF4 hsym4 hcs2
  have hx23_2 : s2.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_1, arm64_norm] using hcs2.2.2.2.2.1
  have hx26_2 : s2.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_1, arm64_norm] using hcs2.2.2.2.2.2.2.2.1
  have hx27_2 : s2.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_1, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1
  apply ProofLib.SepWPp.of_sepWP_frozen hF4 hsym4
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
  intro hF5 hsym5
  refine call_alloc_32_x (entry + bv% (864)) (s0.sp - 480#64) halloc'
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simp [hsp2, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp2_align)
    hF5 hsym5 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (by wp_sep_access) ?_ ?_
  · intro s3 hpc3 hrun3 hsp3 hsp3_align htr3 hF6 hsym6 _ hx0_3
    apply ProofLib.SepWPp.of_sepWP_frozen hF6 hsym6
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    intro _ _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun3, arm64_norm]) hpan_oom hpan
      (by simp [htr3, htr2, htr1, htrace, arm64_norm])
  · intro s3 a0 a1 a2 a3 hpc3 hrun3 hsp3 hsp3_align htr3 hF6 hsym6 hcs3 hx0_3
    have hx23_3 : s3.readReg64 .x23 = x.self := by
      simpa [CalleeSavedPreserved, hx23_2, arm64_norm] using hcs3.2.2.2.2.1
    have hx26_3 : s3.readReg64 .x26 = x.theirA := by
      simpa [CalleeSavedPreserved, hx26_2, arm64_norm] using hcs3.2.2.2.2.2.2.2.1
    have hx27_3 : s3.readReg64 .x27 = s0.sp - 224#64 := by
      simpa [CalleeSavedPreserved, hx27_2, arm64_norm] using hcs3.2.2.2.2.2.2.2.2.1
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 x.ck.key) [1#8])
    rw [hw32 (s0.sp - 224#64)]
    apply ProofLib.SepWPp.of_sepWP_frozen hF6 hsym6 (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    intro hF7 hsym7
    refine call_findIndex_none_x (entry + bv% (900)) x.G.chainsPtr x.theirA (s0.sp - 480#64)
      x.G x.st x.their hfind'
      (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
      (by simp [hsp3, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp3_align)
      hF7 hsym7 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s4 hpc4 hrun4 hsp4 hsp4_align htr4 hF8 hsym8 _ hx0_4
    apply ProofLib.SepWPp.of_sepWP_frozen hF8 hsym8
      (mid := entry + bv% (ls_off% "core::option::expect_failed" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
    intro _ _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) hpan_exp hpan
      (by simp [htr4, htr3, htr2, htr1, htrace, arm64_norm])

end S5X

end Proofs.libsignal.Stage1X.CmkX
