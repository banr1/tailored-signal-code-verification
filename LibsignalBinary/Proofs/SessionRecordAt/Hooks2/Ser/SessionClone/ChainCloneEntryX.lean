/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEntry
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneCk
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneCkX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]` Entry, `sender_ratchet_key`, `sender_ratchet_key_private`, and Top-Level Contract

Verifies the function entry, `sender_ratchet_key` and `sender_ratchet_key_private` cloning paths,
and assembles the top-level contracts `ChainCloneLocal1OkX` and `SenderChainCloneLocal1OkX` for
`<session_structure::Chain as Clone>::clone` (`0x24848`) on `SP2Ext`.
-/

namespace CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X

set_option maxRecDepth 500000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainCloneStateSimp.sp_setPC_pre ChainCloneStateSimp.sp_setMem_setPC_pre
  ChainCloneStateSimp.readReg64_setPC_pre ChainCloneStateSimp.readReg64_setMem_setPC_pre
  ChainCloneStateSimp.readReg32_setPC_pre ChainCloneStateSimp.readReg32_setMem_setPC_pre
  ChainCloneStateSimp.readReg_setPC_pre ChainCloneStateSimp.readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

theorem L1_ChainCloneEntryX : True := trivial

theorem stackAt_chainClone_eq_entry_x (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      stackAt (sp - 208#64) Stage1X.extHookStack ∗
      spillSlotsExist sp ∗
      deadStackSlots sp ∗
      (∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
      (∃∗ v13 : BitVec 64, (sp - 104#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (sp - 96#64) ↦₆₄ v14) ∗
      (∃∗ v15 : BitVec 64, (sp - 88#64) ↦₆₄ v15) ∗
      (∃∗ v16 : BitVec 64, (sp - 80#64) ↦₆₄ v16) ∗
      (∃∗ v17 : BitVec 64, (sp - 72#64) ↦₆₄ v17) ∗
      (∃∗ v18 : BitVec 64, (sp - 64#64) ↦₆₄ v18) ∗
      (∃∗ v19 : BitVec 64, (sp - 56#64) ↦₆₄ v19) ∗
      (∃∗ v20 : BitVec 64, (sp - 48#64) ↦₆₄ v20) ∗
      (∃∗ v21 : BitVec 64, (sp - 40#64) ↦₆₄ v21) ∗
      (∃∗ v22 : BitVec 64, (sp - 32#64) ↦₆₄ v22) ∗
      (∃∗ v23 : BitVec 64, (sp - 24#64) ↦₆₄ v23) ∗
      (∃∗ v24 : BitVec 64, (sp - 16#64) ↦₆₄ v24) ∗
      (∃∗ v25 : BitVec 64, (sp - 8#64) ↦₆₄ v25) := by
  rw [stackAt_chainClone_eq_x sp]
  unfold spillSlotsExist deadStackSlots
  ac_rfl

set_option maxHeartbeats 1600000 in
/-- `priv.length = 0` path (`0x384fc .. 0x38500`, `k ∈ [36, 37)`). -/
theorem chain_clone_priv_nil_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_nil : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro hfl hsym
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none_x (img := img) (A := A) (ext := ext) hC
      x s0 s' hs0_align srkPtr' 1#64 v8 v9 v10 v13 R
      hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some_x (img := img) (A := A) (ext := ext) hC
      x ck s0 s' hs0_align srkPtr' 1#64 v8 v9 v10 v13 R
      hsrk hmax hsrc_klen hck
  clone_fetches_range img.base ext hfn 22 24
  clone_fetches_range img.base ext hfn 57 61
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hck_none hck_some ⊢
  examples_hide_fetches
  have hpriv_buf :
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv_nil]; simp [vecU8Buf]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv_nil]
  rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (232))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · have hfold_priv :
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 40#64) ↦₆₄ 0#64) ∗
          chainPrivLenFrame A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
      ac_rfl
    rw [hfold_priv]
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPpIn.weaken_pre ?_
          (hck_none _ hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by ac_rfl)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm, hpriv_len0]
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace
        · simp only [wp_norm]; assumption
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPpIn.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPpIn.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPpIn.weaken_pre ?_
          (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                  ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          exact Entails.pure_right hck_lt (Entails.refl _)
        · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm, hpriv_len0]
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · exact htrace
        · simp only [wp_norm]; assumption

set_option maxHeartbeats 1600000 in
/-- `0 < priv.length` path (`0x384c4 .. 0x384fc`, `k ∈ [22, 37)`). -/
theorem chain_clone_priv_pos_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro hfl hsym
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hshim := shim_ok_at_x hC
  have halloc := alloc_ok_at_x hC
  have hmemcpy := memcpy_ok_at_x hC
  have hpanic800 := fun s P => chain_clone_panic_800_x (img := img) (A := A) (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
    x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none_x (img := img) (A := A) (ext := ext) hC
      x s0 s' hs0_align srkPtr' privPtr' v8 v9 v10 v13 R
      hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some_x (img := img) (A := A) (ext := ext) hC
      x ck s0 s' hs0_align srkPtr' privPtr' v8 v9 v10 v13 R
      hsrk hmax hsrc_klen hck
  dsimp only [Proofs.libsignal.Stage1X.session2ShimSpecX] at hshim
  clone_fetches_range img.base ext hfn 22 37
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf)) =
    postPred at hpanic800 hck_none hck_some ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic800 hck_none hck_some ⊢
  examples_hide_fetches
  rw [chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧ x.gc.1.priv.ptr ≠ 0⌝ ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧ x.gc.1.priv.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_lt, hpriv_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 :=
    ⟨hpriv_pos, hpow1, by omega⟩
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat =
      x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hshim_state := shim_ok_at_stateX hshim hfl hsym
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (104))
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_alloc hsym_alloc
  have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
  have hsp1 : sf.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (116))
  wp_steps
  wp_call halloc_state (x.gc.1.priv.bytes.length, 1)
  rw [hsp1, hsp]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_post_alloc hsym_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    have htrace_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htrace_alloc_oom, hpost, htrace]
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (800))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_panic hsym_panic
    refine hpanic800 _ _ ?_ ?_ htrace_oom hfl_panic hsym_panic
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace_alloc_ok⟩ => ?_
    have htrace1 : sf_1.trace = s0.trace := by
      rw [htrace_alloc_ok, hpost, htrace]
    let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_priv_post :
        ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          chainPrivPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      have hbuf := vecU8Buf_pos_eq A privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64
      rw [hbuf,
          chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
      have hsrc_ent :
          (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
              x.gc.1.priv.cap.toNat < 2 ^ 63 ∧ x.gc.1.priv.ptr ≠ 0⌝ ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hpriv_le, hpriv_lt, hpriv_ptr⟩ (Entails.refl _)
      have hgroup :
          ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            chainPrivPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            (A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
              (privPtr' ↦ₛ x.gc.1.priv.bytes)) ∗
            (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
              ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
              (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
              chainPrivPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hsrc_ent)))
    have hmemcpy_state := memcpy_ok_at_stateX hmemcpy hfl_post_alloc hsym_post_alloc
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (136))
    wp_steps
    wp_call hmemcpy_state (sf_1.readReg64 Reg.x0, x.gc.1.priv.ptr, x.gc.1.priv.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    have hsp_sf_1 : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
    rw [hsp_sf_1, hsp1, hsp]
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_post_memcpy hsym_post_memcpy
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by dsimp only [privPtr', Stage1X.extHookStack]; ac_rfl)) hfold_priv_post) ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_memcpy hsym_post_memcpy (mid := entry + bv% (244))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl_244 hsym_244
      refine SepWPp.weaken_pre ?_
        ((hck_none _ privPtr' hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hfl_244 hsym_244)
      · rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · rw [State.spAligned]; simp only [wp_norm, arm64_norm, *]
        exact hs0_align
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · simp only [wp_norm, arm64_norm, *]
      · exact htr_sf2
      · simp only [wp_norm, arm64_norm, *]
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_memcpy hsym_post_memcpy (mid := entry + bv% (148))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl_148 hsym_148
      refine SepWPp.weaken_pre ?_
        ((hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) hfl_148 hsym_148)
      · rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
        rw [show (memRegion x.dst 104 ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
              ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
              chainCkSomeCapFrame A x.gc ck x.src ∗
              A.pool ∗
              stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
              spillSlotsExist s0.sp ∗
              ((s0.sp - 144#64) ↦₆₄ v8) ∗
              ((s0.sp - 136#64) ↦₆₄ v9) ∗
              ((s0.sp - 128#64) ↦₆₄ v10) ∗
              ((s0.sp - 104#64) ↦₆₄ v13) ∗
              savedRegsOnStack s0) =
            (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
              chainCkSomeCapFrame A x.gc ck x.src ∗
              memRegion x.dst 104 ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
              A.pool ∗
              stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
              spillSlotsExist s0.sp ∗
              ((s0.sp - 144#64) ↦₆₄ v8) ∗
              ((s0.sp - 136#64) ↦₆₄ v9) ∗
              ((s0.sp - 128#64) ↦₆₄ v10) ∗
              ((s0.sp - 104#64) ↦₆₄ v13) ∗
              savedRegsOnStack s0) by ac_rfl]
        rw [show (memRegion x.dst 104 ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src) ∗
              A.pool ∗
              stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
              spillSlotsExist s0.sp ∗
              ((s0.sp - 144#64) ↦₆₄ v8) ∗
              ((s0.sp - 136#64) ↦₆₄ v9) ∗
              ((s0.sp - 128#64) ↦₆₄ v10) ∗
              ((s0.sp - 104#64) ↦₆₄ v13) ∗
              savedRegsOnStack s0) =
            (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
              ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
              chainCkSomeCapFrame A x.gc ck x.src ∗
              memRegion x.dst 104 ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
              A.pool ∗
              stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
              spillSlotsExist s0.sp ∗
              ((s0.sp - 144#64) ↦₆₄ v8) ∗
              ((s0.sp - 136#64) ↦₆₄ v9) ∗
              ((s0.sp - 128#64) ↦₆₄ v10) ∗
              ((s0.sp - 104#64) ↦₆₄ v13) ∗
              savedRegsOnStack s0) by ac_rfl]
        exact Entails.pure_right hck_lt (Entails.refl _)
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · rw [State.spAligned]; simp only [wp_norm, arm64_norm, *]
        exact hs0_align
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · simp only [wp_norm, arm64_norm, *]
      · exact htr_sf2
      · simp only [wp_norm, arm64_norm, *]

set_option maxHeartbeats 1600000 in
/-- Entry and `srk` clone path (`0x24848 .. 0x384c0`, `k ∈ [0, 22)`). -/
theorem chain_clone_entry_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt s0.sp chainCloneStackX)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro hfl hsym
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hshim := shim_ok_at_x hC
  have halloc := alloc_ok_at_x hC
  have hmemcpy := memcpy_ok_at_x hC
  have hpanic848 := fun s P => chain_clone_panic_848_x (img := img) (A := A) (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
    x s0 s P R
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13 (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey) (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys) (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length) (hpriv_nil : x.gc.1.priv.bytes = []) =>
    chain_clone_priv_nil_x (img := img) (A := A) (ext := ext) hC
      x s0 s' hs0_align srkPtr' v8 v9 v10 v13 R
      hsrk hmax hsrc_klen hpriv_nil
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13 (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey) (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys) (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length) (hpriv_pos : 0 < x.gc.1.priv.bytes.length) =>
    chain_clone_priv_pos_x (img := img) (A := A) (ext := ext) hC
      x s0 s' hs0_align srkPtr' v8 v9 v10 v13 R
      hsrk hmax hsrc_klen hpriv_pos
  dsimp only [Proofs.libsignal.Stage1X.session2ShimSpecX] at hshim
  clone_fetches_range img.base ext hfn 0 22
  have := libsignalSessionCode_fetch_fnAddr_entry (b := img.base)
    (H := Rust.withPanics ext)
    hfn (by decide) (ls_decode% chainCloneLocal1Bin (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  examples_hide_fetches
  rw [chainAt_eq_pure_sep A x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  rw [chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry_x s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v25 => ?_
  refine SepWPp.exists_elim fun v24 => ?_
  refine SepWPp.exists_elim fun v23 => ?_
  refine SepWPp.exists_elim fun v22 => ?_
  refine SepWPp.exists_elim fun v21 => ?_
  refine SepWPp.exists_elim fun v20 => ?_
  refine SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.exists_elim fun v18 => ?_
  refine SepWPp.exists_elim fun v17 => ?_
  refine SepWPp.exists_elim fun v16 => ?_
  refine SepWPp.exists_elim fun v15 => ?_
  refine SepWPp.exists_elim fun v14 => ?_
  refine SepWPp.exists_elim fun v13 => ?_
  refine SepWPp.exists_elim fun v10 => ?_
  refine SepWPp.exists_elim fun v9 => ?_
  refine SepWPp.exists_elim fun v8 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_lt, hsrk_ptr⟩ => ?_
  have hpos_srk : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 :=
    ⟨hpos_srk, hpow1, by omega⟩
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat =
      x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpos_srk (by omega)
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (52))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_shim hsym_shim
  have hshim_state := shim_ok_at_stateX hshim hfl_shim hsym_shim
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_shim hsym_shim (mid := entry + bv% (56))
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_alloc hsym_alloc
  have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (68))
  wp_steps
  wp_call halloc_state (x.gc.1.srk.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, ‹sf.trace = s0.trace›]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_post_alloc hsym_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    have htrace_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := htrace_alloc_oom
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (848))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_panic hsym_panic
    refine hpanic848 _ _ ?_ ?_ htrace_oom hfl_panic hsym_panic
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace1⟩ => ?_
    let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_srk_post :
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          deadStackSlots s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A srkPtr' x.gc.1.srk.bytes hpos_srk hsrk_lt63 hoom64,
          chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen]
      unfold savedRegsOnStack deadStackSlots
      have hsrc_ent :
          (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.srk.bytes.length ≤ x.gc.1.srk.cap.toNat ∧
              x.gc.1.srk.cap.toNat < 2 ^ 63 ∧
              x.gc.1.srk.ptr ≠ 0⌝ ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            chainSrkPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hsrk_le, hsrk_lt, hsrk_ptr⟩ (Entails.refl _)
      have hgroup :
          ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            chainSrkPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
          (memRegion x.dst 104 ∗
            (A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ (srkPtr' ↦ₛ x.gc.1.srk.bytes)) ∗
            (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
              ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
              (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
              chainSrkPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
              ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
              ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
              ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
              (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent))
    have hmemcpy_state := memcpy_ok_at_stateX hmemcpy hfl_post_alloc hsym_post_alloc
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (88))
    wp_steps
    wp_call hmemcpy_state (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    have hsp_sf_1 : sf_1.sp = sf.sp := by simp only [wp_norm, arm64_norm, *]
    rw [hsp_sf_1, ‹sf.sp = s0.sp - 208#64›]
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_post_memcpy hsym_post_memcpy
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by dsimp only [srkPtr', Stage1X.extHookStack]; ac_rfl)) hfold_srk_post) ?_
    by_cases hpriv_nil : x.gc.1.priv.bytes = []
    · refine hpriv_nil_lem _ srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv_nil
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htr_sf2 ?_ hfl_post_memcpy hsym_post_memcpy
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · rw [State.spAligned, hsp_sf2]; exact hsp_sub_align
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
    · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
      refine hpriv_pos_lem _ srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv_pos
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htr_sf2 ?_ hfl_post_memcpy hsym_post_memcpy
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · rw [State.spAligned, hsp_sf2]; exact hsp_sub_align
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]

private theorem protoChain_clone_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    ProtoChainCloneLocal1OkX img A ext := by
  unfold ProtoChainCloneLocal1OkX
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hs0_align hloaded => ?_
  simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1⟩, hmem⟩
  obtain ⟨sf, hsteps,
      ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ |
      ⟨hpan_f, P_f, hmem_f, hpan_post⟩ |
      ⟨_, hfalse⟩⟩ :=
    chain_clone_entry_x hC x s0 hs0_align R hpc hrun hx0 hx1 hF hsym R
      (by simpa [sepConj_assoc] using hmem) hloaded
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hret, hsp_f, hrun_f⟩, ⟨hsp_f, hcc_f⟩,
        Satisfies.mono (sepConj_mono_left hpost_f) hmem_f⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inr (Or.inl ⟨hpan_f, hpan_post hmem_f⟩)))
  · exact (not_satisfies_false_sepConj hfalse).elim

/-- `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]`
    (`0x24848`, 218 instructions) satisfies `ChainCloneLocal1OkX`. -/
theorem chain_clone_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    ChainCloneLocal1OkX img A ext :=
  chainClone_of_protoChainClone_x (protoChain_clone_ok_x hC)

/-- Sender-chain clone (`sender_chain.is_some()` specialization) satisfies `SenderChainCloneLocal1OkX`. -/
theorem senderChain_clone_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    SenderChainCloneLocal1OkX img A ext :=
  senderChainClone_of_chainClone_x (protoChain_clone_ok_x hC)

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
