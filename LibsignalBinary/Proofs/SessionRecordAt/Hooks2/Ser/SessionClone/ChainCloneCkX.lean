/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneCk
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlaced
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]` `chain_key` Stage (`0x38500..0x3856c`)

Verifies the `chain_key: Option<ChainKey>` `None` and `Some` cloning branches of
`<session_structure::Chain as Clone>::clone [local#1]` (`0x24848`, Block `82`) on `SP2Ext` and
under relocatable `[LibsignalPlacement]`.
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

theorem L1_ChainCloneCkX : True := trivial

set_option maxHeartbeats 1600000 in
/-- `chain_key = none` path (`0x38560 .. 0x3856c`, `k ∈ [61, 65)`). -/
theorem chain_clone_ck_none_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
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
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil_x (img := img) (A := A) (ext := ext) hC
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty_x (img := img) (A := A) (ext := ext) hC
      x s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck R
      hsrk hmax hsrc_klen hpos
  clone_fetches_range img.base ext hfn 61 65
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hmks_nil hmks_ne ⊢
  examples_hide_fetches
  rw [chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
  simp only [sepConj_assoc]
  have hck_buf :
      clonedOptChainKeyBuf A x.gc.1.ck optChainKeyNone
        (s.readReg64 (Reg.gpr 28#5)) (s.readReg32 (Reg.gpr 27#5)) x.gc.2.chainKey = emp := by
    rw [hck]; simp only [clonedOptChainKeyBuf, pure_true]
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (732))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPpIn.weaken_pre ?_
      (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hck_buf, emp_sepConj,
          chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen, hlen0]
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
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; rfl
    · simp only [wp_norm, arm64_norm, *]
    · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
    · exact htrace
    · simp only [wp_norm, arm64_norm, *]
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPpIn.of_sepWP (mid := entry + bv% (260))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPpIn.weaken_pre ?_
      (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hck_buf, emp_sepConj,
          chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
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
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
    · exact htrace
    · simp only [wp_norm, arm64_norm, *]

set_option maxHeartbeats 1600000 in
/-- `chain_key = some ck` path (`0x38500 .. 0x38540`, `k ∈ [37, 54)`). -/
theorem chain_clone_ck_some_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : ChainCloneGhost) (ck : ChainKey) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
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
  have hpanic812 := fun s P => chain_clone_panic_812_x (img := img) (A := A) (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
    x s0 s P R
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil_x (img := img) (A := A) (ext := ext) hC
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty_x (img := img) (A := A) (ext := ext) hC
      x s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩ R
      hsrk hmax hsrc_klen hpos
  dsimp only [Proofs.libsignal.Stage1X.session2ShimSpecX] at hshim
  clone_fetches_range img.base ext hfn 37 54
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic812 hmks_nil hmks_ne ⊢
  examples_hide_fetches
  rw [chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (164))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_shim hsym_shim
  have hshim_state := shim_ok_at_stateX hshim hfl_shim hsym_shim
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_shim hsym_shim (mid := entry + bv% (168))
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_alloc hsym_alloc
  have hsp1 : sf.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
  have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (180))
  wp_steps
  wp_call halloc_state (32, 1)
  rw [hsp1, hsp]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_post_alloc hsym_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    have htrace_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htrace_alloc_oom, hpost, htrace]
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (812))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_panic hsym_panic
    refine hpanic812 _ _ ?_ ?_ htrace_oom hfl_panic hsym_panic
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace_alloc_ok⟩ => ?_
    have htrace1 : sf_1.trace = s0.trace := by
      rw [htrace_alloc_ok, hpost, htrace]
    let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_ck_post :
        ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          A.live ckPtr' 32 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          chainCkSomeFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      have hck_buf_eq :
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
            A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
        rw [hck]
        simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
        have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
        have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
        have hv := vecU8Buf_pos_eq A ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
        rw [hck_len] at hv
        exact hv
      rw [hck_buf_eq,
          chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
      have hsrc_ent :
          (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) ⊢
          (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) :=
        Entails.pure_right ⟨hck_le, hck_lt, hck_ptr⟩ (Entails.refl _)
      have hgroup :
          ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            A.live ckPtr' 32 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            chainCkSomeFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            (A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key)) ∗
            (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
              ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
              ((x.src + 88#64) ↦₆₄ 32#64) ∗
              ((x.src + 96#64) ↦₃₂ ck.index) ∗
              (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
              chainCkSomeFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsrc_ent))))
    by_cases hmk_nil : x.gc.2.messageKeys = []
    · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
      have hmemcpy_state := memcpy_ok_at_stateX hmemcpy hfl_post_alloc hsym_post_alloc
      apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (732))
      wp_steps
      wp_call hmemcpy_state (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [hsp_sf_1, hsp1, hsp]
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl_732 hsym_732
      refine SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by simp only [hlen0, ckPtr', Stage1X.extHookStack]; ac_rfl)) hfold_ck_post)
        (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfl_732 hsym_732)
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
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
      · exact htr_sf2
      · simp only [wp_norm, arm64_norm, *]
    · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
      have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
      have hmemcpy_state := memcpy_ok_at_stateX hmemcpy hfl_post_alloc hsym_post_alloc
      apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (260))
      wp_steps
      wp_call hmemcpy_state (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [hsp_sf_1, hsp1, hsp]
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl_260 hsym_260
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by simp only [ckPtr', Stage1X.extHookStack]; ac_rfl)) hfold_ck_post)
        (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfl_260 hsym_260)
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
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
      · exact htr_sf2
      · simp only [wp_norm, arm64_norm, *]

/-! ## Relocatable `[LibsignalPlacement]` `chain_key` proofs (Block `82`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

set_option maxRecDepth 2000000

set_option maxHeartbeats 1600000 in
/-- `chain_key = none` path (`+244`, Block `82`) under `[LibsignalPlacement]`. -/
theorem chain_clone_ck_none_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hpc : s.pc = (blkPl_82).base + 244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
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
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil_placed_x (A := A) (H := H) hC
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty_placed_x (A := A) (H := H) hC
      x s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck R
      hsrk hmax hsrc_klen hpos
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hmks_nil hmks_ne ⊢
  rw [chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
  simp only [sepConj_assoc]
  have hck_buf :
      clonedOptChainKeyBuf A x.gc.1.ck optChainKeyNone
        (s.readReg64 (Reg.gpr 28#5)) (s.readReg32 (Reg.gpr 27#5)) x.gc.2.chainKey = emp := by
    rw [hck]; simp only [clonedOptChainKeyBuf, pure_true]
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply SepWPpLs.of_sepWP (mid := (blkPl_82).base + bv% (732))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPpLs.weaken_pre ?_
      (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hck_buf, emp_sepConj,
          chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen, hlen0]
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
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; rfl
    · simp only [wp_norm, arm64_norm, *]
    · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
    · exact htrace
    · simp only [wp_norm, arm64_norm, *]
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPpLs.of_sepWP (mid := (blkPl_82).base + bv% (260))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPpLs.weaken_pre ?_
      (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hck_buf, emp_sepConj,
          chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
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
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
    · exact htrace
    · simp only [wp_norm, arm64_norm, *]

set_option maxHeartbeats 1600000 in
/-- `chain_key = some ck` path (`+148`, Block `82`) under `[LibsignalPlacement]`. -/
theorem chain_clone_ck_some_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (ck : ChainKey) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hpc : s.pc = (blkPl_82).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
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
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro hcl
  have hshim := shim_placed_ok_at_x hC
  have halloc := alloc_placed_ok_at_x hC
  have hmemcpy := memcpy_placed_ok_at_x hC
  have hpanic812 := fun s P => chain_clone_panic_812_placed_x (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
    hC x s0 s P R
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil_placed_x (A := A) (H := H) hC
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty_placed_x (A := A) (H := H) hC
      x s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩ R
      hsrk hmax hsrc_klen hpos
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic812 hmks_nil hmks_ne ⊢
  rw [chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_82).base + bv% (164))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_shim
  have hshim_state := shim_placed_ok_at_stateX hshim hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_82).base + bv% (168))
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_alloc
  have hsp1 : sf.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_82).base + bv% (180))
  wp_steps
  wp_call halloc_state (32, 1)
  rw [hsp1, hsp]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    have htrace_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htrace_alloc_oom, hpost, htrace]
    apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_82).base + bv% (812))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_panic
    refine hpanic812 _ _ ?_ ?_ htrace_oom hcl_panic
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace_alloc_ok⟩ => ?_
    have htrace1 : sf_1.trace = s0.trace := by
      rw [htrace_alloc_ok, hpost, htrace]
    let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_ck_post :
        ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          A.live ckPtr' 32 1 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          chainCkSomeFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey ∗
          protoChainAt A x.gc x.src ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      have hck_buf_eq :
          clonedOptChainKeyBuf A ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
            A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
        rw [hck]
        simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
        have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
        have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
        have hv := vecU8Buf_pos_eq A ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
        rw [hck_len] at hv
        exact hv
      rw [hck_buf_eq,
          chainAt_eq_ck_some A x.gc ck x.src hsrk hmax hsrc_klen hck]
      have hsrc_ent :
          (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) ⊢
          (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            chainCkSomeFrame A x.gc x.src) :=
        Entails.pure_right ⟨hck_le, hck_lt, hck_ptr⟩ (Entails.refl _)
      have hgroup :
          ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
            (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            A.live ckPtr' 32 1 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
            ((x.src + 88#64) ↦₆₄ 32#64) ∗
            ((x.src + 96#64) ↦₃₂ ck.index) ∗
            chainCkSomeFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            (A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key)) ∗
            (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
              ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
              ((x.src + 88#64) ↦₆₄ 32#64) ∗
              ((x.src + 96#64) ↦₃₂ ck.index) ∗
              (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
              chainCkSomeFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) := by
        ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsrc_ent))))
    by_cases hmk_nil : x.gc.2.messageKeys = []
    · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
      have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_post_alloc
      apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_82).base + bv% (732))
      wp_steps
      wp_call hmemcpy_state (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [hsp_sf_1, hsp1, hsp]
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hcl_732
      refine SepWPp.weaken_pre
        (Entails.trans (Entails.of_eq (by simp only [hlen0, ckPtr', Stage1X.extHookStack]; ac_rfl)) hfold_ck_post)
        (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_732)
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
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
      · exact htr_sf2
      · simp only [wp_norm, arm64_norm, *]
    · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
      have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
      have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_post_alloc
      apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_82).base + bv% (260))
      wp_steps
      wp_call hmemcpy_state (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [hsp_sf_1, hsp1, hsp]
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hcl_260
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by simp only [ckPtr', Stage1X.extHookStack]; ac_rfl)) hfold_ck_post)
        (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_260)
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
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]
      · simp only [wp_norm, arm64_norm, *]; rfl
      · unfold State.readReg32; simp only [wp_norm, arm64_norm, *]
      · exact htr_sf2
      · simp only [wp_norm, arm64_norm, *]

end Placed

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
