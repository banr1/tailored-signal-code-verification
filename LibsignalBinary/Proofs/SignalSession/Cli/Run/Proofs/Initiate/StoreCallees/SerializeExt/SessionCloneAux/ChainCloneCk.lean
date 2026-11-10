/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneBasePart2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneMkPart2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]`: `chain_key` Clone Branches
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
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

/-! ## `chain_key` Clone Branches -/

def chainMkLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      chainMkLenFrame A gc a := by
  unfold protoChainAt chainMkLenFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainCkSomeFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

theorem chainAt_eq_ck_some (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗
      (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
      chainCkSomeFrame A gc a := by
  unfold protoChainAt chainCkSomeFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hck_pos : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have ha96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  have ha100 : a + 72#64 + 28#64 = a + 100#64 := by bv_omega
  rw [hzip_len, hck]
  simp only [optChainKeyAt]
  rw [vecU8At_eq_of_pos A (a + 72#64) gc.1.ck.cap gc.1.ck.ptr (keyToBytes32 ck.key) hck_pos,
      hck_len, ha56, ha64, ha80, ha88, ha96, ha100]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

set_option maxHeartbeats 1200000 in
/-- `chain_key = none` branch (`k ∈ [61, 65)`). -/
theorem chain_clone_ck_none {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil (img := img) (A := A)
      (ext := ext)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty (img := img) (A := A)
      (ext := ext) hA x s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck R
      hsrk hmax hsrc_klen hpos
  clone_fetches_range img.base ext hfn 61 65
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hmks_nil hmks_ne ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (732))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine SepWPpX.weaken_pre ?_
        (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen, hlen0]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply SepWPpX.of_sepWP (mid := entry + bv% (260))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm]; assumption
    · refine SepWPpX.weaken_pre ?_
        (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · rw [hck_buf, emp_sepConj,
            chainAt_eq_mk_len A x.gc x.src hsrk hmax hsrc_klen]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · rw [State.spAligned] at hsp_align ⊢; simp only [wp_norm]; exact hsp_align
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; rfl
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · unfold State.readReg32; simp only [wp_norm]
      · exact htrace
      · simp only [wp_norm]; assumption

set_option maxHeartbeats 1200000 in
/-- `chain_key = some ck` branch (`k ∈ [37, 54)`). -/
theorem chain_clone_ck_some {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : ChainCloneGhost) (ck : ChainKey) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 148#64)
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
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hshim := shim_ok_at hA (ext := ext)
  have halloc := alloc_ok_at (img := img) hA
  have hmemcpy := memcpy_ok_at hA (ext := ext)
  have hpanic812 := fun s P => chain_clone_panic_812 (img := img) (A := A)
    (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil (img := img) (A := A)
      (ext := ext)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty (img := img) (A := A)
      (ext := ext) hA x s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩ R
      hsrk hmax hsrc_klen hpos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [sessionMemcpySpec] at hmemcpy
  clone_fetches_range img.base ext hfn 37 54
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic812 hmks_nil hmks_ne ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
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
        stackAt (s0.sp - 208#64) extHookStack ∗
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
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPpX.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  wpx_of_sepWP (mid := entry + bv% (180))
  wpx_steps
  wpx_apply
  have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
  rw [‹s.sp = s0.sp - 208#64›]
  wp_compact
  wpx_steps
  wpx_apply
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (812))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic812 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_ck_post :
        ((ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
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
          stackAt (s0.sp - 208#64) extHookStack ∗
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
            stackAt (s0.sp - 208#64) extHookStack ∗
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
            stackAt (s0.sp - 208#64) extHookStack ∗
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
      wpx_of_sepWP (mid := entry + bv% (732))
      wpx_steps
      wpx_apply
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [‹sf_1.sp = s0.sp - 208#64›]
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wpx_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPpX.weaken_pre
          (Entails.trans (by rw [hlen0]; exact Entails.refl _) hfold_ck_post)
          (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
        · exact htr_sf2
        · simp only [wp_norm]; assumption
    · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
      have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
      wpx_of_sepWP (mid := entry + bv% (260))
      wpx_steps
      wpx_apply
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [‹sf_1.sp = s0.sp - 208#64›]
      wp_compact
      have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
      have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := ‹_›
      wpx_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPpX.weaken_pre hfold_ck_post
          (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned]; simp only [wp_norm, hsp_sf2]
          exact spAligned_sub s0.sp 208 hs0_align (by decide)
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
        · exact htr_sf2
        · simp only [wp_norm]; assumption

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

def chainCkNoneCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  memRegion (a + 72#64 + 8#64) 24

theorem chainAt_eq_ck_none_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = none) :
    protoChainAt A gc a =
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      chainCkNoneCapFrame A gc a := by
  unfold protoChainAt chainCkNoneCapFrame
  rw [hck]
  dsimp only [optChainKeyAt, optChainKeyNone]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainCkSomeCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) : SepProp :=
  ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
  ((a + 88#64) ↦₆₄ 32#64) ∗
  ((a + 96#64) ↦₃₂ ck.index) ∗
  (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

theorem chainAt_eq_ck_some_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
      ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
      chainCkSomeCapFrame A gc ck a := by
  rw [chainAt_eq_ck_some A gc ck a hsrk hmax hklen hck]
  unfold chainCkSomeFrame chainCkSomeCapFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right hlt
    rw [show (((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact sepConj_mono_right (Entails.pure_right ⟨hle, hptr⟩ (Entails.refl _))
  · apply Entails.pure_left; intro hlt
    rw [show (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hptr⟩
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

def chainPrivLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
  vecU8Buf A gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_priv_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      chainPrivLenFrame A gc a := by
  unfold protoChainAt chainPrivLenFrame
  dsimp only [vecGhostAt, vecU8At, vecU8Buf, vecAt, vecHeader]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainPrivPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
  memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
    (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_priv_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.1.priv.bytes.length) :
    protoChainAt A gc a =
      ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
        gc.1.priv.cap.toNat < 2 ^ 63 ∧
        gc.1.priv.ptr ≠ 0⌝ ∗
      ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
      chainPrivPosFrame A gc a := by
  unfold protoChainAt chainPrivPosFrame
  dsimp only [vecGhostAt]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [vecU8At_eq_of_pos A (a + 24#64) gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes hpos,
      ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
