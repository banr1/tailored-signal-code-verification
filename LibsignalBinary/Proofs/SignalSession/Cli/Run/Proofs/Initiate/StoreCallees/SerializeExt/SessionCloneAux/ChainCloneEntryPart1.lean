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
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneCk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]`: `sender_ratchet_key_private` Clone Branches
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

set_option maxHeartbeats 1200000 in
/-- `priv = []` branch (`k ∈ [22, 24) ∪ [57, 61)`). -/
theorem chain_clone_priv_nil {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 88#64)
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
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
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
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none (img := img) (A := A)
      (ext := ext) hA x s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some (img := img) (A := A)
      (ext := ext) hA x ck s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  clone_fetches_range img.base ext hfn 22 24
  clone_fetches_range img.base ext hfn 57 61
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hck_none hck_some ⊢
  examples_hide_fetches
  have hpriv_buf :
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply SepWPpX.of_sepWP (mid := entry + bv% (232))
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
          stackAt (s0.sp - 208#64) extHookStack ∗
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
          stackAt (s0.sp - 208#64) extHookStack ∗
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
      apply SepWPpX.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPpX.weaken_pre ?_
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
            stackAt (s0.sp - 208#64) extHookStack ∗
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
            stackAt (s0.sp - 208#64) extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPpX.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPpX.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPpX.weaken_pre ?_
          (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) extHookStack ∗
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
                stackAt (s0.sp - 208#64) extHookStack ∗
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
                stackAt (s0.sp - 208#64) extHookStack ∗
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
                stackAt (s0.sp - 208#64) extHookStack ∗
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

set_option maxHeartbeats 1200000 in
/-- `0 < priv.length` branch (`k ∈ [22, 37)`). -/
theorem chain_clone_priv_pos {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 88#64)
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
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
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
  have hpanic800 := fun s P => chain_clone_panic_800 (img := img) (A := A)
    (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none (img := img) (A := A)
      (ext := ext) hA x s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some (img := img) (A := A)
      (ext := ext) hA x ck s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [sessionMemcpySpec] at hmemcpy
  clone_fetches_range img.base ext hfn 22 37
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic800 hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic800 hck_none hck_some ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic800 hck_none hck_some ⊢
  examples_hide_fetches
  rw [chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPpX.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  wpx_of_sepWP (mid := entry + bv% (116))
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (800))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic800 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_priv_post :
        ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
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
          stackAt (s0.sp - 208#64) extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64,
          chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
      have hsrc_ent :
          (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
              x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
              x.gc.1.priv.ptr ≠ 0⌝ ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            chainPrivPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ (Entails.refl _)
      have hgroup :
          ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) extHookStack ∗
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
            (A.live privPtr' x.gc.1.priv.bytes.length 1 ∗ (privPtr' ↦ₛ x.gc.1.priv.bytes)) ∗
            (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
              ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
              (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
              chainPrivPosFrame A x.gc x.src) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) extHookStack ∗
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
    wpx_of_sepWP (mid := entry + bv% (136))
    wpx_steps
    wpx_apply
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    rw [‹sf_1.sp = s0.sp - 208#64›]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPpX.weaken_pre hfold_priv_post ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPpX.weaken_pre ?_
          (hck_none _ privPtr' hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
          exact Entails.of_eq (by ac_rfl)
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
        · exact htr_sf2
        · simp only [wp_norm]; assumption
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
            stackAt (s0.sp - 208#64) extHookStack ∗
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
            stackAt (s0.sp - 208#64) extHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPpX.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPpX.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPpX.weaken_pre ?_
          (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) extHookStack ∗
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
                stackAt (s0.sp - 208#64) extHookStack ∗
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
                stackAt (s0.sp - 208#64) extHookStack ∗
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
                stackAt (s0.sp - 208#64) extHookStack ∗
                spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗
                ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗
                ((s0.sp - 104#64) ↦₆₄ v13) ∗
                savedRegsOnStack s0) by ac_rfl]
          exact Entails.pure_right hck_lt (Entails.refl _)
        · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
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
        · exact htr_sf2
        · simp only [wp_norm]; assumption

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
