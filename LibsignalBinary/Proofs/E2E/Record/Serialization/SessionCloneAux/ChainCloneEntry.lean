/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneCk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Entry, `sender_ratchet_key_private`, and top-level proofs for `<Chain as Clone>::clone` (`0x24848`)
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
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
theorem chain_clone_priv_nil_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name + 88#64)
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
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
    libsignalSessionCode_fnOff_sym_24848
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none_trap (b := b) (C := C) (A := A)
      (abs := abs) hA x s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some_trap (b := b) (C := C) (A := A)
      (abs := abs) hA x ck s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 88 8
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 228 16
  clear hfn
  unfold trTrapProgAt at hpc hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr chainCloneLocal1Name = entry
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
  apply SepWPp.of_sepWP (mid := entry + bv% (232))
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
      apply SepWPp.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
theorem chain_clone_priv_nil {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name + 88#64)
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
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) :=
  SepWPp_kit_of_trTrap (chain_clone_priv_nil_trap hA x s0 s hs0_align srkPtr'
    v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv hpc hrun hsp hsp_align hx29 hx19 hx21 hx22
    hx26 htrace hvregs)

set_option maxHeartbeats 1200000 in
theorem chain_clone_priv_pos_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name + 88#64)
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
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
    libsignalSessionCode_fnOff_sym_24848
  have hshim := shim_ok_at_trap (b := b) (C := C) (abs := abs)
  have halloc := alloc_ok_at_trap (b := b) (C := C) (abs := abs) hA
  have hmemcpy := memcpy_ok_at_trap (b := b) (C := C) (abs := abs)
  have hpanic800 := fun s P => chain_clone_panic_800_trap (b := b) (C := C) (A := A)
    (abs := abs)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none_trap (b := b) (C := C) (A := A)
      (abs := abs) hA x s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some_trap (b := b) (C := C) (A := A)
      (abs := abs) hA x ck s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 88 60
  clear hfn
  unfold trTrapProgAt at hpc hshim halloc hmemcpy hpanic800 hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr chainCloneLocal1Name = entry
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
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (116))
  wp_steps
  wp_apply
  have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
  wp_compact
  wp_steps
  wp_apply
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (800))
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
    apply SepWPp.of_sepWP (mid := entry + bv% (136))
    wp_steps
    wp_apply
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_priv_post ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := entry + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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

set_option maxHeartbeats 1600000 in
theorem chain_clone_priv_pos {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name + 88#64)
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
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) :=
  SepWPp_kit_of_trTrap (chain_clone_priv_pos_trap hA x s0 s hs0_align srkPtr'
    v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv_pos hpc hrun hsp _hsp_align hx29 hx19 hx21 hx22
    hx26 htrace hvregs)

theorem sepWPp_pure_second {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B) Q Qp) :
    SepWPp prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp := by
  rw [show A ∗ ⌜φ⌝ ∗ B = ⌜φ⌝ ∗ A ∗ B by ac_rfl]
  exact SepWPp.pure_elim h

theorem chainAt_eq_pure_sep (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    protoChainAt A gc a =
      ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
      protoChainAt A gc a := by
  unfold protoChainAt
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hp
    exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
  · apply Entails.pure_left; intro _
    exact Entails.refl _

def chainSrkPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  (a ↦₆₄ gc.1.srk.cap) ∗
  A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
  memRegion (gc.1.srk.ptr + BitVec.ofNat 64 gc.1.srk.bytes.length)
    (gc.1.srk.cap.toNat - gc.1.srk.bytes.length) ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_srk_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧
        gc.1.srk.cap.toNat < 2 ^ 63 ∧
        gc.1.srk.ptr ≠ 0⌝ ∗
      ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      (gc.1.srk.ptr ↦ₛ gc.1.srk.bytes) ∗
      chainSrkPosFrame A gc a := by
  have hpos : 0 < gc.1.srk.bytes.length := srk_length_pos hsrk
  unfold protoChainAt chainSrkPosFrame
  dsimp only [vecGhostAt]
  rw [vecU8At_eq_of_pos A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes hpos]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)

def deadStackSlots (sp : BitVec 64) : SepProp :=
  (∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
  (∃∗ w12a : BitVec 32, (sp - 112#64) ↦₃₂ w12a) ∗
  (∃∗ w12b : BitVec 32, (sp - 108#64) ↦₃₂ w12b)

theorem stackAt_chainClone_eq_entry (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      stackAt (sp - 208#64) allocHookStack ∗
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
  rw [stackAt_chainClone_eq sp]
  unfold spillSlotsExist deadStackSlots
  ac_rfl

set_option maxHeartbeats 1200000 in
theorem chain_clone_entry_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hshim := shim_ok_at_trap (b := b) (C := C) (abs := abs)
  have halloc := alloc_ok_at_trap (b := b) (C := C) (abs := abs) hA
  have hmemcpy := memcpy_ok_at_trap (b := b) (C := C) (abs := abs)
  have hpanic848 := fun s P => chain_clone_panic_848_trap (b := b) (C := C) (A := A)
    (abs := abs)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = []) =>
    chain_clone_priv_nil_trap (b := b) (C := C) (A := A)
      (abs := abs) hA x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length) =>
    chain_clone_priv_pos_trap (b := b) (C := C) (A := A)
      (abs := abs) hA x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv_pos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  code_fetches_range libsignalSessionCode chainCloneLocal1Bin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") 0 88
  have := libsignalSessionCode_fetch_fnAddr_entry (b := b)
    (H := Rust.withPanics (trTrapExterns C abs))
    hfn (by decide) (ls_decode% chainCloneLocal1Bin (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  clear hfn
  unfold trTrapProgAt at hpc hshim halloc hmemcpy hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  examples_hide_fetches
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  rw [chainAt_eq_pure_sep A x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  rw [chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 =>
    SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v22 => SepWPp.exists_elim fun v23 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat = x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hsrk_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (68))
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  rw [‹sf.sp = s0.sp - 208#64›, ‹sf.trace = s0.trace›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (848))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic848 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_srk_post :
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          deadStackSlots s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
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
        Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      have hgroup :
          ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            chainSrkPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
    apply SepWPp.of_sepWP (mid := entry + bv% (88))
    wp_steps
    wp_apply
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_srk_post ?_
    by_cases hpriv_nil : x.gc.1.priv.bytes = []
    · refine hpriv_nil_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_nil
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align
    · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
      refine hpriv_pos_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_pos
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align

theorem chain_clone_entry {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) :=
  SepWPp_kit_of_trTrap (chain_clone_entry_trap hA x s0 hs0_align R hpc hrun hx0 hx1)

private theorem protoChain_clone_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    ProtoChainCloneLocal1Ok_trap b C A abs := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hs0_align
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack,
    R, by simpa [sepConj_assoc] using hmem, fun R' hm' hloaded => ?_⟩
  obtain ⟨sf, hsteps,
      ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ |
      ⟨hpan_f, P_f, hmem_f, hpan_post⟩ |
      hoom⟩ :=
    chain_clone_entry_trap hA x s0 hs0_align R hpc hrun hx0 hx1 R' hm' hloaded
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hrun_f, P_f, hmem_f,
      fun hmfR => Satisfies.mono (sepConj_mono_left hpost_f) hmfR, hsp_f, hcc_f⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_f, P_f, hmem_f, hpan_post⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem protoChain_clone_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    ProtoChainCloneLocal1Ok b C A ctl abs :=
  subroutine_ok_kit_of_trTrap (protoChain_clone_ok_trap hA)

theorem chain_clone_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    ChainCloneLocal1Ok_trap b C A abs :=
  chainClone_of_protoChainClone_trap (protoChain_clone_ok_trap hA)

/-- `<session_structure::Chain as Clone>::clone` (`0x24848`) satisfies `ChainCloneLocal1Ok`. -/
theorem chain_clone_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    ChainCloneLocal1Ok b C A ctl abs :=
  subroutine_ok_kit_of_trTrap (chain_clone_ok_trap hA)

theorem senderChain_clone_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    SenderChainCloneLocal1Ok_trap b C A abs :=
  senderChainClone_of_chainClone_trap optSenderChainAt_some_eq_chainAt (protoChain_clone_ok_trap hA)

/-- `SenderChain` specialization of `<Chain as Clone>::clone` satisfies `SenderChainCloneLocal1Ok`. -/
theorem senderChain_clone_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    SenderChainCloneLocal1Ok b C A ctl abs :=
  subroutine_ok_kit_of_trTrap (senderChain_clone_ok_trap hA)

/-! ## Relocatable `[LibsignalPlacement]` entry and top-level proofs (block `82`) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

set_option maxHeartbeats 1200000 in
theorem chain_clone_local1_placed_priv_nil [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (blkPl_82).base + 88#64)
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
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_local1_placed_ck_none (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_local1_placed_ck_some (A := A) (H := H) hshim halloc hmemcpy hpanic x ck s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hck_none hck_some ⊢
  have hpriv_buf :
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (232))
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
      apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [hpriv_buf, emp_sepConj,
              chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
theorem chain_clone_local1_placed_priv_pos [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (blkPl_82).base + 88#64)
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
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
  have hpanic800 := fun s P => chain_clone_local1_placed_panic_800 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_local1_placed_ck_none (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_local1_placed_ck_some (A := A) (H := H) hshim halloc hmemcpy hpanic x ck s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic800 hck_none hck_some ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic800 hck_none hck_some ⊢
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
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (116))
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
  wp_compact
  wp_steps
  wp_call halloc (x.gc.1.priv.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (800))
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (136))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.priv.ptr, x.gc.1.priv.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_priv_post ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (244))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗
            ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗
            ((s0.sp - 104#64) ↦₆₄ v13) ∗
            savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (148))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte]
      · simp only [wp_norm]; assumption
      · refine SepWPp.weaken_pre ?_
          (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        · rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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
                stackAt (s0.sp - 208#64) allocHookStack ∗
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

set_option maxHeartbeats 1200000 in
theorem chain_clone_local1_placed_entry [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H) (lsρ lsRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H) (lsρ lsMemcpySym) sessionMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (blkPl_82).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt s0.sp chainCloneStack)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hpanic848 := fun s P => chain_clone_local1_placed_panic_848 (A := A) (H := H)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    hpanic x s0 s P R
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = []) =>
    chain_clone_local1_placed_priv_nil (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length) =>
    chain_clone_local1_placed_priv_pos (A := A) (H := H) hshim halloc hmemcpy hpanic x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv_pos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [sessionMemcpySpec] at hmemcpy
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  rw [chainAt_eq_pure_sep A x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  rw [chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 =>
    SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 =>
    SepWPp.exists_elim fun v22 => SepWPp.exists_elim fun v23 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat = x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hsrk_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (68))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (x.gc.1.srk.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, ‹sf.trace = s0.trace›]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (848))
    wp_steps
    refine SepWP.done ?_ ?_ ?_
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · refine hpanic848 _ _ ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · exact htrace_oom
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    have hfold_srk_post :
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
          memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A x.gc x.src ∗
          spillSlotsExist s0.sp ∗
          deadStackSlots s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
          stackAt (s0.sp - 208#64) allocHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗
          ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗
          ((s0.sp - 104#64) ↦₆₄ v22) ∗
          savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
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
        Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      have hgroup :
          ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗
            A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
            memRegion x.dst 104 ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            chainSrkPosFrame A x.gc x.src ∗
            spillSlotsExist s0.sp ∗
            ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
            stackAt (s0.sp - 208#64) allocHookStack ∗
            spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗
            ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗
            ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
    apply SepWPp.of_sepWP (mid := (blkPl_82).base + bv% (88))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_srk_post ?_
    by_cases hpriv_nil : x.gc.1.priv.bytes = []
    · refine hpriv_nil_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_nil
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align
    · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
      refine hpriv_pos_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_pos
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› htr_sf2 ‹_›
      rw [State.spAligned, hsp_sf2]
      exact hsp_sub_align

theorem protoChain_clone_local1_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H)
      (lsρ lsRustNoAllocShimSym) CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ProtoChainCloneLocal1PlacedOk A H := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hs0_align
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack,
    R, by simpa [sepConj_assoc] using hmem, fun R' hm' hloaded => ?_⟩
  obtain ⟨sf, hsteps,
      ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ |
      ⟨hpan_f, P_f, hmem_f, hpan_post⟩ |
      hoom⟩ :=
    chain_clone_local1_placed_entry hshim halloc hmemcpy
      hpanic x s0 hs0_align R hpc hrun hx0 hx1 R' hm' hloaded
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hrun_f, P_f, hmem_f,
      fun hmfR => Satisfies.mono (sepConj_mono_left hpost_f) hmfR, hsp_f, hcc_f⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_f, P_f, hmem_f, hpan_post⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem protoChain_clone_local1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ProtoChainCloneLocal1PlacedOk A H :=
  protoChain_clone_local1_placed_ok_of_hooks
    (ls_hook_ok_of_mem hshim)
    (ls_hook_ok_of_mem halloc)
    (ls_hook_ok_of_mem hmemcpy)
    hpanic

theorem chain_clone_local1_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H)
      (lsρ lsRustNoAllocShimSym) CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ChainCloneLocal1PlacedOk A H :=
  chainClone_of_protoChainClone_local1_gen
    (protoChain_clone_local1_placed_ok_of_hooks hshim halloc hmemcpy hpanic)

/-- Relocatable `<Chain as Clone>::clone` (block `82`) satisfies `chainCloneSpec A`. -/
theorem chain_clone_local1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ChainCloneLocal1PlacedOk A H :=
  chainClone_of_protoChainClone_local1_gen
    (protoChain_clone_local1_placed_ok hshim halloc hmemcpy hpanic)

theorem senderChain_clone_local1_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_82 H)
      (lsρ lsRustNoAllocShimSym) CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok (lsProg_82 H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_82 H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    SenderChainCloneLocal1PlacedOk A H :=
  senderChainClone_of_chainClone_local1_gen
    (protoChain_clone_local1_placed_ok_of_hooks hshim halloc hmemcpy hpanic)

/-- Relocatable `SenderChain` specialization of `<Chain as Clone>::clone` (block `82`) satisfies `senderChainCloneSpec A`. -/
theorem senderChain_clone_local1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    SenderChainCloneLocal1PlacedOk A H :=
  senderChainClone_of_chainClone_local1_gen
    (protoChain_clone_local1_placed_ok hshim halloc hmemcpy hpanic)

end Placed

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
