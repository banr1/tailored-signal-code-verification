/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KSteps
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneCk
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack `FromRecordChainClone` (`Chain::clone [local#3]`) — `priv`, Entry, and Top-Level Contracts

Proves `priv = []` (`+88..+92` / `+228..+240`), `0 < priv.length` (`+88..+144`), function entry and
`srk` clone (`+0..+84`), and top-level `FromRecordChainClone.ChainCloneOkExt` and
`FromRecordChainClone.SenderChainCloneOkExt` under 4K-stack `AllocContracts4K b A ext` and
`CliExternsOk P A ext` for `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]`.
-/

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4.ChainClone4K

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  sessionShimSpec sessionMemcpySpec allocFailedIn_of_eq
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.ChainClone3

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int

attribute [local arm64_norm ↓, local wp_norm ↓]
  BS5.sp_setPC_pre BS5.sp_setMem_setPC_pre
  BS5.readReg64_setPC_pre BS5.readReg64_setMem_setPC_pre
  BS5.readReg32_setPC_pre BS5.readReg32_setMem_setPC_pre
  BS5.readReg_setPC_pre BS5.readReg_setMem_setPC_pre

attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## `priv = []` (`+88..+92` / `+228..+240`) and `0 < priv.length` (`+88..+144`) -/

set_option maxHeartbeats 1600000 in
theorem rce_chain_clone_priv_nil {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : ChainClone4KHooks b A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName + 88#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64) (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr') (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗ A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName =
      (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") :=
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    rce_chain_clone_ck_none (b := b) (A := A) (ext := ext) hH x s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    rce_chain_clone_ck_some (b := b) (A := A) (ext := ext) hH x ck s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  code_fetches_range libsignalSessionCode chainCloneBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") 88 8
  code_fetches_range libsignalSessionCode chainCloneBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") 228 16
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName = entry
  generalize (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hck_none hck_some ⊢
  examples_hide_fetches
  have hpriv_buf :
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by simp [hpriv]
  rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := entry + 232#64)
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · have hfold_priv :
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 40#64) ↦₆₄ 0#64) ∗ chainPrivLenFrame A x.gc x.src ∗ A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          protoChainAt A x.gc x.src ∗ A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) := by
      rw [chainAt_eq_priv_len A x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]; ac_rfl
    rw [hfold_priv]
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + 244#64)
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
        · simpa only [wp_norm] using hvregs
        · exact htrace
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗ A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗ chainCkSomeCapFrame A x.gc ck x.src ∗ A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := entry + 148#64)
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
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗ chainCkSomeCapFrame A x.gc ck x.src ∗ A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗ chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗ memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
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
        · simpa only [wp_norm] using hvregs
        · exact htrace

set_option maxHeartbeats 1600000 in
theorem rce_chain_clone_priv_pos {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : ChainClone4KHooks b A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName + 88#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64) (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr') (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A x.gc x.src ∗ A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName =
      (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") :=
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")
  have hshim := hH.shim_ok
  have halloc := hH.alloc_ok
  have hmemcpy := hH.memcpy_ok
  have hpanic800 := fun s P => rce_chain_clone_panic_800 (b := b) (A := A) (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    rce_chain_clone_ck_none (b := b) (A := A) (ext := ext) hH x s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    rce_chain_clone_ck_some (b := b) (A := A) (ext := ext) hH x ck s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hck
  dsimp only [sessionShimSpec] at hshim
  dsimp only [withStack, sessionMemcpySpec] at hmemcpy
  code_fetches_range libsignalSessionCode chainCloneBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") 88 60
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic800 hck_none hck_some ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic800 hck_none hck_some ⊢
  generalize (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
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
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗ chainPrivPosFrame A x.gc x.src ∗ A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
      (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧ x.gc.1.priv.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗ chainPrivPosFrame A x.gc x.src ∗ A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat :
      (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  apply SepWPp.of_sepWP (mid := entry + 116#64)
  wp_steps
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := by rw [‹sf.trace = s.trace›, htrace]
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [‹calleeSavedVRegs sf = _›, hvregs]
  wp_compact
  wp_steps
  wp_call halloc (x.gc.1.priv.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, htr_sf]
  have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
    rw [‹calleeSavedVRegs sf_1 = _›, hvregs_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + 800#64)
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
        ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗ (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗ A.pool ∗
          A.live privPtr' x.gc.1.priv.bytes.length 1 ∗ memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          chainPrivPosFrame A x.gc x.src ∗ spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) ⊢
        (memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          protoChainAt A x.gc x.src ∗ A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64,
          chainAt_eq_priv_pos A x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
      have hsrc_ent :
          (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗ chainPrivPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
              x.gc.1.priv.cap.toNat < 2 ^ 63 ∧ x.gc.1.priv.ptr ≠ 0⌝ ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗ chainPrivPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ (Entails.refl _)
      have hgroup :
          ((privPtr' ↦ₛ x.gc.1.priv.bytes) ∗ (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗ A.pool ∗
            A.live privPtr' x.gc.1.priv.bytes.length 1 ∗ memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
            ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
            chainPrivPosFrame A x.gc x.src ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
          (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            (A.live privPtr' x.gc.1.priv.bytes.length 1 ∗ (privPtr' ↦ₛ x.gc.1.priv.bytes)) ∗
            (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
              ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
              (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗ chainPrivPosFrame A x.gc x.src) ∗
            A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) := by ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hsrc_ent)))
    apply SepWPp.of_sepWP (mid := entry + 136#64)
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.priv.ptr, x.gc.1.priv.bytes)
    have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹_›
    rw [hsp_sf1]
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
      rw [‹calleeSavedVRegs sf_2 = _›, hvregs_sf1]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_priv_post ?_
    cases hck : x.gc.2.chainKey with
    | none =>
      rw [chainAt_eq_ck_none_cap A x.gc x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + 244#64)
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
        · simpa only [wp_norm] using hvregs_sf2
        · exact htr_sf2
    | some ck =>
      rw [chainAt_eq_ck_some_cap A x.gc ck x.src hsrk hmax hsrc_klen hck]
      simp only [sepConj_assoc]
      rw [show (memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
            chainCkSomeCapFrame A x.gc ck x.src ∗ A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
          (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ memRegion x.dst 104 ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗ chainCkSomeCapFrame A x.gc ck x.src ∗ A.pool ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
            ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
      refine SepWPp.pure_elim fun hck_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hck_lt
      apply SepWPp.of_sepWP (mid := entry + 148#64)
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
                ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗ chainCkSomeCapFrame A x.gc ck x.src ∗ A.pool ∗
                stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
              (((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗ chainCkSomeCapFrame A x.gc ck x.src ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
          rw [show (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                  chainCkSomeCapFrame A x.gc ck x.src) ∗
                A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) =
              (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗ ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
                chainCkSomeCapFrame A x.gc ck x.src ∗ memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
                ((s0.sp - 144#64) ↦₆₄ v8) ∗ ((s0.sp - 136#64) ↦₆₄ v9) ∗
                ((s0.sp - 128#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v13) ∗ savedRegsOnStack s0) by ac_rfl]
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
        · simpa only [wp_norm] using hvregs_sf2
        · exact htr_sf2

/-! ## Function Entry, `srk` Clone (`+0..+84`), and `ProtoChainClone4KOkExt` -/

set_option maxHeartbeats 1600000 in
theorem rce_chain_clone_entry {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : ChainClone4KHooks b A ext)
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true) (R : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName =
      (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") :=
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")
  have hshim := hH.shim_ok
  have halloc := hH.alloc_ok
  have hmemcpy := hH.memcpy_ok
  have hpanic848 := fun s P => rce_chain_clone_panic_848 (b := b) (A := A) (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
    x s0 s P R
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = []) =>
    rce_chain_clone_priv_nil (b := b) (A := A) (ext := ext) hH x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length) =>
    rce_chain_clone_priv_pos (b := b) (A := A) (ext := ext) hH x s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 R hsrk hmax hsrc_klen hpriv_pos
  dsimp only [sessionShimSpec] at hshim
  dsimp only [withStack, sessionMemcpySpec] at hmemcpy
  code_fetches_range libsignalSessionCode chainCloneBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") 0 88
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName = entry
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpec A).post x s0 sf)) =
    postPred at hpanic848 hpriv_nil_lem hpriv_pos_lem ⊢
  generalize (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) =
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
  rw [chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen, stackAt_chainClone_eq_entry s0.sp]
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
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_steps
  wp_call hshim ()
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := ‹calleeSavedVRegs sf = _›
  wp_steps
  wp_call halloc (x.gc.1.srk.bytes.length, 1)
  rw [‹sf.sp = s0.sp - 208#64›, ‹sf.trace = s0.trace›]
  have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
    rw [‹calleeSavedVRegs sf_1 = _›, hvregs_sf]
  wp_compact
  apply SepWP.done ‹_› ‹_›
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := entry + 848#64)
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
        ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗ (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗ A.pool ∗
          A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ memRegion x.dst 104 ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          chainSrkPosFrame A x.gc x.src ∗ spillSlotsExist s0.sp ∗ deadStackSlots s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗ ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗ ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
          protoChainAt A x.gc x.src ∗ A.pool ∗
          stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v25) ∗ ((s0.sp - 136#64) ↦₆₄ v24) ∗
          ((s0.sp - 128#64) ↦₆₄ v23) ∗ ((s0.sp - 104#64) ↦₆₄ v22) ∗ savedRegsOnStack s0) := by
      rw [vecU8Buf_pos_eq A srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
          chainAt_eq_srk_pos A x.gc x.src hsrk hmax hsrc_klen]
      unfold savedRegsOnStack deadStackSlots
      have hsrc_ent :
          (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗ chainSrkPosFrame A x.gc x.src) ⊢
          (⌜x.gc.1.srk.bytes.length ≤ x.gc.1.srk.cap.toNat ∧
              x.gc.1.srk.cap.toNat < 2 ^ 63 ∧ x.gc.1.srk.ptr ≠ 0⌝ ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗ chainSrkPosFrame A x.gc x.src) :=
        Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      have hgroup :
          ((srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗ (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
            stackAt (s0.sp - 208#64) allocHookStack ∗ A.pool ∗
            A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗ memRegion x.dst 104 ∗
            ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
            ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
            chainSrkPosFrame A x.gc x.src ∗ spillSlotsExist s0.sp ∗
            ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
              (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗ ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗ ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
              (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗ chainSrkPosFrame A x.gc x.src) ∗
            A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ spillSlotsExist s0.sp ∗
            ((s0.sp - 144#64) ↦₆₄ v25) ∗ ((s0.sp - 136#64) ↦₆₄ v24) ∗
            ((s0.sp - 128#64) ↦₆₄ v23) ∗ ((s0.sp - 104#64) ↦₆₄ v22) ∗
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
              (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) := by ac_rfl
      rw [hgroup]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent))
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 Reg.x0, x.gc.1.srk.ptr, x.gc.1.srk.bytes)
    have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹_›
    rw [hsp_sf1]
    have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
      rw [‹calleeSavedVRegs sf_2 = _›, hvregs_sf1]
    wp_compact
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := ‹_›
    refine SepWP.done ‹_› ‹_› ?_
    refine SepWPp.weaken_pre hfold_srk_post ?_
    by_cases hpriv_nil : x.gc.1.priv.bytes = []
    · refine hpriv_nil_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_nil
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› hvregs_sf2 htr_sf2
      rw [State.spAligned, hsp_sf2]; exact hsp_sub_align
    · have hpriv_pos : 0 < x.gc.1.priv.bytes.length := List.length_pos_of_ne_nil hpriv_nil
      refine hpriv_pos_lem _ srkPtr' v25 v24 v23 v22 hsrk hmax hsrc_klen hpriv_pos
        ‹_› ‹_› hsp_sf2 ?_ ‹_› ‹_› ‹_› ‹_› ‹_› hvregs_sf2 htr_sf2
      rw [State.spAligned, hsp_sf2]; exact hsp_sub_align

theorem rce_protoChain_clone_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : ChainClone4KHooks b A ext) :
    ProtoChainClone4KOkExt b A ext := by
  refine ProofLib.subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hs0_align => ?_
  simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack,
    R, by simpa [sepConj_assoc] using hmem, fun R' hm' hL => ?_⟩
  obtain ⟨sf, hsteps,
      ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ |
      ⟨hpan_f, P_f, hmem_f, hpan_post⟩ |
      ⟨hoom_s, hoom⟩⟩ :=
    rce_chain_clone_entry hH x s0 hs0_align R hpc hrun hx0 hx1 R' hm' hL
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hrun_f, P_f, hmem_f,
      ⟨fun hm_f => Satisfies.mono (sepConj_mono_left hpost_f) hm_f, hsp_f, hcc_f⟩⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_f, P_f, hmem_f, hpan_post⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom⟩)⟩

end CryptoVerification.Cli.LibsignalSpqrV1.M4.ChainClone4K

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks)

/-! ## Top-Level 4K-Stack `ChainCloneOkExt` and `SenderChainCloneOkExt` (`[local#3]`) -/

/-- Construct `ChainClone4K.ChainClone4KHooks` (`[local#3]`) from `AllocContracts4K b A ext`. -/
theorem ChainClone4K.ChainClone4KHooks.of_alloc4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    ChainClone4K.ChainClone4KHooks b A ext where
  shim_ok := by
    have hk :
        (bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")) % 2^64) : BitVec 64) =
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]"))) := rfl
    rw [hk, ChainClone4K.rce_shim_spec_eq]
    exact hA.shim_ok_at
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName
      (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")))
      (by simp only [arm64_norm])
  alloc_ok := by
    have hk :
        (bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")) % 2^64) : BitVec 64) =
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]"))) := rfl
    rw [hk]
    exact hA.alloc_ok_at
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName
      (num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")))
      (by simp only [arm64_norm])
  memcpy_ok := by
    have hk :
        (bv% ((2^64 + ls_off% "memcpy" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")) % 2^64) : BitVec 64) =
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]"))) := rfl
    rw [hk, ChainClone4K.rce_memcpy_spec_eq]
    exact hA.session_memcpy_region_ok_at
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName
      (num% (ls_off% "memcpy" - (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]")))

/-- `<Chain as Clone>::clone [local#3]` satisfies `FromRecordChainClone.ChainCloneOkExt b A ext`
under 4K-stack `AllocContracts4K b A ext`. -/
theorem chain_clone_ok_4k_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt b A ext :=
  ChainClone4K.rce_chainClone_of_protoChainClone
    (ChainClone4K.rce_protoChain_clone_ok (.of_alloc4k hA))

/-- `<Chain as Clone>::clone [local#3]` satisfies `FromRecordChainClone.SenderChainCloneOkExt b A ext`
under 4K-stack `AllocContracts4K b A ext`. -/
theorem senderChain_clone_ok_4k_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt b A ext :=
  ChainClone4K.rce_senderChainClone_of_chainClone
    CryptoVerification.LibsignalTripleRatchet.ChainClone3.optSenderChainAt_some_eq_chainAt
    (ChainClone4K.rce_protoChain_clone_ok (.of_alloc4k hA))

/-- `<Chain as Clone>::clone [local#3]` satisfies `FromRecordChainClone.ChainCloneOkExt b A ext'`
for any `ext'` agreeing on CLI hooks with `CliExternsOk P A ext`. -/
theorem chain_clone_ok_externs_with_on {b : BitVec 64} {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt b A ext' :=
  chain_clone_ok_4k_ext (AllocContracts4K.of_externsOk_on hOk hAg b)

/-- `<Chain as Clone>::clone [local#3]` satisfies `FromRecordChainClone.SenderChainCloneOkExt b A ext'`
for any `ext'` agreeing on CLI hooks with `CliExternsOk P A ext`. -/
theorem senderChain_clone_ok_externs_with_on {b : BitVec 64} {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt b A ext' :=
  senderChain_clone_ok_4k_ext (AllocContracts4K.of_externsOk_on hOk hAg b)

/-- `<Chain as Clone>::clone [local#3]` satisfies
`FromRecordChainClone.ChainCloneOkExt b A (SignalSession.cliExternsWith ext)` under `CliExternsOk P A ext`. -/
theorem chain_clone_ok_externs_with {b : BitVec 64} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt b A
      (SignalSession.cliExternsWith ext) :=
  chain_clone_ok_4k_ext (AllocContracts4K.of_externsOk hOk b)

/-- `<Chain as Clone>::clone [local#3]` satisfies
`FromRecordChainClone.SenderChainCloneOkExt b A (SignalSession.cliExternsWith ext)` under `CliExternsOk P A ext`. -/
theorem senderChain_clone_ok_externs_with {b : BitVec 64} {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt b A
      (SignalSession.cliExternsWith ext) :=
  senderChain_clone_ok_4k_ext (AllocContracts4K.of_externsOk hOk b)

end CryptoVerification.Cli.LibsignalSpqrV1.M4
