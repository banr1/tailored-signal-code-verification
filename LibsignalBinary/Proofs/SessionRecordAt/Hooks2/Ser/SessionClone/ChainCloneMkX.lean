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
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneMk
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]` `message_keys` Clone Loop (`0x38570..0x38748`)

Verifies the empty fast path and non-empty `Vec<MessageKey>` allocation and per-element seed-cloning
loop of `<session_structure::Chain as Clone>::clone [local#1]` (`0x24848`) on `SP2Ext`.
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

theorem L1_ChainCloneMkX : True := trivial

set_option maxHeartbeats 1600000 in
/-- Fast path when `x.gc.2.messageKeys = []` at `+0x2dc` (`0x38748: mov w9, #8`). -/
theorem chain_clone_mks_nil_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (_hC : SerContractsX img A ext)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 732#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      Qp := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  clone_fetches_range img.base ext hfn 183 184
  clear hfn
  have hep := fun s' => chain_clone_epilogue_x (img := img) (A := A) (ext := ext) (Qp := Qp)
    x s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + bv% (736))
  wp_steps
  refine SepWP.done ?_ ?_ ?_
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · refine SepWPpIn.weaken_pre ?_
      (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · have hbuf_nil :
          vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
            ([].zip x.gc.2.messageKeys) = emp := by
        simpa [hnil] using vecBuf_mk_nil_eq A
      rw [hbuf_nil, emp_sepConj]
      exact Entails.refl _
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
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm]; assumption
    · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
    · exact htrace
    · simp only [wp_norm]; assumption

set_option maxHeartbeats 1600000 in
theorem chain_clone_mk_loop_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = mkPtr')
    (hx26 : s.readReg64 (Reg.gpr 26#5) = srcCur)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 (104 * doneLen))
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (keys' : List MessageKeyGhost) (v11' v13' : BitVec 64) (w12b' : BitVec 32),
      keys'.length = rem.length →
      sf.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A) 104 srcCur rem ∗
          arrayAt (messageKeyAt A) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool ∗
          stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro hfl hsym
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hshim := shim_ok_at_x hC
  have halloc := alloc_ok_at_x hC
  have hmemcpy := memcpy_ok_at_x hC
  have hpanic824 := fun s P => chain_clone_panic_824_x (img := img) (A := A) (ext := ext) (Q := Q) x s0 s P R
  dsimp only [Proofs.libsignal.Stage1X.session2ShimSpecX] at hshim
  clone_fetches_range img.base ext hfn 87 108
  clone_fetches_range img.base ext hfn 148 172
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic824 hcont ⊢
  examples_hide_fetches
  induction rem generalizing s doneLen srcCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (644))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_shim hsym_shim
    have hshim_state := shim_ok_at_stateX hshim hfl_shim hsym_shim
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_shim hsym_shim (mid := entry + bv% (648))
    wp_steps
    wp_call hshim_state ()
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_alloc hsym_alloc
    have hsp1 : sf.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (660))
    wp_steps
    wp_call halloc_state (mkg.seed.length, 1)
    rw [hsp1, hsp]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_post_alloc hsym_post_alloc
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
      have htrace_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htrace_alloc_oom, hpost, htrace]
      apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (824))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl_panic hsym_panic
      refine hpanic824 _ _ ?_ ?_ htrace_oom hfl_panic hsym_panic
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hmod, htrace_alloc_ok⟩ => ?_
      have htrace1 : sf_1.trace = s0.trace := by
        rw [htrace_alloc_ok, hpost, htrace]
      rw [List.length_cons,
          memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
          memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun d => ?_
      have hmemcpy_state := memcpy_ok_at_stateX hmemcpy hfl_post_alloc hsym_post_alloc
      apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (404))
      wp_steps
      wp_call hmemcpy_state (sf_1.readReg64 Reg.x0, gk.seed.ptr, mkg.seed)
      have htr_sf2 : sf_2.trace = s0.trace := by rw [‹sf_2.trace = sf_1.trace›, htrace1]
      rw [hsp_sf_1, hsp1, hsp]
      wp_compact
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl_post_memcpy hsym_post_memcpy
      let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
        (sf_1.readReg64 (Reg.gpr 0#5))
      rw [sepConj_left_comm (P := A.live (sf_1.readReg64 (Reg.gpr 0#5)) mkg.seed.length 1) (Q := A.pool)]
      refine SepWPp.weaken_pre
        (fold_iter_messageKeys A gk mkg srcCur
          (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
          (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _
          hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64) ?_
      cases rem' with
        | nil =>
          apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_memcpy hsym_post_memcpy (mid := entry + bv% (688))
          rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
          simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
            sepConj_emp, emp_sepConj, sepConj_assoc]
          wp_steps
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          intro hfl_688 hsym_688
          refine SepWPp.weaken_pre ?_
            (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfl_688 hsym_688)
          · simp only [List.map, List.zip_cons_cons, List.zip_nil_right,
              arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
            exact Entails.of_eq (by ac_rfl)
          · simp only [wp_norm]
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]; assumption
          · simp only [wp_norm]
          · exact htr_sf2
          · simp only [wp_norm, *]
        | cons p2 rem'' =>
          have hrem'_pos : 0 < (p2 :: rem'').length := by simp
          have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem'_pos
              (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
          apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_memcpy hsym_post_memcpy (mid := entry + bv% (408))
          rw [List.length_cons, ofNat_succ_sub_one, off_add_104]
          wp_steps
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          intro hfl_408 hsym_408
          have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
            simp at htot ⊢; omega
          refine SepWPp.weaken_pre ?_
            (ih (by simp) (doneLen + 1) htot' _ (srcCur + 104#64) 0#64 1#64 mkg.counter
              (messageKeyAt A (gk, mkg) srcCur ∗
                messageKeyAt A (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              htr_sf2
              (by simp only [wp_norm, arm64_norm, *])
              hfl_408 hsym_408
              (by simp only [wp_norm, arm64_norm, *])
              (fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f => ?_))
          · exact Entails.of_eq (by ac_rfl)
          · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
              (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f
            rw [List.map_cons, List.zip_cons_cons,
              arrayAt_cons (x := (gk, mkg)),
              arrayAt_cons (x := (gk', (gk, mkg).2)),
              ptr_off_add_104] at hdone
            dsimp only at hdone
            simp only [sepConj_assoc] at hdone
            refine SepWPpIn.weaken_pre ?_ hdone
            exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
/-- Non-empty `message_keys` allocation, loop, and register reload (`0x38570 .. 0x38734`). -/
theorem chain_clone_mks_nonempty_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (x : ChainCloneGhost) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin) (R : SepProp)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 x.gc.2.messageKeys.length)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = x.src)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
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
  have hpanic860 := fun s P => chain_clone_panic_860_x (img := img) (A := A) (ext := ext)
    (Q := fun sf P_f =>
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
    x s0 s P R
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_mk_loop_x (img := img) (A := A) (ext := ext) hC
      (Q := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      s' srcCur mkPtr' v11 v13 w12b F R
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_epilogue_x (img := img) (A := A) (ext := ext)
      (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R))
      x s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  dsimp only [Proofs.libsignal.Stage1X.session2ShimSpecX] at hshim
  clone_fetches_range img.base ext hfn 65 87
  clone_fetches_range img.base ext hfn 172 179
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr chainCloneLocal1Name = entry
  generalize (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) =
    onPanicPred at hpanic860 hloop hep ⊢
  examples_hide_fetches
  rw [chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) =
      (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        ((s0.sp - 208#64) ↦₆₄ spSlots.v0) ∗
        ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
        ((s0.sp - 196#64) ↦₃₂ spSlots.w1b) ∗
        ((s0.sp - 192#64) ↦₆₄ spSlots.v2) ∗
        ((s0.sp - 184#64) ↦₆₄ spSlots.v3) ∗
        ((s0.sp - 176#64) ↦₆₄ spSlots.v4) ∗
        ((s0.sp - 168#64) ↦₆₄ spSlots.v5) ∗
        ((s0.sp - 160#64) ↦₆₄ spSlots.v6) ∗
        ((s0.sp - 152#64) ↦₆₄ spSlots.v7) ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        savedRegsCore s0) by ac_rfl]
  refine SepWPp.pure_elim fun ⟨hmk_le, hmk_lt, hmk_ptr⟩ => ?_
  have hmul_eq : BitVec.ofNat 64 x.gc.2.messageKeys.length * 104#64 =
      BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length) :=
    mul_104_eq x.gc.2.messageKeys.length
  have hmul_toNat : (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)).toNat =
      104 * x.gc.2.messageKeys.length :=
    toNat_mul_104 hmax
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hmk_lay : LayoutOk (104 * x.gc.2.messageKeys.length) 8 :=
    ⟨by omega, hpow8, by unfold maxMessageKeys at hmax; omega⟩
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (292))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_shim hsym_shim
  have hshim_state := shim_ok_at_stateX hshim hfl_shim hsym_shim
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_shim hsym_shim (mid := entry + bv% (296))
  wp_steps
  wp_call hshim_state ()
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_alloc hsym_alloc
  have hsp1 : sf.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
  have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (308))
  wp_steps
  wp_call halloc_state (104 * x.gc.2.messageKeys.length, 8)
  rw [hsp1, hsp]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl_post_alloc hsym_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    have htrace_oom : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
      rw [htrace_alloc_oom, hpost, htrace]
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (860))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_panic hsym_panic
    refine hpanic860 _ _ ?_ ?_ htrace_oom hfl_panic hsym_panic
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod8, htrace_alloc_ok⟩ => ?_
    have htrace1 : sf_1.trace = s0.trace := by
      rw [htrace_alloc_ok, hpost, htrace]
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (408))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl_loop hsym_loop
    let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
    refine SepWPp.weaken_pre ?_
      (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
        (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
          memRegion x.dst 104 ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
          ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
          chainMkSourceFrame A x.gc x.src ∗
          ((s0.sp - 208#64) ↦₆₄ x28) ∗
          ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
          ((s0.sp - 196#64) ↦₃₂ w27) ∗
          ((s0.sp - 192#64) ↦₆₄ x25) ∗
          ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
          ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
          ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
          ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          savedRegsCore s0)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l => ?_)
        hfl_loop hsym_loop)
    · rw [hzip_len, BitVec.add_zero]
      exact Entails.of_eq (by dsimp only [mkPtr']; ac_rfl)
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · simp only [wp_norm, *]
    · simp only [wp_norm, *]
    · simp only [wp_norm]; rfl
    · simp only [wp_norm, *]
    · simp only [wp_norm, hzip_len]
    · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
    · exact htrace1
    · simp only [wp_norm, *]
    · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
      have hsp_l_align : sf_l.spAligned = true := by
        rw [State.spAligned, hsp_l]
        exact spAligned_sub s0.sp 208 hs0_align (by decide)
      have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
        (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
        sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (736))
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · refine SepWPpIn.weaken_pre ?_
          (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        ·
          have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
            simp [hklen]
          have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
            rw [hzip'_len]; exact hpos
          have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
            rw [hzip'_len]; exact hmax
          have hbuf_eq := vecBuf_mk_pos_eq A mkPtr' (keys'.zip x.gc.2.messageKeys)
            hzip'_pos hzip'_max hoom64
          rw [hzip'_len] at hbuf_eq
          rw [hbuf_eq,
              chainAt_eq_mk_source A x.gc x.src hsrk hmax hsrc_klen hpos,
              spillSlotsExist_eq_struct s0.sp,
              savedRegsOnStack_eq_core s0]
          have hsp_fold :
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ⊢
                (∃∗ s : SpillSlots,
                  ((s0.sp - 208#64) ↦₆₄ s.v0) ∗
                  ((s0.sp - 200#64) ↦₃₂ s.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ s.w1b) ∗
                  ((s0.sp - 192#64) ↦₆₄ s.v2) ∗
                  ((s0.sp - 184#64) ↦₆₄ s.v3) ∗
                  ((s0.sp - 176#64) ↦₆₄ s.v4) ∗
                  ((s0.sp - 168#64) ↦₆₄ s.v5) ∗
                  ((s0.sp - 160#64) ↦₆₄ s.v6) ∗
                  ((s0.sp - 152#64) ↦₆₄ s.v7)) := by
              apply Entails.sepExists_right
                ⟨x28, spSlots.w1a, w27, x25, privPtr',
                  BitVec.ofNat 64 x.gc.1.priv.bytes.length, srkPtr',
                  BitVec.ofNat 64 x.gc.1.srk.bytes.length, x.dst⟩
              dsimp only
              exact Entails.refl _
          have hsr_fold :
              (((s0.sp - 120#64) ↦₆₄ v11') ∗
                ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                savedRegsCore s0) ⊢
              (∃∗ p : BitVec 64 × BitVec 32,
                ((s0.sp - 120#64) ↦₆₄ p.1) ∗
                ((s0.sp - 108#64) ↦₃₂ p.2) ∗
                savedRegsCore s0) := by
            apply Entails.sepExists_right (v11', w12b')
            dsimp only
            exact Entails.refl _
          have hsrc_fold :
              (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                chainMkSourceFrame A x.gc x.src) ⊢
              (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
                  x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
                ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                chainMkSourceFrame A x.gc x.src) :=
            Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
          have hgroup_pre :
              (arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
                ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                ((s0.sp - 120#64) ↦₆₄ v11') ∗
                ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                ((s0.sp - 104#64) ↦₆₄ v13') ∗
                A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                chainMkSourceFrame A x.gc x.src ∗
                ((s0.sp - 208#64) ↦₆₄ x28) ∗
                ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                ((s0.sp - 196#64) ↦₃₂ w27) ∗
                ((s0.sp - 192#64) ↦₆₄ x25) ∗
                ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                ((s0.sp - 152#64) ↦₆₄ x.dst) ∗
                ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                savedRegsCore s0) =
              (memRegion x.dst 104 ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
                vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
                (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
                  arrayAt (messageKeyAt A) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
                clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
                (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
                  arrayAt (messageKeyAt A) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
                  chainMkSourceFrame A x.gc x.src) ∗
                A.pool ∗
                stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
                (((s0.sp - 208#64) ↦₆₄ x28) ∗
                  ((s0.sp - 200#64) ↦₃₂ spSlots.w1a) ∗
                  ((s0.sp - 196#64) ↦₃₂ w27) ∗
                  ((s0.sp - 192#64) ↦₆₄ x25) ∗
                  ((s0.sp - 184#64) ↦₆₄ privPtr') ∗
                  ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
                  ((s0.sp - 168#64) ↦₆₄ srkPtr') ∗
                  ((s0.sp - 160#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
                  ((s0.sp - 152#64) ↦₆₄ x.dst)) ∗
                ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
                ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
                ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
                ((s0.sp - 104#64) ↦₆₄ v13') ∗
                (((s0.sp - 120#64) ↦₆₄ v11') ∗
                  ((s0.sp - 108#64) ↦₃₂ w12b') ∗
                  savedRegsCore s0)) := by
            ac_rfl
          rw [hgroup_pre]
          exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsrc_fold
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono hsp_fold
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right hsr_fold))))))))))))
        · simp only [wp_norm]
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]; assumption
        · rw [State.spAligned] at hsp_l_align ⊢; simp only [wp_norm]; exact hsp_l_align
        · simp only [wp_norm]; assumption
        · simp only [wp_norm]
        · simp only [wp_norm]
        · simp only [wp_norm]
        · simp only [wp_norm]
        · simp only [wp_norm]
        · simp only [wp_norm]
        · simp only [wp_norm]
        · simp only [wp_norm]
        · unfold State.readReg32; simp only [wp_norm, htrunc32]
        · exact htr_l
        · simp only [wp_norm, *]

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
