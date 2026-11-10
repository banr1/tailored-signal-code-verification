/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneCkXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneCk
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEntry
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryX
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `Chain::clone [local#1]` Entry and Top-Level Contracts (Block `82`)

Verifies the entry, `sender_ratchet_key`, and `sender_ratchet_key_private` cloning paths and
establishes the budget-threaded Block `82` contracts `ProtoChainCloneLocal1PlacedOkX`,
`ChainCloneLocal1PlacedOkX`, and `SenderChainCloneLocal1PlacedOkX`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryXPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ChainKey PublicKey ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
  extract_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Placed (blkPl_82 lsProg_82)
open CryptoVerification.RustHeap (LayoutOk arrayAt vecBuf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (ChainCloneGhost)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (
  beq_ofNat_zero_eq_false cap_add_one_beq_zero_false
  chainAt_eq_ck_none_cap chainAt_eq_ck_some_cap
  chainAt_eq_priv_len chainAt_eq_priv_pos chainAt_eq_pure_sep chainAt_eq_srk_pos
  chainCkSomeCapFrame chainCloneStackX chainPrivLenFrame chainPrivPosFrame chainSrkPosFrame
  deadStackSlots
  fp_neg_8 fp_neg_12 fp_neg_24 fp_neg_32 fp_neg_40 fp_neg_48
  fp_neg_8_int fp_neg_12_int fp_neg_24_int fp_neg_32_int fp_neg_40_int fp_neg_48_int
  protoChainAt savedRegsOnStack sepWPp_pure_second spillSlotsExist
  srk_length_pos stackAt_chainClone_eq_entry_x vecU8Buf_pos_eq
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.ChainCloneStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  ChainCloneEnv chainCloneEvents fitsEvents_chainClone_of_fitsEnv
  protoChainCloneSpecX
  ProtoChainCloneLocal1PlacedOkX ChainCloneLocal1PlacedOkX SenderChainCloneLocal1PlacedOkX
  SepWPpLs sepWPp_of_sepWP_lscl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueXBudget (
  chainClone_of_protoChainClone_placed_x senderChainClone_of_chainClone_placed_x
  shim_placed_ok_at_stateX_82 allocNoOom_placed_ok_at_stateX_82 memcpy_placed_ok_at_stateX_82
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlacedBudget (
  evsFromCk evsFromMks evsFromPriv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneCkXBudget (
  chain_clone_ck_none_placed_x chain_clone_ck_some_placed_x
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## `evsFromPriv` and `chainCloneEvents` reductions -/

theorem evsFromPriv_of_nil {gc : ChainGhost × ReceiverChain} (hpriv : gc.1.priv.bytes = []) :
    evsFromPriv gc = evsFromCk gc := by
  simp [evsFromPriv, hpriv]

theorem evsFromPriv_of_pos {gc : ChainGhost × ReceiverChain} (hpos : 0 < gc.1.priv.bytes.length) :
    evsFromPriv gc = rustAllocEvents gc.1.priv.bytes.length 1 ++ evsFromCk gc := by
  simp [evsFromPriv, Nat.ne_of_gt hpos]

theorem chainCloneEvents_of_srk_pos {gc : ChainGhost × ReceiverChain}
    (hsrk_pos : 0 < gc.1.srk.bytes.length) :
    chainCloneEvents gc = rustAllocEvents gc.1.srk.bytes.length 1 ++ evsFromPriv gc := by
  cases h : gc.2.chainKey <;>
    simp [chainCloneEvents, evsFromPriv, evsFromCk, evsFromMks, h,
      Nat.ne_of_gt hsrk_pos, List.append_assoc]

/-! ## `priv = []` branch (`+88 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_priv_nil_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st stCur : M.σ) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv : x.gc.1.priv.bytes = [])
    (hfits : FitsEvents M lim stCur (evsFromPriv x.gc))
    (hst_eq : M.stepEvents (evsFromPriv x.gc) stCur = M.stepEvents (chainCloneEvents x.gc) st)
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
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
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
        (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf))
      Qp := by
  rw [evsFromPriv_of_nil hpriv] at hfits hst_eq
  have hck_none := fun s' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stCur s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 hsrk hmax hsrc_klen hck hfits hst_eq
  have hck_some := fun s' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x ck st stCur s0 s' hs0_align
      srkPtr' 1#64 v8 v9 v10 v13 hsrk hmax hsrc_klen hck hfits hst_eq
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf)) =
    postPred at hck_none hck_some ⊢
  intro hcl
  have hpriv_buf :
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) 1#64 x.gc.1.priv.bytes = emp := by
    rw [hpriv]; simp [vecU8Buf, vecBuf, arrayAt]
  have hpriv_len0 : BitVec.ofNat 64 x.gc.1.priv.bytes.length = 0#64 := by
    simp [hpriv]
  rw [chainAt_eq_priv_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
  simp only [sepConj_assoc]
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_82).base + bv% (232))
  wp_steps_sync_pool ((blkPl_82).base + bv% (232))
  refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_232 => ?_
  have hfold_priv : ∀ (sPool : State),
      (A.pool lim stCur sPool ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 40#64) ↦₆₄ 0#64) ∗
        chainPrivLenFrame A.repAlloc x.gc x.src ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stCur sPool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    rw [chainAt_eq_priv_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hpriv_len0]
    sep_ac_rfl
  rw [hfold_priv _]
  cases hck : x.gc.2.chainKey with
  | none =>
    rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl hcl_232 (mid := (blkPl_82).base + bv% (244))
    wp_steps_sync_pool ((blkPl_82).base + bv% (244))
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_244 => ?_
    refine SepWPp.weaken_pre ?_
      (hck_none _ hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_244)
    · rw [hpriv_buf, emp_sepConj,
          chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
      exact Entails.of_eq (by sep_ac_rfl)
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
    rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    rw [show (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim stCur _ ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim stCur _ ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) by sep_ac_rfl]
    refine SepWPp.pure_elim fun hck_lt => ?_
    have hcap_ne := cap_add_one_beq_zero_false hck_lt
    apply sepWPp_of_sepWP_lscl hcl_232 (mid := (blkPl_82).base + bv% (148))
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase CryptoVerification.E2E.Record.Placed.blkPC_82 (blkPl_82).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      CryptoVerification.E2E.Record.Placed.blkLib_eq_82
      (mid := (blkPl_82).base + bv% (148))
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, bne, hcap_ne, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun hcl_148 => ?_
    refine SepWPp.weaken_pre ?_
      (hck_some _ ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_148)
    · rw [hpriv_buf, emp_sepConj,
          chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (Entails.pure_right hck_lt (Entails.refl _)))))
      exact Entails.of_eq (by sep_ac_rfl)
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

/-! ## `0 < priv.length` branch (`+88 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_priv_pos_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st stCur : M.σ) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
    (hfits : FitsEvents M lim stCur (evsFromPriv x.gc))
    (hst_eq : M.stepEvents (evsFromPriv x.gc) stCur = M.stepEvents (chainCloneEvents x.gc) st)
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
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
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
        (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf))
      Qp := by
  rw [evsFromPriv_of_pos hpriv_pos] at hfits hst_eq
  obtain ⟨hfits_priv, hfits_ck⟩ := (fitsEvents_append M lim _ _ stCur).mp hfits
  rw [M.stepEvents_append] at hst_eq
  let stCk := M.stepEvents (rustAllocEvents x.gc.1.priv.bytes.length 1) stCur
  have hck_none := fun s' privPtr' (hck : x.gc.2.chainKey = none) =>
    chain_clone_ck_none_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stCk s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hck hfits_ck hst_eq
  have hck_some := fun s' privPtr' ck (hck : x.gc.2.chainKey = some ck) =>
    chain_clone_ck_some_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x ck st stCk s0 s' hs0_align
      srkPtr' privPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hck hfits_ck hst_eq
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf)) =
    postPred at hck_none hck_some ⊢
  intro hcl
  rw [chainAt_eq_priv_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
          x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
          x.gc.1.priv.ptr ≠ 0⌝ ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
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
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        chainPrivPosFrame A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by sep_ac_rfl]
  refine SepWPp.pure_elim fun ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ => ?_
  have hpriv_lt63 : x.gc.1.priv.bytes.length < 2 ^ 63 := by omega
  have hpriv_toNat : (BitVec.ofNat 64 x.gc.1.priv.bytes.length).toNat = x.gc.1.priv.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_beq0 : (BitVec.ofNat 64 x.gc.1.priv.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hpriv_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpriv_lay : LayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_pos, hpow1, by omega⟩
  have hpriv_rlay : RustLayoutOk x.gc.1.priv.bytes.length 1 := ⟨hpriv_lay, by decide⟩
  apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := Program.rebase CryptoVerification.E2E.Record.Placed.blkPC_82 (blkPl_82).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
    CryptoVerification.E2E.Record.Placed.blkLib_eq_82
    (mid := (lsρ lsRustNoAllocShimSym))
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [wp_norm, hpriv_beq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  refine SepWP.done (by simp only [wp_norm, hpriv_beq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm]; assumption) fun hcl_shim => ?_
  have hshim_state := shim_placed_ok_at_stateX_82 hC hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_82).base + bv% (104))
  wp_call hshim_state ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, *] at *
  refine SepWP.done ‹_› ‹_› fun hcl_after_shim => ?_
  apply sepWPp_of_sepWP_lscl hcl_after_shim (mid := lsρ lsRustAllocSym)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_alloc => ?_
  have halloc_state := allocNoOom_placed_ok_at_stateX_82 hC hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_82).base + bv% (116))
  wp_call halloc_state (x.gc.1.priv.bytes.length, 1, stCur)
  have hsp_sf : sf.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf]
  refine SepWP.done ‹_› ‹_› fun hcl_post_alloc => ?_
  have hacp1 := ‹AllocCallPreserved _ sf_1›
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹sf_1.sp = _›.trans hsp_sf
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have htrace1 : sf_1.trace = s0.trace := hacp1.2.1.trans htr_sf
  let privPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_priv_post : ∀ (sPool : State),
      (A.pool lim stCk sPool ∗
        (privPtr' ↦ₛ x.gc.1.priv.bytes) ∗
        (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        A.live privPtr' x.gc.1.priv.bytes.length 1 ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
        ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        chainPrivPosFrame A.repAlloc x.gc x.src ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) ⊢
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stCk sPool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    rw [vecU8Buf_pos_eq A.repAlloc privPtr' x.gc.1.priv.bytes hpriv_pos hpriv_lt63 hoom64,
        chainAt_eq_priv_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen hpriv_pos]
    have hsrc_ent :
        (((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          chainPrivPosFrame A.repAlloc x.gc x.src) ⊢
        (⌜x.gc.1.priv.bytes.length ≤ x.gc.1.priv.cap.toNat ∧
            x.gc.1.priv.cap.toNat < 2 ^ 63 ∧
            x.gc.1.priv.ptr ≠ 0⌝ ∗
          ((x.src + 32#64) ↦₆₄ x.gc.1.priv.ptr) ∗
          ((x.src + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
          (x.gc.1.priv.ptr ↦ₛ x.gc.1.priv.bytes) ∗
          chainPrivPosFrame A.repAlloc x.gc x.src) :=
      Entails.pure_right ⟨hpriv_le, hpriv_cap_lt, hpriv_ptr⟩ (Entails.refl _)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hsrc_ent))))
    exact Entails.of_eq (by dsimp only [stCk, RustCliAllocBudget.repAlloc]; sep_ac_rfl)
  apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_memcpy => ?_
  have hmemcpy_state := memcpy_placed_ok_at_stateX_82 hC hcl_memcpy
  apply sepWPp_of_sepWP_lscl hcl_memcpy (mid := (blkPl_82).base + bv% (136))
  wp_call hmemcpy_state (privPtr', x.gc.1.priv.ptr, x.gc.1.priv.bytes)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, *] at *
  have hsp_sf2 : sf_2.sp = s0.sp - 208#64 :=
    ‹sf_2.sp = _›.trans (by simp only [wp_norm, arm64_norm, hsp_sf1])
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf1]
  wp_compact
  refine SepWP.done ‹_› ‹_› fun hcl_post_memcpy => ?_
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by simp only [privPtr', extHookStack]; sep_ac_rfl)) (hfold_priv_post _)) ?_
  cases hck : x.gc.2.chainKey with
  | none =>
    rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl hcl_post_memcpy (mid := (blkPl_82).base + bv% (244))
    wp_steps_sync_pool ((blkPl_82).base + bv% (244))
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_244 => ?_
    refine SepWPp.weaken_pre ?_
      (hck_none _ privPtr' hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_244)
    · rw [chainAt_eq_ck_none_cap A.repAlloc x.gc x.src hsrk hmax hsrc_klen hck]
      exact Entails.of_eq (by sep_ac_rfl)
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
    rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    simp only [sepConj_assoc]
    rw [show (memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim stCk _ ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) =
        (⌜x.gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          memRegion x.dst 104 ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
          ((x.src + 72#64) ↦₆₄ x.gc.1.ck.cap) ∗
          chainCkSomeCapFrame A.repAlloc x.gc ck x.src ∗
          A.pool lim stCk _ ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
          spillSlotsExist s0.sp ∗
          ((s0.sp - 144#64) ↦₆₄ v8) ∗
          ((s0.sp - 136#64) ↦₆₄ v9) ∗
          ((s0.sp - 128#64) ↦₆₄ v10) ∗
          ((s0.sp - 104#64) ↦₆₄ v13) ∗
          savedRegsOnStack s0) by sep_ac_rfl]
    refine SepWPp.pure_elim fun hck_lt => ?_
    have hcap_ne := cap_add_one_beq_zero_false hck_lt
    apply sepWPp_of_sepWP_lscl hcl_post_memcpy (mid := (blkPl_82).base + bv% (148))
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase CryptoVerification.E2E.Record.Placed.blkPC_82 (blkPl_82).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      CryptoVerification.E2E.Record.Placed.blkLib_eq_82
      (mid := (blkPl_82).base + bv% (148))
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, hcap_ne, Bool.false_eq_true, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun hcl_148 => ?_
    refine SepWPp.weaken_pre ?_
      (hck_some _ privPtr' ck hck ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_148)
    · rw [chainAt_eq_ck_some_cap A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (Entails.pure_right hck_lt (Entails.refl _))))))
      exact Entails.of_eq (by dsimp only [stCk]; sep_ac_rfl)
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

/-! ## Entry (`+0 → ret`): `srk` clone and `priv` dispatch -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_entry_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st : M.σ) (s0 : State) (hs0_align : s0.spAligned = true)
    (hfits_env : FitsEnv M lim st (ChainCloneEnv x.gc))
    (hpc : s0.pc = (blkPl_82).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.dst)
    (hx1 : s0.readReg64 .x1 = x.src) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s0
      (memRegion x.dst 104 ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim st s0 ∗
        stackAt s0.sp chainCloneStackX)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf))
      Qp := by
  let stPriv := M.stepEvents (rustAllocEvents x.gc.1.srk.bytes.length 1) st
  have hpriv_nil_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv : x.gc.1.priv.bytes = [])
      (hfits_p : FitsEvents M lim stPriv (evsFromPriv x.gc))
      (hst_p : M.stepEvents (evsFromPriv x.gc) stPriv = M.stepEvents (chainCloneEvents x.gc) st) =>
    chain_clone_priv_nil_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stPriv s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv hfits_p hst_p
  have hpriv_pos_lem := fun s' srkPtr' v8 v9 v10 v13
      (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
      (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
      (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
      (hpriv_pos : 0 < x.gc.1.priv.bytes.length)
      (hfits_p : FitsEvents M lim stPriv (evsFromPriv x.gc))
      (hst_p : M.stepEvents (evsFromPriv x.gc) stPriv = M.stepEvents (chainCloneEvents x.gc) st) =>
    chain_clone_priv_pos_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stPriv s0 s' hs0_align
      srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv_pos hfits_p hst_p
  generalize (fun sf P_f =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf)) =
    postPred at hpriv_nil_lem hpriv_pos_lem ⊢
  intro hcl
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hsp_sub_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208 hs0_align (by decide)
  rw [chainAt_eq_pure_sep A.repAlloc x.gc x.src]
  simp only [sepConj_assoc]
  refine sepWPp_pure_second fun ⟨hsrk, hmax, hsrc_klen⟩ => ?_
  have hsrk_pos : 0 < x.gc.1.srk.bytes.length := srk_length_pos hsrk
  have hfits_all : FitsEvents M lim st (chainCloneEvents x.gc) :=
    fitsEvents_chainClone_of_fitsEnv M lim st x.gc hfits_env
  have hevs_srk := chainCloneEvents_of_srk_pos (gc := x.gc) hsrk_pos
  rw [hevs_srk] at hfits_all
  obtain ⟨hfits_srk, hfits_priv⟩ := (fitsEvents_append M lim _ _ st).mp hfits_all
  have hst_priv :
      M.stepEvents (evsFromPriv x.gc) stPriv = M.stepEvents (chainCloneEvents x.gc) st := by
    rw [hevs_srk, M.stepEvents_append]
  rw [chainAt_eq_srk_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen,
      stackAt_chainClone_eq_entry_x s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v25 => SepWPp.exists_elim fun v24 =>
    SepWPp.exists_elim fun v23 => SepWPp.exists_elim fun v22 =>
    SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v15 => SepWPp.exists_elim fun v14 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v10 =>
    SepWPp.exists_elim fun v9 => SepWPp.exists_elim fun v8 => ?_
  refine sepWPp_pure_second fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
  have hsrk_lt63 : x.gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hsrk_toNat : (BitVec.ofNat 64 x.gc.1.srk.bytes.length).toNat = x.gc.1.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrk_beq0 : (BitVec.ofNat 64 x.gc.1.srk.bytes.length == 0#64) = false :=
    beq_ofNat_zero_eq_false hsrk_pos (by omega)
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsrk_lay : LayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_pos, hpow1, by omega⟩
  have hsrk_rlay : RustLayoutOk x.gc.1.srk.bytes.length 1 := ⟨hsrk_lay, by decide⟩
  apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := Program.rebase CryptoVerification.E2E.Record.Placed.blkPC_82 (blkPl_82).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
    CryptoVerification.E2E.Record.Placed.blkLib_eq_82
    (mid := (lsρ lsRustNoAllocShimSym))
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [wp_norm, hsrk_beq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
  simp only [State.setMem_setMem]
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  refine SepWP.done (by simp only [wp_norm, hsrk_beq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [wp_norm]; assumption) fun hcl_shim => ?_
  have hshim_state := shim_placed_ok_at_stateX_82 hC hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_82).base + bv% (56))
  wp_call hshim_state ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, *] at *
  refine SepWP.done ‹_› ‹_› fun hcl_after_shim => ?_
  apply sepWPp_of_sepWP_lscl hcl_after_shim (mid := lsρ lsRustAllocSym)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_alloc => ?_
  have halloc_state := allocNoOom_placed_ok_at_stateX_82 hC hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_82).base + bv% (68))
  wp_call halloc_state (x.gc.1.srk.bytes.length, 1, st)
  have hsp_sf : sf.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf]
  refine SepWP.done ‹_› ‹_› fun hcl_post_alloc => ?_
  have hacp1 := ‹AllocCallPreserved _ sf_1›
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹sf_1.sp = _›.trans hsp_sf
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have htrace1 : sf_1.trace = s0.trace := hacp1.2.1.trans htr_sf
  let srkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_srk_post : ∀ (sPool : State),
      (A.pool lim stPriv sPool ∗
        (srkPtr' ↦ₛ x.gc.1.srk.bytes) ∗
        (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        A.live srkPtr' x.gc.1.srk.bytes.length 1 ∗
        memRegion x.dst 104 ∗
        ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
        ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        chainSrkPosFrame A.repAlloc x.gc x.src ∗
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
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stPriv sPool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    rw [vecU8Buf_pos_eq A.repAlloc srkPtr' x.gc.1.srk.bytes hsrk_pos hsrk_lt63 hoom64,
        chainAt_eq_srk_pos A.repAlloc x.gc x.src hsrk hmax hsrc_klen]
    unfold savedRegsOnStack deadStackSlots
    have hsrc_ent :
        (((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          chainSrkPosFrame A.repAlloc x.gc x.src) ⊢
        (⌜x.gc.1.srk.bytes.length ≤ x.gc.1.srk.cap.toNat ∧
            x.gc.1.srk.cap.toNat < 2 ^ 63 ∧
            x.gc.1.srk.ptr ≠ 0⌝ ∗
          ((x.src + 8#64) ↦₆₄ x.gc.1.srk.ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
          (x.gc.1.srk.ptr ↦ₛ x.gc.1.srk.bytes) ∗
          chainSrkPosFrame A.repAlloc x.gc x.src) :=
      Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsrc_ent)))
    exact Entails.of_eq (by dsimp only [stPriv, RustCliAllocBudget.repAlloc]; sep_ac_rfl)
  apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_memcpy => ?_
  have hmemcpy_state := memcpy_placed_ok_at_stateX_82 hC hcl_memcpy
  apply sepWPp_of_sepWP_lscl hcl_memcpy (mid := (blkPl_82).base + bv% (88))
  wp_call hmemcpy_state (srkPtr', x.gc.1.srk.ptr, x.gc.1.srk.bytes)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  have htr_sf2 : sf_2.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, *] at *
  have hsp_sf2 : sf_2.sp = s0.sp - 208#64 :=
    ‹sf_2.sp = _›.trans (by simp only [wp_norm, arm64_norm, hsp_sf1])
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf1]
  wp_compact
  refine SepWP.done ‹_› ‹_› fun hcl_post_memcpy => ?_
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by simp only [srkPtr', extHookStack]; sep_ac_rfl)) (hfold_srk_post _)) ?_
  by_cases hpriv_nil : x.gc.1.priv.bytes = []
  · refine hpriv_nil_lem _ srkPtr' v8 v9 v10 v13 hsrk hmax hsrc_klen hpriv_nil
      hfits_priv hst_priv ?_ ?_ hsp_sf2 ?_ ?_ ?_ ?_ ?_ ?_ htr_sf2 ?_ hcl_post_memcpy
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
      hfits_priv hst_priv ?_ ?_ hsp_sf2 ?_ ?_ ?_ ?_ ?_ ?_ htr_sf2 ?_ hcl_post_memcpy
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · rw [State.spAligned, hsp_sf2]; exact hsp_sub_align
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]

/-! ## Top-level `subroutine_ok` contracts (Block `82`) -/

theorem protoChain_clone_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    ProtoChainCloneLocal1PlacedOkX M A lim H := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hs0_align hloaded => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits_env⟩, hmem⟩
  obtain ⟨sf, hsteps,
      ⟨hret, hrun_f, P_f, hmem_f, hsp_f, hcc_f, hpost_f⟩ |
      ⟨hpan_f, P_f, hmem_f, hpan_post⟩ |
      ⟨_, hfalse⟩⟩ :=
    chain_clone_entry_placed_x hC
      (Qp := fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX M A lim).onPanic (x, st) s0 sf ∗ R))
      x st s0 hs0_align hfits_env hpc hrun hx0 hx1 hcl R
      (by simpa [sepConj_assoc] using hmem) hloaded
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hret, hsp_f, hrun_f⟩, ⟨hsp_f, hcc_f⟩,
        Satisfies.mono (sepConj_mono_left hpost_f) hmem_f⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inr (Or.inl ⟨hpan_f, hpan_post hmem_f⟩)))
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem chain_clone_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    ChainCloneLocal1PlacedOkX M A lim H :=
  chainClone_of_protoChainClone_placed_x (protoChain_clone_placed_ok_x hC)

theorem senderChain_clone_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    SenderChainCloneLocal1PlacedOkX M A lim H :=
  senderChainClone_of_chainClone_placed_x (protoChain_clone_placed_ok_x hC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEntryXPlacedBudget
