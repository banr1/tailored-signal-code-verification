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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneCk
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `Chain::clone [local#1]` `chain_key` Stage (Block `82`)

Verifies the relocatable `chain_key = none` (`+244 → ret`) and `chain_key = some ck` (`+148 → ret`)
branches of Block `82` (`Chain::clone [local#1]`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneCkXBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey PublicKey ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
)
open CryptoVerification.E2E.Record.Placed (blkPl_82 lsProg_82)
open CryptoVerification.RustHeap (LayoutOk vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (ChainGhost optChainKeyNone)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (ChainCloneGhost)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (
  beq_ofNat_zero_eq_false chainAt_eq_ck_some chainAt_eq_mk_len chainCkSomeFrame
  clonedOptChainKeyBuf
  fp_neg_8 fp_neg_12 fp_neg_24 fp_neg_32 fp_neg_40 fp_neg_48
  fp_neg_8_int fp_neg_12_int fp_neg_24_int fp_neg_32_int fp_neg_40_int fp_neg_48_int
  protoChainAt savedRegsOnStack spillSlotsExist vecU8Buf_pos_eq
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.ChainCloneStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  chainCloneEvents protoChainCloneSpecX
  SepWPpLs sepWPp_of_sepWP_lscl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueXBudget (
  shim_placed_ok_at_stateX_82 allocNoOom_placed_ok_at_stateX_82 memcpy_placed_ok_at_stateX_82
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlacedBudget (
  evsFromCk evsFromMks
  chain_clone_mks_nil_placed_x chain_clone_mks_nonempty_placed_x
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

/-! ## `evsFromCk` stage reductions -/

theorem evsFromCk_of_none {gc : ChainGhost × ReceiverChain} (hck : gc.2.chainKey = none) :
    evsFromCk gc = evsFromMks gc := by
  simp [evsFromCk, hck]

theorem evsFromCk_of_some {gc : ChainGhost × ReceiverChain} {ck : ChainKey}
    (hck : gc.2.chainKey = some ck) :
    evsFromCk gc = rustAllocEvents 32 1 ++ evsFromMks gc := by
  simp [evsFromCk, hck]

/-! ## `chain_key = none` branch (`+244 → ret`) -/

theorem chain_clone_ck_none_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st stCur : M.σ) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = none)
    (hfits : FitsEvents M lim stCur (evsFromCk x.gc))
    (hst_eq : M.stepEvents (evsFromCk x.gc) stCur = M.stepEvents (chainCloneEvents x.gc) st)
    (hpc : s.pc = (blkPl_82).base + 244#64)
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
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
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
  rw [evsFromCk_of_none hck] at hfits hst_eq
  have hmks_nil := fun s' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stCur s0 s' srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hnil hst_eq
  have hmks_ne := fun s' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stCur s0 s' hs0_align
      srkPtr' privPtr' optChainKeyNone (s.readReg64 (Reg.gpr 28#5))
      v9 v10 v13 (s.readReg32 (Reg.gpr 27#5)) x.gc.1.ck
      hsrk hmax hsrc_klen hpos hfits hst_eq
  intro hcl
  rw [chainAt_eq_mk_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen]
  simp only [sepConj_assoc]
  have hck_buf :
      clonedOptChainKeyBuf A.repAlloc x.gc.1.ck optChainKeyNone
        (s.readReg64 (Reg.gpr 28#5)) (s.readReg32 (Reg.gpr 27#5)) x.gc.2.chainKey = emp := by
    rw [hck]; simp only [clonedOptChainKeyBuf, pure_true]
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_82).base + bv% (732))
    wp_steps_sync_pool ((blkPl_82).base + bv% (732))
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl1 => ?_
    refine SepWPp.weaken_pre ?_
      (hmks_nil _ hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl1)
    · rw [hck_buf, emp_sepConj,
          chainAt_eq_mk_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen, hlen0]
      exact Entails.of_eq (by sep_ac_rfl)
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
    · simp only [wp_norm]; exact htrace
    · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_82).base + bv% (260))
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase CryptoVerification.E2E.Record.Placed.blkPC_82 (blkPl_82).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      CryptoVerification.E2E.Record.Placed.blkLib_eq_82
      (mid := (blkPl_82).base + bv% (260))
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun hcl1 => ?_
    refine SepWPp.weaken_pre ?_
      (hmks_ne _ hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl1)
    · rw [hck_buf, emp_sepConj,
          chainAt_eq_mk_len A.repAlloc x.gc x.src hsrk hmax hsrc_klen]
      exact Entails.of_eq (by sep_ac_rfl)
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
    · simp only [wp_norm]; exact htrace
    · simp only [wp_norm]; assumption

/-! ## `chain_key = some ck` branch (`+148 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_ck_some_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (ck : ChainKey) (st stCur : M.σ) (s0 s : State)
    (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' v8 v9 v10 v13 : BitVec 64)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hck : x.gc.2.chainKey = some ck)
    (hfits : FitsEvents M lim stCur (evsFromCk x.gc))
    (hst_eq : M.stepEvents (evsFromCk x.gc) stCur = M.stepEvents (chainCloneEvents x.gc) st)
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
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
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
  rw [evsFromCk_of_some hck] at hfits hst_eq
  obtain ⟨hfits_ck, hfits_mks⟩ := (fitsEvents_append M lim _ _ stCur).mp hfits
  obtain ⟨⟨hck_max, hck_enf, hck_ram, hck_va⟩, -⟩ : FitsEvents M lim stCur [.alloc 32] := hfits_ck
  rw [M.stepEvents_append] at hst_eq
  let stMks := M.stepEvents (rustAllocEvents 32 1) stCur
  have hmks_nil := fun s' ckPtr' (hnil : x.gc.2.messageKeys = []) =>
    chain_clone_mks_nil_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stMks s0 s' srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hnil hst_eq
  have hmks_ne := fun s' ckPtr' (hpos : 0 < x.gc.2.messageKeys.length) =>
    chain_clone_mks_nonempty_placed_x (M := M) (A := A) (lim := lim) (H := H) hC (Qp := Qp)
      x st stMks s0 s' hs0_align
      srkPtr' privPtr' 32#64 ckPtr'
      v9 v10 v13 ck.index ⟨32#64, ckPtr'⟩
      hsrk hmax hsrc_klen hpos hfits_mks hst_eq
  intro hcl
  rw [chainAt_eq_ck_some A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
  simp only [sepConj_assoc]
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        chainCkSomeFrame A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) by sep_ac_rfl]
  refine SepWPp.pure_elim fun ⟨hck_le, hck_lt, hck_ptr⟩ => ?_
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hck_lay : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hck_rlay : RustLayoutOk 32 1 := ⟨hck_lay, by decide⟩
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have htrunc32_ck : BitVec.truncate 32 (BitVec.zeroExtend 64 ck.index) = ck.index :=
    (BitVec.setWidth_setWidth_of_le ck.index (by decide)).trans (BitVec.setWidth_eq ck.index)
  apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_shim => ?_
  have hshim_state := shim_placed_ok_at_stateX_82 hC hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_82).base + bv% (168))
  wp_call hshim_state ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, *] at *
  refine SepWP.done ‹_› ‹_› fun hcl_after_shim => ?_
  apply sepWPp_of_sepWP_lscl hcl_after_shim (mid := lsρ lsRustAllocSym)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_alloc => ?_
  have halloc_state := allocNoOom_placed_ok_at_stateX_82 hC hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_82).base + bv% (180))
  wp_call halloc_state (32, 1, stCur)
  have hsp_sf : sf.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf]
  refine SepWP.done ‹_› ‹_› fun hcl_post_alloc => ?_
  have hacp1 := ‹AllocCallPreserved _ sf_1›
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹sf_1.sp = _›.trans hsp_sf
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have htrace1 : sf_1.trace = s0.trace := hacp1.2.1.trans htr_sf
  let ckPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  have hfold_ck_post : ∀ (sPool : State),
      (A.pool lim stMks sPool ∗
        (ckPtr' ↦ₛ keyToBytes32 ck.key) ∗
        (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        A.live ckPtr' 32 1 ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
        ((x.src + 88#64) ↦₆₄ 32#64) ∗
        ((x.src + 96#64) ↦₃₂ ck.index) ∗
        chainCkSomeFrame A.repAlloc x.gc x.src ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) ⊢
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stMks sPool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) := by
    intro sPool
    have hck_buf_eq :
        clonedOptChainKeyBuf A.repAlloc ⟨32#64, ckPtr'⟩ 32#64 ckPtr' ck.index x.gc.2.chainKey =
          A.live ckPtr' 32 1 ∗ (ckPtr' ↦ₛ keyToBytes32 ck.key) := by
      rw [hck]
      simp only [clonedOptChainKeyBuf, and_self, pure_true, emp_sepConj]
      have hpos32 : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
      have hlt32 : (keyToBytes32 ck.key).length < 2 ^ 63 := by rw [hck_len]; decide
      have hv := vecU8Buf_pos_eq A.repAlloc ckPtr' (keyToBytes32 ck.key) hpos32 hlt32 hoom64
      rw [hck_len] at hv
      exact hv
    rw [hck_buf_eq,
        chainAt_eq_ck_some A.repAlloc x.gc ck x.src hsrk hmax hsrc_klen hck]
    have hsrc_ent :
        (((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          chainCkSomeFrame A.repAlloc x.gc x.src) ⊢
        (⌜32 ≤ x.gc.1.ck.cap.toNat ∧ x.gc.1.ck.cap.toNat < 2 ^ 63 ∧ x.gc.1.ck.ptr ≠ 0⌝ ∗
          ((x.src + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
          ((x.src + 80#64) ↦₆₄ x.gc.1.ck.ptr) ∗
          ((x.src + 88#64) ↦₆₄ 32#64) ∗
          ((x.src + 96#64) ↦₃₂ ck.index) ∗
          (x.gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          chainCkSomeFrame A.repAlloc x.gc x.src) :=
      Entails.pure_right ⟨hck_le, hck_lt, hck_ptr⟩ (Entails.refl _)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hsrc_ent)))))
    exact Entails.of_eq (by dsimp only [stMks]; sep_ac_rfl)
  apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_memcpy => ?_
  have hmemcpy_state := memcpy_placed_ok_at_stateX_82 hC hcl_memcpy
  by_cases hmk_nil : x.gc.2.messageKeys = []
  · have hlen0 : BitVec.ofNat 64 x.gc.2.messageKeys.length = 0#64 := by simp [hmk_nil]
    apply sepWPp_of_sepWP_lscl hcl_memcpy (mid := (blkPl_82).base + bv% (732))
    wp_call hmemcpy_state (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := by
      simp only [wp_norm, arm64_norm, *] at *
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 :=
      ‹sf_2.sp = _›.trans (by simp only [wp_norm, arm64_norm, hsp_sf1])
    have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := by
      simp only [wp_norm, arm64_norm, *] at *
    wp_simp_pre [wp_norm, arm64_norm, hsp_sf1]
    wp_compact
    wp_steps_sync_pool ((blkPl_82).base + bv% (732))
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_732 => ?_
    refine SepWPp.weaken_pre ?_
      (hmks_nil _ ckPtr' hmk_nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_732)
    · refine Entails.trans ?_ (hfold_ck_post _)
      simp only [hlen0, ckPtr', extHookStack]
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
    · simp only [wp_norm]; assumption
    · unfold State.readReg32; simp only [wp_norm]; rw [hx27_sf2, htrunc32_ck]
    · simp only [wp_norm]; exact htr_sf2
    · simp only [wp_norm]; assumption
  · have hpos : 0 < x.gc.2.messageKeys.length := List.length_pos_of_ne_nil hmk_nil
    have hbeq0 : (BitVec.ofNat 64 x.gc.2.messageKeys.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by unfold maxMessageKeys at hmax; omega)
    apply sepWPp_of_sepWP_lscl hcl_memcpy (mid := (blkPl_82).base + bv% (260))
    wp_call hmemcpy_state (ckPtr', x.gc.1.ck.ptr, keyToBytes32 ck.key)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := by
      simp only [wp_norm, arm64_norm, *] at *
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 :=
      ‹sf_2.sp = _›.trans (by simp only [wp_norm, arm64_norm, hsp_sf1])
    have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = BitVec.zeroExtend 64 ck.index := by
      simp only [wp_norm, arm64_norm, *] at *
    wp_simp_pre [wp_norm, arm64_norm, hsp_sf1]
    wp_compact
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := Program.rebase CryptoVerification.E2E.Record.Placed.blkPC_82 (blkPl_82).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none))
      CryptoVerification.E2E.Record.Placed.blkLib_eq_82
      (mid := (blkPl_82).base + bv% (260))
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
    refine SepWP.done (by simp only [wp_norm, hbeq0, Bool.not_false, ↓reduceIte])
      (by simp only [wp_norm]; assumption) fun hcl_260 => ?_
    refine SepWPp.weaken_pre ?_
      (hmks_ne _ ckPtr' hpos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_260)
    · refine Entails.trans ?_ (hfold_ck_post _)
      simp only [ckPtr', extHookStack]
      exact Entails.of_eq (by sep_ac_rfl)
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
    · simp only [wp_norm]; exact htr_sf2
    · simp only [wp_norm]; assumption

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneCkXBudget
