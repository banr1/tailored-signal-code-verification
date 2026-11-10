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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneMk
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `Chain::clone [local#1]` `message_keys` Clone Loop (Block `82`)

Defines deterministic stage event suffixes (`evsMkLoop`, `evsFromMks`, `evsFromCk`, `evsFromPriv`)
and verifies the empty (`+732 → ret`) and non-empty (`+260 → ret`) `message_keys` cloning paths of
Block `82` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (
  MessageKeyGenerator PublicKey ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl lsρ
  lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
)
open CryptoVerification.E2E.Record.Placed (blkPl_82 lsProg_82)
open CryptoVerification.RustHeap (
  LayoutOk arrayAt arrayAt_cons arrayAt_nil vecBuf vecU8Buf
)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost MessageKeyGhost VecPin messageKeyAt
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (ChainCloneGhost)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (
  SpillSlots beq_ofNat_zero_eq_false chainAt_eq_mk_source chainMkSourceFrame
  clonedMessageKeyGhost clonedOptChainKeyBuf fold_iter_messageKeys
  fp_neg_8 fp_neg_12 fp_neg_24 fp_neg_32 fp_neg_40 fp_neg_48
  fp_neg_8_int fp_neg_12_int fp_neg_24_int fp_neg_32_int fp_neg_40_int fp_neg_48_int
  map_snd_zip_of_length_eq memRegion_104_eq_slots104 memRegion_mk_cons
  messageKeyAt_eq_source mul104_beq_eq_false mul_104_eq off_add_104
  ofNat_succ_sub_one protoChainAt ptr_off_add_104 savedRegsCore
  savedRegsOnStack savedRegsOnStack_eq_core spillSlotsExist
  spillSlotsExist_eq_struct toNat_mul_104 vecBuf_mk_nil_eq vecBuf_mk_pos_eq
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1.ChainCloneStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget (
  chainCloneEvents protoChainCloneSpecX
  SepWPpLs sepWPp_of_sepWP_lscl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueXBudget (
  chain_clone_epilogue_placed_x
  shim_placed_ok_at_stateX_82 allocNoOom_placed_ok_at_stateX_82 memcpy_placed_ok_at_stateX_82
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

/-! ## Stage event suffixes and `chainCloneEvents` decomposition -/

/-- Remaining per-`MessageKey` `seed` allocation events in the `mk_loop` tail `rem`. -/
def evsMkLoop (rem : List (MessageKeyGhost × MessageKeyGenerator)) : List AllocEvent :=
  (rem.map Prod.snd).flatMap (fun mkg => rustAllocEvents mkg.seed.length 1)

theorem evsMkLoop_nil : evsMkLoop [] = [] := rfl

theorem evsMkLoop_cons (gk : MessageKeyGhost) (mkg : MessageKeyGenerator)
    (rem : List (MessageKeyGhost × MessageKeyGenerator)) :
    evsMkLoop ((gk, mkg) :: rem) = rustAllocEvents mkg.seed.length 1 ++ evsMkLoop rem := rfl

/-- Deterministic `AllocEvent` suffix emitted from the `message_keys` stage to return. -/
def evsFromMks (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  if gc.2.messageKeys = [] then []
  else
    rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
      gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1)

/-- Deterministic `AllocEvent` suffix emitted from the `chain_key` stage to return. -/
def evsFromCk (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (match gc.2.chainKey with
   | none => []
   | some _ => rustAllocEvents 32 1) ++ evsFromMks gc

/-- Deterministic `AllocEvent` suffix emitted from the `priv` stage to return. -/
def evsFromPriv (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (if gc.1.priv.bytes.length = 0 then []
   else rustAllocEvents gc.1.priv.bytes.length 1) ++ evsFromCk gc

theorem evsFromMks_of_nil {gc : ChainGhost × ReceiverChain} (hnil : gc.2.messageKeys = []) :
    evsFromMks gc = [] := by
  simp [evsFromMks, hnil]

theorem evsFromMks_of_pos {gc : ChainGhost × ReceiverChain}
    (hpos : 0 < gc.2.messageKeys.length)
    (hsrc_klen : gc.1.keys.length = gc.2.messageKeys.length) :
    evsFromMks gc =
      rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
        evsMkLoop (gc.1.keys.zip gc.2.messageKeys) := by
  have hne : gc.2.messageKeys ≠ [] := List.ne_nil_of_length_pos hpos
  unfold evsFromMks evsMkLoop
  simp only [hne, ↓reduceIte, map_snd_zip_of_length_eq gc.1.keys gc.2.messageKeys hsrc_klen]

abbrev evsMkLoop_x := evsMkLoop
abbrev evsMkLoop_nil_x := @evsMkLoop_nil
abbrev evsMkLoop_cons_x := @evsMkLoop_cons
abbrev evsFromMks_x := evsFromMks
abbrev evsFromCk_x := evsFromCk
abbrev evsFromPriv_x := evsFromPriv
abbrev evsFromMks_of_nil_x := @evsFromMks_of_nil
abbrev evsFromMks_of_pos_x := @evsFromMks_of_pos

theorem chainCloneEvents_eq_srk_priv (gc : ChainGhost × ReceiverChain) :
    chainCloneEvents gc =
      (if gc.1.srk.bytes.length = 0 then [] else rustAllocEvents gc.1.srk.bytes.length 1) ++
      evsFromPriv gc := by
  unfold chainCloneEvents evsFromPriv evsFromCk evsFromMks
  simp only [List.append_assoc]
  split_ifs <;> rfl

/-! ## Empty `message_keys` fast path (`+732 → ret`) -/

theorem chain_clone_mks_nil_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (_hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st stCur : M.σ) (s0 s : State)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hnil : x.gc.2.messageKeys = [])
    (hst_eq : M.stepEvents (evsFromMks x.gc) stCur = M.stepEvents (chainCloneEvents x.gc) st)
    (hpc : s.pc = (blkPl_82).base + 732#64)
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
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf))
      Qp := by
  have hstCur : stCur = M.stepEvents (chainCloneEvents x.gc) st := by
    rwa [evsFromMks_of_nil hnil, AllocCostModel.stepEvents] at hst_eq
  subst hstCur
  have hep := fun s' => chain_clone_epilogue_placed_x (M := M) (A := A) (lim := lim)
    (H := H) (Qp := Qp)
    x st s0 s' srkPtr' privPtr' 8#64 x25 x28 v9 v10 v13 w27 [] ckPin'
    hsrk hmax (by simp [hnil]) hsrc_klen
  intro hcl
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_82).base + bv% (736))
  wp_steps_sync_pool ((blkPl_82).base + bv% (736))
  refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl1 => ?_
  refine SepWPp.weaken_pre ?_
    (hep _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl1)
  · have hbuf_nil :
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc)
          (BitVec.ofNat 64 x.gc.2.messageKeys.length) 8#64
          ([].zip x.gc.2.messageKeys) = emp := by
      simpa [hnil] using vecBuf_mk_nil_eq A.repAlloc
    rw [hbuf_nil]
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
  · simp only [wp_norm]
  · simp only [wp_norm]; assumption
  · simp only [wp_norm]; assumption
  · unfold State.readReg32 at hw27 ⊢; simp only [wp_norm]; exact hw27
  · simp only [wp_norm]; exact htrace
  · simp only [wp_norm]; assumption

/-! ## `MessageKey` clone loop (`+408 → +688`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_mk_loop_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Q Qp : State → SepProp → Prop}
    (_x : ChainCloneGhost) (s0 : State) (hs0_align : s0.spAligned = true)
    (total : Nat) (hmax : total ≤ maxMessageKeys)
    (rem : List (MessageKeyGhost × MessageKeyGenerator))
    (hne : rem ≠ [])
    (doneLen : Nat) (htot : doneLen + rem.length = total)
    (stCur : M.σ) (hfits : FitsEvents M lim stCur (evsMkLoop rem))
    (s : State) (srcCur mkPtr' v11 v13 : BitVec 64) (w12b : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_82).base + 408#64)
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
      sf.pc = (blkPl_82).base + 688#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 208#64 →
      sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      sf.readReg64 (Reg.gpr 19#5) = mkPtr' →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) sf
        (arrayAt (messageKeyAt A.repAlloc) 104 srcCur rem ∗
          arrayAt (messageKeyAt A.repAlloc) 104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
            (keys'.zip (rem.map Prod.snd)) ∗
          A.pool lim (M.stepEvents (evsMkLoop rem) stCur) sf ∗
          stackAt (s0.sp - 208#64) extHookStack ∗
          ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
          ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
          ((s0.sp - 120#64) ↦₆₄ v11') ∗
          ((s0.sp - 108#64) ↦₃₂ w12b') ∗
          ((s0.sp - 104#64) ↦₆₄ v13') ∗
          F)
        Q Qp) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (messageKeyAt A.repAlloc) 104 srcCur rem ∗
        memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * rem.length) ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * total)) ∗
        ((s0.sp - 120#64) ↦₆₄ v11) ∗
        ((s0.sp - 108#64) ↦₃₂ w12b) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        F)
      Q Qp := by
  intro hcl
  induction rem generalizing s doneLen srcCur stCur v11 w12b v13 F with
  | nil => exact (hne rfl).elim
  | cons head rem' ih =>
    rcases head with ⟨gk, mkg⟩
    rw [evsMkLoop_cons] at hfits
    obtain ⟨hfits_seed, hfits_rem'⟩ := (fitsEvents_append M lim _ _ stCur).mp hfits
    have hlt_done : doneLen < total := by simp at htot; omega
    have hrem_le : rem'.length + 1 ≤ maxMessageKeys := by simp at htot; omega
    have hcmp : (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false :=
      mul104_beq_eq_false hlt_done hmax
    rw [arrayAt_cons, messageKeyAt_eq_source A.repAlloc gk mkg srcCur]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hseed_pos, hseed_le, hseed_cap_lt, hseed_ptr⟩ => ?_
    have hseed_lt63 : mkg.seed.length < 2 ^ 63 := by omega
    have hseed_toNat : (BitVec.ofNat 64 mkg.seed.length).toNat = mkg.seed.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hseed_beq0 : (BitVec.ofNat 64 mkg.seed.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hseed_pos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hseed_lay : LayoutOk mkg.seed.length 1 := ⟨hseed_pos, hpow2, by omega⟩
    have hseed_rlay : RustLayoutOk mkg.seed.length 1 := ⟨hseed_lay, by decide⟩
    apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_shim => ?_
    have hshim_state := shim_placed_ok_at_stateX_82 hC hcl_shim
    apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_82).base + bv% (648))
    wp_call hshim_state ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    have htr_sf : sf.trace = s0.trace := by
      simp only [wp_norm, arm64_norm, *] at *
    refine SepWP.done ‹_› ‹_› fun hcl_after_shim => ?_
    apply sepWPp_of_sepWP_lscl hcl_after_shim (mid := lsρ lsRustAllocSym)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_alloc => ?_
    have halloc_state := allocNoOom_placed_ok_at_stateX_82 hC hcl_alloc
    apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_82).base + bv% (660))
    wp_call halloc_state (mkg.seed.length, 1, stCur)
    have hsp_alloc : sf.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm, hsp_alloc]
    refine SepWP.done ‹_› ‹_› fun hcl_post_alloc => ?_
    have hacp1 := ‹AllocCallPreserved _ sf_1›
    have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹sf_1.sp = _›.trans hsp_alloc
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have htrace1 : sf_1.trace = s0.trace := by
      have htr_pre : _ = s0.trace := htr_sf
      exact hacp1.2.1.trans (by simp only [wp_norm, arm64_norm, *])
    rw [List.length_cons,
        memRegion_mk_cons mkPtr' doneLen rem'.length hrem_le,
        memRegion_104_eq_slots104 (mkPtr' + BitVec.ofNat 64 (104 * doneLen))]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d => ?_
    apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_memcpy => ?_
    have hmemcpy_state := memcpy_placed_ok_at_stateX_82 hC hcl_memcpy
    apply sepWPp_of_sepWP_lscl hcl_memcpy (mid := (blkPl_82).base + bv% (404))
    wp_call hmemcpy_state (sf_1.readReg64 Reg.x0, gk.seed.ptr, mkg.seed)
    wp_simp_pre [wp_norm, arm64_norm, hsp_sf1]
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    have htr_sf2 : sf_2.trace = s0.trace := by
      simp only [wp_norm, arm64_norm, *] at *
    wp_compact
    wp_steps_sync_pool ((blkPl_82).base + bv% (404))
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_404 => ?_
    let gk' := clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length)
      (sf_1.readReg64 (Reg.gpr 0#5))
    rw [← emp_sepConj (stackAt (s0.sp - 208#64) extHookStack)]
    simp only [sepConj_assoc]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (fold_iter_messageKeys A.repAlloc gk mkg srcCur
        (mkPtr' + BitVec.ofNat 64 (104 * doneLen))
        (sf_1.readReg64 (Reg.gpr 0#5)) emp (stackAt (s0.sp - 208#64) extHookStack) _ _
        hseed_pos hseed_le hseed_cap_lt hseed_ptr hoom64)) ?_
    simp only [emp_sepConj, sepConj_emp, sepConj_assoc]
    rw [List.length_cons, ofNat_succ_sub_one, off_add_104] at hcl_404 ⊢
    cases rem' with
    | nil =>
      simp only [List.length_nil, Nat.mul_zero, memRegion_zero, arrayAt_nil,
        sepConj_emp, emp_sepConj, sepConj_assoc] at hcl_404 ⊢
      apply sepWPp_of_sepWP_lscl hcl_404 (mid := (blkPl_82).base + bv% (688))
      wp_steps_sync_pool ((blkPl_82).base + bv% (688))
      refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_688 => ?_
      refine SepWPp.weaken_pre ?_
        (hcont _ [gk'] 0#64 1#64 mkg.counter rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_688)
      · simp only [evsMkLoop_cons, evsMkLoop_nil, List.append_nil,
          List.map, List.zip_cons_cons, List.zip_nil_right,
          arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_assoc]
        exact Entails.of_eq (by sep_ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · simp only [wp_norm]; exact htr_sf2
      · simp only [wp_norm]; assumption
    | cons p2 rem'' =>
      have hrem'_pos : 0 < (p2 :: rem'').length := by simp
      have hrem'_beq0 : (BitVec.ofNat 64 (p2 :: rem'').length == 0#64) = false :=
        beq_ofNat_zero_eq_false hrem'_pos
          (by unfold maxMessageKeys at hrem_le; simp at hrem_le ⊢; omega)
      apply sepWPp_of_sepWP_lscl hcl_404 (mid := (blkPl_82).base + bv% (408))
      wp_steps_sync_pool ((blkPl_82).base + bv% (408))
      refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_next => ?_
      have htot' : (doneLen + 1) + (p2 :: rem'').length = total := by
        simp at htot ⊢; omega
      refine SepWPp.weaken_pre ?_
        (ih (by simp) (doneLen + 1) htot'
          (M.stepEvents (rustAllocEvents mkg.seed.length 1) stCur) hfits_rem'
          _ (srcCur + 104#64) 0#64 1#64 mkg.counter
          (messageKeyAt A.repAlloc (gk, mkg) srcCur ∗
            messageKeyAt A.repAlloc (gk', mkg) (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) ∗ F)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          (fun sf_f keys'_tail v11' v13' w12b' hklen' hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f hcl_f => ?_)
          hcl_next)
      · exact Entails.of_eq (by sep_ac_rfl)
      · simp only [wp_norm]
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]; assumption
      · simp only [wp_norm]
      · simp only [wp_norm]
      · simp only [wp_norm]
      · simp only [wp_norm]
      · simp only [wp_norm]; exact htr_sf2
      · simp only [wp_norm]; assumption
      · have hdone := hcont sf_f (gk' :: keys'_tail) v11' v13' w12b'
          (by simp [hklen']) hpc_f hrun_f hsp_f hx29_f hx19_f htr_f hvregs_f hcl_f
        rw [evsMkLoop_cons, M.stepEvents_append,
          List.map_cons, List.zip_cons_cons,
          arrayAt_cons (x := (gk, mkg)),
          arrayAt_cons (x := (gk', (gk, mkg).2)),
          ptr_off_add_104] at hdone
        dsimp only at hdone
        simp only [sepConj_assoc] at hdone
        refine SepWPp.weaken_pre ?_ hdone
        exact Entails.of_eq (by sep_ac_rfl)

/-! ## Non-empty `message_keys` allocation and loop (`+260 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem chain_clone_mks_nonempty_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (st stCur : M.σ) (s0 s : State) (hs0_align : s0.spAligned = true)
    (srkPtr' privPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpos : 0 < x.gc.2.messageKeys.length)
    (hfits : FitsEvents M lim stCur (evsFromMks x.gc))
    (hst_eq : M.stepEvents (evsFromMks x.gc) stCur = M.stepEvents (chainCloneEvents x.gc) st)
    (hpc : s.pc = (blkPl_82).base + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
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
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf))
      Qp := by
  generalize hQpost :
    (fun sf P_f =>
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (protoChainCloneSpecX M A lim).post (x, st) s0 sf)) = Qpost
  have hevs_eq := evsFromMks_of_pos hpos hsrc_klen
  rw [hevs_eq] at hfits hst_eq
  obtain ⟨hfits_arr, hfits_loop⟩ := (fitsEvents_append M lim _ _ stCur).mp hfits
  rw [M.stepEvents_append] at hst_eq
  have hzip_len : (x.gc.1.keys.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
    simp [hsrc_klen]
  have hzip_ne : x.gc.1.keys.zip x.gc.2.messageKeys ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hzip_len]; exact hpos)
  have hloop := fun s' srcCur mkPtr' v11 v13 w12b F =>
    chain_clone_mk_loop_placed_x (M := M) (A := A) (lim := lim) (H := H)
      hC
      (Q := Qpost)
      (Qp := Qp)
      x s0 hs0_align
      x.gc.2.messageKeys.length hmax
      (x.gc.1.keys.zip x.gc.2.messageKeys) hzip_ne
      0 (by simp [hzip_len])
      (M.stepEvents (rustAllocEvents (104 * x.gc.2.messageKeys.length) 8) stCur) hfits_loop
      s' srcCur mkPtr' v11 v13 w12b F
  have hep := fun s' mkPtr' v10' v13' keys' (hklen : keys'.length = x.gc.2.messageKeys.length) =>
    chain_clone_epilogue_placed_x (M := M) (A := A) (lim := lim) (H := H) (Qp := Qp)
      x st s0 s' srkPtr' privPtr' mkPtr' x25 x28 mkPtr' v10' v13' w27 keys' ckPin'
      hsrk hmax hklen hsrc_klen
  intro hcl
  rw [chainAt_eq_mk_source A.repAlloc x.gc x.src hsrk hmax hsrc_klen hpos,
      spillSlotsExist_eq_struct s0.sp,
      savedRegsOnStack_eq_core s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ⟨v11, w12b⟩ => ?_
  refine SepWPp.exists_elim fun spSlots => ?_
  rw [show (memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
          x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A.repAlloc) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
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
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        arrayAt (messageKeyAt A.repAlloc) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
        chainMkSourceFrame A.repAlloc x.gc x.src ∗
        A.pool lim stCur s ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
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
        savedRegsCore s0) by sep_ac_rfl]
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
  have hmk_rlay : RustLayoutOk (104 * x.gc.2.messageKeys.length) 8 := ⟨hmk_lay, by decide⟩
  apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_shim => ?_
  rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
  have hshim_state := shim_placed_ok_at_stateX_82 hC hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_82).base + bv% (296))
  wp_call hshim_state ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  have htr_sf : sf.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, *] at *
  refine SepWP.done ‹_› ‹_› fun hcl_after_shim => ?_
  apply sepWPp_of_sepWP_lscl hcl_after_shim (mid := lsρ lsRustAllocSym)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_alloc => ?_
  have halloc_state := allocNoOom_placed_ok_at_stateX_82 hC hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_82).base + bv% (308))
  wp_call halloc_state (104 * x.gc.2.messageKeys.length, 8, stCur)
  have hsp_alloc : sf.sp = s0.sp - 208#64 := by simp only [wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm, hsp_alloc]
  refine SepWP.done ‹_› ‹_› fun hcl_post_alloc => ?_
  have hacp1 := ‹AllocCallPreserved _ sf_1›
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := ‹sf_1.sp = _›.trans hsp_alloc
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have htrace1 : sf_1.trace = s0.trace := by
    exact hacp1.2.1.trans (by simp only [wp_norm, arm64_norm, *])
  apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_82).base + bv% (408))
  wp_steps_sync_pool ((blkPl_82).base + bv% (408))
  refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_loop => ?_
  let mkPtr' := sf_1.readReg64 (Reg.gpr 0#5)
  refine SepWPp.weaken_pre ?_
    (hloop _ x.gc.1.mkPtr mkPtr' v11 v13 w12b
      (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
        memRegion x.dst 104 ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
        chainMkSourceFrame A.repAlloc x.gc x.src ∗
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
      (fun sf_l keys' v11' v13' w12b' hklen_l hpc_l hrun_l hsp_l hx29_l hx19_l htr_l hvregs_l hcl_l => ?_)
      hcl_loop)
  · rw [hzip_len, BitVec.add_zero]
    exact Entails.of_eq (by dsimp only [mkPtr']; sep_ac_rfl)
  · simp only [wp_norm]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm]; rfl
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, hzip_len]
  · simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
  · simp only [wp_norm]; exact htrace1
  · simp only [wp_norm, arm64_norm, *]
  · have hklen : keys'.length = x.gc.2.messageKeys.length := hklen_l.trans hzip_len
    have hsp_l_align : sf_l.spAligned = true := by
      rw [State.spAligned, hsp_l]
      exact spAligned_sub s0.sp 208 hs0_align (by decide)
    have htrunc32 : BitVec.truncate 32 (BitVec.zeroExtend 64 w27) = w27 :=
      (BitVec.setWidth_setWidth_of_le w27 (by decide)).trans (BitVec.setWidth_eq w27)
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      map_snd_zip_of_length_eq x.gc.1.keys x.gc.2.messageKeys hsrc_klen,
      hst_eq, sepConj_assoc]
    apply sepWPp_of_sepWP_lscl hcl_l (mid := (blkPl_82).base + bv% (736))
    wp_steps_sync_pool ((blkPl_82).base + bv% (736))
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm]; assumption) fun hcl_736 => ?_
    subst hQpost
    refine SepWPp.weaken_pre ?_
      (hep _ mkPtr' (BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) v13' keys' hklen
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_736)
    · have hzip'_len : (keys'.zip x.gc.2.messageKeys).length = x.gc.2.messageKeys.length := by
        simp [hklen]
      have hzip'_pos : 0 < (keys'.zip x.gc.2.messageKeys).length := by
        rw [hzip'_len]; exact hpos
      have hzip'_max : (keys'.zip x.gc.2.messageKeys).length ≤ maxMessageKeys := by
        rw [hzip'_len]; exact hmax
      have hbuf_eq := vecBuf_mk_pos_eq A.repAlloc mkPtr' (keys'.zip x.gc.2.messageKeys)
        hzip'_pos hzip'_max hoom64
      rw [hzip'_len] at hbuf_eq
      rw [hbuf_eq,
          chainAt_eq_mk_source A.repAlloc x.gc x.src hsrk hmax hsrc_klen hpos,
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
            arrayAt (messageKeyAt A.repAlloc) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
            chainMkSourceFrame A.repAlloc x.gc x.src) ⊢
          (⌜x.gc.2.messageKeys.length ≤ x.gc.1.mkCap.toNat ∧
              x.gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ x.gc.1.mkPtr ≠ 0⌝ ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            arrayAt (messageKeyAt A.repAlloc) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
            chainMkSourceFrame A.repAlloc x.gc x.src) :=
        Entails.pure_right ⟨hmk_le, hmk_lt, hmk_ptr⟩ (Entails.refl _)
      have hgroup_pre : ∀ (pPool : SepProp),
          (pPool ∗
            arrayAt (messageKeyAt A.repAlloc) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
            arrayAt (messageKeyAt A.repAlloc) 104 mkPtr' (keys'.zip x.gc.2.messageKeys) ∗
            stackAt (s0.sp - 208#64) extHookStack ∗
            ((s0.sp - 136#64) ↦₆₄ mkPtr') ∗
            ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (104 * x.gc.2.messageKeys.length)) ∗
            ((s0.sp - 120#64) ↦₆₄ v11') ∗
            ((s0.sp - 108#64) ↦₃₂ w12b') ∗
            ((s0.sp - 104#64) ↦₆₄ v13') ∗
            A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
            memRegion x.dst 104 ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            ((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
            chainMkSourceFrame A.repAlloc x.gc x.src ∗
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
            vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
            (A.live mkPtr' (104 * x.gc.2.messageKeys.length) 8 ∗
              arrayAt (messageKeyAt A.repAlloc) 104 mkPtr' (keys'.zip x.gc.2.messageKeys)) ∗
            clonedOptChainKeyBuf A.repAlloc ckPin' x25 x28 w27 x.gc.2.chainKey ∗
            (((x.src + 56#64) ↦₆₄ x.gc.1.mkPtr) ∗
              arrayAt (messageKeyAt A.repAlloc) 104 x.gc.1.mkPtr (x.gc.1.keys.zip x.gc.2.messageKeys) ∗
              chainMkSourceFrame A.repAlloc x.gc x.src) ∗
            pPool ∗
            stackAt (s0.sp - 208#64) extHookStack ∗
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
              savedRegsCore s0)) := fun _ => by sep_ac_rfl
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
    · simp only [wp_norm]; exact htr_l
    · simp only [wp_norm]; exact hvregs_l

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneMkXPlacedBudget
