/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget159Aux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget159
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget549Aux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Segment S5 (`PqRecv`) Proofs

Re-exports `spqrRecvRawSpecPlaced`, `PqRecvEnv`, `pqRecv_159_placed_ok`, and
`pqRecv_159_placed_ok_x`, and proves the block `433` (`549`) counterparts (`pqRecv_549_placed_ok`,
`pqRecv_549_placed_ok_x`) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget

open scoped LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp (
  sessionStateAt_atState trAt_atState trRestAt_atState speBodyAt_atState
  protocolAddressAt_atState signalMessageAt_atState signalMessageRestAt_atState
  vecU8At_atState vecU8_atState spqrRecvKeyAt_atState spqrRecvResultAt_atState
  vecArg_at_atState
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (
  steps_of_sepWP_placed_state s5_out_add_np_evs
  tryDecryptFnOnPanic_eq_tryDecryptOnPanic
  spqrRecvRawSpecPlaced PqRecvEnv
  fitsEnv_recv_of_pqRecvEnv fitsEnv_fmt_of_pqRecvEnv_err pqRecvEnv_of_err_parts
  onPanic_of_spqrRecv_budget_placed
)

open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget549Aux (
  pqRecv_dealloc_tail_549_placed pqRecv_recv_err_true_549_placed pqRecv_recv_err_false_549_placed
)
open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Decrypt
  CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  Crypto SignalProtocolError TripleRatchet SessionState MessageKeyGenerator
)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ lsroCheck lsro_intro_chk lsRustDeallocSym
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8 vecU8At vecHeader)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser uuidTryParse errTag utf8 speWord protocolAddressAt tapeAfter
  sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost trAt spqrRecvResultAt spqrRecvKeyAt
  TryDecryptGhost VecArg LibsignalCodeRoLoaded withLsCodeRoLoaded
  logOff extHookStack spqrRecvStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkPl_434 blkLib_eq_434 tryDecryptPlacedImg tryDecryptSubStack
  tryDecryptSavedRegs tryDecryptCommonHeap segPqRecvPC_at segDeriveKeysPC_at errTailPC_at
  speTag speBodyAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  tryDecryptMidMetaCore steps_done_of_sepWP_midMeta_placed modelFn_error_panic_eq
  mr_cut mr_cut_add stackAt_sub sp_fp_eq sp56_weaken buf_to_mr sepWP_8_mr7_to_64
  concat56_8_cbz64_zero concat56_8_cbz64_ne_zero concat56_8_cbz32_ne_zero
  byte_ne_zero_cbz32 byte_ne_zero_cbz64_32
  speBodyAt_invalidState_fold speBodyAt_pqRatchet_fold
  pointsTo8_memRegion7_to_64 pointsTo64_to_8_memRegion7
  trRestAt trAt_split_pq signalMessageRestAt signalMessageAt_split_pq
  cap_add_one_ne_zero extractLsb0_8_append56 spqrRecvRawSpec
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees (
  lsFormatInnerSym lsTryDecryptCoinsRoSym lsroCheck_tryDecryptCoinsRoSym
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv SeqEnv FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv formatInnerBudgetEnvSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (
  steps_call_out_placed steps_call_out_placed_cro
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ErrTailStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  tryDecryptOnPanic tryDecryptFnOnPanic S5SeamPlaced S5SeamXPlaced
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-! ## Re-Exports from `PqRecvBudgetDefs`, `PqRecvBudget159Aux`, `PqRecvBudget159`, `PqRecvBudget549Aux` -/

abbrev spqrRecvRawSpecPlaced := @PqRecvBudgetDefs.spqrRecvRawSpecPlaced
abbrev PqRecvEnv := @PqRecvBudgetDefs.PqRecvEnv
abbrev pqRecv_dealloc_tail_159_placed := @PqRecvBudget159Aux.pqRecv_dealloc_tail_159_placed
abbrev pqRecv_recv_err_true_159_placed := @PqRecvBudget159Aux.pqRecv_recv_err_true_159_placed
abbrev pqRecv_recv_err_false_159_placed := @PqRecvBudget159Aux.pqRecv_recv_err_false_159_placed
abbrev pqRecv_159_placed_ok := @PqRecvBudget159.pqRecv_159_placed_ok
abbrev pqRecv_159_placed_ok_x := @PqRecvBudget159.pqRecv_159_placed_ok_x
abbrev pqRecv_dealloc_tail_549_placed := @PqRecvBudget549Aux.pqRecv_dealloc_tail_549_placed
abbrev pqRecv_recv_err_true_549_placed := @PqRecvBudget549Aux.pqRecv_recv_err_true_549_placed
abbrev pqRecv_recv_err_false_549_placed := @PqRecvBudget549Aux.pqRecv_recv_err_false_549_placed

set_option maxHeartbeats 800000 in
theorem pqRecv_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpecPlaced A lim S RecvEnv)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S (PqRecvEnv S RecvEnv fmtEnv) := by
  intro x st trG tr st1 mkg draws R s0 s hfits hpqr_eq h5 hL
  unfold PqRecvStatePlaced CryptoVerification.LibsignalTripleRatchet.Decrypt.PqRecvStatePlaced at h5
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hfits_recv := fitsEnv_recv_of_pqRecvEnv hfits
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold tryDecryptCommonHeap at hmem
  simp only [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState,
    signalMessageAt_atState, RustCliAllocBudget.atState_pool,
    RustCliAllocBudget.atState_live] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (∃ evs, PqRecvEnv S RecvEnv fmtEnv x tr evs ∧
            DeriveKeysStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
              x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (∃ evs, PqRecvEnv S RecvEnv fmtEnv x tr evs ∧
            ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
              x trG tr st1 e draws R s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed_state hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_434).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid := fun sm =>
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trAt A.repAlloc (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 16 ∗
      ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool lim st sm) ?_ ?_
  · wp_steps_sync_pool (lsmpl.base 329)
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗
          (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call : sm.mem ⊨
        (spqrRecvRawSpecPlaced A lim S RecvEnv).pre ((stArg, msgArg, sp + 1280#64), st) sm ∗
        ((trRestAt A.repAlloc sp trG tr ∗
          signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
            (seedPtr ↦ₛ mkg.seed) ∗
            memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
              (seedCap.toNat - mkg.seed.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 16 ∗
          ((sp + 16#64) ↦₆₄ seedPtr) ∗
          memRegion (sp + 24#64) 4 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₆₄ seedCap) ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 784 ∗
          ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
          memRegion (sp + 1116#64) 164 ∗
          memRegion (sp + 1328#64) 80 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          tapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
            (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [spqrRecvRawSpecPlaced, PqRecvBudgetDefs.spqrRecvRawSpecPlaced,
        spqrRecvRawSpec, stArg, msgArg]
      simp only [vecArg_at_atState, RustCliAllocBudget.atState_pool]
      dsimp only [VecArg.at]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfits_recv, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_out_placed_cro ((stArg, msgArg, sp + 1280#64), st) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => Or.inr ⟨hpan,
          onPanic_of_spqrRecv_budget_placed (st_v := stArg) (msg_v := msgArg)
            (ret := sp + 1280#64) (st_m := st) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvRawSpecPlaced, PqRecvBudgetDefs.spqrRecvRawSpecPlaced,
        spqrRecvRawSpec, stArg, msgArg] at hpost1
      simp only [vecArg_at_atState, spqrRecvResultAt_atState,
        RustCliAllocBudget.atState_pool] at hpost1
      dsimp only [VecArg.at] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨evs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hevs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      set st_r := M.stepEvents evs1 st
      have hpq_evs : PqRecvEnv S RecvEnv fmtEnv x tr evs1 := by
        unfold PqRecvEnv PqRecvBudgetDefs.PqRecvEnv; rw [hrecv]; exact hevs1
      have hpost1' : sf1.mem ⊨
          vecU8At A.repAlloc (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A.repAlloc (sp + 1304#64) pqrKey ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
               (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_r sf1) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np_evs hnpF ?_
      suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf1 s' ∧
          (DeriveKeysStatePlaced (blkPl_434).base A lim st_r ctl
              x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∨
            (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) by
        obtain ⟨s', hsteps, hok | hpan⟩ := this
        · exact ⟨s', hsteps, Or.inl ⟨evs1, hpq_evs, hok⟩⟩
        · exact ⟨s', hsteps, Or.inr hpan⟩
      unfold DeriveKeysStatePlaced
        CryptoVerification.LibsignalTripleRatchet.Decrypt.DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt (A.atState lim st_r sf) x.ss x.G.afterTrFrom st1 ∗
              trAt (A.atState lim st_r sf) ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else (A.atState lim st_r sf).live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                  (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At (A.atState lim st_r sf) ((s0.sp - 1504#64) + 0x500#64)
                newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt (A.atState lim st_r sf) ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap (A.atState lim st_r sf) ctl tryDecryptPlacedImg x draws s0 ∗ R))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      simp only [sessionStateAt_atState, trAt_atState, vecU8At_atState, spqrRecvKeyAt_atState,
        protocolAddressAt_atState, signalMessageAt_atState,
        RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps_sync_pool ((blkPl_434).base + 1500#64)
      wp_done
    | error sd =>
      refine steps_call_out_placed_cro ((stArg, msgArg, sp + 1280#64), st) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => Or.inr ⟨hpan,
          onPanic_of_spqrRecv_budget_placed (st_v := stArg) (msg_v := msgArg)
            (ret := sp + 1280#64) (st_m := st) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvRawSpecPlaced, PqRecvBudgetDefs.spqrRecvRawSpecPlaced,
        spqrRecvRawSpec, stArg, msgArg] at hpost1
      simp only [vecArg_at_atState, spqrRecvResultAt_atState,
        RustCliAllocBudget.atState_pool] at hpost1
      dsimp only [VecArg.at] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨evs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hevs1, hpost1⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      set st_r := M.stepEvents evs1 st
      have hfits_fmt := fitsEnv_fmt_of_pqRecvEnv_err hrecv hfits hevs1
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
           ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
           memRegion (sp + 1296#64) 32 ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
               (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_r sf1) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        refine s5_out_add_np_evs hnpF ?_
        obtain ⟨s', hsteps, (⟨evs2, evs3, hevs2, hevs3, hok⟩ | hpan)⟩ :=
          pqRecv_recv_err_true_549_placed C A lim st_r ctl S fmtEnv H x trG tr st1 mkg draws R s0
            hfits_fmt hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hclf1 hLf1 hpost1'
        · refine ⟨s', hsteps, Or.inl ⟨(evs1 ++ evs2) ++ evs3,
            pqRecvEnv_of_err_parts hrecv hevs1 hevs2 hevs3, ?_⟩⟩
          simpa only [M.stepEvents_append, ↓reduceIte, Bool.false_eq_true] using hok
        · exact ⟨s', hsteps, Or.inr hpan⟩
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        refine s5_out_add_np_evs hnpF ?_
        obtain ⟨s', hsteps, (⟨evs2, evs3, hevs2, hevs3, hok⟩ | hpan)⟩ :=
          pqRecv_recv_err_false_549_placed C A lim st_r ctl S fmtEnv H x trG tr st1 mkg draws R s0
            hfits_fmt hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hclf1 hLf1 hpost1'
        · refine ⟨s', hsteps, Or.inl ⟨(evs1 ++ evs2) ++ evs3,
            pqRecvEnv_of_err_parts hrecv hevs1 hevs2 hevs3, ?_⟩⟩
          simpa only [M.stepEvents_append, ↓reduceIte, Bool.false_eq_true] using hok
        · exact ⟨s', hsteps, Or.inr hpan⟩

theorem pqRecv_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpecPlaced A lim S RecvEnv)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S5SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C decFn A lim ctl uuidTryParse S (PqRecvEnv S RecvEnv fmtEnv) := by
  unfold S5SeamXPlaced
  simp only [tryDecryptFnOnPanic_eq_tryDecryptOnPanic]
  exact pqRecv_549_placed_ok C A lim ctl S RecvEnv fmtEnv H hrecv_call hfmt_call hdealloc_call


end LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget
