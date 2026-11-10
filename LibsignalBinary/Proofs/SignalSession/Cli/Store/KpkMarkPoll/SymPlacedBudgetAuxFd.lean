/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable Post-`one_time.get` Dispatch for `KpkMarkPoll`

Proves `kpk_after_ot_get_58_placed_fd` (`+88`) on Block `578` (`lsProg_578 H`), threading
`FdsGe3Closed` across all post-`one_time.get` branches.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAuxFd

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speAt speWord)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX extHookStack finishGrowStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkBaseKeysOk KpkMarkAns KpkMarkPollGhost KpkSeenOk ReadRule baseKeyEntry baseKeysName
   cliBcmpName cliBcmpSpec dirAt getResultAt hasChunk keyName kpkMarkOf utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (bind_sepWP_state_mark bind_sepWPp_state_mark cs_vregs cs_x19 cs_x20 cs_x26 cs_x29 epiloguePre
   getResultAt_b0_ok_unpack header3_entails_memRegion24 kpkMarkRoBundlePlaced kpkMinStk kpkSubMax
   sepWPp_conseq sepWPp_of_sepWP_fs_placed sepWPp_of_sepWP_lscro setWidth_32_setWidth_64
   slot_b0_err_collapse slot_b0_ok_collapse slot_b0_put_collapse spAligned_sub_f0
   speAt_read_invalidState_eq_words subStack_split vecU8Tail vecU8_empty_of_zero_one_zero)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced
   kpkMarkPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudgetFd
  (kpk_call_decimal_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudget
  (freeOnlyEvs_kpkDropBothEvents kpkDropBothEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudgetFd
  (kpk_drop_both_6c_placed_fd kpk_drop_both_f0_placed_fd kpk_put_and_epilogue_b8_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudgetFd
  (kpk_read_err_c4_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudgetFd
  (kpkMark_final_ext_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget
  (KpkLastResortPreAfterGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudgetFd
  (kpk_last_resort_118_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (KpkMarkEnvSpec KpkOneTimeConsTailEnv KpkOneTimePreAfterGetEnv)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

/-! ## `FdsGe3Closed`-Threaded Post-`one_time.get` Dispatch (`+88`) -/

set_option maxHeartbeats 1200000 in
/-- Dispatches at `+88` right after `one_time.get` returns `gr` under `[LibsignalPlacement]`,
`RustCliAllocBudget M`, and `FdsGe3Closed`. -/
theorem kpk_after_ot_get_58_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok (lsProg_578 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok (lsProg_578 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (x : KpkMarkPollGhost) (st0 st : M.σ) (evsOt : List AllocEvent)
    (s0 sm2 : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 nameCap namePtr : BitVec 64) (tmp32 : BitVec 32)
    (gr : Except Unit (List (BitVec 8)))
    {Q Qp : State → SepProp → Prop}
    (hst : st = M.stepEvents evsOt st0)
    (hfit0 : FitsEnv M lim st0 (MarkEnv s0.fs.files x))
    (hEnv : KpkMarkEnvSpec M lim rd DecEnv GetEnv PutEnv MarkEnv s0.fs.files x st0)
    (hevsOt : KpkOneTimePreAfterGetEnv DecEnv GetEnv s0.fs.files x evsOt)
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hwDot : unpack64 wDot = utf8 ".base-ke")
    (hBkOk : KpkBaseKeysOk pathOk x.kg.lastResort x.id)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hot_chg : x.kg.oneTime.changed.length < 2 ^ 32)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hn_len : (keyName x.id).length ≤ nameCap.toNat)
    (hn_lt : nameCap.toNat < 2 ^ 63) (hn_ptr : namePtr ≠ 0#64)
    (hgr : gr = x.kg.oneTime.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_578).base + bv% (88))
    (hrun : sm2.status = .Running)
    (hsp : sm2.sp = s0.sp - 0xf0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hfs : FsInv s0.fs.files s0.trace sm2)
    (hfds : FdsGe3Closed sm2.fs)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx23 : sm2.readReg64 .x23 = x.id.setWidth 64)
    (hx24 : sm2.readReg64 .x24 = namePtr)
    (hx26 : sm2.readReg64 .x26 = x.self)
    (hx28 : sm2.readReg64 .x28 = x.signedId.setWidth 64)
    (hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).post (x, st0) s0 sf) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) sm2
      (getResultAt A.repAlloc (s0.sp - 0xb0#64) gr ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        bytesAt false namePtr (keyName x.id) ∗
        vecU8Tail A.repAlloc nameCap namePtr (keyName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool lim st sm2)
      Q Qp := by

  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hdec_le : decStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hsp_al : sm2.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have herr_c4 := @kpk_read_err_c4_placed_fd _ M A lim H hFsAlloc
  have hdrop_f0 := @kpk_drop_both_f0_placed_fd _ M A lim H hFsAlloc
  have hdrop_6c := @kpk_drop_both_6c_placed_fd _ M A lim H hFsAlloc
  have hput_ep := @kpk_put_and_epilogue_b8_placed_fd _ M A lim H PutEnv decStk getStk putStk hPut
  have hlr118 :=
    @kpk_last_resort_118_placed_fd _ M A lim H rd pathOk DecEnv GetEnv PutEnv MarkEnv
      decStk getStk putStk stk hFsAlloc hP hBcmp hDecimal hGet hPut hFs
  clear hFsAlloc hP hBcmp hGet hPut
  dsimp only [lsProg_578] at hFs hDecimal herr_c4 hdrop_f0 hdrop_6c hput_ep hlr118 hpc ⊢
  rcases gr with ⟨⟩ | bytesBs
  · have hne : (speWord 1 + 2#64 != 0#64) = true := rfl
    change SepWPp _ _ _ (speAt A.repAlloc (utf8 "read") (s0.sp - 0xb0#64) .invalidState ∗ _) _ _
    rw [speAt_read_invalidState_eq_words A.repAlloc (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
          (s0.sp - 0xa0#64) (s0.sp - 0x98#64) (s0.sp - 0x90#64) (s0.sp - 0x88#64)
          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega),
        subStack_split s0.sp hext_le hhi]
    kpk_sep_norm
    refine SepWPp.exists_elim fun errBs => SepWPp.exists_elim fun errCap =>
      SepWPp.exists_elim fun errPtr => SepWPp.exists_elim fun fnPtr => ?_
    apply SepWPp.of_sepWP_ret
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + bv% (196))
    wp_steps_sync_pool ((blkPl_578).base + bv% (196))
    apply bind_sepWP_state_mark; intro st_c4; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_c4
    refine herr_c4 x st s0 st_c4 nameCap namePtr (keyName x.id)
      errBs errCap errPtr fnPtr _
      (kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa8#64) ↦₆₄ errCap) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ errPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
        ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
      hn_len hn_lt hn_ptr
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      hsp_align
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      hcrl_c4
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by dsimp only [st_c4]; kpk_norm)
      (by unfold epiloguePre; kpk_sep_focus)
      fun sf P_f htr_f hfs_f hsp_f hcs_f hPf =>
        hk_final sf P_f hsp_f hcs_f <| by
          have htr_eq : sf.trace = sm2.trace := htr_f.trans (by dsimp only [st_c4]; kpk_norm)
          have hfds_sf : FdsGe3Closed sf.fs := by
            have hfs_eq : sf.fs = sm2.fs := hfs_f.trans (by dsimp only [st_c4]; kpk_norm)
            rwa [hfs_eq]
          rcases hgr with ⟨hget1_err, hsm2_tr⟩
          have hmark_err :
              MarkEnv s0.fs.files x (evsOt ++ optDeallocBufEvents nameCap) :=
            hEnv.mark_ot_err evsOt nameCap hevsOt hn_len hn_lt hget1_err.symm
          have hres_eq :
              ((.readErr : KpkMarkAns), x.kg) =
                  kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
                sf.trace = s0.trace ∧
                MarkEnv s0.fs.files x (evsOt ++ optDeallocBufEvents nameCap) := by
            refine ⟨?_, htr_eq.trans hsm2_tr, hmark_err⟩
            unfold kpkMarkOf
            rw [← hget1_err]
          have hpool_err :
              M.stepEvents (optDeallocBufEvents nameCap) st =
                M.stepEvents (evsOt ++ optDeallocBufEvents nameCap) st0 := by
            rw [hst, M.stepEvents_append]
          refine Entails.trans hPf ?_
          rw [hpool_err]
          have hb0 := slot_b0_err_collapse s0.sp (speWord 1) errCap errPtr
            (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length)
            (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
            (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8)
          have hm80 := header3_entails_memRegion24 (s0.sp - 0x80#64) (s0.sp - 0x78#64)
            (s0.sp - 0x70#64) nameCap namePtr (BitVec.ofNat 64 (keyName x.id).length)
            (by bv_omega) (by bv_omega)
          refine Entails.trans ?_
            (kpkMark_final_ext_placed_fd (pathOk := pathOk) (MarkEnv := MarkEnv)
              hstk hhi_stk x st0 s0 sf wDot wR0 wR7 wM0 wM6
              f0 f1 f2 f3 tmp32 (evsOt ++ optDeallocBufEvents nameCap) (.readErr, x.kg)
              hfds_sf hres_eq)
          kpk_sep_norm
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono hb0 (sepConj_mono_left hm80))))))))))))))))))
          sep_focus

  · rcases hgr with ⟨hget1_symm, hsm2_tr⟩
    have hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok bytesBs :=
      hget1_symm.symm
    have heq0 : (okTagVec + 2#64 != 0#64) = false := rfl
    rw [getResultAt_b0_ok_unpack A.repAlloc s0.sp bytesBs, subStack_split s0.sp hext_le hhi]
    kpk_sep_norm
    refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr => ?_
    refine SepWPp.pure_elim fun ⟨hb_len, hb_lt, hb_ptr⟩ => ?_
    rcases bytesBs with _ | ⟨b0_byte, bs_tail⟩
    · have hnil_beq : (BitVec.ofNat 64 ([] : List (BitVec 8)).length == 0#64) = true := rfl
      apply sepWPp_of_sepWP_fs_placed
        (mid := (blkPl_578).base + bv% (240))
        hFs hcrl hfs
      wp_steps_sync_pool ((blkPl_578).base + bv% (240))
      apply bind_sepWP_state_mark; intro st_f0; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_f0 hfs_f0
      refine hdrop_f0 st s0 st_f0 bytesCap bytesPtr [] nameCap namePtr (keyName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 0x90#64) 16 ∗
          kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x)
        hFs hfs_f0 hb_len hb_lt hb_ptr hn_len hn_lt hn_ptr
        (by dsimp only [st_f0]; kpk_norm)
        (by dsimp only [st_f0]; kpk_norm)
        hsp_align
        (by dsimp only [st_f0]; kpk_norm)
        (by dsimp only [st_f0]; kpk_norm)
        hcrl_f0
        (by dsimp only [st_f0]; kpk_norm)
        (by dsimp only [st_f0]; kpk_norm)
        (by dsimp only [st_f0]; kpk_norm)
        (by dsimp only [st_f0]; kpk_norm)
        (by unfold epiloguePre; kpk_sep_focus)
        fun slr hpclr hrunlr hsplr hcrllr hfslr htrlr hfslr_eq r19 r20 r23 r26 r28 r29 hvlr => by
          let evsOneTime : List AllocEvent := evsOt ++ kpkDropBothEvents bytesCap nameCap
          let st_lr : M.σ := M.stepEvents (kpkDropBothEvents bytesCap nameCap) st
          have hst_lr : st_lr = M.stepEvents evsOneTime st0 := by
            simp only [st_lr, evsOneTime, hst, M.stepEvents_append]
          have hfit_lr_pre :
              FitsEnv M lim st_lr (KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x) := by
            rw [hst_lr]
            exact hEnv.fit_lr_pre evsOt bytesCap nameCap hfit0 hevsOt hget1 hb_lt hn_len hn_lt
          have hfds_lr : FdsGe3Closed slr.fs := by
            have hfs_eq : slr.fs = sm2.fs := hfslr_eq.trans (by dsimp only [st_f0]; kpk_norm)
            rwa [hfs_eq]
          exact hlr118 x st0 st_lr evsOneTime s0 slr
            wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 tmp32 _
            hst_lr
            hfit_lr_pre
            (fun evsPre fileCap seenBs seenCap hevsPre hf_len hf_lt hlr_ok hs_len hs_lt => by
              rw [hst_lr]
              exact hEnv.fit_lr_ok evsOt bytesCap nameCap evsPre fileCap seenBs seenCap
                hfit0 hevsOt hget1 hb_lt hn_len hn_lt hevsPre hf_len hf_lt hlr_ok hs_len hs_lt)
            (fun evsPre fileCap hevsPre hf_len hf_lt hlr_err =>
              hEnv.mark_lr_err evsOt bytesCap nameCap evsPre fileCap
                hevsOt hget1 hb_lt hn_len hn_lt hevsPre hf_len hf_lt hlr_err)
            (fun evsPre fileCap seenBs seenCap evs_after hevsPre hf_len hf_lt hlr_ok hs_len hs_lt
                hevs_after =>
              hEnv.mark_lr_ok evsOt bytesCap nameCap evsPre fileCap seenBs seenCap evs_after
                hevsOt hget1 hb_lt hn_len hn_lt hevsPre hf_len hf_lt hlr_ok hs_len hs_lt
                hevs_after)
            hstk hhi_stk hsp_align hwDot hBkOk hSeenOk hlr_chg hget1
            (by kpk_norm) hrunlr hsplr r29
            (by
              rw [htrlr]; dsimp only [st_f0]
              (try conv_lhs => simp only [wp_norm, arm64_norm, *])
              try ((first | rfl | exact hsm2_tr)))
            hcrllr hfslr hfds_lr hvlr
            (r19.trans (by dsimp only [st_f0]; kpk_norm))
            (r20.trans (by dsimp only [st_f0]; kpk_norm))
            (r23.trans (by dsimp only [st_f0]; kpk_norm))
            (r26.trans (by dsimp only [st_f0]; kpk_norm))
            (r28.trans (by dsimp only [st_f0]; kpk_norm))
            (by
              have hb0 := slot_b0_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
              have hm80 := header3_entails_memRegion24 (s0.sp - 0x80#64) (s0.sp - 0x78#64)
                (s0.sp - 0x70#64) nameCap namePtr (BitVec.ofNat 64 (keyName x.id).length)
                (by bv_omega) (by bv_omega)
              rw [subStack_split s0.sp hext_le hhi]
              unfold epiloguePre
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono hb0 (sepConj_mono_left hm80))))))))))))
              sep_focus)
            hk_final
    · let consBs := b0_byte :: bs_tail
      have hlen_ne0 : (BitVec.ofNat 64 (b0_byte :: bs_tail).length == 0#64) = false := by
        apply beq_false_of_ne
        intro h0
        have ht := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
        change (b0_byte :: bs_tail).length = 0 at ht
        simp at ht
      have hans_ok :
          (KpkMarkAns.ok, { x.kg with oneTime := x.kg.oneTime.put (keyName x.id) [] }) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1]
      have hfit_cons_ot : FitsEnv M lim st (KpkOneTimeConsTailEnv DecEnv PutEnv x) := by
        rw [hst]
        exact hEnv.fit_ot_cons evsOt b0_byte bs_tail hfit0 hevsOt hget1
      apply sepWPp_of_sepWP_fs_placed
        (mid := lsmpl.base 597) hFs hcrl hfs
      apply sepWP_seq_lscro hcrl
        (mid := (blkPl_578).base + bv% (108))
      wp_steps_sync_pool ((blkPl_578).base + bv% (108))
      apply bind_sepWP_state_mark; intro st_6c; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_6c
      exact hdrop_6c st s0 st_6c bytesCap bytesPtr consBs nameCap namePtr (keyName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
          ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
          memRegion (s0.sp - 0x90#64) 16 ∗
          kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x)
        hb_len hb_lt hb_ptr hn_len hn_lt hn_ptr
        (by dsimp only [st_6c]; kpk_norm)
        (by dsimp only [st_6c]; kpk_norm)
        hsp_align
        (by dsimp only [st_6c]; kpk_norm)
        (by dsimp only [st_6c]; kpk_norm)
        hcrl_6c
        (by dsimp only [st_6c]; kpk_norm)
        (by dsimp only [st_6c]; kpk_norm)
        (by dsimp only [st_6c]; kpk_norm)
        (by dsimp only [st_6c]; kpk_norm)
        (by unfold epiloguePre; kpk_sep_focus)

        fun sd hpcd hrund hspd _hcrld htrd hfsd r19 r20 r23 r26 _r28 r29 hvd => by
          have hsd_al : sd.spAligned = true := spAligned_sub_f0 hsp_align hspd
          have hx23_sd : sd.readReg64 .x23 = x.id.setWidth 64 :=
            r23.trans (by dsimp only [st_6c]; kpk_norm)
          let st_d : M.σ := M.stepEvents (kpkDropBothEvents bytesCap nameCap) st
          have hfit_dec_put :
              FitsEnv M lim st_d
                (SeqEnv (DecEnv x.id) (PutEnv x.kg.oneTime (keyName x.id) [])) :=
            hfit_cons_ot.seq_right (freeOnlyEvs_kpkDropBothEvents bytesCap nameCap)
          have hfit_dec2 : FitsEnv M lim st_d (DecEnv x.id) := hfit_dec_put.seq_left
          wp_steps_sync_pool (lsmpl.base 597)
          apply SepWP.done
            (by kpk_norm)
            (by wp_norm_lhs)
          intro hcrl_dec2 _hfs_dec2
          apply bind_sepWPp_state_mark; intro st_dec2
          have hsp_dec2 : st_dec2.sp = s0.sp - 0xf0#64 := by
            (try dsimp only [st_dec2]); (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            try ((first | rfl | exact hspd))
          have htr_dec2 : st_dec2.trace = s0.trace := by
            (try dsimp only [st_dec2]); (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            (try rw [htrd]); dsimp only [st_6c]
            (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            try (first | rfl | exact hsm2_tr)
          have hfds_dec2 : FdsGe3Closed st_dec2.fs := by
            have h1 : st_dec2.fs = sd.fs := by
              dsimp only [st_dec2]; simp only [wp_norm, arm64_norm]
            have h2 : st_6c.fs = sm2.fs := by dsimp only [st_6c]; kpk_norm
            rw [h1, hfsd, h2]
            exact hfds
          refine kpk_call_decimal_placed_fd hDecimal { n := x.id, ret := s0.sp - 0x80#64 } st_d
            (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                (kpkSubMax decStk getStk putStk - decStk) ∗
              ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
              ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
              ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
              memRegion (s0.sp - 0x90#64) 16 ∗
              kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
              memRegion (s0.sp - 0xf0#64) 8 ∗
              ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
              ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
              memRegion (s0.sp - 0xc8#64) 24 ∗
              memRegion (s0.sp - 0x68#64) 4 ∗
              ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
              dirAt A.repAlloc x.self x.kg.oneTime ∗
              dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
              (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
              epiloguePre s0 x)
            (ret_pc := (blkPl_578).base + bv% (160))
            (by dsimp only [st_dec2]; kpk_norm)
            (by dsimp only [st_dec2]; kpk_norm)
            (spAligned_sub_f0 hsp_align hsp_dec2)
            (by dsimp only [st_dec2]; kpk_norm)
            hcrl_dec2
            hfds_dec2
            (by
              dsimp only [st_dec2]
              (try rw [show sd.readReg64 .x29 = s0.sp - 0x60#64 from r29])
              kpk_norm)
            (by dsimp only [st_dec2]; kpk_norm)
            hfit_dec2
            (by
              rw [hsp_dec2]
              have hstk_re :
                  stackAt (s0.sp - 0xf0#64) extHookStack ∗
                    memRegion
                      (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                      (kpkSubMax decStk getStk putStk - extHookStack) =
                  memRegion
                    (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                    (kpkSubMax decStk getStk putStk - decStk) ∗
                    stackAt (s0.sp - 0xf0#64) decStk := by
                rw [sepConj_comm (stackAt _ _) _,
                    ← subStack_split s0.sp hext_le hhi,
                    subStack_split s0.sp hdec_le hhi]
              have hm80 := header3_entails_memRegion24 (s0.sp - 0x80#64) (s0.sp - 0x78#64)
                (s0.sp - 0x70#64) nameCap namePtr (BitVec.ofNat 64 (keyName x.id).length)
                (by bv_omega) (by bv_omega)
              have hswap_d :
                  A.pool lim st_d st_dec2 ∗
                    ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
                    stackAt (s0.sp - 0xf0#64) extHookStack ∗
                    (memRegion
                        (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                        (kpkSubMax decStk getStk putStk - extHookStack) ∗
                      ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
                      ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
                      ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                      memRegion (s0.sp - 0x90#64) 16 ∗
                      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
                      memRegion (s0.sp - BitVec.ofNat 64 stk)
                        (stk - kpkMinStk decStk getStk putStk) ∗
                      memRegion (s0.sp - 0xf0#64) 8 ∗
                      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                      memRegion (s0.sp - 0xc8#64) 24 ∗
                      ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
                      ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
                      memRegion (s0.sp - 0x68#64) 4 ∗
                      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                      dirAt A.repAlloc x.self x.kg.oneTime ∗
                      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
                      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
                      epiloguePre s0 x) =
                  (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
                    ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
                    ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length)) ∗
                    (stackAt (s0.sp - 0xf0#64) extHookStack ∗
                      memRegion
                        (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                        (kpkSubMax decStk getStk putStk - extHookStack)) ∗
                    A.pool lim st_d st_dec2 ∗
                    (((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
                      ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
                      ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                      memRegion (s0.sp - 0x90#64) 16 ∗
                      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
                      memRegion (s0.sp - BitVec.ofNat 64 stk)
                        (stk - kpkMinStk decStk getStk putStk) ∗
                      memRegion (s0.sp - 0xf0#64) 8 ∗
                      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                      memRegion (s0.sp - 0xc8#64) 24 ∗
                      memRegion (s0.sp - 0x68#64) 4 ∗
                      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                      dirAt A.repAlloc x.self x.kg.oneTime ∗
                      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
                      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
                      epiloguePre s0 x) := by
                sep_ac_rfl
              refine Entails.trans (Entails.of_eq hswap_d) ?_
              rw [hstk_re]
              refine Entails.trans (sepConj_mono_left hm80) ?_
              kpk_sep_norm
              sep_focus)

            fun sm3 evsDec2 hpcm3 hrunm3 hspm3 hcsm3 hcrlm3 hfdsm3 htrm3 hevsDec2 => ?_
          have hsm3_sp : sm3.sp = s0.sp - 0xf0#64 := hspm3.trans hsp_dec2
          have hsm3_al : sm3.spAligned = true := spAligned_sub_f0 hsp_align hsm3_sp
          have hsm3_tr : sm3.trace = s0.trace := htrm3.trans htr_dec2
          have hsm3_fp : sm3.readReg64 .x29 = s0.sp - 0x60#64 := by
            rw [(cs_x29 hcsm3)]; dsimp only [st_dec2]
            (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            try ((first | rfl | exact r29))
          have hsm3_19 : sm3.readReg64 .x19 = x.fut := by
            have h1 : st_dec2.readReg64 .x19 = sd.readReg64 .x19 := by
              dsimp only [st_dec2]; kpk_norm
            have h2 : st_6c.readReg64 .x19 = x.fut := by
              dsimp only [st_6c]; kpk_norm
            exact (cs_x19 hcsm3).trans (h1.trans (r19.trans h2))
          have hsm3_20 : sm3.readReg64 .x20 = x.out := by
            have h1 : st_dec2.readReg64 .x20 = sd.readReg64 .x20 := by
              dsimp only [st_dec2]; kpk_norm
            have h2 : st_6c.readReg64 .x20 = x.out := by
              dsimp only [st_6c]; kpk_norm
            exact (cs_x20 hcsm3).trans (h1.trans (r20.trans h2))
          have hsm3_26 : sm3.readReg64 .x26 = x.self := by
            have h1 : st_dec2.readReg64 .x26 = sd.readReg64 .x26 := by
              dsimp only [st_dec2]; kpk_norm
            have h2 : st_6c.readReg64 .x26 = x.self := by
              dsimp only [st_6c]; kpk_norm
            exact (cs_x26 hcsm3).trans (h1.trans (r26.trans h2))
          have hsm3_v : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
            rw [(cs_vregs hcsm3)]; dsimp only [st_dec2]
            (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            try (first | rfl | exact hvd)
          let st_p : M.σ := M.stepEvents evsDec2 st_d
          have hfit_put :
              FitsEnv M lim st_p (PutEnv x.kg.oneTime (keyName x.id) []) :=
            hfit_dec_put.seq_right hevsDec2
          change SepWPp _ _ _ ((vecU8 A.repAlloc (s0.sp - 0x80#64) (keyName x.id) ∗ _ ∗ _) ∗ _) _ _
          rw [hsp_dec2]
          kpk_sep_norm
          apply sepWPp_of_sepWP_lscro
            (mid := (blkPl_578).base + bv% (184))
            hcrlm3
          wp_steps_sync_pool ((blkPl_578).base + bv% (184))
          apply bind_sepWP_state_mark; intro st_b8
          apply SepWP.done (by kpk_norm) (by kpk_norm)
          intro hcrl_b8
          have hfds_b8 : FdsGe3Closed st_b8.fs := by
            have hfs_eq : st_b8.fs = sm3.fs := by
              dsimp only [st_b8]; simp only [wp_norm, arm64_norm]
            rwa [hfs_eq]
          refine hput_ep x st_p s0 st_b8 x.self (s0.sp - 0x80#64) (s0.sp - 0xb0#64)
            x.kg.oneTime (keyName x.id) [] _
            (((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
              memRegion (s0.sp - 0x90#64) 16 ∗
              kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
              memRegion (s0.sp - 0xf0#64) 8 ∗
              ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
              ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
              memRegion (s0.sp - 0xc8#64) 24 ∗
              memRegion (s0.sp - 0x68#64) 4 ∗
              ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
              dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
              (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
            hhi hot_chg hfit_put
            (by dsimp only [st_b8]; kpk_norm)
            (by dsimp only [st_b8]; kpk_norm)
            hsp_align
            (by
              dsimp only [st_b8]
              (try conv_lhs => simp only [wp_norm, arm64_norm, *])
              try ((first | rfl | exact hsm3_sp)))
            (by
              dsimp only [st_b8]
              (try conv_lhs => simp only [wp_norm, arm64_norm, *])
              try ((first | rfl | exact hsm3_tr)))
            hcrl_b8
            hfds_b8
            (by
              dsimp only [st_b8]
              (try conv_lhs => simp only [wp_norm, arm64_norm, *])
              try ((first | rfl | exact hsm3_v)))
            (by dsimp only [st_b8]; kpk_norm)
            (by dsimp only [st_b8]; kpk_norm)
            (by dsimp only [st_b8]; kpk_norm)
            (by
              dsimp only [st_b8]
              (try conv_lhs => simp only [wp_norm, arm64_norm, *])
              try ((first | rfl | exact hsm3_19)))
            (by
              dsimp only [st_b8]
              (try conv_lhs => simp only [wp_norm, arm64_norm, *])
              try ((first | rfl | exact hsm3_20)))
            (by
              have hv_emp := vecU8_empty_of_zero_one_zero A.repAlloc
                (s0.sp - 0xb0#64) (s0.sp - 0xa8#64) (s0.sp - 0xa0#64)
                (by bv_omega) (by bv_omega)
              have hstk_m :
                  stackAt (s0.sp - 0xf0#64) decStk ∗
                    memRegion
                      (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                      (kpkSubMax decStk getStk putStk - decStk) =
                  stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) := by
                rw [sepConj_comm (stackAt _ _) _, ← subStack_split s0.sp hdec_le hhi]
              have hswap_p :
                  A.pool lim st_p st_b8 ∗
                    vecU8 A.repAlloc (s0.sp - 0x80#64) (keyName x.id) ∗
                    stackAt (s0.sp - 0xf0#64) decStk ∗
                    memRegion
                      (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                      (kpkSubMax decStk getStk putStk - decStk) ∗
                    ((s0.sp - 0xb0#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa8#64) ↦₆₄ 1#64) ∗
                    ((s0.sp - 0xa0#64) ↦₆₄ 0#64) ∗
                    ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                    memRegion (s0.sp - 0x90#64) 16 ∗
                    kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
                    memRegion (s0.sp - BitVec.ofNat 64 stk)
                      (stk - kpkMinStk decStk getStk putStk) ∗
                    memRegion (s0.sp - 0xf0#64) 8 ∗
                    ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                    ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                    memRegion (s0.sp - 0xc8#64) 24 ∗
                    memRegion (s0.sp - 0x68#64) 4 ∗
                    ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                    dirAt A.repAlloc x.self x.kg.oneTime ∗
                    dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
                    (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
                    epiloguePre s0 x =
                  (((s0.sp - 0xb0#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa8#64) ↦₆₄ 1#64) ∗
                    ((s0.sp - 0xa0#64) ↦₆₄ 0#64)) ∗
                    (stackAt (s0.sp - 0xf0#64) decStk ∗
                      memRegion
                        (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                        (kpkSubMax decStk getStk putStk - decStk)) ∗
                    dirAt A.repAlloc x.self x.kg.oneTime ∗
                    vecU8 A.repAlloc (s0.sp - 0x80#64) (keyName x.id) ∗
                    epiloguePre s0 x ∗ A.pool lim st_p st_b8 ∗
                    (((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                      memRegion (s0.sp - 0x90#64) 16 ∗
                      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
                      memRegion (s0.sp - BitVec.ofNat 64 stk)
                        (stk - kpkMinStk decStk getStk putStk) ∗
                      memRegion (s0.sp - 0xf0#64) 8 ∗
                      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                      memRegion (s0.sp - 0xc8#64) 24 ∗
                      memRegion (s0.sp - 0x68#64) 4 ∗
                      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
                      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList)) := by
                sep_ac_rfl
              refine Entails.trans (Entails.of_eq hswap_p) ?_
              rw [hstk_m]
              refine Entails.trans (sepConj_mono_left hv_emp) ?_
              kpk_sep_norm
              sep_focus)
            fun sf_p evsPut P_p htr_p hfds_p hsp_p hcs_p hevsPut hPp =>
              hk_final sf_p P_p hsp_p hcs_p <| by
                let evsTail : List AllocEvent :=
                  kpkDropBothEvents bytesCap nameCap ++ (evsDec2 ++ evsPut)
                have htail : KpkOneTimeConsTailEnv DecEnv PutEnv x evsTail :=
                  Or.inr ⟨kpkDropBothEvents bytesCap nameCap, evsDec2 ++ evsPut, rfl,
                    freeOnlyEvs_kpkDropBothEvents bytesCap nameCap,
                    Or.inr ⟨evsDec2, evsPut, rfl, hevsDec2, hevsPut⟩⟩
                have hmark_cons : MarkEnv s0.fs.files x (evsOt ++ evsTail) :=
                  hEnv.mark_ot_cons evsOt b0_byte bs_tail evsTail hevsOt hget1 htail
                have hpool_cons :
                    M.stepEvents evsPut st_p = M.stepEvents (evsOt ++ evsTail) st0 := by
                  simp only [st_p, st_d, hst, evsTail, M.stepEvents_append, List.append_assoc]
                refine Entails.trans hPp ?_
                rw [hpool_cons]
                have hb0_p := slot_b0_put_collapse s0.sp (BitVec.ofNat 64 consBs.length)
                refine Entails.trans ?_
                  (kpkMark_final_ext_placed_fd (pathOk := pathOk) (MarkEnv := MarkEnv)
                    hstk hhi_stk x st0 s0 sf_p wDot wR0 wR7 wM0 wM6
                    f0 f1 f2 f3 tmp32 (evsOt ++ evsTail)
                    (.ok, { x.kg with oneTime := x.kg.oneTime.put (keyName x.id) [] })
                    hfds_p ⟨hans_ok, htr_p, hmark_cons⟩)
                rw [subStack_split s0.sp hext_le hhi]
                kpk_sep_norm
                refine Entails.trans ?_
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono_right (sepConj_mono_left hb0_p)))))))))))))))))
                sep_focus

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAuxFd
