/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveIdPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Store
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Matched-Session Stage P4 Composition

Composes `stageP4_matched_saveIdentity_vregs_placed` (`Matched.M4SaveIdPlacedBudget`) and
`stageP4_matched_storeSession_vregs_placed` (`Matched.M4StorePlacedBudget`) to prove
`stageP4_matched_placed_ok : StageP4MatchedPlacedStmt A lim` under `StageP4MatchedEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding IdentityStoreKitPlacedOkI
  SessionOnlyKitPlacedOkSE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SepWPp.congr_post_drop_left SepWPp.drop_swap_focus_pre SepWPp.focus_pre
  SessionExtraRel saveIdCallStack saveIdVtablesAt storeSessionCallStack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  prevSessionsEmptyAt saveIdStack_le_matched stack_matched_to_saveId
  stack_matched_to_storeSession stageP4MatchedCallStack storeSessionStack_le_matched
  storeSessionVtablesPlacedAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  SessionStoreBudgetEnv StoreStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedBranchPlaced StageP4MatchedEnv StageP4MatchedPlacedStmt
  StageP4MatchedSaveErrEnv StageP4MatchedStoreStepEnv
  fitsEnv_saveStep_of_matched fitsEnv_storeStep_of_matched
  stageP4MatchedExitAtPlaced stageP4MatchedPrePlaced stageP4MatchedSharedPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveIdPlacedBudget (
  stageP4MatchedSaveIdErrPostPlaced stageP4MatchedSaveIdOkPostPlaced
  stageP4MatchedSaveIdPrePlaced stageP4MatchedSaveIdSharedPlaced
  stageP4_matched_saveIdentity_vregs_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlacedBudget (
  stageP4MatchedStoreErrPostPlaced stageP4MatchedStoreOkPostPlaced
  stageP4MatchedStorePrePlaced stageP4MatchedStoreSharedPlaced
  stageP4_matched_storeSession_vregs_placed
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedPlacedStmt
)

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` matched-session Stage P4
(`(blkPl_518).base + 0x34dc → s0.readReg64 .x30`, `opkIdIsSome = 2#32`) over general
`prevSessionsEmptyAt A.repAlloc coroPtr g` under `StageP4MatchedEnv`. -/
theorem stageP4_matched_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    StageP4MatchedPlacedStmt A lim := by
  intro ext Scope encRecord kit kitEnv ikit ikitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt
    st0 s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss
    hExtra hrec_ok haddr_ss haddr_id hfits hpt_le hcap_lt hptr_nz hsp_ub hfs
    hcro hpc hrun hsp_align _htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_matched kit ikit) hsp_ub
  have hsp_store : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_matched kit ikit) hsp_ub
  have hfits_save : FitsEnv M lim st0 (SaveStepEnv ikit ikitEnv ist0 peer.val remoteIk) :=
    fitsEnv_saveStep_of_matched hfits
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4MatchedSaveIdPrePlaced A lim st0 ikit s0 s coroPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr ptCap ptPtr v_3d0 b_2c0 pt peer remoteIk ist0 g G ss.state)
    (by
      unfold stageP4MatchedPrePlaced stageP4MatchedSharedPlaced
        stageP4MatchedSaveIdPrePlaced stageP4MatchedSaveIdSharedPlaced
      rw [stack_matched_to_saveId kit ikit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_matched_saveIdentity_vregs_placed ext ikit ikitEnv hdealloc hDropSS3 hikit hiVt
    st0 s0 s coroPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0
    b_2c0 pt peer remoteIk ist0 g G ss.state _ _
    haddr_id hfits_save hpt_le hsp_save
    (hfs.mono (fun _ h => h.2) id)
    hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c evs1 s1 P1 hevs1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 _
      hcro1 hvregs1 hP1 => ?_)
    (fun evs sf Pf hevs hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  · -- P4.1 Ok(c) → P4.4 store_session at +0x3cc
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit)
      (T := stageP4MatchedStorePrePlaced A lim (M.stepEvents evs1 st0) kit s0 s1 coroPtr outPtr
        remoteAddrPtr sessionStorePtr ptCap ptPtr b_2c0 pt peer sst0 g G ss)
      hP1
      ((stack_matched_to_saveId kit ikit s.sp hsp_ub).symm.trans
        (stack_matched_to_storeSession kit ikit s.sp hsp_ub))
      (by unfold stageP4MatchedSaveIdOkPostPlaced stageP4MatchedSaveIdSharedPlaced; sep_focus)
      (by unfold stageP4MatchedStorePrePlaced stageP4MatchedStoreSharedPlaced; rw [hsp1]; sep_focus)
      ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.2 peer.val remoteIk (.ok c))
    have hfits_store :
        FitsEnv M lim (M.stepEvents evs1 st0) (StoreStepEnv kit kitEnv sst0 peer.val ⟨some ss⟩) :=
      ((fitsEnv_storeStep_of_matched hfits).seq_right hevs1).seq_left
    refine stageP4_matched_storeSession_vregs_placed ext Scope encRecord kit kitEnv hdealloc hDropSS3
      hkit hsVt (M.stepEvents evs1 st0) s0 s1 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr
      ptCap ptPtr b_2c0 pt peer sst0 g G ss _ _
      hExtra hrec_ok haddr_ss hfits_store hpt_le hcap_lt hptr_nz hsp_store
      (hfs1.mono (fun _ h => h.1) id)
      hcro1 hpc1 hrun1 hsp1_align
      hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1) hx26_1 hx27_1 hvregs1
      (fun evs2 sf Pf hevs2 hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
      (fun evs2 sf Pf hevs2 hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    · -- P4.4 Ok(())
      have hevs_tot :
          StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss
            (evs1 ++ evs2) :=
        SeqEnv.append hevs1 hevs2
      have hst_tot :
          M.stepEvents evs2 (M.stepEvents evs1 st0) = M.stepEvents (evs1 ++ evs2) st0 :=
        (M.stepEvents_append evs1 evs2 st0).symm
      refine ⟨storeSessionVtablesPlacedAt kit,
        stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs1 ++ evs2) st0) kit ikit
          s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId (vecResultAt A.repAlloc outPtr (.ok pt))
          pt peer remoteIk
          (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
          (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .ok c (evs1 ++ evs2) hevs_tot hrel1 hrel2
          (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf (Entails.of_eq ?_)
      rw [hst_tot]
      unfold stageP4MatchedStoreOkPostPlaced stageP4MatchedStoreSharedPlaced
        stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced
      rw [hsp1, stack_matched_to_storeSession kit ikit s.sp hsp_ub]
      sep_ac_rfl
    · -- P4.4 Err(())
      have hevs_tot :
          StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss
            (evs1 ++ evs2) :=
        SeqEnv.append hevs1 hevs2
      have hst_tot :
          M.stepEvents evs2 (M.stepEvents evs1 st0) = M.stepEvents (evs1 ++ evs2) st0 :=
        (M.stepEvents_append evs1 evs2 st0).symm
      refine ⟨storeSessionVtablesPlacedAt kit,
        stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs1 ++ evs2) st0) kit ikit
          s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId (storePollPlacedOutAt outPtr (.error ()))
          pt peer remoteIk
          (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
          (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .storeErr c (evs1 ++ evs2) hevs_tot hrel1 hrel2
          (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf (Entails.of_eq ?_)
      rw [hst_tot]
      unfold stageP4MatchedStoreErrPostPlaced stageP4MatchedStoreSharedPlaced
        stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced
      rw [hsp1, stack_matched_to_storeSession kit ikit s.sp hsp_ub]
      sep_ac_rfl
  · -- P4.1 Err(())
    refine ⟨saveIdVtablesAt ikit,
      stageP4MatchedExitAtPlaced A lim (M.stepEvents evs st0) kit ikit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (savePollPlacedOutAt outPtr (.error ()))
        pt peer remoteIk sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())),
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      .saveErr evs hevs hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4MatchedSaveIdErrPostPlaced stageP4MatchedSaveIdSharedPlaced
      stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced
    rw [stack_matched_to_saveId kit ikit s.sp hsp_ub]
    sep_ac_rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4PlacedBudget
