/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget -- proof-setup: allow-public-import

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced

/-!
# Pre-`FdsGe3Closed` `initiate` Slot Producer

Pool-carried `FdsGe3Closed` (`AllocWithFds.withFds`) conversions for `pathSpecPlaced` (block 596),
`dirGetSpecPlaced` (block 589), and `ExistingStoreCalleesPlaced`, reducing the pre-`FdsGe3Closed`
`initiate` slot obligation on block 579 calling block 521 to `CliInitSlotOkPlacedAt H (withFds A)`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAtFd

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (extHookStack publicKeySerializeStackX)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsFormatInnerSym lsReadFileSym lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule cliBcmpName cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.KitInst
  (rodata_cliIdentity_kpSlot_placed rodata_cliIdentity_regIdSlot_placed
   rodata_cliIdentity_saveSlot_placed rodata_cliIdentity_trustSlot_placed
   rodata_cliSession_loadSlot_placed rodata_cliSession_storeSlot_placed)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (dirPutNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_542 lsProg_543 lsProg_569 lsProg_586 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunNeeds RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced cliDirPutStk initProgPlaced sessLoadPoll_stk_le
   stk_sub_ge_base stk_sub_ge_dirGet)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced pathNeed)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced filesOk₀ scopeIn)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
  (dirGet_placed_caller_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget
  (dirPut_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget (dirPutStr_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (CliInitSlotOkPlacedAt ExternNoAllocFailed Stage3OkEventsFit Stage3OkEventsOut
   cliInitSlotOkPlacedAt_of_local stage3PlacedOk_okEvents w3Local_placed_ok_of_seams)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostSpqrAllocHooks_withFds withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
  (hookSat_stringCloneBudget_withFds_of_enforced)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (SessKitHooksPlaced cliAddrText_placed_ok cliGrowOneDir_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
  (cliExistingStoreCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (cliDirPutStrNeedPlaced cliGhostExterns_blackBox_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (CliInitiateBudgetFits)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced spqrInitialStateInnerSpec verifySignatureInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd
  (subroutine_ok_semInitSlot_preFd_of_withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (slotWithPreFdsGe3Closed withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks cliExternsPlaced_bcmp_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (dirGetSpecPlaced dirPutSpecPlaced dirPutStrSpecPlaced pathSpecPlaced readFileSpecPlaced
   sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget
  (idSavePoll_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget
  (idSaveShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok publicKeyEq_placed_ok_of_bb)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlacedBudget
  (idTrustShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
  (sessLoadPoll_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlacedBudget
  (sessLoadShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget
  (sessStoreShim_placed_ok_of_deps)

/-! ## Pool-`FdsGe3Closed` Conversions -/

private theorem pull_pure_6 {Q : Prop} {P1 P2 P3 P4 P5 Pool R : SepProp} {m : Memory}
    (h : m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (⌜Q⌝ ∗ Pool)) ∗ R) :
    Q ∧ (m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ Pool) ∗ R) := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ Pool) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h
  rwa [satisfies_pure_sepConj] at h'

private theorem push_pure_5 {Q : Prop} {P1 P2 P3 P4 Pool R : SepProp} {m : Memory}
    (hq : Q) (h : m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ Pool) ∗ R) :
    m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ (⌜Q⌝ ∗ Pool)) ∗ R := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ Pool) ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨hq, h⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h'

private theorem push_pure_6 {Q : Prop} {P1 P2 P3 P4 P5 Pool R : SepProp} {m : Memory}
    (hq : Q) (h : m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ Pool) ∗ R) :
    m ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (⌜Q⌝ ∗ Pool)) ∗ R := by
  have h' : m ⊨ ⌜Q⌝ ∗ ((P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ Pool) ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨hq, h⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h'

theorem pathSpecPlaced_withFdsGe3Closed_of_withFds [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (hok : subroutine_ok prog entry (pathSpecPlaced (withFds A) lim PathEnv stk)) :
    subroutine_ok prog entry (withFdsGe3Closed (pathSpecPlaced A lim PathEnv stk)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hfds0, hpre0⟩ := extract_withFdsGe3Closed hpre
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre0
  have hpre_fds : s0.mem ⊨ (pathSpecPlaced (withFds A) lim PathEnv stk).pre (x, st) s0 ∗ R := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [pathSpecPlaced] at hpre1 ⊢
    rw [withFds_pool_enforced A henf st s0]
    exact push_pure_6 hfds0 hpre1
  refine subroutine_ok.mono_outcome hok (x, st) R s0 hpc hrun hpre_fds hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hexc⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed, pathSpecPlaced, withLsCodeRoLoaded] at hpost ⊢
    rw [withFds_repAlloc] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    obtain ⟨hfds_sf, hbody⟩ := pull_pure_6 hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds_sf, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, hbody⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem dirGetSpecPlaced_withFds_of_withFdsGe3Closed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (hok : subroutine_ok prog entry
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk))) :
    subroutine_ok prog entry (dirGetSpecPlaced rd pathOk (withFds A) lim GetEnv stk) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [dirGetSpecPlaced] at hpre0
  rw [withFds_repAlloc, withFds_pool_enforced A henf st s0] at hpre0
  obtain ⟨hfds0, hpre1⟩ := pull_pure_6 hpre0
  have hpre_fd : s0.mem ⊨
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv stk)).pre (x, st) s0 ∗ R := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfds0, satisfies_lscro_pre hcrl hpre1⟩
  refine subroutine_ok.mono_outcome hok (x, st) R s0 hpc hrun hpre_fd hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hexc⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hfds_sf, hpost1⟩ := hpost
    dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost1 ⊢
    rw [withFds_repAlloc]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost1 ⊢
    rcases hpost1 with ⟨evs, hpost1⟩
    refine ⟨evs, ?_⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf]
    exact push_pure_5 hfds_sf hpost1
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-! ## `ExistingStoreCalleesPlaced (withFds A)` -/

private theorem cliGhostExterns_bcmp_keepsFs_sat (mmpl : Obj.MultiPlacement)
    (gh' : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) cliBcmpName
      (withVmPreserved cliBcmpSpec).keepsFs := by
  refine cliGhostExterns_sat_of_cliExternsPlaced mmpl gh' W ?_
  rcases cliExternsPlaced_bcmp_budget_sat mmpl W with ⟨f, hf, hok⟩
  have hbcmp := CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_bcmp mmpl W
  rw [hbcmp] at hf
  injection hf with hfg
  subst hfg
  exact ⟨_, hbcmp, hok.keepsFs fun _ => rfl⟩

private theorem sessDeserialize_false_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} :
    subroutine_ok prog (lsmpl.base 46)
      (sessDeserializeSpecPlaced (fun _ => False) A lim (fun _ _ => False)) := by
  refine subroutine_ok_outcome_intro fun ⟨_, _⟩ _ _ _ _ hpre _ => ?_
  obtain ⟨_, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1 with ⟨_, _, _, hf, _⟩
  exact False.elim hf

/-- Discharges all 16 fields of `ExistingStoreCalleesPlaced (withFds A)` from `RunHooksPlaced` at
`A` and `withFds A` together with `withLsRetAddr624AndFds` `readFile` `HookSat`. -/
theorem w3Exist_withFds_placed_ok_of_hooks_fd [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (henf : lim.enforced = true)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hh0 : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hh' : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      (withFds A) lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hh3' : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W (withFds A) lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hReadSatFd : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))) :
    ExistingStoreCalleesPlaced (withFds A) lim (cliExistingStoreCalleesEnvs ReadEnv)
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) cliRunBudgets := by
  let H := cliGhostExterns gh' (cliExternsPlaced mmpl W)
  have hPath589_fds : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)) :=
    pathSpecPlaced_withFdsGe3Closed_of_withFds henf
      ((SessKitHooksPlaced.of_runHooks hh').path
        (callerProg := lsProg_589 H) (i := 589) (Nat.le_refl pathNeed) (by decide))
  have hGetFd : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed
        (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
          cliRunBudgets.dirGetNeed)) :=
    dirGet_placed_caller_ok_of_deps_fd
      (callerProg := lsProg_589 H) (i := 589)
      (pathProg := lsProg_589 H) (jPath := 589)
      (fun _ hp => hp.2) hh0.allocFs (cliGhostExterns_bcmp_keepsFs_sat mmpl gh' W)
      (by decide) (by decide) hPath589_fds hReadSatFd
      (hh0.fs (lsProg_589 H) 589)
      (Nat.le_refl cliRunBudgets.dirGetNeed)
      (fun _ _ _ _ h => h) (by decide)
  have hGet' : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed) :=
    dirGetSpecPlaced_withFds_of_withFdsGe3Closed henf hGetFd
  have hAddr' := cliAddrText_placed_ok hh'
  have hPutStr' : subroutine_ok (lsProg_543 H) (lsmpl.base 543)
      (dirPutStrSpecPlaced (withFds A) lim DirPutStrEnv cliDirPutStrNeedPlaced) :=
    dirPutStr_placed_ok_of_deps hh'.alloc hh'.panics hh'.memcpyRO hh'.bcmp
      (growProg := lsProg_586 H) (jGrow := 586)
      (by decide) (by decide) (cliGrowOneDir_placed_ok hh'.alloc hh'.panics)
      (Nat.le_refl cliDirPutStrNeedPlaced)
  have hPut' : subroutine_ok (lsProg_542 H) (lsmpl.base 542)
      (dirPutSpecPlaced (withFds A) lim DirPutEnv cliDirPutStk) :=
    dirPut_placed_caller_ok_of_deps
      (callerProg := lsProg_542 H) (i := 542)
      hh'.alloc hh'.bcmp
      (growProg := lsProg_586 H) (jGrow := 586)
      (by decide) (by decide) (cliGrowOneDir_placed_ok hh'.alloc hh'.panics)
      (Nat.le_refl dirPutNeedPlaced) (by decide)
  have hEq := publicKeyEq_placed_ok_of_bb (cliGhostExterns_blackBox_eq mmpl gh' W)
  have hDec' := identityKey_decode_placed_ok (A := withFds A) H
  exact
    { dirGet := hGet'
      addressText := hAddr'
      dirPut := hPut'
      idTrustShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact idTrustShim_placed_ok_of_deps hh'.alloc (by omega)
      idTrustPoll := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have := stk_sub_ge_dirGet hstk
        have : extHookStack ≤ 65536 := by decide
        exact idTrustPoll_placed_ok_of_deps hh'.alloc hGet' hDec' hEq (by omega)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      sessLoadShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x20 + extHookStack ≤ 516880 := by decide
        exact sessLoadShim_placed_ok_of_deps hh'.alloc (by omega)
      sessLoadPoll := fun {stk} hstk =>
        sessLoadPoll_placed_ok_of_deps hh'.alloc hAddr' hGet'
          (sessDeserialize_false_placed_ok (prog := lsProg_569 H))
          (hh3'.fs (prog := lsProg_569 H) (i := 569))
          (sessLoadPoll_stk_le (by decide) hstk)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      idSaveShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact idSaveShim_placed_ok_of_deps hh'.alloc (by omega)
      idSavePoll := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have := stk_sub_ge_dirGet hstk
        have : cliDirPutStrNeedPlaced ≤ 65536 := by decide
        have : publicKeySerializeStackX ≤ 65536 := by decide
        have : extHookStack ≤ 65536 := by decide
        exact idSavePoll_placed_ok_of_deps hh'.alloc hGet' hPutStr' hDec' hEq (by omega)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      sessStoreShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact sessStoreShim_placed_ok_of_deps hh'.alloc (by omega)
      rodata_idVt_keyPairSlot := rodata_cliIdentity_kpSlot_placed
      rodata_idVt_regIdSlot := rodata_cliIdentity_regIdSlot_placed
      rodata_idVt_saveSlot := rodata_cliIdentity_saveSlot_placed
      rodata_idVt_trustSlot := rodata_cliIdentity_trustSlot_placed
      rodata_sessVt_loadSlot := rodata_cliSession_loadSlot_placed
      rodata_sessVt_storeSlot := rodata_cliSession_storeSlot_placed }

/-! ## Reduction to `CliInitSlotOkPlacedAt (withFds A)` -/

/-- Any `CliInitSlotOkPlacedAt H (withFds A) lim InitEnv X W` with `lim.enforced = true`
immediately discharges the pre-only `FdsGe3Closed` W3 slot obligation on `lsProg_579 H` calling
`lsmpl.base 521`. -/
theorem cliInitSlotOkPlacedAt_preFd_of_withFds [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hSlot : CliInitSlotOkPlacedAt H (withFds A) lim InitEnv X W) :
    ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
      sEnvs.initiate = InitEnv →
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      needs.initiate = cliInitiateNeed cliRunBudgets →
      (slotWithPreFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).initiate).OkPlaced
        (lsProg_579 H) (lsmpl.base 521) := by
  intro S sEnvs needs henv hfiles hS hinitOk hneed stk hlo hhi
  exact subroutine_ok_semInitSlot_preFd_of_withFds henf
    (hSlot S sEnvs needs henv hfiles hS hinitOk hneed stk hlo hhi)

theorem cliInitSlotOkPlacedAt_preFd_of_seams [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hGSpqr : CliGhostSpqrAllocHooks M A lim gh')
    (hStrFsT : ∀ f, gh'.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone0 : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hStrCloneFd : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsStringCloneSym
      (withFdsGe3Closed (stringCloneBudgetSpec M A lim)))
    (hFmt0 : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim))
    (hFmt' : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M (withFds A) lim))
    (hReadSatFd : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)))
    (hSpqrInit' : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec (withFds A) lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X) W X x s0 st0) :
    ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
      sEnvs.initiate = InitEnv →
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      needs.initiate = cliInitiateNeed cliRunBudgets →
      (slotWithPreFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (lsmpl.base 521) := by
  let hAlloc' := cliGhostSpqrAllocHooks_withFds hGSpqr
  let hStrClone' := hookSat_stringCloneBudget_withFds_of_enforced henf hStrCloneFd
  let hh0 :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced.of_hooks
      mmpl gh' W hGSpqr hStrFsT hStrClone0 hFmt0
  let hh' :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced.of_hooks
      mmpl gh' W hAlloc' hStrFsT hStrClone' hFmt'
  let hh3' :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced.of_hooks
      mmpl gh' W hAlloc' hStrFsT hStrClone' hFmt'
  have hExist' :=
    w3Exist_withFds_placed_ok_of_hooks_fd mmpl gh' W A lim henf ReadEnv hh0 hh' hh3' hReadSatFd
  have hLocal' : ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
      InitLocalCalleesPlaced (withFds A) lim InitStateEnv mmpl gh' W stk :=
    fun hstk hstk64 =>
      w3Local_placed_ok_of_seams mmpl gh' W (withFds A) lim InitStateEnv cliRunBudgets
        hh3' hSpqrInit' hVerifySig hstk hstk64
  exact cliInitSlotOkPlacedAt_preFd_of_withFds henf
    (cliInitSlotOkPlacedAt_of_local mmpl gh' W X hh3' hExist' hLocal'
      (fun S _ => stage3PlacedOk_okEvents (withFds A) lim InitStateEnv InitEnv mmpl gh' W X
        cliRunBudgets S)
      hghNoAlloc hFits)

end

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAtFd
