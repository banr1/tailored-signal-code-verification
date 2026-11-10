/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P1 Instantiation

Discharges `stageP1VtablesPlacedAt` under `LibsignalRoLoaded lsmpl s0.mem` and instantiates
parametric-kit and concrete CLI Stage P1 contracts (`StageP1OkCliPlacedStmt`,
`StageP1OkTrapPlacedStmt`, `StageP1UntrustedCliPlacedStmt`, and `StageP1UntrustedTrapPlacedStmt`)
from `hDropNz : lsmpl.base 547 ≠ 0#64`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalRoLoaded ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Pqxdh.ResponderClosure
  (ClosureCalleeSaved PanicOomProp decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt
   decryptPrekeySavedRegsAt processPrekeyInnerInitAt processPrekeyPostTrustAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (loadCallStack p1LoadedRecordAt stageP1CallStack stageP1ProgPlaced
   stageP1UntrustedCallStack)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack noAllocShimSpec sessionMemcpyRegionSpec withStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (apiDecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsFiles IdentityStoreSpec IdentityVtablesPlacedOk LibsignalCodeRoLoaded
   SessionOnlyVtablesPlacedOk SessionStoreSpec extract_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust (trustCallStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (loadPollNeed loadShimNeed)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (trustPollNeed trustShimNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliKitStk cliPollIdKitPlaced
   cliPollId_vtablesPlacedOk cliPollSessKit cliPollSessKitPlaced cliPollSess_vtablesPlacedOk
   dpPollEntryPlaced dpPollProgPlaced satisfies_stageP1VtablesPlacedAt stageP1VtablesPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlacedBudget
  (stageP1_ok_kit_x_ext_placed)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudget
  (stageP1_untrusted_ok_kit_x_ext_placed)
open LibsignalBinary.Proofs.Common.StringClonePlaced
  (lsRustAllocPlacedSym lsRustNoAllocShimPlacedSym)
open LibsignalBinary.Proofs.Common.StringClonePlacedBudget
  (stringCloneBudget_placed_codeLoaded_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (session_memcpy_region_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv StageP1UntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollIdBudgetEnv cliPollId_kitPlacedOkI cliPollSessBudgetEnv cliPollSess_kitPlacedOkSE)

/-! ## 1. Vtable Introduction & Callee Discharges on `dpPollProgPlaced ext` -/

private theorem stageP1ProgPlaced_eq_dpPollProgPlaced [LibsignalPlacement]
    (ext : String → Option (State → State)) :
    stageP1ProgPlaced ext = dpPollProgPlaced ext :=
  rfl

private theorem sepWPp_intro_stageP1VtablesPlacedAt [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {target : BitVec 64} {s0 : State}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {P P' : SepProp} {Q post onPanic : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hsess : SessionOnlyVtablesPlacedOk kit)
    (hid : IdentityVtablesPlacedOk ikit)
    (hpre : stageP1VtablesPlacedAt kit ikit ∗ P = P')
    (hwp : SepWPp prog target s0 P' Q onPanic)
    (hpost : ∀ sf P_f, Q sf P_f → ∃ Drop P_clean, (P_f ⊢ Drop ∗ P_clean) ∧ post sf P_clean) :
    SepWPp prog target s0 P post onPanic := by
  intro R hm hL
  have hm' : s0.mem ⊨ P' ∗ R := by
    rw [← hpre, sepConj_assoc]
    exact satisfies_stageP1VtablesPlacedAt hsess hid hro hm
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hq⟩ | hrest
  · obtain ⟨Drop, P_clean, hent, hp⟩ := hpost sf P_f hq
    have hm1 : sf.mem ⊨ (Drop ∗ P_clean) ∗ R := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hm1
    exact Or.inl ⟨hpc, hrun, P_clean, Satisfies.drop_left hm1, hp⟩
  · exact Or.inr hrest

private theorem session2Memcpy_dpPoll_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hAlloc : AllocContractsXCliPlaced A lim ext) :
    subroutine_ok (dpPollProgPlaced ext) (lsρ "memcpy")
      (withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX) := by
  have h := session_memcpy_region_lscro_of_cli (callerProg := dpPollProgPlaced ext) (i := 518)
    hAlloc (stk := extHookStack) (by decide) (by decide) (by decide)
  refine subroutine_ok_mono h
    (fun ⟨dst, src, bs⟩ R s0 hpre => ?_)
    (fun ⟨dst, src, bs⟩ R s0 sf hpost => ?_)
  · obtain ⟨hcrl, hrest⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpyBudgetSpecX] at hrest ⊢
    rw [sepConj_assoc] at hrest
    have h1 : s0.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        ((⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧
            (s0.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp extHookStack) ∗ R) :=
      (satisfies_pure_sepConj _ _ _).mpr ⟨hcrl, by simpa only [sepConj_assoc] using hrest⟩
    have h2 : s0.mem ⊨
        ((⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧
            (s0.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗
          stackAt s0.sp extHookStack ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R := by
      convert h1 using 1; sep_ac_rfl
    simpa only [sepConj_assoc] using h2
  · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, session2MemcpyBudgetSpecX] at hpost ⊢
    have h1 : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗
        (⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
          ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp extHookStack ∗ R)) := by
      convert hpost using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h1.2.1.1, h1.2.1.2, h1.1⟩, by simpa only [sepConj_assoc] using h1.2.2⟩

private theorem dealloc_dpPoll_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hDealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (dpPollProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
  ls_hook_ok_ultra_of_mem (i := 518) hDealloc (by decide)

private theorem stringClone_dpPoll_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hShim : HookSat ext lsRustNoAllocShimPlacedSym sessionShimBudgetSpec)
    (hAllocHook : HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext "memcpy" sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 623) (withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (stringCloneBudget_placed_codeLoaded_ok
      (callerProg := dpPollProgPlaced ext) (i := 518)
      hShim hAllocHook hMemcpy (by decide))

private theorem dropSessionStructure_dpPoll_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hDealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (dpPollProgPlaced ext) (lsmpl.base 512)
      (withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (drop_session_structure4_placed_ok_at (callerProg := dpPollProgPlaced ext) (i := 518)
      hDealloc (by decide))

private theorem extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A_rep : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤ loadCallStack (cliPollSessKitPlaced A_rep F0 scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk, loadShimNeed, loadPollNeed, allocHookStack]
  omega

private theorem extHookStack_le_cliPollId_trustCallStack [LibsignalPlacement]
    (A_rep : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤ trustCallStack (cliPollIdKitPlaced A_rep F0 peer (cliKitStk B)) := by
  dsimp only [extHookStack, trustCallStack, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced,
    cliIdStoreSpecFull, cliIdentityStoreSpec, cliKitStk, trustShimNeed, trustPollNeed,
    allocHookStack]
  omega

/-! ## 2. Spatial Pre/Post Abbreviations (Reducible, Vtable-Free) -/

/-- Vtable-free spatial precondition for budget-threaded Stage P1 (`is_trusted_identity =.ok true`). -/
@[reducible] def stageP1OkPreAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (s0 : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 b_4f2 : BitVec 8) : SepProp :=
  decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr ∗
  cells (coroPtr + 0x70#64) 14 ∗
  cells (coroPtr + 0xe0#64) 4 ∗
  memRegion (coroPtr + 0x100#64) 336 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
  cells (coroPtr + 0x2c8#64) 25 ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
  ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
  cells (coroPtr + 0x428#64) 8 ∗
  cells (coroPtr + 0x490#64) 4 ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  (sp ↦₆₄ v_sp0) ∗
  ((sp + 0x98#64) ↦₆₄ u_98) ∗
  ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
  ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
  ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (s0.sp - 0x60#64) 12 ∗
  lsLogOff ∗
  kit.storeAt sessStorePtr st ∗
  ikit.identityAt idStorePtr ist ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
  A.pool lim st_b s0 ∗
  stackAt sp (stageP1CallStack kit ikit)

/-- Vtable-free postcondition for budget-threaded Stage P1 (`is_trusted_identity =.ok true`). -/
@[reducible] def stageP1OkPostAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st : kit.StoreState) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (sf : State) (P_f : SepProp) : Prop :=
  (∃ opt : Option (SessionRecord (List (BitVec 8))), ∃ evs : List AllocEvent,
    StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey evs ∧
    kit.loadRel st peer.val (.ok opt) ∧
    ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
    sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
    (P_f ⊢
      ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
        decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
          preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
          kyberStorePtr kyberStoreVt rngPtr ∗
        decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
          preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
          kyberStorePtr kyberStoreVt rngPtr ∗
        p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
        ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
        processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
          spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
        processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
          spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
        ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
        cells (coroPtr + 0x398#64) 2 ∗
        ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
        (sp ↦₆₄ 0#64) ∗
        ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
        ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
        ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
        ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        memRegion (sp + 0x3e0#64) 368 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        lsLogOff ∗
        kit.storeAt sessStorePtr st ∗
        ikit.identityAt idStorePtr
          (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
        protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
        ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
        A.pool lim (M.stepEvents evs st_b) sf ∗
        stackAt sp (stageP1CallStack kit ikit))) ∧
  sf.sp = sp ∧
  sf.readReg64 .x8 = kyberStorePtr ∧
  sf.readReg64 .x9 = msgPtr ∧
  sf.readReg64 .x10 = kyberStoreVt ∧
  sf.readReg64 .x11 = preKeyStorePtr ∧
  sf.readReg64 .x12 = remoteAddrPtr ∧
  sf.readReg64 .x13 = preKeyStoreVt ∧
  sf.readReg64 .x14 = localAddrPtr ∧
  sf.readReg64 .x15 = idStorePtr ∧
  sf.readReg64 .x16 = ikit.id_vt ∧
  sf.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
  sf.readReg64 .x19 = coroPtr ∧
  sf.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
  sf.readReg64 .x22 = spkStorePtr ∧
  sf.readReg64 .x23 = coroPtr + 0xe0#64 ∧
  sf.readReg64 .x24 = spkStoreVt ∧
  sf.readReg64 .x25 = sp + 0x210#64 ∧
  sf.readReg64 .x28 = sp + 0xa90#64 ∧
  sf.readReg64 .x29 = s0.sp - 0x60#64 ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
  LibsignalCodeRoLoaded lsmpl sf.mem

/-- Vtable-free spatial precondition for budget-threaded Stage P1 (`is_trusted_identity =.ok false`). -/
@[reducible] def stageP1UntrustedPreAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (s0 : State)
    (sp outPtr coroPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8) : SepProp :=
  decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr ∗
  cells (coroPtr + 0x70#64) 14 ∗
  cells (coroPtr + 0xe0#64) 4 ∗
  memRegion (coroPtr + 0x100#64) 336 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
  cells (coroPtr + 0x2c8#64) 25 ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
  ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
  (sp ↦₆₄ v_sp0) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
  ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
  ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0xa90#64) 6 ∗
  cells (s0.sp - 0x60#64) 12 ∗
  memRegion outPtr 48 ∗
  lsLogOff ∗
  kit.storeAt sessStorePtr st ∗
  ikit.identityAt idStorePtr ist ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
  A.pool lim st_b s0 ∗
  stackAt sp (stageP1UntrustedCallStack kit ikit)

/-- Vtable-free postcondition for budget-threaded Stage P1 (`is_trusted_identity =.ok false`). -/
@[reducible] def stageP1UntrustedPostAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st : kit.StoreState) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (sf : State) (P_f : SepProp) : Prop :=
  (∃ opt : Option (SessionRecord (List (BitVec 8))), ∃ evs : List AllocEvent,
    StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey evs ∧
    kit.loadRel st peer.val (.ok opt) ∧
    ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
    sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
      ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
    (P_f ⊢
      ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
        decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
          preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
          kyberStorePtr kyberStoreVt rngPtr ∗
        decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
          preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
          kyberStorePtr kyberStoreVt rngPtr ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗
        cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
        processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
          spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
        ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        cells (coroPtr + 0x398#64) 2 ∗
        (sp ↦₆₄ 0#64) ∗
        ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
        ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
        ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0xa90#64) 6 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
        lsLogOff ∗
        kit.storeAt sessStorePtr st ∗
        ikit.identityAt idStorePtr
          (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
        protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
        ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
        A.pool lim (M.stepEvents evs st_b) sf ∗
        stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
  sf.sp = s0.sp ∧
  ClosureCalleeSaved s0 sf ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
  LibsignalCodeRoLoaded lsmpl sf.mem

/-! ## 3. Generic-`ext` Vtable-Discharged Stage-P1 Theorems -/

set_option maxHeartbeats 800000 in
/-- Generic-`ext` budget-threaded Stage P1 (`is_trusted_identity =.ok true`,
`dpPollEntryPlaced → dpPollEntryPlaced + 0x868`) discharging `stageP1VtablesPlacedAt` from
`SessionOnlyVtablesPlacedOk` and `IdentityVtablesPlacedOk`. -/
theorem stageP1_ok_placed_of_vtables [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st : kit.StoreState} {ist : ikit.IdState} {st_b : M.σ}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hAlloc : AllocContractsXCliPlaced A lim ext)
    (hDealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hSkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext)
    (hSvt : SessionOnlyVtablesPlacedOk kit)
    (hIkit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hIvt : IdentityVtablesPlacedOk ikit)
    (hstack_lt : stageP1CallStack kit ikit ≤ 2 ^ 64)
    (hext_load : extHookStack ≤ loadCallStack kit)
    (hext_trust : extHookStack ≤ trustCallStack ikit)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_true : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true)
    (hfits : FitsEnv M lim st_b (StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey))
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 b_4f2 : BitVec 8)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (dpPollProgPlaced ext) s0)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (dpPollProgPlaced ext)
      (dpPollEntryPlaced + 0x868#64) s0
      (stageP1OkPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
        sp coroPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr
        v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2)
      (stageP1OkPostAt A lim st_b Scope encRecord kit kitEnv ikit ikitEnv st ist
        peer remoteIdKey s0
        sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr)
      Qp := by
  have hwp0 := stageP1_ok_kit_x_ext_placed
    (A := A) (lim := lim) (st0 := st_b) (ext := ext)
    (Scope := Scope) (encRecord := encRecord)
    (kit := kit) (kitEnv := kitEnv) (ikit := ikit) (ikitEnv := ikitEnv)
    (st := st) (ist := ist) (Qp := Qp)
    peer remoteIdKey
  rw [stageP1ProgPlaced_eq_dpPollProgPlaced ext] at hwp0
  have hwp := hwp0
    (dealloc_dpPoll_ok hDealloc)
    (session2Memcpy_dpPoll_ok hAlloc)
    (hSkit.loadShim (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hSkit.loadPoll (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hSkit.loadFutDrop (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustShim (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustPoll (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustFutDrop (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    hstack_lt hext_load hext_trust
    haddr_ss haddr_id hload_ok htrust_true hfits
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390 b_4f2
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine sepWPp_intro_stageP1VtablesPlacedAt hcrl.2 hSvt hIvt
    (by dsimp only [stageP1OkPreAt, stageP1VtablesPlacedAt]; sep_ac_rfl) hwp
    fun sf P_f hpost => ?_
  rcases hpost with ⟨⟨opt, evs, hrel_load, hrel_trust, henv, htr_f, hent⟩, hregs⟩
  refine ⟨stageP1VtablesPlacedAt kit ikit, _, ?_,
    ⟨⟨opt, evs, henv, hrel_load, hrel_trust, htr_f, Entails.refl _⟩, hregs⟩⟩
  refine Entails.trans hent (Entails.of_eq ?_)
  simp only [sepExists_sepConj_right]
  refine congrArg sepExists (funext fun v_a8 => ?_)
  refine congrArg sepExists (funext fun v_b8 => ?_)
  refine congrArg sepExists (funext fun v_d0 => ?_)
  dsimp only [stageP1VtablesPlacedAt]
  sep_ac_rfl

set_option maxHeartbeats 800000 in
/-- Generic-`ext` budget-threaded Stage P1 (`is_trusted_identity =.ok false`,
`dpPollEntryPlaced → s0.readReg64.x30`) discharging `stageP1VtablesPlacedAt` from
`SessionOnlyVtablesPlacedOk` and `IdentityVtablesPlacedOk`. -/
theorem stageP1_untrusted_placed_of_vtables [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st : kit.StoreState} {ist : ikit.IdState} {st_b : M.σ}
    {Qp : State → SepProp → Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hAlloc : AllocContractsXCliPlaced A lim ext)
    (hDealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hShim : HookSat ext lsRustNoAllocShimPlacedSym sessionShimBudgetSpec)
    (hAllocHook : HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext "memcpy" sessionMemcpyRegionBudgetSpec)
    (hSkit : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext)
    (hSvt : SessionOnlyVtablesPlacedOk kit)
    (hIkit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hIvt : IdentityVtablesPlacedOk ikit)
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (hext_load : extHookStack ≤ loadCallStack kit)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hload_ok : ∀ ans, kit.loadRel st peer.val ans → ans.isOk = true)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (hfits : FitsEnv M lim st_b (StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey))
    (s0 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr
     v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (b_390 : BitVec 8)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hfs : FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
      (dpPollProgPlaced ext) s0)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_def : s0.sp - 0xcd0#64 = sp)
    (hx0 : s0.readReg64 .x0 = outPtr)
    (hx1 : s0.readReg64 .x1 = coroPtr)
    (hx2 : s0.readReg64 .x2 = ctxPtr) :
    SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s0
      (stageP1UntrustedPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
        sp outPtr coroPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr
        v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390)
      (stageP1UntrustedPostAt A lim st_b encRecord kit kitEnv ikit ikitEnv st ist
        peer remoteIdKey s0
        sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr idStorePtr
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr)
      Qp := by
  have hwp0 := stageP1_untrusted_ok_kit_x_ext_placed
    (A := A) (lim := lim) (st0 := st_b) (ext := ext)
    (Scope := Scope) (encRecord := encRecord)
    (kit := kit) (kitEnv := kitEnv) (ikit := ikit) (ikitEnv := ikitEnv)
    (st := st) (ist := ist) (Qp := Qp)
    peer remoteIdKey
  rw [stageP1ProgPlaced_eq_dpPollProgPlaced ext] at hwp0
  have hwp := hwp0
    (dropSessionStructure_dpPoll_ok hDealloc)
    (dealloc_dpPoll_ok hDealloc)
    (session2Memcpy_dpPoll_ok hAlloc)
    (stringClone_dpPoll_ok hShim hAllocHook hMemcpy)
    (hSkit.loadShim (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hSkit.loadPoll (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hSkit.loadFutDrop (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustShim (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustPoll (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    (hIkit.trustFutDrop (callerProg := dpPollProgPlaced ext) (callerBlk := 518) (by decide))
    hstack_lt hext_load
    haddr_ss haddr_id hload_ok htrust_false hfits
    s0 sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr idStorePtr
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    b_390
    hcrl hfs hpc hrun hsp_align hsp_def hx0 hx1 hx2
  refine sepWPp_intro_stageP1VtablesPlacedAt hcrl.2 hSvt hIvt
    (by dsimp only [stageP1UntrustedPreAt, stageP1VtablesPlacedAt]; sep_ac_rfl) hwp
    fun sf P_f hpost => ?_
  rcases hpost with ⟨⟨opt, evs, hrel_load, hrel_trust, henv, htr_f, hent⟩, hregs⟩
  refine ⟨stageP1VtablesPlacedAt kit ikit, _, ?_,
    ⟨⟨opt, evs, henv, hrel_load, hrel_trust, htr_f, Entails.refl _⟩, hregs⟩⟩
  refine Entails.trans hent (Entails.of_eq ?_)
  simp only [sepExists_sepConj_right]
  refine congrArg sepExists (funext fun v_a8 => ?_)
  refine congrArg sepExists (funext fun v_b8 => ?_)
  refine congrArg sepExists (funext fun v_d0 => ?_)
  dsimp only [stageP1VtablesPlacedAt]
  sep_ac_rfl

/-! ## 4. Parametric-Kit & Concrete CLI Stage-P1 Statements & Instantiations -/

/-- Parametric-kit budget-threaded CLI Stage P1 (`is_trusted_identity =.ok true`,
`dpPollEntryPlaced → dpPollEntryPlaced + 0x868`) on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem stageP1_ok_placed_of_kits [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    {kitEnv : SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      kitEnv scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hIkit : IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      ikitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      stageP1CallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true) →
      FitsEnv M lim st_b (StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 b_4f2 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (dpPollEntryPlaced + 0x868#64) s0
          (stageP1OkPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2)
          (stageP1OkPostAt A lim st_b scopeKit encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          Qp := by
  intro σ kit ikit st_b st ist hstack_lt
  exact stageP1_ok_placed_of_vtables peer remoteIdKey hh.alloc hh.codecHooks.dealloc
    hSkit (cliPollSess_vtablesPlacedOk F0 scopeKit peer σ hDropNz)
    hIkit (cliPollId_vtablesPlacedOk F0 peer σ hDropNz)
    hstack_lt
    (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B F0 peer)
    (extHookStack_le_cliPollId_trustCallStack A.repAlloc B F0 peer)

/-- Concrete CLI-instantiated budget-threaded Stage P1 (`is_trusted_identity =.ok true`,
`onPanic := fun _ _ => False`) statement binding `kitEnv` to `cliPollSessBudgetEnv` and `ikitEnv`
to `cliPollIdBudgetEnv`. -/
def StageP1OkCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      stageP1CallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true) →
      FitsEnv M lim st_b (StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 b_4f2 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (dpPollEntryPlaced + 0x868#64) s0
          (stageP1OkPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2)
          (stageP1OkPostAt A lim st_b scopeKit encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          (fun _ _ => False)

/-- Instantiates `StageP1OkCliPlacedStmt` via `stageP1_ok_placed_of_kits`. -/
theorem stageP1_ok_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP1OkCliPlacedStmt :=
  fun mmpl gh W B F0 peer remoteIdKey hh hRead hDeser =>
    stageP1_ok_placed_of_kits mmpl gh W B F0 peer remoteIdKey hDropNz hh
      (cliPollSess_kitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)

/-- Budget-threaded counterpart of `Poll.StageP1OkTrapPlacedStmt` (`onPanic := PanicOomProp s0`). -/
def StageP1OkTrapPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
      stageP1CallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true) →
      FitsEnv M lim st_b (StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 b_4f2 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (dpPollEntryPlaced + 0x868#64) s0
          (stageP1OkPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2)
          (stageP1OkPostAt A lim st_b scopeKit encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          (PanicOomProp s0)

/-- Instantiates `StageP1OkTrapPlacedStmt` via `stageP1_ok_placed_of_kits`. -/
theorem stageP1_ok_trap_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP1OkTrapPlacedStmt :=
  fun mmpl gh W B F0 peer remoteIdKey st_b st ist hh hRead hDeser
    hstack_lt haddr_ss haddr_id hload_ok htrust_true hfits s0 =>
    stageP1_ok_placed_of_kits mmpl gh W B F0 peer remoteIdKey hDropNz hh
      (cliPollSess_kitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)
      st_b st ist hstack_lt haddr_ss haddr_id hload_ok htrust_true hfits s0

/-- Parametric-kit budget-threaded CLI Stage P1 (`is_trusted_identity =.ok false`,
`dpPollEntryPlaced → s0.readReg64.x30`) on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem stageP1_untrusted_placed_of_kits [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    {kitEnv : SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      kitEnv scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hIkit : IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      ikitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
      FitsEnv M lim st_b (StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s0
          (stageP1UntrustedPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp outPtr coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390)
          (stageP1UntrustedPostAt A lim st_b encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          Qp := by
  intro σ kit ikit st_b st ist hstack_lt
  exact stageP1_untrusted_placed_of_vtables peer remoteIdKey
    hh.alloc hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)
    hSkit (cliPollSess_vtablesPlacedOk F0 scopeKit peer σ hDropNz)
    hIkit (cliPollId_vtablesPlacedOk F0 peer σ hDropNz)
    hstack_lt
    (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B F0 peer)

/-- Concrete CLI-instantiated budget-threaded Stage P1 (`is_trusted_identity =.ok false`,
`onPanic := fun _ _ => False`) statement binding `kitEnv` to `cliPollSessBudgetEnv` and `ikitEnv`
to `cliPollIdBudgetEnv`. -/
def StageP1UntrustedCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
      FitsEnv M lim st_b (StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s0
          (stageP1UntrustedPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp outPtr coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390)
          (stageP1UntrustedPostAt A lim st_b encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          (fun _ _ => False)

/-- Instantiates `StageP1UntrustedCliPlacedStmt` via `stageP1_untrusted_placed_of_kits`. -/
theorem stageP1_untrusted_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP1UntrustedCliPlacedStmt :=
  fun mmpl gh W B F0 peer remoteIdKey hh hRead hDeser =>
    stageP1_untrusted_placed_of_kits mmpl gh W B F0 peer remoteIdKey hDropNz hh
      (cliPollSess_kitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)

/-- Budget-threaded counterpart of `Poll.StageP1UntrustedTrapPlacedStmt` (`onPanic := PanicOomProp s0`). -/
def StageP1UntrustedTrapPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles)
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
      stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
      FitsEnv M lim st_b (StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 : BitVec 8),
        LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s0
          (stageP1UntrustedPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp outPtr coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390)
          (stageP1UntrustedPostAt A lim st_b encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          (PanicOomProp s0)

/-- Instantiates `StageP1UntrustedTrapPlacedStmt` via `stageP1_untrusted_placed_of_kits`. -/
theorem stageP1_untrusted_trap_placed_inst [LibsignalPlacement] (hDropNz : lsmpl.base 547 ≠ 0#64) :
    StageP1UntrustedTrapPlacedStmt :=
  fun mmpl gh W B F0 peer remoteIdKey st_b st ist hh hRead hDeser
    hstack_lt haddr_ss haddr_id hload_ok htrust_false hfits s0 =>
    stageP1_untrusted_placed_of_kits mmpl gh W B F0 peer remoteIdKey hDropNz hh
      (cliPollSess_kitPlacedOkSE mmpl gh W B F0 peer hDropNz hh hRead hDeser)
      (cliPollId_kitPlacedOkI mmpl gh W B F0 peer hDropNz hh hRead)
      st_b st ist hstack_lt haddr_ss haddr_id hload_ok htrust_false hfits s0

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
