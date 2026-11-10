/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import ProofLib.SepLogic.WPp

/-!
# Kit-Parametric and `withFds` Untyped Poll and `v3` Rejection

Discharges untrusted-identity Stage P1, trusted-identity Stage P1 bind, and `v3` poll rejection
from `CliDecPkPollKitsPlacedOk` (without raw `hRead`/`hDeser` hypotheses), and specializes `v3`
poll rejection to `withFds A`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (ApiError PreKeySignalMessage SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  loadCallStack p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack
  stageP1UntrustedCallStack
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt
  processPrekeyInnerInitAt processPrekeyPostTrustAt
)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack noAllocShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliIdentityStoreSpec cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced
  cliSessionStoreSpec cliSignedPreKeyStoreSpecPlaced
)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (loadPollNeed loadShimNeed)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem decResAt dpPollNeed dpSlotArgsPlaced
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt dpFutStartAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  DpKitStk LsTokenInit StageP1PostRegs apiDecResultAt_untrusted_entails_decResAt
  cliIdInv_opened_peer cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted
  cliKitStk cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced cliPollId_vtablesPlacedOk
  cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced
  cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
  cliPollStoresKitsAtPlaced_entails_storesAt cliSessInv_opened_scopeKit cliSess_loadRel_isOk
  closStackUnusedP1OkAt closStackUnusedUntrustedAt clos_stack_3280_of_p1_untrusted
  clos_stack_3280_split_for_p1_ok clos_stack_3280_split_for_p1_untrusted
  closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At coro_of_p1_untrusted_entails_dpFutDoneAt
  dpClosSubStack dpFutStartAt_split_for_p1_placed dpPollEntryPlaced
  dpPollNeed_eq_frame_add_subStack dpPollProgPlaced pmKyberId pmPreKeyId preKeyMsgAt_eq_idKey_sep
  preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left slotOutTr_of_err sp_frame_sub_add
  stackAt_poll_entry_split stackAt_subStack_split stageP1CallStack_le_subStack
  stageP1UntrustedCallStack_le_subStack stageP2PostP1At storesAt_entails_cliPollStoresKitsAtPlaced
  subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn scopeKit)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd (
  CliDecPkPollKitsPlacedOk CliDecPkPollKitsPlacedOkFds cliDecPkPollKitsFds_toWithFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget (
  DecPkD3UntypedPollEnv DecPkStoreOk StageP2V3RejectEnv cliIdOwnInv_of_storeOk
  cliKpkInvFull_of_storeOk cliPkInv_of_storeOk cliSpkInv_of_storeOk dpPollPre_unpack_d3_placedBudget
  stageP2V3RejectEnv_nonempty
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget (
  MsgCondV3 stageP2_v3_reject_placedBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollIdBudgetEnv cliPollSessBudgetEnv cliPollStageP1_fsAt_placed
  dpPollPost_of_decResAt_placed runHooks_to_stages stageP1_untrusted_mangled_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1_ok_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn)

/-! ## 1. Untrusted-Identity Stage P1 via Store-Kit Contracts -/

private theorem extHookStack_le_cliPollSess_loadCallStack_d3 [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤ loadCallStack (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk, loadShimNeed, loadPollNeed, allocHookStack]
  omega

set_option maxHeartbeats 800000 in
/-- Kit-parametric counterpart of `D3PollRejectAuxPlacedBudget.closure_untrusted_d3_placedBudget_ok`
replacing `hRead`/`hDeser` with `SessionOnlyKitPlacedOkSE` + `IdentityStoreKitPlacedOkI`. -/
theorem closure_untrusted_d3_placedBudget_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hsub : ∀ r, Scope r → scopeIn r) (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hIkit : IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs, CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out) (hx1 : s0.readReg64 .x1 = y.fut) (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F) (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f => (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only; dsimp only [dpPollEntrySpatialPlaced] at hm_base
  let σ := cliKitStk B; let sp := s0.sp - 0xcd0#64
  let pid := pmPreKeyId y.g.msg; let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg; let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  have hent_stores := storesAt_entails_cliPollStoresKitsAtPlaced (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer) (pid := pid) (sid := sid)
    (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer) (cliIdOwnInv_of_storeOk hstoreOk)
    (cliIdInv_opened_peer hfPeer) (cliPkInv_of_storeOk hstoreOk pid)
    (cliSpkInv_of_storeOk hstoreOk sid) (cliKpkInvFull_of_storeOk hstoreOk kid sid kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗ lsLogOff ∗
        A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut, preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63, stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0, b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗ cells (y.fut + 0x250#64) 6 ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗ ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ (sp ↦₆₄ v_sp0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗ cells (s0.sp - 0x60#64) 12 ∗ memRegion y.out 48 ∗ lsLogOff ∗ kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗ protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗ stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut ∗ closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗ memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗ spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗ kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := stageP1_untrusted_mangled_placed_ok (M := M) (A := A) (lim := lim)
    (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)) (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit) (kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity)
    (st_b := y.st) y.g.peer y.g.msg.identityKey hh.alloc hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    hSkit hIkit
    hp1_64 (extHookStack_le_cliPollSess_loadCallStack_d3 A.repAlloc B y.g.F y.g.peer) rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0 (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp.mono_post_panic ?_ (fun _ _ hf _ _ => False.elim hf) hwp
  rintro sf P_f ⟨⟨_opt, evs, hevs_p1, _hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
  refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
  intro hsteps hmf
  have htr_eq : sf.trace = s0.trace := by
    simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
      cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull, cliIdentityStoreSpec] using htr_evs
  have hout := slotOutTr_of_err StoresGhost.opened s0.trace sf.trace
    (err := ApiError.untrustedIdentity y.g.peer.val) nofun nofun hans
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
  rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
  have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
    (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
  have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0 0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
  have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  let Leftover : SepProp := coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hmf_reord : sf.mem ⊨
      (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗
        (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
          decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
          memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
          processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
          ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗ cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut) ∗
        memRegion y.cx 32 ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗ stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
          ((sp ↦₆₄ 0#64) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ closStackUnusedUntrustedAt sp))) ∗ R := by
    have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
        y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
    rw [htrust_id] at hmf2; dsimp only [Fr_inner] at hmf2
    refine Satisfies.mono ?_ hmf2; dsimp only [Leftover, cliPollStoresKitsAtPlaced]; sep_frame
  rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
  have hmf_folded : sf.mem ⊨
      (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗
        dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
          stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280)) ∗ R :=
    Satisfies.mono (sepConj_mono_left (sepConj_mono hres (sepConj_mono hstores_back
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono hcoro
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280))))))))))))) hmf_reord
  dsimp only [sp] at hmf_folded
  rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
  have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
    StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
    hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
  exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded

/-! ## 2. Trusted-Identity Stage P1 Bind & Poll Dispatcher via Store-Kit Contracts -/

private theorem sepWPp_bind_p1_noPanic {prog : Program} {mid ret : BitVec 64}
    {s0 : State} {P P_p1 F : SepProp} {Q1 Q Qpan : State → SepProp → Prop}
    (hp1 : SepWPp prog mid s0 P_p1 Q1 (fun _ _ => False)) (hP : P = P_p1 ∗ F)
    (hnext : ∀ sm P_m, Steps prog s0 sm → sm.pc = mid → sm.status = .Running →
      Q1 sm P_m → SepWPp prog ret sm (P_m ∗ F) Q Qpan) :
    SepWPp prog ret s0 P Q Qpan := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hq1⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ := hp1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hsteps hpcm hrunm hq1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem stageP1Ok_trace_eq_placedBudget [LibsignalPlacement] {A : RustAlloc}
    {F0 : FsFiles} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {σ : DpKitStk} {remoteIdKey : IdentityKey}
    {opt : Option (SessionRecord (List (BitVec 8)))} {s0 sf : State}
    (htr : sf.trace = s0.trace ++
      (cliPollSessKitPlaced A F0 Scope peer σ).loadEvs encodeRecord peer.val (.ok opt) ++
      (cliPollIdKitPlaced A F0 peer σ).trustEvs peer.val remoteIdKey .receiving (.ok true)) :
    sf.trace = s0.trace := by
  simpa [cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec, cliPollIdKitPlaced,
    cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec] using htr

private theorem p1Ok_recombine_entails_stageP2_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (_hneed : dpPollNeed B ≤ stk') (_hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st1 : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64; let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg; let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg; let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores (ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving (.ok true)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim st1 s1 ∗ stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - stageP1CallStack kit ikit) ∗ memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗ spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗ dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit) ⊢
    stageP2PostP1At (A.atState lim st1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64; let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg; let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg; let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hp1_ent :
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
        p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
        processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
        processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
        ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
        (sp ↦₆₄ 0#64) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool lim st1 s1) ∗
      (memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48) ⊢
      stageP2PostP1At (A.atState lim st1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
      p1LoadedRecordAt scopeKit A.repAlloc y.fut opt :=
    Entails.of_eq (by
      dsimp only [stageP2PostP1At, LibsignalBinary.Heap.RustCliAllocBudget.atState, kit, ikit, pkKit, spkKit, kpkKit,
        cliPollSessKitPlaced, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollPkKitPlaced,
        cliPreKeyStoreSpecPlaced, cliPollSpkKitPlaced, cliSignedPreKeyStoreSpecPlaced,
        cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced]; sep_frame)
  have hpm_ent := Entails.of_eq (preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
      .receiving (.ok true) = StoresGhost.opened.identity := rfl
  let Pass : SepProp :=
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗ lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · rw [htrust_id]; dsimp only [cliPollStoresKitsAtPlaced, Pass, sp, σ, pid, sid, kid, kbk, kit, ikit]; sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]; sep_frame

set_option maxHeartbeats 800000 in
/-- Kit-parametric counterpart of `D3PollRejectAuxPlacedBudget.closure_trusted_p1_d3_placedBudget_bind`
calling `stageP1_ok_placed_of_kits` directly instead of `stageP1_ok_placed_inst` (`hRead`/`hDeser`). -/
theorem closure_trusted_p1_d3_placedBudget_bind_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hsub : ∀ r, Scope r → scopeIn r) (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hIkit : IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hfits_p1 : FitsEnv M lim y.st
      (StageP1OkEnv (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv) StoresGhost.opened.sessions
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey))
    (R : SepProp) (s0 : State) (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hstk_sp : stk' ≤ s0.sp.toNat) (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out) (hx1 : s0.readReg64 .x1 = y.fut) (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F) (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R)
    (hcont : ∀ (opt : Option (SessionRecord (List (BitVec 8)))) (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64),
      StageP1OkEnv (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv) StoresGhost.opened.sessions
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey evs_p1 →
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)).loadRel
        StoresGhost.opened.sessions y.g.peer.val (.ok opt) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 → s1.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.sp = s0.sp - 0xcd0#64 → dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = dpPollEntryPlaced + 0x868#64 → s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
        (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
           (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
         coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
        (fun sf P_f => (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic y s0 sf ∗ R))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f => (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only; dsimp only [dpPollEntrySpatialPlaced] at hm_base
  let σ := cliKitStk B; let sp := s0.sp - 0xcd0#64
  let pid := pmPreKeyId y.g.msg; let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg; let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat := (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_entails_cliPollStoresKitsAtPlaced (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer) (pid := pid) (sid := sid)
    (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer) (cliIdOwnInv_of_storeOk hstoreOk)
    (cliIdInv_opened_peer hfPeer) (cliPkInv_of_storeOk hstoreOk pid)
    (cliSpkInv_of_storeOk hstoreOk sid) (cliKpkInvFull_of_storeOk hstoreOk kid sid kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗ lsLogOff ∗
        A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut, preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63, stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0, b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
  simp only [Nat.reduceMul] at hm_flat; dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗ ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗ ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    (sp ↦₆₄ v_sp0) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗ cells (s0.sp - 0x60#64) 12 ∗ lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗ ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗ stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - stageP1CallStack kit ikit) ∗ memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗ spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗ dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := stageP1_ok_placed_of_kits (Qp := fun _ _ => False)
    mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey hDropNz
    (runHooks_to_stages hh) hSkit hIkit y.st StoresGhost.opened.sessions StoresGhost.opened.identity
    hp1_64 rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0
    u_398 u_3a0 b_390 b_4f2 hro0 (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine sepWPp_bind_p1_noPanic hwp rfl ?_
  intro s1 P_1 hsteps01 hpc1 hrun1 hq1
  rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
    hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
  have htr1 : s1.trace = s0.trace := stageP1Ok_trace_eq_placedBudget htr_evs
  have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true := hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
  have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
    ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
  refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
  simp only [sepExists_sepConj_left]
  refine sepWPp_sepExists_left fun v_a8 => sepWPp_sepExists_left fun v_b8 => sepWPp_sepExists_left fun v_d0 => ?_
  have hrecomb := p1Ok_recombine_entails_stageP2_placedBudget A lim stk' hneed hstk63 y (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
  dsimp only at hrecomb; refine sepWPp_conseq_pre hrecomb ?_
  exact hcont opt evs_p1 s1 coins v_a8 v_b8 v_d0 hevs_p1 hload_rel hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-- Kit-parametric counterpart of `D3PollRejectAuxPlacedBudget.decPk_d3_untyped_poll_reject_placedBudget`. -/
theorem decPk_d3_untyped_poll_reject_placedBudget_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2Env : DecPkGhost → Option (SessionRecord (List (BitVec 8))) → List AllocEvent → Prop}
    (MsgCond : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧ MsgCond F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (hP2_ne : ∀ g : DecPkGhost, MsgCond g.F g.peer.val g.me.val g.msg → ∃ opt0 evs2, P2Env g opt0 evs2)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (hp2 : ∀ (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim
        (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv P2Env) B S))
      (R : SepProp) (s0 : State) (opt : Option (SessionRecord (List (BitVec 8))))
      (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64),
      FilesOkPeer Scope y.g.F y.g.peer.val → DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F →
      MsgCond y.g.F y.g.peer.val y.g.me.val y.g.msg →
      S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none →
      y.g.coins.length < 2 ^ 63 →
      StageP1OkEnv (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv) StoresGhost.opened.sessions
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 y.st) (P2Env y.g opt) →
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok opt) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 → s1.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat →
      s1.pc = dpPollEntryPlaced + 0x868#64 → s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
        (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
           y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
         coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
        (fun sf P_f => (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget
            (dpSlotPollKStatePlaced A lim (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv P2Env) B S)
            stk')).post y s0 sf ∗ R)) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget
            (dpSlotPollKStatePlaced A lim (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv P2Env) B S)
            stk')).onPanic y s0 sf ∗ R))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget
        (dpSlotPollKStatePlaced A lim (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv P2Env) B S) stk')) := by
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ := dpPollPre_unpack_d3_placedBudget
    (MsgCond := fun F peer me pm => MsgCond F peer me pm ∧ ∀ coins, S.decryptPrekey F peer me pm coins = some none)
    (fun F peer me pm hf hd => let ⟨h1, h2, h3, h4⟩ := hok F peer me pm hf hd; ⟨h1, h2, h3, h4⟩) stk' y R s0 hpre
  obtain ⟨hmsgCond, hAns0⟩ := hpure.msgCond
  have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := hAns0 y.g.coins
  obtain ⟨b, htrusted⟩ := trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    exact closure_untrusted_d3_placedBudget_of_kits A lim hDropNz mmpl gh W B S Scope hh hsub
      stk' hneed hstk63 y (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      (fun evs hevs => hpure.fits evs (Or.inl hevs)) (fun _ h => Or.inl h) R s0 hpc hrun hsp
      hpure.rocl hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.storeOk hans htrusted hm_base
  | true =>
    obtain ⟨opt0, evs2_0, hp2_0⟩ := hP2_ne y.g hmsgCond
    have hfits_p1 : FitsEnv M lim y.st
        (StageP1OkEnv (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
          (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv) StoresGhost.opened.sessions
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
          StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey) :=
      fun evs1 hevs1 => ((fitsEvents_append M lim evs1 evs2_0 y.st).mp
        (hpure.fits (evs1 ++ evs2_0) (Or.inr ⟨opt0, Or.inr ⟨evs1, evs2_0, rfl, hevs1, hp2_0⟩⟩))).1
    refine closure_trusted_p1_d3_placedBudget_bind_of_kits A lim hDropNz mmpl gh W B S Scope hh hsub
      stk' hneed hstk63 y (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      hfits_p1 R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.rocl hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.storeOk htrusted hm_base ?_
    intro opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hevs_p1 hload_rel hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1
    have hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st) (P2Env y.g opt) :=
      fun evs2 hp2_evs => ((fitsEvents_append M lim evs_p1 evs2 y.st).mp
        (hpure.fits (evs_p1 ++ evs2) (Or.inr ⟨opt, Or.inr ⟨evs_p1, evs2, rfl, hevs_p1, hp2_evs⟩⟩))).2
    exact hp2 y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hpure.filesOkPeer hpure.storeOk hmsgCond hans hpure.coins_lt
      hevs_p1 hfits_p2 hload_rel hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1

/-! ## 3. `v3` Poll Reject via Store-Kit Contracts & `withFds A` Specialization -/

/-- Kit-parametric counterpart of `D3V3RejectPlacedBudget.decPk_v3_reject_poll_placedBudget`
reusing `stageP2_v3_reject_placedBudget` verbatim. -/
theorem decPk_v3_reject_poll_placedBudget_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondV3 Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget
        (dpSlotPollKStatePlaced A lim
          (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv (fun _ _ => StageP2V3RejectEnv)) B S)
        stk')) :=
  decPk_d3_untyped_poll_reject_placedBudget_of_kits A lim
    (P2Env := fun _ _ => StageP2V3RejectEnv) (MsgCondV3 Scope)
    hDropNz mmpl gh W B S Scope hh hKits hsub hok
    (fun _ _ => ⟨none, stageP2V3RejectEnv_nonempty⟩)
    stk' hneed hstk63
    (fun y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hfPeer _hstoreOk hv3Cond hans _hcoins
         hevs_p1 hfits_p2 hload_rel _hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1 =>
      stageP2_v3_reject_placedBudget A lim mmpl gh W B S Scope hh hinjK hsub stk' hneed hstk63
        y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hfPeer hv3Cond hans hfits_p2
        (fun evs2 hevs2 => Or.inr ⟨opt, Or.inr ⟨evs_p1, evs2, rfl, hevs_p1, hevs2⟩⟩)
        hload_rel htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1)

/-- `withFds A` specialization of `decPk_v3_reject_poll_placedBudget_of_kits` from
`CliDecPkPollKitsPlacedOkFds`. -/
theorem decPk_v3_reject_poll_placedBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (henf : lim.enforced = true)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondV3 Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget
        (dpSlotPollKStatePlaced (withFds A) lim
          (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv (fun _ _ => StageP2V3RejectEnv)) B S)
        stk')) :=
  decPk_v3_reject_poll_placedBudget_of_kits (withFds A) lim
    hDropNz mmpl gh W B S Scope hh (cliDecPkPollKitsFds_toWithFds henf hKits) hinjK hsub hok stk' hneed hstk63

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd
