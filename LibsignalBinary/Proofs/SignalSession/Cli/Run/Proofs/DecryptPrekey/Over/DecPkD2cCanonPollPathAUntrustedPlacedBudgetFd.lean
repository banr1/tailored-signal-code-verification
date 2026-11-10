/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Kit-Parametric D2(c) Untrusted-Identity Poll Branch

Proves `closure_untrusted_d2c_frozen_placed_ok_of_kits`, discharging the `trusted = .ok false`
branch of Block `518` under `DecPkOkD2c` directly from `CanonPollKitsPlacedOk` (`hKits.sessOk`,
`hKits.idOk`).
-/

@[expose] public section

open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (loadCallStack stageP1UntrustedCallStack)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyInnerInitAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack noAllocShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (dirAt)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOutTr)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c decPkDefD2c decPkDefD2c_eq_decPkDef_of_untrusted dpFutDoneAt dpFutStartAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit apiDecResultAt_untrusted_entails_decResAt cliIdStoreSpecFull cliIdStoreSpecFullPlaced cliId_trustRel_eq_of_trusted cliKitStk cliKpkStoreSpecFullPlaced cliPollIdKit cliPollIdKitPlaced cliPollId_vtablesPlacedOk cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk closStackUnusedUntrustedAt clos_stack_3280_of_p1_untrusted clos_stack_3280_split_for_p1_untrusted closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At coro_of_p1_untrusted_entails_dpFutDoneAt decPkDef_of_trust_err dpClosSubStack dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel pmKyberId pmPreKeyId preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt slotOutTr_of_err sp_frame_sub_add stackAt_poll_entry_split stackAt_subStack_split stageP1UntrustedCallStack_le_subStack)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalPlacement lsmpl)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAUntrustedPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

open Arm64 Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv StageP1UntrustedMangledPlacedStmt
   stageP1_untrusted_mangled_placed_ok
   cliPollSessBudgetEnv cliPollIdBudgetEnv
   cliPollStageP1_fsAt_placed dpPollPost_of_decResAt_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
  (CanonPollKitsPlacedOk)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

private theorem extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤
      loadCallStack (cliPollSessKitPlaced A F0 CryptoVerification.SignalSession.Cli.Slots.scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
    CryptoVerification.RustHeap.allocHookStack]
  omega

set_option maxHeartbeats 800000 in
/-- Statement-parameterized kit-threaded untrusted-identity branch (`trusted = .ok false`) of
`subroutine_ok_of_sepWPp_steps` for Block `518` under `[LibsignalPlacement]` and `DecPkOkD2c`
(`0` `lsReadFileSym` hypotheses). -/
theorem closure_untrusted_d2c_of_kits_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedMangledPlacedStmt)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CanonPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
    y.g.stores hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
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
    memRegion y.out 48 ∗
    lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (encRecord := CryptoVerification.E2E.Record.encodeRecord)
    (kit := kit) (kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions) (ist := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity)
    (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show LibsignalBinary.Heap.SpecBudget.withVmPreserved noAllocShimSpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec from rfl) ▸
      hh.codecHooks.shim)
    hh.codecHooks.alloc
    ((show LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec from rfl) ▸
      hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (hKits.sessOk y.g.F y.g.peer)
    (hKits.idOk y.g.F y.g.peer)
    hp1_64
    (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer)
    rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer σ).loadRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0
    (cliPollStageP1_fsAt_placed hh y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, evs, hevs_p1, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : CryptoVerification.SignalSession.Cli.Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS, decPkDefD2c_eq_decPkDef_of_untrusted X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins (by rw [htrusted]; decide)]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err CryptoVerification.SignalSession.Cli.StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗
            cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗
            cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗
            cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
            coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
              ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, cliPollStoresKitsAtPlaced]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
      CryptoVerification.SignalSession.Cli.StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro _ _ hfalse _ _
    exact False.elim hfalse

/-- `LibsignalFrozen` kit-threaded untrusted-identity branch (`trusted = .ok false`) for Block `518`
under `[LibsignalPlacement]` and `DecPkOkD2c` (with no `lsReadFileSym` hypotheses). -/
theorem closure_untrusted_d2c_frozen_placed_ok_of_kits [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CanonPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn CryptoVerification.SignalSession.Cli.Slots.scopeKit)
    (hsub : ∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hfr0 : CryptoVerification.LibsignalFrozen lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
              (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
              (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  have hro0 : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr0.2, hfr0.1⟩
  exact closure_untrusted_d2c_of_kits_placed_ok stageP1_untrusted_mangled_placed_ok
    A lim hDropNz mmpl gh W X B S Scope hh hKits hinjK hsub hS stk' hneed hstk63 y
    hfits_p1 hevs_sub R s0 hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAUntrustedPlacedBudgetFd
