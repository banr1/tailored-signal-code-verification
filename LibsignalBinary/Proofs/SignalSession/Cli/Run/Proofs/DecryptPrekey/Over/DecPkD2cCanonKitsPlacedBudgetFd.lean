/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib

/-!
# Poll-Kit Bundle and `slotWithPreFdsGe3Closed` Adapter for `decrypt_prekey`

Provides `CanonPollKitsPlacedOk` (the 6-kit `fds = false` CLI `decrypt_prekey` poll bundle over
`PublicApi.StoreKit.PlacedBudget`), Stage-P4 kit projections (`preKeyRemoveKitPlacedOk_of_fullStore`,
`kyberPreKeyMarkKitPlacedOk_of_fullStore`, `cliPollSess_seqFreeKitPlacedOkSE_of_kits`), and the
Block-`520` `withFds A` → `slotWithPreFdsGe3Closed` adapter
`slotOk_decPkFrozenPlaced_withFds_to_preFd`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxHeartbeats 400000

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (ApiError SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliKyberPreKeyVtSym cliPreKeyVtSym cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunNeeds RunSem SlotCtx decResAt slotOut slotTrace
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced
  cliPollSelfKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  KyberPreKeyMarkKitPlacedOk
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (
  PreKeyRemoveKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk
  PreKeyStoreKitPlacedOk SessionOnlyKitPlacedOkSE SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  SessKitHooksPlaced cliAddrText_placed_ok_of_sessHooks cliDirPut_placed_ok_of_sessHooks
  cliSessStorePoll_rocl_seqFree_placed_ok cliSessStoreShim_rocl_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv cliPollSpkFullBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessSeqFreeBudgetEnv
  cliSerializeCanonSeqFree_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (
  slotWithPreFdsGe3Closed subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed
  withPreFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  decPkSlotSpecBasePlaced decPkSlotSpecFrozenPlaced decPkSlotSpecPlaced decPkSlotSpecPlacedOf
  slotFramePlaced
)

/-! ## 1. 6-Kit `fds = false` CLI `decrypt_prekey` Poll Bundle -/

/-- Plain (`fds = false`) bundle of the 6 CLI store-kit `PlacedOk*` contracts consumed across
Stage P1, Stage P2, and Stage P4 of `decrypt_prekey` poll (`dpPollProgPlaced ext`). -/
structure CanonPollKitsPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : LibsignalHooks) : Prop where
  sessOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord ext
  idOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer B ReadEnv) ext
  selfOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentitySelfStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv) ext
  spkOk : ∀ (F0 : FsFiles) (sid : BitVec 32),
    SignedPreKeyStoreKitPlacedOk A lim
      (cliPollSpkKitPlaced A.repAlloc F0 sid (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 sid (cliKitStk B) ReadEnv) ext
  kpkOk : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) ext
  pkOk : ∀ (F0 : FsFiles) (pid : BitVec 32),
    PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) ext

/-! ## 2. Stage-P4 Store-Kit Projections (`0` `hRead` / `hDeser`) -/

private theorem futDropBudgetSpec_false_eq (fdsOk : FsState → Prop) :
    futDropBudgetSpec fdsOk false = futDropBudgetSpec :=
  rfl

/-- Projects `PreKeyStoreKitPlacedOk` at `cliPollPkFullBudgetEnv` to `PreKeyRemoveKitPlacedOk`
at `cliPollPkBudgetEnv` (`removePollEnv` agrees definitionally). -/
theorem preKeyRemoveKitPlacedOk_of_fullStore [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {pid : BitVec 32} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (h : PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) H) :
    PreKeyRemoveKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
      (cliPollPkBudgetEnv A.repAlloc F0 pid (cliKitStk B) ReadEnv) H where
  removeShim hblk := h.removeShim hblk
  removePoll hblk := h.removePoll hblk
  removeFutDrop hblk := futDropBudgetSpec_false_eq _ ▸ h.removeFutDrop hblk

/-- Projects `KyberPreKeyStoreKitPlacedOk` at `cliPollKpkFullBudgetEnv` to `KyberPreKeyMarkKitPlacedOk`
at `cliPollKpkBudgetEnv` (`markPollEnv` agrees definitionally). -/
theorem kyberPreKeyMarkKitPlacedOk_of_fullStore [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {kid sid : BitVec 32} {kbk : PublicKey} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    (h : KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) H) :
    KyberPreKeyMarkKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B))
      (cliPollKpkBudgetEnv A.repAlloc F0 kid sid kbk (cliKitStk B) ReadEnv) H where
  markShim hblk := h.markShim hblk
  markPoll hblk := h.markPoll hblk
  markFutDrop hblk := futDropBudgetSpec_false_eq _ ▸ h.markFutDrop hblk

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-- Upgrades `SessionOnlyKitPlacedOkSE` from `cliPollSessBudgetEnv` (`hKits.sessOk`) to SeqFree
`cliPollSessSeqFreeBudgetEnv` with no `hRead` / `hDeser` premises. -/
theorem cliPollSess_seqFreeKitPlacedOkSE_of_kits [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSess : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B) DeserEnv ReadEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hhS := SessKitHooksPlaced.of_runHooks (toSkeletonRunHooks hh)
  have hAddr := cliAddrText_placed_ok_of_sessHooks hhS
  have hPut := cliDirPut_placed_ok_of_sessHooks hhS
  have hSer := cliSerializeCanonSeqFree_placed_ok mmpl gh W hh
  exact
    { loadShim := fun hblk => hSess.loadShim hblk
      loadPoll := fun hblk => hSess.loadPoll hblk
      loadFutDrop := fun hblk => hSess.loadFutDrop hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hhS.alloc (Nat.le_refl _) hblk
      storePoll := fun hblk =>
        cliSessStorePoll_rocl_seqFree_placed_ok (serProg := lsProg_52 H)
          (serBlk := 52) hhS.alloc hAddr hSer hPut (Nat.le_refl _) hblk
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      storeFutDrop := fun hblk => hSess.storeFutDrop hblk }

/-! ## 3. Slot-`520` `withFds A` → `slotWithPreFdsGe3Closed` Adapter -/

private theorem slotFramePlaced_withFds_enforced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true) (st : M.σ) (ctx : SlotCtx) (s : State) :
    slotFramePlaced (withFds A) lim st ctx s =
      ⌜FdsGe3Closed s.fs⌝ ∗ slotFramePlaced A lim st ctx s := by
  unfold slotFramePlaced
  rw [withFds_pool_enforced A henf]
  dsimp only [withFds_repAlloc]
  sep_ac_rfl

private theorem decPkSlotSpecFrozenPlaced_withFds_to_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (h : subroutine_ok prog entry (decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk)) :
    subroutine_ok prog entry
      (withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)) := by
  refine subroutine_ok_mono h (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · dsimp only [withFdsGe3Closed, decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf,
      decPkSlotSpecBasePlaced, withFds_repAlloc] at hpre ⊢
    rw [slotFramePlaced_withFds_enforced A henf]
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [withFdsGe3Closed, decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf,
      decPkSlotSpecBasePlaced, decPkSlotSpecPlaced, withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨g', hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨e, hpost⟩
    rw [withFds_pool_enforced A henf] at hpost
    let Body : List AllocEvent → StoresGhost →
        Except (ApiError AddrVal Unit) (List (BitVec 8)) → SepProp :=
      fun evs' g'' e' =>
        ⌜DecPkEnv x evs' ∧ slotTrace s0 sf ∧
            slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g'' e' s0 sf⌝ ∗
          storesAt A.repAlloc x.stores g'' ∗ decResAt A.repAlloc x.ret e' ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((s0.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs' st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
    have hpost' : sf.mem ⊨ ⌜FdsGe3Closed sf.fs⌝ ∗ (Body evs g' e ∗ R) := by
      dsimp only [Body]
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hfds, hbody⟩
    have hex : sf.mem ⊨ (∃∗ evs', ∃∗ g'', ∃∗ e', Body evs' g'' e') ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ R) := by
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨g', ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨e, ?_⟩
      have hcomb : sf.mem ⊨ ⌜FdsGe3Closed sf.fs⌝ ∗ (Body evs g' e ∗ R) :=
        (satisfies_pure_sepConj _ _ _).mpr ⟨hfds, hbody⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hcomb
    dsimp only [Body] at hex
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hex

private theorem decPkSlotSpecFrozenPlaced_withFds_to_preFd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (h : subroutine_ok prog entry (decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk)) :
    subroutine_ok prog entry
      (withPreFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)) :=
  subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed
    (decPkSlotSpecFrozenPlaced_withFds_to_withFds henf h)

/-- Slot-level lift from `(slotsOfSigPkFrozenPlaced (withFds A) …).decryptPrekey.OkPlaced` to
`(slotWithPreFdsGe3Closed (slotsOfSigPkFrozenPlaced A …).decryptPrekey).OkPlaced`. -/
theorem slotOk_decPkFrozenPlaced_withFds_to_preFd [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {sEnvs : RunSlotEnvs} {S : RunSem} {needs : RunNeeds}
    (h : (slotsOfSigPkFrozenPlaced (withFds A) lim sEnvs S needs).decryptPrekey.OkPlaced
      prog entry) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced prog entry :=
  fun stk h1 h2 => decPkSlotSpecFrozenPlaced_withFds_to_preFd henf (h stk h1 h2)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
