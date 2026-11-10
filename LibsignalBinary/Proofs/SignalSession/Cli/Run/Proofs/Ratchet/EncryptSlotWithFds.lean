/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreKitWithFds
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded Store-Kit and Outer Slot Bridges for `encrypt` (Placed)

Converts `encSlotSpecPlaced (withFds A)` to two-sided `withFdsGe3Closed (encSlotSpecPlaced A)` when
`lim.enforced = true`, and assembles `SessionOnlyKitPlacedOkSE (withFds A)` and
`IdentityStoreKitPlacedOkI (withFds A)` from a `withFdsGe3Closed` `Dir::get` (Block `589`)
contract.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsBlackBoxU8Sym lsmpl withLsCodeLoaded)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityVtRoSym cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit (saveShimNeed trustShimNeed)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (loadShimNeed storeShimNeed)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunCompose (EncGhost RunSem SlotCtx)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
  (serializeCanonSeqFreeSpecX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
  (cliIdKitOkIE_fds_placed_direct_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliDirPutStr_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
  (cliSessKitOkSE_fds_seqFree_placed_of_polls)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliAddrText_placed_ok cliDirPut_placed_ok sessStorePoll_seqFree_placed_ok_of_depsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (encSlotSpecPlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (dirGetSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
  (idSavePoll_placed_ok_of_get_put_bb_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
  (idTrustPoll_placed_ok_of_get_bb_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd
  (sessLoadPoll_placed_ok_of_deps_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
  (subroutine_ok_addrText_withFdsGe3Closed_of_withFds
   subroutine_ok_dirPutStr_withFdsGe3Closed_of_withFds
   subroutine_ok_sessDeserialize_withFdsGe3Closed_of_withFds
   subroutine_ok_sessStorePoll_withFdsGe3Closed_of_withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreKitWithFds
  (identityStoreKitPlacedOkI_withFds_of_fds sessionOnlyKitPlacedOkSE_withFds_of_fds)

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α}
    (h : subroutine_ok P entry spec1)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec1.post x s0 sf ∗ R) → (sf.mem ⊨ spec2.post x s0 sf ∗ R))
    (hpanic : ∀ x R s0 sf,
      (sf.mem ⊨ spec1.onPanic x s0 sf ∗ R) → (sf.mem ⊨ spec2.onPanic x s0 sf ∗ R))
    (hoom : ∀ x R s0 sf,
      (sf.mem ⊨ spec1.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec2.onOom x s0 sf ∗ R))
    (hexc : spec1.onExit = spec2.onExit := by rfl) :
    subroutine_ok P entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre2 hsp => ?_
  refine h.mono_outcome x R s0 hpc hrun (hpre x R s0 hpre2) hsp ?_
  intro sf hout
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hst, hp⟩ | ⟨c, hst, hp⟩ | ⟨hst, hp⟩
  · exact .inl ⟨hret, hcc, hpost x R s0 sf hp⟩
  · exact .inr (.inl ⟨hst, hpanic x R s0 sf hp⟩)
  · exact .inr (.inr (.inl ⟨c, hst, hexc ▸ hp⟩))
  · exact .inr (.inr (.inr ⟨hst, hoom x R s0 sf hp⟩))

/-! ## Outer `encSlotSpecPlaced` conversion under `withFds` -/

theorem slotFramePlaced_withFds_enforced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (st : M.σ) (x : SlotCtx) (s : State) :
    slotFramePlaced (withFds A) lim st x s =
      (slotFramePlaced A lim st x s ∗ ⌜FdsGe3Closed s.fs⌝) := by
  dsimp only [slotFramePlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
    withFds_repAlloc]
  rw [withFds_pool_enforced A henf st s]
  sep_ac_rfl

/-- Converts `subroutine_ok` for `encSlotSpecPlaced (withFds A)` to two-sided `withFdsGe3Closed (encSlotSpecPlaced A)` when `lim.enforced = true`. -/
theorem subroutine_ok_encSlot_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {EncEnv : EncGhost → List AllocEvent → Prop} {S : RunSem}
    {stk : Nat} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (encSlotSpecPlaced (withFds A) lim EncEnv S stk)) :
    subroutine_ok P entry
      (withFdsGe3Closed (encSlotSpecPlaced A lim EncEnv S stk)) := by
  refine subroutine_ok_of_pre_post h ?_ ?_ (fun _ _ _ _ hp => hp) (fun _ _ _ _ ho => ho)
  · intro ⟨x, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, encSlotSpecPlaced, withLsCodeRoLoaded] at hpre ⊢
    rw [slotFramePlaced_withFds_enforced A henf st x.toSlotCtx s0]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, encSlotSpecPlaced, withLsCodeRoLoaded, withFds_repAlloc] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, g', e, hpost⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    have hpull : sf.mem ⊨
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜EncEnv x evs ∧
              CryptoVerification.SignalSession.Cli.RunCompose.slotTrace s0 sf ∧
              CryptoVerification.SignalSession.Cli.RunCompose.slotOut
                (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
              (∀ m, e = .ok (.preKeySignalMessage m) → m.serialized.length < 2 ^ 42)⌝ ∗
            CryptoVerification.SignalSession.Cli.MainHops.storesAt A.repAlloc x.stores g' ∗
            CryptoVerification.SignalSession.Cli.RunCompose.encResAt A.repAlloc x.ret e ∗
            CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.peer x.peerA ∗
            CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.me x.meA ∗
            (x.ptA ↦ₛ x.ptext) ∗
            CryptoVerification.SignalSession.Cli.RunCompose.nowCellAt s0.sp
              CryptoVerification.SignalSession.Cli.RunCompose.unixEpoch ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp stk ∗ anyHeap) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpull
    rcases hpull with ⟨hfds, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, g', e, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩

/-! ## Store-kit `withFds` assembly -/

/-- Assembles `SessionOnlyKitPlacedOkSE (withFds A)` at `w1SessKitPlaced` and
`w1BinarySessKitPlacedBudgetFixed` from a `withFdsGe3Closed` `Dir::get` (Block `589`) contract. -/
theorem w1BinarySessKitPlaced_withFds_okSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hhWf : RunHooksPlaced (withFds A) lim H)
    (hGet589 : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed
        (dirGetSpecPlaced cliIo.rd cliWrOk A lim
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (RunBudgets.dirGetNeed ⟨B.readFile⟩))))
    (hDeserWf : subroutine_ok (lsProg_569 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit (withFds A) lim
        (ofBytesEnv RecordDeserializeCancelEnv)))
    (hSerSeqFreeWf : subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M (withFds A) lim))) :
    SessionOnlyKitPlacedOkSE (withFds A) lim
      (w1SessKitPlaced (withFds A).repAlloc B F0 peer)
      (w1BinarySessKitPlacedBudgetFixed (withFds A).repAlloc B F0 peer)
      scopeKit encodeRecord H := by
  have hAddrWf := cliAddrText_placed_ok hhWf
  have hAddrFd := subroutine_ok_addrText_withFdsGe3Closed_of_withFds henf hAddrWf
  have hDeserFd := subroutine_ok_sessDeserialize_withFdsGe3Closed_of_withFds henf hDeserWf
  have h569Fd := sessLoadPoll_placed_ok_of_deps_fd hh.allocFs hAddrFd hGet589 hDeserFd
    (hh.fs (lsProg_569 H) 569) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hPutWf := cliDirPut_placed_ok hhWf
  have h570Wf := sessStorePoll_seqFree_placed_ok_of_depsX hhWf.alloc hAddrWf hSerSeqFreeWf hPutWf
    (Nat.le_refl _) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h570Fd := subroutine_ok_sessStorePoll_withFdsGe3Closed_of_withFds henf h570Wf
  have hFds := cliSessKitOkSE_fds_seqFree_placed_of_polls
    (F0 := F0) (peer := peer)
    (AddrValEnv := AddrTextValEnv DecimalEnv)
    (vtSym := cliSessionVtRoSym) (idVtSym := cliIdentityVtRoSym)
    hDropNz hh.allocFs h569Fd h570Fd
    (Nat.le_refl loadShimNeed) (Nat.le_refl storeShimNeed)
  exact sessionOnlyKitPlacedOkSE_withFds_of_fds henf hFds

/-- Assembles `IdentityStoreKitPlacedOkI (withFds A)` at `w1IdKitPlaced` and
`w1BinaryIdKitPlacedBudgetFixed` from a `withFdsGe3Closed` `Dir::get` (Block `589`) contract. -/
theorem w1BinaryIdKitPlaced_withFds_okIE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hhWf : RunHooksPlaced (withFds A) lim H)
    (hGet589 : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed
        (dirGetSpecPlaced cliIo.rd cliWrOk A lim
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (RunBudgets.dirGetNeed ⟨B.readFile⟩))))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    IdentityStoreKitPlacedOkI (withFds A) lim
      (w1IdKitPlaced (withFds A).repAlloc B F0 peer)
      (w1BinaryIdKitPlacedBudgetFixed (withFds A).repAlloc B F0 peer) H := by
  have hPut543Wf := cliDirPutStr_placed_ok hhWf
  have hPut543Fd := subroutine_ok_dirPutStr_withFdsGe3Closed_of_withFds henf hPut543Wf
  have h566Fd := idTrustPoll_placed_ok_of_get_bb_fd hh.allocFs hGet589 h_bb
    (Nat.le_refl _) (by decide) (by decide)
  have h565Fd := idSavePoll_placed_ok_of_get_put_bb_fd hh.allocFs hGet589 hPut543Fd h_bb
    (Nat.le_refl _) (by decide) (by decide) (by decide) (by decide)
  have hIdFds := cliIdKitOkIE_fds_placed_direct_of_polls
    (F0 := F0) (peer := peer) (vtSym := cliIdentityVtRoSym)
    hDropNz hh.allocFs h566Fd h565Fd
    (Nat.le_refl trustShimNeed) (Nat.le_refl saveShimNeed)
  exact identityStoreKitPlacedOkI_withFds_of_fds henf hIdFds

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds
