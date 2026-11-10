/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# `withFds` and `withFdsGe3Closed` Block-`520` Untyped/Bad-KEM Rejection Slot

Composes `v3` and `v4` bad-KEM poll rejection from `CliDecPkPollKitsPlacedOkFds` via `withFds A`
and unwraps the resulting contract under `lim.enforced = true` to prove
`withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)` on block `520`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
   libsignalFrozen_of_keepsFrozen libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsFrozen subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
   withLsFrozen)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunNeeds)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed decPkDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollSessKitPlaced dpPollEntryPlaced dpPollProgPlaced
   subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ scopeIn scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (MsgCondBadKem)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnv DecPkD3UntypedEnvOf DecPkD3UntypedPollEnv PqxdhAcceptBadKemErrEnv
   StageP2BadKemRejectEnv StageP2V3RejectEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
  (CliDecPkPollKitsPlacedOk CliDecPkPollKitsPlacedOkFds cliDecPkPollKitsFds_toWithFds)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd
  (closure_trusted_p1_d3_placedBudget_bind_of_kits closure_untrusted_d3_placedBudget_of_kits
   decPk_v3_reject_poll_placedBudget_of_kits)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudgetFd
  (stageP2_badKem_reject_full_placedBudget_of_kits)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget
  (cliDecryptPrekey_pkToENone_reject_slot_placedBudget cliDpPoll_pkToENone_reject_ok_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget
  (DecPkOkD3Untyped DecPkStoreOk decPkDef_eq_some_none_of_d3b3 dpPollPre_unpack_d3_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget (MsgCondV3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decPkSlotSpecFrozenPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (cliFiles_eq_of_trace_eq_placed cliPollIdBudgetEnv cliPollSessBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

/-! ## 1. Hook Bundle Adapters & Poll-Env Monotonicity Helpers -/

private theorem toClosureRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem toSkeletonRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem stageP2BadKemRejectEnv_nonempty [LibsignalPlacement]
    {A : CryptoVerification.RustHeap.RustAlloc} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {AcceptErrEnv : List AllocEvent → Prop} (g : DecPkGhost) :
    ∃ opt0 evs2, StageP2BadKemRejectEnv (A := A) B ReadEnv AcceptErrEnv g opt0 evs2 :=
  ⟨none, _, Or.inl (Or.inl rfl)⟩

private theorem pure_sepConj_mono {φ ψ : Prop} (h : φ → ψ) (P : SepProp) :
    ⌜φ⌝ ∗ P ⊢ ⌜ψ⌝ ∗ P :=
  Entails.pure_left fun hφ => by
    have hEq : ψ = True := propext ⟨fun _ => trivial, fun _ => h hφ⟩
    rw [hEq, pure_true, sepConj_comm, sepConj_emp]
    exact Entails.refl P

private theorem pollEnv_v3_sub [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {AcceptErrEnv : List AllocEvent → Prop}
    {TargetEnv : DecPkGhost → List AllocEvent → Prop}
    (hsEnv : ∀ g evs,
      DecPkD3UntypedEnvOf (A := A.repAlloc) B ReadEnv DeserEnv AcceptErrEnv g evs →
      TargetEnv g evs) :
    ∀ g evs,
      DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv
        (fun _ _ => StageP2V3RejectEnv) g evs →
      TargetEnv g evs := by
  intro g evs h
  apply hsEnv g evs
  rcases h with h1 | ⟨opt, hseq⟩
  · exact Or.inl h1
  · refine Or.inr ⟨opt, ?_⟩
    rcases hseq with hp1 | ⟨e₁, e₂, rfl, hp1, hp2⟩
    · exact Or.inl hp1
    · exact Or.inr ⟨e₁, e₂, rfl, hp1, Or.inl hp2⟩

private theorem pollEnv_badKem_sub [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {AcceptErrEnv : List AllocEvent → Prop}
    {TargetEnv : DecPkGhost → List AllocEvent → Prop}
    (hsEnv : ∀ g evs,
      DecPkD3UntypedEnvOf (A := A.repAlloc) B ReadEnv DeserEnv AcceptErrEnv g evs →
      TargetEnv g evs) :
    ∀ g evs,
      DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv
        (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv AcceptErrEnv) g evs →
      TargetEnv g evs := by
  intro g evs h
  apply hsEnv g evs
  rcases h with h1 | ⟨opt, hseq⟩
  · exact Or.inl h1
  · refine Or.inr ⟨opt, ?_⟩
    rcases hseq with hp1 | ⟨e₁, e₂, rfl, hp1, hp2⟩
    · exact Or.inl hp1
    · exact Or.inr ⟨e₁, e₂, rfl, hp1, Or.inr hp2⟩

private theorem dpPollSpecStateBudget_mono_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : DecPkGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {B : RunBudgets} {S : RunSem} {stk' : Nat}
    (hsub : ∀ g evs, Env₁ g evs → Env₂ g evs)
    (h : subroutine_ok prog entry
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim Env₁ B S) stk'))) :
    subroutine_ok prog entry
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim Env₂ B S) stk')) := by
  refine subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _ => ?_
  let y₁ :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.DpPollGhostStateBudget
      (dpSlotPollKStatePlaced A lim Env₁ B S) :=
    { out := y.out, fut := y.fut, cx := y.cx, g := y.g, st := y.st }
  have hpre_ent :
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim Env₂ B S) stk')).pre y s0 ⊢
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim Env₁ B S) stk')).pre y₁ s0 := by
    dsimp only [withLsFrozen, dpPollSpecStateBudget, dpSlotPollKStatePlaced, y₁]
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left ?_)))))
    exact pure_sepConj_mono
      (fun ⟨hF, hfOk, hdOk, hfit⟩ => ⟨hF, hfOk, hdOk, fun evs he => hfit evs (hsub y.g evs he)⟩) _
  refine h.mono_outcome y₁ R s0 hpc hrun
    (Satisfies.mono (sepConj_mono_left hpre_ent) hpre) hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    dsimp only [withLsFrozen, dpPollSpecStateBudget, dpSlotPollKStatePlaced, y₁]
    refine sepConj_mono_left ?_
    refine Entails.sepExists_elim fun ws => Entails.sepExists_right ws ?_
    refine sepConj_mono_right (sepConj_mono_right ?_)
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    refine Entails.sepExists_elim fun g' => Entails.sepExists_right g' ?_
    refine Entails.sepExists_elim fun e => Entails.sepExists_right e ?_
    exact pure_sepConj_mono (fun ⟨hevs, htr, hout'⟩ => ⟨hsub y.g evs hevs, htr, hout'⟩) _
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-! ## 2. Closed `[LibsignalFullPlacement]` `MsgCondBadKem` Poll via Store-Kit Contracts -/

/-- Kit-parametric counterpart of `D3BadKemRejectAuxPlacedBudget.decPk_badKem_reject_poll_full_placedBudget`:
closed `[LibsignalFullPlacement]` `dpPollProgPlaced` `subroutine_ok` for `MsgCondBadKem`. -/
theorem decPk_badKem_reject_poll_full_placedBudget_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondBadKem Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget
          (dpSlotPollKStatePlaced A lim
            (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv
              (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv))
            B S)
          stk')) := by
  let P2Env := StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv
  let DecPkEnv := DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv P2Env
  let hhSkel := toSkeletonRunHooksPlaced hh
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hfroz0, hp0⟩ := extract_withLsFrozen hpre
  have hpre_cro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨LibsignalCodeRoLoaded.of_libsignalFrozen hfroz0, hp0⟩
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d3_placedBudget (W := W) (Scope := Scope)
      (MsgCond := fun F peer me pm =>
        MsgCondBadKem Scope F peer me pm ∧ ∀ coins, S.decryptPrekey F peer me pm coins = some none)
      (fun F peer me pm hf hd =>
        let ⟨h1, h2, h3, h4⟩ := hok F peer me pm hf hd
        ⟨h1, ⟨h2.keyPairLt, h2.preKeysWf, h2.baseKeysLt⟩, h3, h4⟩)
      stk' y R s0 hpre_cro
  obtain ⟨hbadCond, hAns0⟩ := hpure.msgCond
  have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none :=
    hAns0 y.g.coins
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    exact closure_untrusted_d3_placedBudget_of_kits
      A lim hDropNz mmpl gh W B S Scope hhSkel hsub
      stk' hneed hstk63 y
      (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      (fun evs hevs => hpure.fits evs (Or.inl hevs))
      (fun _ h => Or.inl h)
      R s0 hpc hrun hsp
      hpure.rocl hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.storeOk
      hans htrusted hm_base
  | true =>
    obtain ⟨opt0, evs2_0, hp2_0⟩ :=
      stageP2BadKemRejectEnv_nonempty (A := A.repAlloc) (B := B) (ReadEnv := ReadEnv)
        (AcceptErrEnv := PqxdhAcceptBadKemErrEnv) y.g
    have hfits_p1 : FitsEnv M lim y.st
        (StageP1OkEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
          (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.peer.val y.g.msg.identityKey) :=
      fun evs1 hevs1 =>
        ((fitsEvents_append M lim evs1 evs2_0 y.st).mp
          (hpure.fits (evs1 ++ evs2_0) (Or.inr ⟨opt0, Or.inr ⟨evs1, evs2_0, rfl, hevs1, hp2_0⟩⟩))).1
    refine closure_trusted_p1_d3_placedBudget_bind_of_kits
      A lim hDropNz mmpl gh W B S Scope hhSkel hsub
      stk' hneed hstk63 y
      (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      hfits_p1 R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.rocl hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.storeOk
      htrusted hm_base ?_
    intro opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hevs_p1 hload_rel hsteps01 htr1 _hro1 hs1_sp
      hsp_sub hpc1 hrun1 halign1 hregs1
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hfroz0 hsteps01.keepsFrozen
    have hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st) (P2Env y.g opt) :=
      fun evs2 hp2_evs =>
        ((fitsEvents_append M lim evs_p1 evs2 y.st).mp
          (hpure.fits (evs_p1 ++ evs2) (Or.inr ⟨opt, Or.inr ⟨evs_p1, evs2, rfl, hevs_p1, hp2_evs⟩⟩))).2
    have hevs_sub : ∀ evs_p2, P2Env y.g opt evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
      fun evs_p2 hp2_evs => Or.inr ⟨opt, Or.inr ⟨evs_p1, evs_p2, rfl, hevs_p1, hp2_evs⟩⟩
    have hs1_files : s1.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hhSkel hsteps01 htr1).trans hpure.files_eq
    exact stageP2_badKem_reject_full_placedBudget_of_kits
      A lim mmpl gh W B S Scope hDropNz hG hh hKits hinjK hsub stk' hneed hstk63
      y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0
      hpure.filesOkPeer ⟨hpure.storeOk.keyPairLt, hpure.storeOk.preKeysWf, hpure.storeOk.baseKeysLt⟩
      hbadCond hans hpure.coins_lt
      hfits_p2 hevs_sub hload_rel htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1 hs1_files

/-- `withFds A` specialization of `decPk_badKem_reject_poll_full_placedBudget_of_kits` from
`CliDecPkPollKitsPlacedOkFds`. -/
theorem decPk_badKem_reject_poll_full_placedBudget_withFds [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (henf : lim.enforced = true)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M (withFds A) lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOkFds A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondBadKem Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget
          (dpSlotPollKStatePlaced (withFds A) lim
            (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv
              (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv))
            B S)
          stk')) :=
  decPk_badKem_reject_poll_full_placedBudget_of_kits (withFds A) lim
    hDropNz mmpl gh W B S Scope hG hh (cliDecPkPollKitsFds_toWithFds henf hKits) hinjK hsub hok stk' hneed hstk63

/-! ## 3. Unwrapping `decPkSlotSpecFrozenPlaced (withFds A)` into `withFdsGe3Closed` -/

/-- Under `lim.enforced = true`, `decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk`
entails `withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)` on `subroutine_ok`. -/
theorem subroutine_ok_decPkSlotSpecFrozenPlaced_withFdsGe3Closed_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk)) :
    subroutine_ok prog entry
      (withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  have hpre_ent :
      (withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)).pre (x, st) s0 ⊢
      (decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk).pre (x, st) s0 := by
    dsimp only [withFdsGe3Closed, decPkSlotSpecFrozenPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
      withFds_repAlloc]
    rw [withFds_pool_enforced A henf st s0]
    exact Entails.of_eq (by sep_ac_rfl)
  refine hok.mono_outcome (x, st) R s0 hpc hrun
    (Satisfies.mono (sepConj_mono_left hpre_ent) hpre) hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed, decPkSlotSpecFrozenPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
      withLsCodeRoLoaded, withFds_repAlloc] at hpost ⊢
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, g', e, hpost⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    exact ⟨evs, g', e, Satisfies.of_eq hpost (by sep_ac_rfl)⟩
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-! ## 4. Block-`520` Slot Composition via Store-Kit Contracts & `withFdsGe3Closed` -/

/-- Kit-parametric block-`520` untyped/bad-KEM rejection slot theorem. -/
theorem decPkD3Untyped_slotOk_of_kits_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim cliRunBudgets ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets ReadEnv DeserEnv
        PqxdhAcceptBadKemErrEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3Untyped ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : cliDecryptPrekeyNeed cliRunBudgets ≤ needs.decryptPrekey) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  intro stk hstk1 hstk2
  refine cliDecryptPrekey_pkToENone_reject_slot_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim mmpl gh W (by decide) cliRunBudgets S ?_ stk (Nat.le_trans hneed hstk1) hstk2
  intro stk' hdp1 hdp2
  exact cliDpPoll_pkToENone_reject_ok_placedBudget A lim mmpl gh W cliRunBudgets S scopeIn
    (fun F peer me pm hf hd => by
      have hd' := hdecPkOk F peer me pm hd
      exact ⟨(hfiles ▸ hf).1, hd'.1, hd'.2, fun coins =>
        hdecPk ▸ decPkDef_eq_some_none_of_d3b3
          X ⟨W.C, W.Q⟩ scopeIn F peer me pm coins hd'.2.2.1 hd'.2.2.2.2⟩)
    stk'
    (fun S' hok3 =>
      dpPollSpecStateBudget_mono_env (pollEnv_v3_sub hsEnv)
        (subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
          (decPk_v3_reject_poll_placedBudget_of_kits A lim h547 mmpl gh W cliRunBudgets S' scopeIn
            (toSkeletonRunHooksPlaced hh) hKits encodeInjOn_deserializeScopeP_Q
            (fun _ hr => hr)
            (fun F peer me pm hf hd =>
              let ⟨hfp, hs, hm, hc⟩ := hok3 F peer me pm hf hd
              ⟨hfp, ⟨hs.keyPairLt, hs.preKeysWf, hs.baseKeysLt⟩, ⟨hm.1, hm.2⟩, hc⟩)
            stk' hdp1 hdp2)))
    (fun S' hok4 =>
      dpPollSpecStateBudget_mono_env (pollEnv_badKem_sub hsEnv)
        (decPk_badKem_reject_poll_full_placedBudget_of_kits A lim h547 mmpl gh W cliRunBudgets S' scopeIn
          hG hh hKits encodeInjOn_deserializeScopeP_Q
          (fun _ hr => hr)
          (fun F peer me pm hf hd =>
            let ⟨hfp, hs, hm, hc⟩ := hok4 F peer me pm hf hd
            ⟨hfp, ⟨hs.keyPairLt, hs.preKeysWf, hs.baseKeysLt⟩, hm, hc⟩)
          stk' hdp1 hdp2))

/-- `withFdsGe3Closed` block-`520` untyped/bad-KEM rejection slot theorem from
`CliDecPkPollKitsPlacedOkFds`, instantiating `decPkD3Untyped_slotOk_of_kits_placedBudget` at
`withFds A`. -/
theorem decPkD3Untyped_slotOk_withFdsGe3Closed_of_pollKits [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M (withFds A) lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOkFds A lim cliRunBudgets ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets ReadEnv DeserEnv
        PqxdhAcceptBadKemErrEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3Untyped ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : cliDecryptPrekeyNeed cliRunBudgets ≤ needs.decryptPrekey) :
    ∀ stk, needs.decryptPrekey ≤ stk → stk ≤ 2 ^ 63 →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)
        (withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim sEnvs.decryptPrekey S stk)) := by
  intro stk hstk1 hstk2
  exact subroutine_ok_decPkSlotSpecFrozenPlaced_withFdsGe3Closed_of_withFds henf
    (decPkD3Untyped_slotOk_of_kits_placedBudget (A := withFds A) (lim := lim)
      X mmpl gh W h547 hG (toClosureRunHooksPlaced hh) (cliDecPkPollKitsFds_toWithFds henf hKits)
      S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed stk hstk1 hstk2)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudgetFd
