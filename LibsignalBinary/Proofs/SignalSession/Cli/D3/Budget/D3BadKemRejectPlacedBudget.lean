/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Untyped/Bad-KEM (`pkToE? pm = none`) Block-`520` `decrypt_prekey` Rejection

Combines the `v3` and `v4` bad-KEM poll contracts into a unified `dpPollProgPlaced` rejection
theorem (`cliDpPoll_pkToENone_reject_ok_placedBudget`), lifts it to block `520`
(`cliDecryptPrekey_pkToENone_reject_slot_placedBudget`, `decPkD3Untyped_hdecPk_of_seams`), and
re-exports the `DecPkD3UntypedEnv` credit bounds and `SingleSlotFineSpec` witnesses.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsFrozen subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
   withLsFrozen)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds RunSem dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed decPkDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollEntryPlaced dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ scopeIn scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (MsgCondBadKem)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnv DecPkD3UntypedEnvOf DecPkD3UntypedPollEnv DecPkD3UntypedRejectEnv
   DecPkKeyFilesBounded PqxdhAcceptBadKemErrEnv StageP2BadKemRejectEnv StageP2UntypedRejectEnv
   StageP2V3RejectEnv decPkKeyFilesBounded_of_cliPqInputs decPkKeyFilesBounded_of_pqOrD3Recv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
  (decPkD3UntypedCum decPkD3UntypedEnv_fine_groupSpec decPkD3UntypedEnv_nonvacuous_alloc
   decPkD3UntypedEnv_of_inputs_singleSlotFineSpec decPkD3UntypedEnv_phaseCreditSpec
   decPkD3UntypedEnv_r3b_singleSlotFineSpec decPkD3UntypedEnv_singleSlotFineSpec
   decPkD3UntypedGrpS decPkD3UntypedLive decPkD3UntypedMaxReq decPkD3UntypedPeak
   decPkD3Untyped_caps_le decPkD3Untyped_caps_le_1MiB nonvacuous_alloc)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudget
  (decPk_badKem_reject_poll_full_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget
  (DecPkOkD3Untyped DecPkStoreOk MsgCondPkToENone)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget
  (MsgCondV3 decPk_v3_reject_poll_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decPkSlotSpecFrozenPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv readFileSpecPlaced sessDeserializeSpecPlaced)

/-! ## 1. `LibsignalFullPlacement` Constructor Aligned with `libsignalPlacementOf` -/

/-- Builds a `[LibsignalFullPlacement]` instance whose underlying `toLibsignalPlacement` is
definitionally `libsignalPlacementOf mpl hblk hext_nodup`. -/
@[instance_reducible]
def libsignalFullPlacementOf (mpl : Obj.MultiPlacement)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hpl : libsignalSessionLib.Placeable mpl) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hpl

private theorem toClosureRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-! ## 2. Poll Dispatch and Block-`520` Caller-Slot Reduction -/

/-- Unified `pkToE? pm = none` poll rejection theorem under `[LibsignalPlacement]`, dispatching
message version `3` to `hv3_poll` and `4` to `hv4_poll`. -/
theorem cliDpPoll_pkToENone_reject_ok_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondPkToENone Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat)
    (hv3_poll : ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
        MsgCondV3 Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        dpPollEntryPlaced
        (withLsFrozen lsmpl
          (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S') stk')))
    (hv4_poll : ∀ S' : RunSem,
      (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
        FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
        MsgCondBadKem Scope F peer me pm ∧
        (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        dpPollEntryPlaced
        (withLsFrozen lsmpl
          (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S') stk'))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')) := by
  refine subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _hL => ?_
  have hpre_cro : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    obtain ⟨hfr, hp0⟩ := extract_withLsFrozen hpre
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨LibsignalCodeRoLoaded.of_libsignalFrozen hfr, hp0⟩
  obtain ⟨hpure, _⟩ := D3PollRejectAuxPlacedBudget.dpPollPre_unpack_d3_placedBudget (W := W)
    (MsgCond := fun F peer me pm => MsgCondPkToENone Scope F peer me pm ∧
      ∀ coins, S.decryptPrekey F peer me pm coins = some none)
    (fun F peer me pm hf hd =>
      let ⟨h1, h2, h3, h4⟩ := hok F peer me pm hf hd
      ⟨h1, ⟨h2.keyPairLt, h2.preKeysWf, h2.baseKeysLt⟩, h3, h4⟩)
    stk' y R s0 hpre_cro
  obtain ⟨⟨⟨body, hparse⟩, hpkNone, hAcct, hnoMatch⟩, hAns0⟩ := hpure.msgCond
  let g0 : DecPkGhost := y.g
  let S' : RunSem :=
    { S with decPkOk := fun F peer me pm =>
        S.decPkOk F peer me pm ∧ F = g0.F ∧ peer = g0.peer.val ∧ me = g0.me.val ∧ pm = g0.msg }
  let y' :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.DpPollGhostStateBudget
        (dpSlotPollKStatePlaced A lim DecPkEnv B S') :=
    ⟨y.out, y.fut, y.cx, g0, y.st⟩
  have hpre' : s0.mem ⊨ (withLsFrozen lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S') stk')).pre y' s0 ∗ R := by
    have hiff : S'.decPkOk g0.F g0.peer.val g0.me.val g0.msg ↔
        S.decPkOk g0.F g0.peer.val g0.me.val g0.msg :=
      and_iff_left ⟨rfl, rfl, rfl, rfl⟩
    simpa only [withLsFrozen, dpPollSpecStateBudget, dpSlotPollKStatePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
      y', g0, propext hiff] using hpre
  rcases version_three_or_four_of_pksmParse_some hparse with hv3 | hv4
  · exact (hv3_poll S' (fun F peer me pm _ hd => by
      have ⟨_, hF, hp, hm, hpm⟩ :
          S.decPkOk F peer me pm ∧ F = g0.F ∧ peer = g0.peer.val ∧ me = g0.me.val ∧ pm = g0.msg := hd
      subst hF; subst hp; subst hm; subst hpm
      exact ⟨hpure.filesOkPeer,
        ⟨hpure.storeOk.keyPairLt, hpure.storeOk.preKeysWf, hpure.storeOk.baseKeysLt⟩,
        ⟨hv3, hnoMatch⟩, hAns0⟩)).mono_outcome
      y' R s0 hpc hrun hpre' hsp (fun _ hout => hout)
  · have hkpBad := (pkToE?_eq_none_iff_of_pksmParse_v4 hparse hv4).mp hpkNone
    exact (hv4_poll S' (fun F peer me pm _ hd => by
      have ⟨_, hF, hp, hm, hpm⟩ :
          S.decPkOk F peer me pm ∧ F = g0.F ∧ peer = g0.peer.val ∧ me = g0.me.val ∧ pm = g0.msg := hd
      subst hF; subst hp; subst hm; subst hpm
      exact ⟨hpure.filesOkPeer,
        ⟨hpure.storeOk.keyPairLt, hpure.storeOk.preKeysWf, hpure.storeOk.baseKeysLt⟩,
        ⟨hAcct, hv4, hkpBad, hnoMatch⟩, hAns0⟩)).mono_outcome
      y' R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Caller-block (`i < 619`) `decPkSlotSpecFrozenPlaced` reduction for `pkToE? pm = none` at
`lsmpl.base 520`. -/
theorem cliDecryptPrekey_pkToENone_reject_slot_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (B : RunBudgets) (S : RunSem)
    (hpoll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        dpPollEntryPlaced
        (withLsFrozen lsmpl
          (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')))
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  have hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W)) := inferInstance
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
    rw [CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact hcaller
  exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlot_ok_state_frozen_placed
    B S stk hstk hstk64
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget.cliDecryptPrekey_ok_state_frozen_placed_at_block
      (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget.dpSlotPollKStatePlaced_inv_vm
        A lim DecPkEnv B S)
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget.dpSlotPollKStatePlaced_res_vm
        A lim DecPkEnv B S)
      (fun stk' h1 h2 => by
        rw [CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl gh W]
        exact hpoll stk' h1 h2)
      stk
      (by simp only [CryptoVerification.SignalSession.Cli.RunProofs.dpWrapFrame, dpPollNeed,
        cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

private theorem r20m3_pure_sepConj_mono {φ ψ : Prop} (h : φ → ψ) (P : SepProp) :
    ⌜φ⌝ ∗ P ⊢ ⌜ψ⌝ ∗ P :=
  Entails.pure_left fun hφ => by
    have hEq : ψ = True := propext ⟨fun _ => trivial, fun _ => h hφ⟩
    rw [hEq, pure_true, sepConj_comm, sepConj_emp]
    exact Entails.refl P

private theorem r20m3_toSkeletonRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem r20m3_pollEnv_v3_sub [LibsignalPlacement] {M : AllocCostModel}
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

private theorem r20m3_pollEnv_badKem_sub [LibsignalPlacement] {M : AllocCostModel}
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

private theorem r20m3_dpPollSpecStateBudget_mono_env [LibsignalPlacement]
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
    exact r20m3_pure_sepConj_mono
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
    exact r20m3_pure_sepConj_mono (fun ⟨hevs, htr, hout'⟩ => ⟨hsub y.g evs hevs, htr, hout'⟩) _
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- Environment-monotonicity, `DecPkOkD3Untyped` conversion, and `slotsOfSigPkFrozenPlaced`
threading lemma combining `v3` and `v4` bad-KEM poll contracts into the block-`520` slot contract. -/
theorem decPkD3Untyped_slotOk_of_poll_and_slot_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets ReadEnv DeserEnv
        PqxdhAcceptBadKemErrEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3Untyped ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : cliDecryptPrekeyNeed cliRunBudgets ≤ needs.decryptPrekey)
    (hM1 : ∀ (stk' : Nat), dpPollNeed cliRunBudgets ≤ stk' → stk' ≤ 2 ^ 63 →
      (∀ S' : RunSem,
        (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
          FilesOkPeer scopeIn F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
          MsgCondV3 scopeIn F peer me pm ∧
          (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
        subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          dpPollEntryPlaced
          (withLsFrozen lsmpl
            (dpPollSpecStateBudget
              (dpSlotPollKStatePlaced A lim sEnvs.decryptPrekey cliRunBudgets S') stk'))) →
      (∀ S' : RunSem,
        (∀ F peer me pm, S'.filesOk F peer me → S'.decPkOk F peer me pm →
          FilesOkPeer scopeIn F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
          MsgCondBadKem scopeIn F peer me pm ∧
          (∀ coins, S'.decryptPrekey F peer me pm coins = some none)) →
        subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          dpPollEntryPlaced
          (withLsFrozen lsmpl
            (dpPollSpecStateBudget
              (dpSlotPollKStatePlaced A lim sEnvs.decryptPrekey cliRunBudgets S') stk'))) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        dpPollEntryPlaced
        (withLsFrozen lsmpl
          (dpPollSpecStateBudget
            (dpSlotPollKStatePlaced A lim sEnvs.decryptPrekey cliRunBudgets S) stk')))
    (hM2 :
      (∀ stk', dpPollNeed cliRunBudgets ≤ stk' → stk' ≤ 2 ^ 63 →
        subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          dpPollEntryPlaced
          (withLsFrozen lsmpl
            (dpPollSpecStateBudget
              (dpSlotPollKStatePlaced A lim sEnvs.decryptPrekey cliRunBudgets S) stk'))) →
      ∀ stk, cliDecryptPrekeyNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (lsmpl.base 520)
          (decPkSlotSpecFrozenPlaced A lim sEnvs.decryptPrekey S stk)) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let _ := X
  have _ := hfiles
  have _ := hdecPk
  have _ := hdecPkOk
  intro stk hstk1 hstk2
  refine hM2 ?_ stk (Nat.le_trans hneed hstk1) hstk2
  intro stk' hdp1 hdp2
  exact hM1 stk' hdp1 hdp2
    (fun S' hok3 =>
      r20m3_dpPollSpecStateBudget_mono_env (r20m3_pollEnv_v3_sub hsEnv)
        (subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
          (decPk_v3_reject_poll_placedBudget A lim h547 mmpl gh W cliRunBudgets S' scopeIn
            (r20m3_toSkeletonRunHooksPlaced hh) hRead hDeser encodeInjOn_deserializeScopeP_Q
            (fun _ hr => hr)
            (fun F peer me pm hf hd =>
              let ⟨hfp, hs, hm, hc⟩ := hok3 F peer me pm hf hd
              ⟨hfp, ⟨hs.keyPairLt, hs.preKeysWf, hs.baseKeysLt⟩, ⟨hm.1, hm.2⟩, hc⟩)
            stk' hdp1 hdp2)))
    (fun S' hok4 =>
      r20m3_dpPollSpecStateBudget_mono_env (r20m3_pollEnv_badKem_sub hsEnv)
        (decPk_badKem_reject_poll_full_placedBudget A lim h547 mmpl gh W cliRunBudgets S' scopeIn
          hG hh hRead hDeser encodeInjOn_deserializeScopeP_Q
          (fun _ hr => hr)
          (fun F peer me pm hf hd =>
            let ⟨hfp, hs, hm, hc⟩ := hok4 F peer me pm hf hd
            ⟨hfp, ⟨hs.keyPairLt, hs.preKeysWf, hs.baseKeysLt⟩, hm, hc⟩)
          stk' hdp1 hdp2))

/-! ## 3. Block-`520` Slot Theorems -/

/-- `ReadEnv`-parametric `[LibsignalFullPlacement]` block-`520` slot contract for
`pkToE? pm = none`. -/
theorem decPkD3Untyped_slotOk_full_of_readEnv_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
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
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkD3Untyped_slotOk_of_poll_and_slot_placedBudget X mmpl gh W h547 hG hh hRead hDeser
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed
    (fun stk' _h1 _h2 hv3 hv4 =>
      cliDpPoll_pkToENone_reject_ok_placedBudget A lim mmpl gh W cliRunBudgets S scopeIn
        (fun F peer me pm hf hd => by
          have hd' := hdecPkOk F peer me pm hd
          exact ⟨(hfiles ▸ hf).1, hd'.1, hd'.2, fun coins =>
            hdecPk ▸ D3PollRejectAuxPlacedBudget.decPkDef_eq_some_none_of_d3b3
              X ⟨W.C, W.Q⟩ scopeIn F peer me pm coins hd'.2.2.1 hd'.2.2.2.2⟩)
        stk' hv3 hv4)
    (fun hpoll stk hstk1 hstk2 =>
      cliDecryptPrekey_pkToENone_reject_slot_placedBudget
        (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
        A lim mmpl gh W (by decide) cliRunBudgets S hpoll stk hstk1 hstk2)

/-- Concrete CLI specialization of `decPkD3Untyped_slotOk_full_of_readEnv_placedBudget` at
`DecPkD3UntypedEnv` (`ReadFileRuleEnv cliIo.rd`, `SessDeserializeCancelEnv`). -/
theorem decPkD3Untyped_slotOk_full_cli_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile
        (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs, DecPkD3UntypedEnv A.repAlloc W cliRunBudgets g evs → sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3Untyped ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : cliDecryptPrekeyNeed cliRunBudgets ≤ needs.decryptPrekey) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkD3Untyped_slotOk_full_of_readEnv_placedBudget X mmpl gh W h547 hG hh hRead hDeser
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Discharges the block-`520` `decrypt_prekey` slot premise of
`D3MainLiftGlueF3.mainOkUntypedD3F3_of_seams` for `decPkNeed ≤ 4194304`. -/
theorem decPkD3Untyped_hdecPk_of_seams
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hpl : libsignalSessionLib.Placeable mpl)
    (ghFixed : CliGhostHooks)
    {brkStart : BitVec 64}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (sEnvs : CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    {decPkNeed : Nat}
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hneed : cliDecryptPrekeyNeed cliRunBudgets ≤ decPkNeed := by decide)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hh : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
        (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hReadPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits cliRunBudgets.readFile ReadEnv))
    (hDeserPoll : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (mpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits DeserEnv))
    (hsEnv : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ g evs,
        DecPkD3UntypedEnvOf
          (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
          cliRunBudgets ReadEnv DeserEnv PqxdhAcceptBadKemErrEnv g evs →
        (sEnvs W γ tp).decryptPrekey g evs) :
    mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvs W γ tp)
          (cliRunSemD3 W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520) := by
  have _ := hdecPkNeed
  intro h547 W γ tp
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hblk hext_nodup hpl
  exact decPkD3Untyped_slotOk_full_of_readEnv_placedBudget
    defaultExtrasF3 mmpl ghFixed W h547
    (hG γ tp)
    (toClosureRunHooksPlaced (hh h547 W γ tp))
    (hReadPoll h547 W γ tp)
    (hDeserPoll h547 W γ tp)
    (cliRunSemD3 W) (sEnvs W γ tp) (cliRunNeeds decPkNeed)
    (hsEnv W γ tp) rfl rfl
    (fun _ _ _ _ h => ⟨⟨h.1.keyPairLt, h.1.preKeysWf, h.1.baseKeysLt⟩, h.2⟩)
    hneed

/-! ## 4. Envelope and `SingleSlotFineSpec` Re-Exports -/

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  StageP2V3RejectEnv DecPkD3UntypedPollEnv PqxdhAcceptBadKemErrEnv StageP2BadKemRejectEnv
  StageP2UntypedRejectEnv
)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  DecPkD3UntypedEnvOf DecPkD3UntypedEnv DecPkD3UntypedRejectEnv DecPkKeyFilesBounded
  decPkKeyFilesBounded_of_cliPqInputs
)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  decPkKeyFilesBounded_of_pqOrD3Recv
)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget (
  decPkD3UntypedCum decPkD3UntypedLive decPkD3UntypedPeak decPkD3UntypedMaxReq
  decPkD3UntypedGrpS
)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget (
  decPkD3Untyped_caps_le decPkD3Untyped_caps_le_1MiB decPkD3UntypedEnv_phaseCreditSpec
  decPkD3UntypedEnv_fine_groupSpec decPkD3UntypedEnv_singleSlotFineSpec
)

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget (
  decPkD3UntypedEnv_of_inputs_singleSlotFineSpec decPkD3UntypedEnv_r3b_singleSlotFineSpec
  decPkD3UntypedEnv_nonvacuous_alloc nonvacuous_alloc
)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget
