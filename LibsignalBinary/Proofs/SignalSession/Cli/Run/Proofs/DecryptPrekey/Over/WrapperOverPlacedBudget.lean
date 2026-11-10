/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` D2(c) Wrapper-to-Slot Lift

Lifts budget-threaded `CliDpPollOkD2cStatePlacedAt` and `CliDpPollOkD2cStatePlacedStmt` from
Block `518` (`dpPollEntryPlaced`) through outer Block `520` (`lsmpl.base 520`) to
`OverDecPkD2cSlotOkPlaced` and its `LibsignalFrozen` counterpart.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunNeeds RunSem dpPollNeed mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c cliDecryptPrekeyNeed decPkDefD2c dpWrapFrame
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q scopeIn scopeKit
)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget (
  DecPkD2cSlotOkPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget (
  CliDpPollOkD2cStatePlacedAt CliDpPollOkD2cStatePlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (
  dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget (
  cliDecryptPrekey_ok_state_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  decPkSlotSpecPlaced dpSlotPollKStatePlaced dpSlot_ok_state_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)

abbrev OverDecPkD2cSlotOkPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  DecPkD2cSlotOkPlaced mmpl g W A lim DecPkEnv

theorem cliDecryptPrekey_slotOk_d2c_of_pollAt_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X B S Scope)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl g W
  have hEq : dpPollProgPlaced H =
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  intro stk h1 h2
  have hstk : cliDecryptPrekeyNeed B ≤ stk := hneed ▸ h1
  exact dpSlot_ok_state_placed B S stk hstk h2
    (cliDecryptPrekey_ok_state_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hh (hEq ▸ hRead) (hEq ▸ hDeser) hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢; omega)
      h2 hi)

theorem cliDecryptPrekey_slotOk_d2c_of_poll_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStatePlacedStmt A lim ReadEnv DeserEnv DecPkEnv)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim (DecPkEnv W X B Scope) S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_d2c_of_pollAt_placed A lim ReadEnv DeserEnv (DecPkEnv W X B Scope)
    mmpl g W hi X B S Scope needs hh hRead hDeser hinjK hsub hS hok
    (hpoll mmpl g W X B S Scope) hneed

theorem decPkD2cSlotOk_of_poll_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hpoll : ∀ X S,
      CliDpPollOkD2cStatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X cliRunBudgets S scopeIn) :
    DecPkD2cSlotOkPlaced mmpl g W A lim DecPkEnv := by
  intro X S needs sEnvs hsDec hfiles hdec hdecOk hneed
  dsimp only [slotsOfPlaced]
  rw [hsDec]
  exact cliDecryptPrekey_slotOk_d2c_of_pollAt_placed
    (prog := lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 579)
    A lim ReadEnv DeserEnv DecPkEnv mmpl g W (by decide)
    X cliRunBudgets S scopeIn needs
    hh hRead hDeser
    encodeInjOn_deserializeScopeP_Q
    (fun _ h => h) hdec
    (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
    (hpoll X S) hneed

/-! ## `LibsignalFrozen` Variants -/

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget (
  CliDpPollOkD2cStateFrozenPlacedAt CliDpPollOkD2cStateFrozenPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget (
  cliDecryptPrekey_ok_state_frozen_placed_at_block
)

/-- Base (unwrapped) budget-threaded `[LibsignalPlacement]` D2(c) slot contract. -/
def decPkSlotSpecBasePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
      s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = lsρ CryptoVerification.SignalSession.Cli.cliSessionVtSym ∧
      s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = lsρ CryptoVerification.SignalSession.Cli.cliIdentityVtSym ∧
      s.readReg64 .x7 = x.stores + 0xc8#64 ∧
      s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat ∧
      LibsignalBinary.Heap.FitsEnv M lim st (DecPkEnv x)⌝ ∗
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced A lim st x.toSlotCtx s ∗
    CryptoVerification.LibsignalPublicApiRepr.preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
    (s.sp ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliPreKeyVtSym) ∗
    ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
    ((s.sp + 16#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliSignedPreKeyVtSym) ∗
    ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
    ((s.sp + 32#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliKyberPreKeyVtSym) ∗
    memRegion x.ret 48 ∗ stackAt s.sp stk
  post := (decPkSlotSpecPlaced A lim DecPkEnv S stk).post
  onPanic := (decPkSlotSpecPlaced A lim DecPkEnv S stk).onPanic

/-- `CodeOk`-parameterized budget-threaded `[LibsignalPlacement]` D2(c) slot contract. -/
def decPkSlotSpecPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  { decPkSlotSpecBasePlaced A lim DecPkEnv S stk with
    pre := fun x s0 => (decPkSlotSpecBasePlaced A lim DecPkEnv S stk).pre x s0 ∗ ⌜CodeOk s0.mem⌝ }

/-- `LibsignalFrozen`-guarded budget-threaded `[LibsignalPlacement]` D2(c) slot contract. -/
abbrev decPkSlotSpecFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  decPkSlotSpecPlacedOf (CryptoVerification.LibsignalFrozen lsmpl) A lim DecPkEnv S stk

theorem dpSlot_ok_state_frozen_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : CryptoVerification.SignalSession.Cli.RunCompose.decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.cliDecryptPrekeySpecStateBudget
          (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  have hstack5 : ∀ (sp : BitVec 64) (x : DecPkGhost),
      CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt sp
        ((CryptoVerification.SignalSession.Cli.RunCompose.dpSlotArgsPlaced x).drop 8) =
        (sp ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliPreKeyVtSym) ∗
          ((sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
          ((sp + 16#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliSignedPreKeyVtSym) ∗
          ((sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
          ((sp + 32#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliKyberPreKeyVtSym) := by
    intro sp x
    simp only [CryptoVerification.SignalSession.Cli.RunCompose.dpSlotArgsPlaced, List.drop,
      CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt, sepConj_emp, BitVec.add_assoc]
    rfl
  have hpost_ent : ∀ (x : DecPkGhost) (st : M.σ) (s0 sf : State),
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.cliDecryptPrekeySpecStateBudget
          (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk)).post
          ⟨x.ret, x, st⟩ s0 sf ⊢
        (decPkSlotSpecPlaced A lim DecPkEnv S stk).post (x, st) s0 sf := by
    intro x st s0 sf
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen]
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.cliDecryptPrekeySpecStateBudget
    have ent_bind : ∀ {α : Type} {X R Q : SepProp} {P : α → SepProp},
        (X ⊢ ∃∗ a, P a) → (∀ a, P a ∗ R ⊢ Q) → (X ∗ R ⊢ Q) := by
      intro α X R Q P hX hk
      refine Entails.trans (sepConj_mono_left hX) ?_
      rw [sepExists_sepConj_left]; exact Entails.sepExists_elim hk
    have ent_pure_r : ∀ {φ : Prop} {P Q : SepProp}, φ → (P ⊢ Q) → (P ⊢ ⌜φ⌝ ∗ Q) := by
      intro φ P Q hφ hPQ
      have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
      rw [hEq, pure_true, sepConj_comm, sepConj_emp]; exact hPQ
    refine ent_bind (Entails.refl _) fun ws => ?_
    rw [sepConj_assoc]; refine Entails.pure_left fun _ => ?_
    have r1 : (CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt x.ret ws ∗
            (dpSlotPollKStatePlaced A lim DecPkEnv B S).res x st s0 sf ws) ∗
          (CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt s0.sp
            (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
            stackAt s0.sp stk) =
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).res x st s0 sf ws ∗
          (CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt x.ret ws ∗
            CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt s0.sp
              ((CryptoVerification.SignalSession.Cli.RunCompose.dpSlotArgsPlaced x).drop 8) ∗
            stackAt s0.sp stk) := by ac_rfl
    rw [r1]; unfold dpSlotPollKStatePlaced
    refine ent_bind (Entails.refl _) fun evs => ?_
    refine ent_bind (Entails.refl _) fun g' => ?_
    refine ent_bind (Entails.refl _) fun e => ?_
    rw [sepConj_assoc]; refine Entails.pure_left fun ⟨hevs, htrace, hout⟩ => ?_
    rw [hstack5]
    have r2 : (CryptoVerification.SignalSession.Cli.MainHops.storesAt A.repAlloc x.stores g' ∗
          CryptoVerification.SignalSession.Cli.RunCompose.dpResHeap A.repAlloc ws e ∗
          CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.peer x.peerA ∗
          CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.me x.meA ∗
          CryptoVerification.LibsignalPublicApiRepr.preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗ anyHeap) ∗
            (CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt x.ret ws ∗
            ((s0.sp ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliPreKeyVtSym) ∗
              ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
              ((s0.sp + 16#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliSignedPreKeyVtSym) ∗
              ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
              ((s0.sp + 32#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliKyberPreKeyVtSym)) ∗
            stackAt s0.sp stk) =
        (CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt x.ret ws ∗
          CryptoVerification.SignalSession.Cli.RunCompose.dpResHeap A.repAlloc ws e) ∗
          (CryptoVerification.SignalSession.Cli.MainHops.storesAt A.repAlloc x.stores g' ∗
            CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.peer x.peerA ∗
            CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.me x.meA ∗
            CryptoVerification.LibsignalPublicApiRepr.preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
            (s0.sp ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliPreKeyVtSym) ∗
            ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
            ((s0.sp + 16#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliSignedPreKeyVtSym) ∗
            ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
            ((s0.sp + 32#64) ↦₆₄ lsρ CryptoVerification.SignalSession.Cli.cliKyberPreKeyVtSym) ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp stk ∗ anyHeap) := by ac_rfl
    rw [r2]
    refine Entails.trans
      (sepConj_mono_left
        (CryptoVerification.SignalSession.Cli.RunCompose.dpWords_resHeap_entails_decResAt A.repAlloc x.ret ws e)) ?_
    unfold decPkSlotSpecPlaced CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
    refine Entails.sepExists_right evs (Entails.sepExists_right g' (Entails.sepExists_right e ?_))
    exact ent_pure_r ⟨hevs, htrace, hout⟩ (Entails.of_eq (by ac_rfl))
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  have ⟨hfr, hpre0⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen (spec := decPkSlotSpecBasePlaced A lim DecPkEnv S stk) hpre
  dsimp only [decPkSlotSpecBasePlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hspatial⟩ := hpre0
  have hpre₁ : s0.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.cliDecryptPrekeySpecStateBudget
          (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk)).pre ⟨x.ret, x, st⟩ s0 ∗ R := by
    have htake : ((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).take 8 =
        [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
         s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
      simp only [dpSlotPollKStatePlaced, CryptoVerification.SignalSession.Cli.RunCompose.dpSlotArgsPlaced, List.take,
        hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    have hinv_sp : s0.mem ⊨ (dpSlotPollKStatePlaced A lim DecPkEnv B S).inv x st s0 ∗
          CryptoVerification.SignalSession.Cli.RunProofs.dpWordsAt s0.sp
            (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
      unfold dpSlotPollKStatePlaced
      rw [hstack5, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF0, hfOk, hdOk, hfit⟩,
        by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.cliDecryptPrekeySpecStateBudget
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  refine hw.mono_outcome ⟨x.ret, x, st⟩ R s0 hpc hrun hpre₁ hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
  · exact Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left (hpost_ent x st s0 sf)) hpost⟩
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧
            S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗
        (anyHeap ∗ R) := by
      simpa only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.cliDecryptPrekeySpecStateBudget,
        dpSlotPollKStatePlaced, sepConj_assoc] using hp
    rw [satisfies_pure_sepConj] at hp'; obtain ⟨⟨_, hp_none⟩, hany⟩ := hp'
    have hp_goal : sf.mem ⊨
          ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ (anyHeap ∗ R) := by
      rw [satisfies_pure_sepConj]; exact ⟨hp_none, hany⟩
    simpa only [decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced,
      decPkSlotSpecPlaced, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      sepConj_assoc] using hp_goal
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- Extern-parametric `LibsignalFrozen` D2(c) `decryptPrekey` slot contract. -/
def DecPkD2cSlotOkFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : CryptoVerification.LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds)
    (sEnvs : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = CryptoVerification.SignalSession.Cli.Slots.filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget.slotOkPlaced
      (lsProg_579 H) (lsmpl.base 520)
      (mkSlot (decPkSlotSpecFrozenPlaced A lim sEnvs.decryptPrekey S) needs.decryptPrekey)

/-- `LibsignalFrozen` D2(c) `decryptPrekey` slot contract. -/
abbrev OverDecPkD2cSlotOkFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives),
    DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) X W A lim DecPkEnv

theorem cliDecryptPrekey_slotOk_d2c_of_pollAt_full_placed [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X B S Scope)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl g W
  have hEq : dpPollProgPlaced H =
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  intro stk h1 h2
  have hstk : cliDecryptPrekeyNeed B ≤ stk := hneed ▸ h1
  exact dpSlot_ok_state_frozen_placed B S stk hstk h2
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hh (hEq ▸ hRead) (hEq ▸ hDeser) hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢; omega)
      h2 hi)

theorem cliDecryptPrekey_slotOk_d2c_of_poll_full_placed [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hpoll : CliDpPollOkD2cStateFrozenPlacedStmt A lim ReadEnv DeserEnv DecPkEnv)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced A lim (DecPkEnv W X B Scope) S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_d2c_of_pollAt_full_placed A lim ReadEnv DeserEnv (DecPkEnv W X B Scope)
    mmpl g W hi X B S Scope needs hh hRead hDeser hinjK hsub hS hok
    (hpoll mmpl g W X B S Scope) hneed

theorem decPkD2cSlotOk_of_poll_full_placed [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hpoll : ∀ X S,
      CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl g W X cliRunBudgets S scopeIn) :
    OverDecPkD2cSlotOkFrozenPlaced mmpl g W A lim DecPkEnv := by
  intro X S needs sEnvs hsDec hfiles hdec hdecOk hneed
  rw [hsDec]
  exact cliDecryptPrekey_slotOk_d2c_of_pollAt_full_placed
    (prog := lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 579)
    A lim ReadEnv DeserEnv DecPkEnv mmpl g W (by decide)
    X cliRunBudgets S scopeIn needs
    hh hRead hDeser
    encodeInjOn_deserializeScopeP_Q
    (fun _ h => h) hdec
    (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
    (hpoll X S) hneed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlacedBudget
