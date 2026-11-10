/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `decrypt_prekey` Slot Adapter (Placed)

Budget-threaded `[LibsignalPlacement]` poll and wrapper contracts (`DpPollKStateBudget`,
`dpPollSpecStateBudget`, `cliDecryptPrekeySpecStateBudget`) and wrapper-to-slot adapters
(`dpSlot_ok_state_placed`, `dpSlot_ok_state_frozen_placed`) for
`signal_session_handshake::decrypt_prekey`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet (extract_withLsFrozen withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.E2E CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunSem SlotCtx decPkNeed decResAt dpPollNeed dpResHeap dpSlotArgsPlaced
   dpWords_resHeap_entails_decResAt slotOut slotOutTr slotTrace slotTraceFT)
open CryptoVerification.SignalSession.Cli.RunProofs
  (dpCxAt dpFutDoneAt dpFutStartAt dpWordsAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)

/-- Budget-threaded `[LibsignalPlacement]` counterpart of `slotFramePlaced`. -/
def slotFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : SlotCtx) (s : State) :
    SepProp :=
  ⌜x.coins.length < 2 ^ 63⌝ ∗
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗
    protocolAddressAt A.repAlloc x.me x.meA ∗
    coinsInstalledPlaced x.coinsP x.coins ∗
    tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s

theorem slotFramePlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : SlotCtx) (s : State) :
    slotFramePlaced A lim st x s =
      CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced (A.atState lim st s) x :=
  rfl

/-- Budget-threaded `[LibsignalPlacement]` `decrypt_prekey` slot contract carrying
`withLsCodeRoLoaded lsmpl`. -/
def decPkSlotSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
          s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = lsρ cliSessionVtSym ∧
          s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = lsρ cliIdentityVtSym ∧
          s.readReg64 .x7 = x.stores + 0xc8#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat ∧
          FitsEnv M lim st (DecPkEnv x)⌝ ∗
        slotFramePlaced A lim st x.toSlotCtx s ∗ preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
        (s.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
        ((s.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
        ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
        ((s.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
        memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
          ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
          ⌜DecPkEnv x evs ∧ slotTrace s0 sf ∧
            slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
          storesAt A.repAlloc x.stores g' ∗ decResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((s0.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (x, _) _ _ =>
        ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ anyHeap }

/-- Budget-threaded state-coupled poll contract over `M : AllocCostModel` (`inv` and `res` observe
full machine `State` so `A.pool lim st s` threads cleanly). -/
structure DpPollKStateBudget (M : AllocCostModel) where
  Ghost : Type
  args : Ghost → List (BitVec 64)
  inv : Ghost → M.σ → State → SepProp
  res : Ghost → M.σ → State → State → List (BitVec 64) → SepProp
  panics : Ghost → Prop
  need : Nat

/-- Ghost of a budget-threaded state-coupled poll: result slot, future, `Context`, `K`'s ghost, and
initial cost-model state `st`. -/
structure DpPollGhostStateBudget {M : AllocCostModel} (K : DpPollKStateBudget M) where
  out : BitVec 64
  fut : BitVec 64
  cx : BitVec 64
  g : K.Ghost
  st : M.σ

/-- Budget-threaded state-coupled contract for one poll of a fresh `message_decrypt_prekey` future. -/
def dpPollSpecStateBudget {M : AllocCostModel} (K : DpPollKStateBudget M) (stk : Nat) :
    Spec (DpPollGhostStateBudget K) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.fut ∧ s.readReg64 .x2 = x.cx ∧
      (K.args x.g).length = 13 ∧ stk ≤ s.sp.toNat⌝ ∗
      memRegion x.out 48 ∗ dpFutStartAt x.fut (K.args x.g) ∗ dpCxAt x.cx ∗
      K.inv x.g x.st s ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt x.out ws ∗ K.res x.g x.st s0 sf ws) ∗
      dpFutDoneAt x.fut ∗ memRegion x.cx 32 ∗ stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ K.panics x.g⌝ ∗ anyHeap

/-- Ghost of a budget-threaded state-coupled `decrypt_prekey` call: sret slot (`x8`), `K`'s ghost,
and initial cost-model state `st`. -/
structure DecryptPrekeyGhostStateBudget {M : AllocCostModel} (K : DpPollKStateBudget M) where
  ret : BitVec 64
  g : K.Ghost
  st : M.σ

/-- Budget-threaded state-coupled contract for `signal_session_handshake::decrypt_prekey` under `K`. -/
def cliDecryptPrekeySpecStateBudget {M : AllocCostModel}
    (K : DpPollKStateBudget M) (stk : Nat) : Spec (DecryptPrekeyGhostStateBudget K) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (K.args x.g).length = 13 ∧
      (K.args x.g).take 8 =
        [s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
          s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6, s.readReg64 .x7] ∧
      stk ≤ s.sp.toNat⌝ ∗
      dpWordsAt s.sp ((K.args x.g).drop 8) ∗ memRegion x.ret 48 ∗
      K.inv x.g x.st s ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt x.ret ws ∗ K.res x.g x.st s0 sf ws) ∗
      dpWordsAt s0.sp ((K.args x.g).drop 8) ∗ stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ K.panics x.g⌝ ∗ anyHeap

/-- Budget-threaded `[LibsignalPlacement]` instantiation of `DpPollKStateBudget`. -/
def dpSlotPollKStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem) :
    DpPollKStateBudget M where
  Ghost := DecPkGhost
  args := dpSlotArgsPlaced
  inv := fun x st s =>
    ⌜s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg ∧
      FitsEnv M lim st (DecPkEnv x)⌝ ∗
      slotFramePlaced A lim st x.toSlotCtx s ∗ preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg
  res := fun x st s0 sf ws =>
    ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
      ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
      ⌜DecPkEnv x evs ∧ slotTraceFT s0.fs s0.trace sf.fs sf.trace ∧
        slotOutTr (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0.trace sf.trace⌝ ∗
        storesAt A.repAlloc x.stores g' ∗ dpResHeap A.repAlloc ws e ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ anyHeap
  panics := fun x => S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none
  need := dpPollNeed B

section PlacedConsequenceHelpers

private theorem sepConj_pure_of_true_placed {φ : Prop} (P : SepProp) (hφ : φ) : P ∗ ⌜φ⌝ = P := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, sepConj_emp]

private theorem pure_sepConj_eq_of_true_placed {φ : Prop} (P : SepProp) (hφ : φ) : ⌜φ⌝ ∗ P = P := by
  rw [sepConj_comm, sepConj_pure_of_true_placed P hφ]

private theorem ent_pure_left_placed {φ : Prop} {P Q : SepProp} (h : φ → (P ⊢ Q)) : ⌜φ⌝ ∗ P ⊢ Q :=
  Entails.pure_left h

private theorem ent_pure_right_placed {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_eq_of_true_placed Q hφ]; exact h

private theorem ent_bind_placed {α : Type} {X R Q : SepProp} {P : α → SepProp}
    (hX : X ⊢ ∃∗ x, P x) (hk : ∀ x, P x ∗ R ⊢ Q) : X ∗ R ⊢ Q := by
  refine Entails.trans (sepConj_mono_left hX) ?_
  rw [sepExists_sepConj_left]; exact Entails.sepExists_elim hk

private theorem dpWords5_eq_placed (a w₀ w₁ w₂ w₃ w₄ : BitVec 64) :
    dpWordsAt a [w₀, w₁, w₂, w₃, w₄] =
      (a ↦₆₄ w₀) ∗ ((a + 8#64) ↦₆₄ w₁) ∗ ((a + 16#64) ↦₆₄ w₂) ∗
        ((a + 24#64) ↦₆₄ w₃) ∗ ((a + 32#64) ↦₆₄ w₄) := by
  simp only [dpWordsAt, sepConj_emp, BitVec.add_assoc]; rfl

private theorem dpSlotStack5_placed_eq [LibsignalPlacement] (sp : BitVec 64) (x : DecPkGhost) :
    dpWordsAt sp ((dpSlotArgsPlaced x).drop 8) =
      (sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
        ((sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗ ((sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
        ((sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) :=
  dpWords5_eq_placed sp (lsρ cliPreKeyVtSym) (x.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (x.stores + 120#64) (lsρ cliKyberPreKeyVtSym)

private theorem subroutine_ok_of_outcome_map_placed {α β : Type} {prog : Program}
    {entry : BitVec 64} {spec₁ : Spec α} {spec₂ : Spec β} (f : β → α)
    (h : subroutine_ok prog entry spec₁)
    (hconseq : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec₂.pre y s0 ∗ R) →
        (s0.mem ⊨ spec₁.pre (f y) s0 ∗ R) ∧
          ∀ sf, SubroutineOutcome spec₁ (f y) R s0 sf → SubroutineOutcome spec₂ y R s0 sf) :
    subroutine_ok prog entry spec₂ :=
  subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _ =>
    let ⟨hpre₁, hm⟩ := hconseq y R s0 hpre
    h.mono_outcome (f y) R s0 hpc hrun hpre₁ hsp hm

private theorem dpSlotState_post_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem)
    (stk : Nat) (x : DecPkGhost) (st : M.σ) (s0 sf : State) :
    (withLsCodeRoLoaded lsmpl
      (cliDecryptPrekeySpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk)).post
        ⟨x.ret, x, st⟩ s0 sf ⊢
      (decPkSlotSpecPlaced A lim DecPkEnv S stk).post (x, st) s0 sf := by
  dsimp only [withLsCodeRoLoaded]
  unfold cliDecryptPrekeySpecStateBudget
  refine ent_bind_placed (Entails.refl _) fun ws => ?_
  rw [sepConj_assoc]; refine ent_pure_left_placed fun _ => ?_
  have r1 : (dpWordsAt x.ret ws ∗
          (dpSlotPollKStatePlaced A lim DecPkEnv B S).res x st s0 sf ws) ∗
        (dpWordsAt s0.sp (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
          stackAt s0.sp stk) =
      (dpSlotPollKStatePlaced A lim DecPkEnv B S).res x st s0 sf ws ∗ (dpWordsAt x.ret ws ∗
          dpWordsAt s0.sp ((dpSlotArgsPlaced x).drop 8) ∗ stackAt s0.sp stk) := by ac_rfl
  rw [r1]; unfold dpSlotPollKStatePlaced
  refine ent_bind_placed (Entails.refl _) fun evs => ?_
  refine ent_bind_placed (Entails.refl _) fun g' => ?_
  refine ent_bind_placed (Entails.refl _) fun e => ?_
  rw [sepConj_assoc]; refine ent_pure_left_placed fun ⟨hevs, htrace, hout⟩ => ?_
  rw [dpSlotStack5_placed_eq]
  have r2 : (storesAt A.repAlloc x.stores g' ∗ dpResHeap A.repAlloc ws e ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ anyHeap) ∗
          (dpWordsAt x.ret ws ∗
          ((s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
            ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
            ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
            ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym)) ∗ stackAt s0.sp stk) =
      (dpWordsAt x.ret ws ∗ dpResHeap A.repAlloc ws e) ∗ (storesAt A.repAlloc x.stores g' ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap) := by ac_rfl
  rw [r2]
  refine Entails.trans
    (sepConj_mono_left (dpWords_resHeap_entails_decResAt A.repAlloc x.ret ws e)) ?_
  unfold decPkSlotSpecPlaced withLsCodeRoLoaded
  refine Entails.sepExists_right evs (Entails.sepExists_right g' (Entails.sepExists_right e ?_))
  exact ent_pure_right_placed ⟨hevs, htrace, hout⟩ (Entails.of_eq (by ac_rfl))

end PlacedConsequenceHelpers

/-- Budget-threaded `[LibsignalPlacement]` state-coupled wrapper-to-slot adapter for `decrypt_prekey`. -/
theorem dpSlot_ok_state_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (cliDecryptPrekeySpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecPlaced A lim DecPkEnv S stk) := by
  refine subroutine_ok_of_outcome_map_placed (fun (x, st) => ⟨x.ret, x, st⟩) hw
    fun (x, st) R s0 hpre => ?_
  have ⟨hrocl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [decPkSlotSpecPlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hspatial⟩ := hpre0
  refine ⟨?_, ?_⟩
  · have htake : ((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).take 8 =
        [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
         s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
      simp only [dpSlotPollKStatePlaced, dpSlotArgsPlaced, List.take,
        hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    have hinv_sp : s0.mem ⊨ (dpSlotPollKStatePlaced A lim DecPkEnv B S).inv x st s0 ∗
          dpWordsAt s0.sp (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
      unfold dpSlotPollKStatePlaced
      rw [dpSlotStack5_placed_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF0, hfOk, hdOk, hfit⟩,
        by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hrocl, ?_⟩
    unfold cliDecryptPrekeySpecStateBudget; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono (sepConj_mono_left
          (dpSlotState_post_entails_placed A lim DecPkEnv B S stk x st s0 sf)) hpost⟩
    · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
      have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧
              S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗
          (anyHeap ∗ R) := by
        simpa only [withLsCodeRoLoaded,
          cliDecryptPrekeySpecStateBudget, dpSlotPollKStatePlaced, sepConj_assoc] using hp
      rw [satisfies_pure_sepConj] at hp'; obtain ⟨⟨_, hp_none⟩, hany⟩ := hp'
      have hp_goal : sf.mem ⊨
            ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ (anyHeap ∗ R) := by
        rw [satisfies_pure_sepConj]; exact ⟨hp_none, hany⟩
      simpa only [decPkSlotSpecPlaced, withLsCodeRoLoaded, sepConj_assoc] using hp_goal
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

def decPkSlotSpecBasePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
      s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = lsρ cliSessionVtSym ∧
      s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = lsρ cliIdentityVtSym ∧
      s.readReg64 .x7 = x.stores + 0xc8#64 ∧
      s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat ∧
      FitsEnv M lim st (DecPkEnv x)⌝ ∗
    slotFramePlaced A lim st x.toSlotCtx s ∗ preKeyMsgAt A.repAlloc x.msgG x.msgA x.msg ∗
    (s.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
    ((s.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
    ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
    ((s.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
    memRegion x.ret 48 ∗ stackAt s.sp stk
  post := (decPkSlotSpecPlaced A lim DecPkEnv S stk).post
  onPanic := (decPkSlotSpecPlaced A lim DecPkEnv S stk).onPanic

def decPkSlotSpecPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  { decPkSlotSpecBasePlaced A lim DecPkEnv S stk with
    pre := fun x s0 => (decPkSlotSpecBasePlaced A lim DecPkEnv S stk).pre x s0 ∗ ⌜CodeOk s0.mem⌝ }

abbrev decPkSlotSpecFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecPkGhost × M.σ) :=
  decPkSlotSpecPlacedOf (LibsignalFrozen lsmpl) A lim DecPkEnv S stk

/-- `LibsignalFrozen`-guarded budget-threaded wrapper-to-slot adapter for `decrypt_prekey`. -/
theorem dpSlot_ok_state_frozen_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (withLsFrozen lsmpl
        (cliDecryptPrekeySpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  refine subroutine_ok_of_outcome_map_placed (fun (x, st) => ⟨x.ret, x, st⟩) hw
    fun (x, st) R s0 hpre => ?_
  have ⟨hfr, hpre0⟩ :=
    extract_withLsFrozen (spec := decPkSlotSpecBasePlaced A lim DecPkEnv S stk) hpre
  dsimp only [decPkSlotSpecBasePlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hspatial⟩ := hpre0
  refine ⟨?_, ?_⟩
  · have htake : ((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).take 8 =
        [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
         s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
      simp only [dpSlotPollKStatePlaced, dpSlotArgsPlaced, List.take,
        hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    have hinv_sp : s0.mem ⊨ (dpSlotPollKStatePlaced A lim DecPkEnv B S).inv x st s0 ∗
          dpWordsAt s0.sp (((dpSlotPollKStatePlaced A lim DecPkEnv B S).args x).drop 8) ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
      unfold dpSlotPollKStatePlaced
      rw [dpSlotStack5_placed_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF0, hfOk, hdOk, hfit⟩,
        by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
    dsimp only [withLsFrozen]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    unfold cliDecryptPrekeySpecStateBudget; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono (sepConj_mono_left
          (dpSlotState_post_entails_placed A lim DecPkEnv B S stk x st s0 sf)) hpost⟩
    · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
      have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧
              S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗
          (anyHeap ∗ R) := by
        simpa only [withLsFrozen,
          cliDecryptPrekeySpecStateBudget, dpSlotPollKStatePlaced, sepConj_assoc] using hp
      rw [satisfies_pure_sepConj] at hp'
      obtain ⟨⟨_, hp_none⟩, hany⟩ := hp'
      have hp_goal : sf.mem ⊨
            ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ (anyHeap ∗ R) := by
        rw [satisfies_pure_sepConj]; exact ⟨hp_none, hany⟩
      simpa only [decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced,
        decPkSlotSpecPlaced, withLsCodeRoLoaded, sepConj_assoc] using hp_goal
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
