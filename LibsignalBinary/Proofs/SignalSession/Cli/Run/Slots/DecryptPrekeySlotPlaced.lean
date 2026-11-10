/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlot
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `decrypt_prekey` Slot Adapter

Relocatable `[LibsignalPlacement]` definitions (`slotFramePlaced`, `decPkSlotSpecPlaced`,
`dpSlotPollKStatePlaced`) and wrapper-to-slot adapters (`dpSlot_ok_state_placed`,
`dpSlot_ok_state_frozen_placed`) for `signal_session_handshake::decrypt_prekey`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs (dpWordsAt)

/-- Relocatable `[LibsignalPlacement]` counterpart of `RunCompose.slotFrame`. -/
def slotFramePlaced [LibsignalPlacement] (A : RustAlloc) (x : SlotCtx) : SepProp :=
  ⌜x.coins.length < 2 ^ 63⌝ ∗
  storesAt A x.stores StoresGhost.opened ∗ protocolAddressAt A x.peer x.peerA ∗
    protocolAddressAt A x.me x.meA ∗ coinsInstalledPlaced x.coinsP x.coins ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool

/-- Relocatable `[LibsignalPlacement]` `decrypt_prekey` slot contract carrying
`withLsCodeRoLoaded lsmpl`. -/
def decPkSlotSpecPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    Spec DecPkGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
          s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = lsρ cliSessionVtSym ∧
          s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = lsρ cliIdentityVtSym ∧
          s.readReg64 .x7 = x.stores + 0xc8#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat⌝ ∗
        slotFramePlaced A x.toSlotCtx ∗ preKeyMsgAt A x.msgG x.msgA x.msg ∗
        (s.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
        ((s.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
        ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
        ((s.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
        memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
          ⌜slotTrace s0 sf ∧
            slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ decResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          preKeyMsgAt A x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((s0.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }

def decPkSlotSpecBasePlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    Spec DecPkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
      s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = lsρ cliSessionVtSym ∧
      s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = lsρ cliIdentityVtSym ∧
      s.readReg64 .x7 = x.stores + 0xc8#64 ∧
      s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat⌝ ∗
    slotFramePlaced A x.toSlotCtx ∗ preKeyMsgAt A x.msgG x.msgA x.msg ∗
    (s.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
    ((s.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
    ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
    ((s.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
    memRegion x.ret 48 ∗ stackAt s.sp stk
  post := (decPkSlotSpecPlaced A S stk).post
  onPanic := (decPkSlotSpecPlaced A S stk).onPanic

def decPkSlotSpecPlacedOf [LibsignalPlacement] (CodeOk : Memory → Prop)
    (A : RustAlloc) (S : RunSem) (stk : Nat) : Spec DecPkGhost :=
  { decPkSlotSpecBasePlaced A S stk with
    pre := fun x s0 => (decPkSlotSpecBasePlaced A S stk).pre x s0 ∗ ⌜CodeOk s0.mem⌝ }

abbrev decPkSlotSpecFrozenPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    Spec DecPkGhost :=
  decPkSlotSpecPlacedOf (LibsignalFrozen lsmpl) A S stk

example [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    decPkSlotSpecPlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A S stk =
      decPkSlotSpecPlaced A S stk := rfl

example [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    decPkSlotSpecFrozenPlaced A S stk =
      withLsFrozen lsmpl (decPkSlotSpecBasePlaced A S stk) := rfl

/-- The 13 ABI argument words passed to `decrypt_prekey` under `[LibsignalPlacement]`. -/
def dpSlotArgsPlaced [LibsignalPlacement] (x : DecPkGhost) : List (BitVec 64) :=
  [ x.msgA, x.peerA, x.meA, x.stores + 240#64, lsρ cliSessionVtSym, x.stores,
    lsρ cliIdentityVtSym, x.stores + 200#64, lsρ cliPreKeyVtSym, x.stores + 80#64,
    lsρ cliSignedPreKeyVtSym, x.stores + 120#64, lsρ cliKyberPreKeyVtSym ]

/-- Relocatable `[LibsignalPlacement]` state-coupled `RunProofs.DpPollKState`. -/
def dpSlotPollKStatePlaced [LibsignalPlacement] (A : RustAlloc) (B : RunBudgets) (S : RunSem) :
    RunProofs.DpPollKState where
  Ghost := DecPkGhost
  args := dpSlotArgsPlaced
  inv := fun x fs _ => ⌜fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.decPkOk x.F x.peer.val x.me.val x.msg⌝ ∗
      slotFramePlaced A x.toSlotCtx ∗ preKeyMsgAt A x.msgG x.msgA x.msg
  res := fun x fs0 tr0 fs1 tr1 ws =>
    ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
      ⌜slotTraceFT fs0 tr0 fs1 tr1 ∧
        slotOutTr (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e tr0 tr1⌝ ∗
        storesAt A x.stores g' ∗ dpResHeap A ws e ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        preKeyMsgAt A x.msgG x.msgA x.msg ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ anyHeap
  panics := fun x => S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none
  need := dpPollNeed B

abbrev K₀_statePlaced [LibsignalPlacement] (B : RunBudgets) (S : RunSem) :
    RunProofs.DpPollKState :=
  dpSlotPollKStatePlaced E2E.HooksE.A0 B S

section PlacedConsequenceHelpers

private theorem sepConj_pure_of_true_placed {φ : Prop} (P : SepProp) (hφ : φ) : P ∗ ⌜φ⌝ = P := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩; rw [hEq, pure_true, sepConj_emp]

private theorem pure_sepConj_eq_of_true_placed {φ : Prop} (P : SepProp) (hφ : φ) : ⌜φ⌝ ∗ P = P := by
  rw [sepConj_comm, sepConj_pure_of_true_placed P hφ]

private theorem ent_pure_left_placed {φ : Prop} {P Q : SepProp} (h : φ → (P ⊢ Q)) : ⌜φ⌝ ∗ P ⊢ Q :=
  Entails.pure_left h

private theorem ent_pure_right_placed {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_eq_of_true_placed Q hφ]; exact h

private theorem ent_bind_placed {α : Type} {A R Q : SepProp} {P : α → SepProp}
    (hA : A ⊢ ∃∗ x, P x) (hk : ∀ x, P x ∗ R ⊢ Q) : A ∗ R ⊢ Q := by
  refine Entails.trans (sepConj_mono_left hA) ?_
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

private theorem dpSlotState_post_entails_placed [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (S : RunSem) (stk : Nat) (x : DecPkGhost) (s0 sf : State) :
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (RunProofs.cliDecryptPrekeySpecState (dpSlotPollKStatePlaced A B S) stk)).post ⟨x.ret, x⟩ s0 sf ⊢
      (decPkSlotSpecPlaced A S stk).post x s0 sf := by
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  unfold RunProofs.cliDecryptPrekeySpecState; refine ent_bind_placed (Entails.refl _) fun ws => ?_
  rw [sepConj_assoc]; refine ent_pure_left_placed fun _ => ?_
  have r1 : (dpWordsAt x.ret ws ∗
          (dpSlotPollKStatePlaced A B S).res x s0.fs s0.trace sf.fs sf.trace ws) ∗
        (dpWordsAt s0.sp (((dpSlotPollKStatePlaced A B S).args x).drop 8) ∗ stackAt s0.sp stk) =
      (dpSlotPollKStatePlaced A B S).res x s0.fs s0.trace sf.fs sf.trace ws ∗ (dpWordsAt x.ret ws ∗
          dpWordsAt s0.sp ((dpSlotArgsPlaced x).drop 8) ∗ stackAt s0.sp stk) := by ac_rfl
  rw [r1]; unfold dpSlotPollKStatePlaced; refine ent_bind_placed (Entails.refl _) fun g' => ?_
  refine ent_bind_placed (Entails.refl _) fun e => ?_
  rw [sepConj_assoc]; refine ent_pure_left_placed fun ⟨htrace, hout⟩ => ?_
  rw [dpSlotStack5_placed_eq]
  have r2 : (storesAt A x.stores g' ∗ dpResHeap A ws e ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        preKeyMsgAt A x.msgG x.msgA x.msg ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ anyHeap) ∗
          (dpWordsAt x.ret ws ∗
          ((s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
            ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
            ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
            ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym)) ∗ stackAt s0.sp stk) =
      (dpWordsAt x.ret ws ∗ dpResHeap A ws e) ∗ (storesAt A x.stores g' ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          preKeyMsgAt A x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ lsρ cliPreKeyVtSym) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 80#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((s0.sp + 24#64) ↦₆₄ (x.stores + 120#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap) := by ac_rfl
  rw [r2]; refine Entails.trans (sepConj_mono_left (dpWords_resHeap_entails_decResAt A x.ret ws e)) ?_
  unfold decPkSlotSpecPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  refine Entails.sepExists_right g' (Entails.sepExists_right e ?_)
  exact ent_pure_right_placed ⟨htrace, hout⟩ (Entails.of_eq (by ac_rfl))

end PlacedConsequenceHelpers

/-- Relocatable `[LibsignalPlacement]` state-coupled wrapper-to-slot adapter for `decrypt_prekey`. -/
theorem dpSlot_ok_state_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (RunProofs.cliDecryptPrekeySpecState (dpSlotPollKStatePlaced A B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecPlaced A S stk) := by
  refine subroutine_ok_of_outcome_map_placed (fun x => ⟨x.ret, x⟩) hw fun x R s0 hpre => ?_
  have ⟨hrocl, hpre0⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [decPkSlotSpecPlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le⟩, hspatial⟩ := hpre0
  refine ⟨?_, ?_⟩
  · have htake : ((dpSlotPollKStatePlaced A B S).args x).take 8 =
        [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
         s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
      simp only [dpSlotPollKStatePlaced, dpSlotArgsPlaced, List.take,
        hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    have hinv_sp : s0.mem ⊨ (dpSlotPollKStatePlaced A B S).inv x s0.fs s0.trace ∗
          dpWordsAt s0.sp (((dpSlotPollKStatePlaced A B S).args x).drop 8) ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
      unfold dpSlotPollKStatePlaced
      rw [dpSlotStack5_placed_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF0, hfOk, hdOk⟩,
        by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hrocl, ?_⟩
    unfold RunProofs.cliDecryptPrekeySpecState; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono (sepConj_mono_left (dpSlotState_post_entails_placed A B S stk x s0 sf)) hpost⟩
    · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
      have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨
              S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none)⌝ ∗
          (anyHeap ∗ R) := by
        simpa only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
          RunProofs.cliDecryptPrekeySpecState, dpSlotPollKStatePlaced, sepConj_assoc] using hp
      rw [satisfies_pure_sepConj] at hp'; obtain ⟨⟨_, hp_or⟩, hany⟩ := hp'
      have hp_goal : sf.mem ⊨ ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none ∨
            allocFailedIn s0 sf⌝ ∗ (anyHeap ∗ R) := by
        rw [satisfies_pure_sepConj]; exact ⟨hp_or.symm, hany⟩
      simpa only [decPkSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        sepConj_assoc] using hp_goal
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem decPk_slot_ok_state_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hstk : decPkNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (RunProofs.cliDecryptPrekeySpecState (K₀_statePlaced B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  dpSlot_ok_state_placed B S stk hstk hstk64 hw

/-- `LibsignalFrozen`-guarded state-coupled wrapper-to-slot adapter for `decrypt_prekey`. -/
theorem dpSlot_ok_state_frozen_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (B : RunBudgets) (S : RunSem) (stk : Nat)
    (_hstk : decPkNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (withLsFrozen lsmpl
        (RunProofs.cliDecryptPrekeySpecState (dpSlotPollKStatePlaced A B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecFrozenPlaced A S stk) := by
  refine subroutine_ok_of_outcome_map_placed (fun x => ⟨x.ret, x⟩) hw fun x R s0 hpre => ?_
  have ⟨hfr, hpre0⟩ := extract_withLsFrozen (spec := decPkSlotSpecBasePlaced A S stk) hpre
  dsimp only [decPkSlotSpecBasePlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le⟩, hspatial⟩ := hpre0
  refine ⟨?_, ?_⟩
  · have htake : ((dpSlotPollKStatePlaced A B S).args x).take 8 =
        [s0.readReg64 .x0, s0.readReg64 .x1, s0.readReg64 .x2, s0.readReg64 .x3,
         s0.readReg64 .x4, s0.readReg64 .x5, s0.readReg64 .x6, s0.readReg64 .x7] := by
      simp only [dpSlotPollKStatePlaced, dpSlotArgsPlaced, List.take,
        hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7]
    have hinv_sp : s0.mem ⊨ (dpSlotPollKStatePlaced A B S).inv x s0.fs s0.trace ∗
          dpWordsAt s0.sp (((dpSlotPollKStatePlaced A B S).args x).drop 8) ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ R := by
      unfold dpSlotPollKStatePlaced
      rw [dpSlotStack5_placed_eq, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF0, hfOk, hdOk⟩,
        by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hspatial⟩
    dsimp only [withLsFrozen]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    unfold RunProofs.cliDecryptPrekeySpecState; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, rfl, htake, hsp_le⟩,
      by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_sp⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
    · exact Or.inl ⟨hret, hcc,
        Satisfies.mono (sepConj_mono_left (dpSlotState_post_entails_placed A B S stk x s0 sf)) hpost⟩
    · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
      have hp' : sf.mem ⊨ ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨
              S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none)⌝ ∗
          (anyHeap ∗ R) := by
        simpa only [withLsFrozen,
          RunProofs.cliDecryptPrekeySpecState, dpSlotPollKStatePlaced, sepConj_assoc] using hp
      rw [satisfies_pure_sepConj] at hp'; obtain ⟨⟨_, hp_or⟩, hany⟩ := hp'
      have hp_goal : sf.mem ⊨ ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none ∨
            allocFailedIn s0 sf⌝ ∗ (anyHeap ∗ R) := by
        rw [satisfies_pure_sepConj]; exact ⟨hp_or.symm, hany⟩
      simpa only [decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced,
        decPkSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sepConj_assoc] using hp_goal
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem decPk_slot_ok_state_frozen_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hstk : decPkNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hw : subroutine_ok prog entry
      (withLsFrozen lsmpl
        (RunProofs.cliDecryptPrekeySpecState (K₀_statePlaced B S) stk))) :
    subroutine_ok prog entry (decPkSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) :=
  dpSlot_ok_state_frozen_placed B S stk hstk hstk64 hw

end CryptoVerification.SignalSession.Cli.RunCompose
