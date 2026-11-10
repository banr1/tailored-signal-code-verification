/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Common
public import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogue
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPaths
import LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplit
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoop
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKey
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeed
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKey
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKey
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePath
import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPath

/-!
# Seam Composition for `RatchetState::consume_message_key` from Callee Contracts

Composes the six segment theorems (`PrologueSplit`, `TakePath`, `TooFarPath`, `StoreLoop`,
`AdvanceEpilogue`, and `PanicPaths`) to prove `ConsumeMessageKeyMeetsSpec` (and placed
`CmkPlacedRunStmt` on Block 24) from the out-of-line callee contracts `FindIndexOk`, `HmacOk`, and
`GrowOneOk`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

/-- `RatchetState::consume_message_key` satisfies `ConsumeMessageKeyMeetsSpec` given `FindIndexOk`, `HmacOk`, and `GrowOneOk`. -/
theorem consume_message_key_run_of (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (hfind : FindIndexOk img F alloc A) (hhmac : HmacOk img F alloc)
    (hgrow : GrowOneOk img F alloc A) :
    ConsumeMessageKeyMeetsSpec F A alloc img :=
  cmk_of_seams hfind hhmac hgrow
    (prologueSplit_past_ok F A alloc img) (prologueSplit_tooFar_ok F A alloc img) (prologueSplit_advance_ok F A alloc img)
    (takePath_ok F A alloc img) (tooFarPath_ok F A alloc img) (storeLoop_iter_ok F A alloc img)
    (advanceEpilogue_ok F A alloc img)
    (loopNoChainPanic_ok F A alloc img) (epiloguePanic_ok F A alloc img)

private theorem set_set_same {α : Type} (xs : List α) (i : Nat) (a b : α) :
    (xs.set i a).set i b = xs.set i b := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem getElem?_set_self {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) (a : α) :
    (xs.set i a)[i]? = some a := by
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_set_self]

/-- Relocatable `cmkPlacedSpec` backed by `LibsignalRoLoaded`. -/
def cmkPlacedRoSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) : Spec ConsumeMessageKeyGhost :=
  { cmkPlacedSpec F A with
    pre := fun x s => (cmkPlacedSpec F A).pre x s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }

/-- Relocatable correctness statement for `RatchetState::consume_message_key` (Block 24). -/
def CmkPlacedRunStmt [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
  H "memmove" = some hookMemmove →
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base (cmkPlacedRoSpec F A)

/-- Compose the six placed segment contracts into `CmkPlacedRunStmt`. -/
theorem cmk_placed_of_seams [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hfind : FindIndexPlacedOk H A)
    (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A)
    (hs0_past : ProloguePastPlacedSpec F A H)
    (hs0_tooFar : PrologueTooFarPlacedSpec F A H)
    (hs0_adv : PrologueAdvanceEntryPlacedSpec F A H)
    (hs1 : TakePath.TakePathPlacedSpec F A H)
    (hs2 : TooFarPathPlacedSpec F A H)
    (hs3_iter : StoreLoopIterPlacedSpec F A H)
    (hs4 : AdvanceEpiloguePlacedSpec F A H)
    (hs5_loop : LoopNoChainPanicPlacedSpec F A H)
    (hs5_ep : EpiloguePanicPlacedSpec F A H) :
    CmkPlacedRunStmt F A H := by
  intro hA hmm
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre_ro hsp
  have hpre_split : s0.mem ⊨ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A).pre x s0 ∗ R) := by
    dsimp only [cmkPlacedRoSpec] at hpre_ro
    have heq : ((cmkPlacedSpec F A).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A).pre x s0 ∗ R) := by ac_rfl
    rwa [heq] at hpre_ro
  rw [satisfies_pure_sepConj] at hpre_split
  rcases hpre_split with ⟨hro, hpre⟩
  have hexp : H cmkExpectFailedSym = some Rust.panicked := hA.2.2.2.2.1
  have hovf : H cmkPanicAddOverflowSym = some Rust.panicked := hA.2.2.2.2.2
  suffices h_out : reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s0 from
    h_out.mono_outcome fun _ hout => hout
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hratchet : s0.mem ⊨ ratchetAt A x.self x.G x.st ∗
      (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
       ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStack ∗ A.pool ∗ R) := by
    simp only [cmkPlacedSpec, withLsCodeLoaded] at hpre
    exact Satisfies.of_eq hpre
  have hok : ChainsOk x.st := chainsOk_of_ratchetAt hratchet
  by_cases hlt : x.counter < x.ck.index
  · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
      hs0_past x R s0 hpc hrun hsp hpre hlt hL
    exact reaches_outcome_steps hsteps1 (hs1 hA hmm hfind x R s0 s1 hlt hst1)
  · have hle : x.ck.index ≤ x.counter := BitVec.not_lt.mp hlt
    by_cases hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps
    · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
        hs0_adv x R s0 hpc hrun hsp hpre hle hj hL
      have hL1 := hsteps1.codeLoaded hL
      by_cases hck_lt : x.ck.index < x.counter
      · simp only [hck_lt, ↓reduceIte] at hst1
        cases hci : x.st.findReceiverChainIndex x.their with
        | none =>
          have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, Or.inr hci⟩
          exact reaches_outcome_steps hsteps1
            (hs5_loop hA hfind hhmac x R s0 s1 hck_lt hci hpan_model hst1)
        | some ci =>
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | ⟨hpan2, hq2⟩⟩ :=
            storeLoop_placed_of_iter hs3_iter hA hmm hfind hhmac hgrow x x.G x.st x.ck ci ch R s0 s1
              hck_lt hci hch hst1 hL1
          · refine reaches_outcome_steps (hsteps1.trans hsteps2) ?_
            let n := (x.counter - x.ck.index).toNat
            let ckc := chainStepN F n x.ck
            let chc : ReceiverChain :=
              { ch with messageKeys := (skippedKeys F n x.ck ++ ch.messageKeys).take maxMessageKeys }
            let stc : RatchetState := { x.st with receiverChains := x.st.receiverChains.set ci chc }
            by_cases hc_max : x.counter = BitVec.allOnes 32
            · have hpan_model : (x.model F).1 = .error .panic :=
                (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
                  ⟨hle, hj, Or.inl hc_max⟩
              exact hs5_ep hexp hovf hfind hhmac x G2 stc ckc R s0 s2 hck_end (Or.inl hc_max) hpan_model hst2
            · obtain ⟨ch', hch', hmodel⟩ :=
                consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
              rw [hch] at hch'; cases hch'
              have hci_lt : ci < x.st.receiverChains.length := (List.getElem?_eq_some_iff.mp hch).1
              have hchc_get : stc.receiverChains[ci]? = some chc := getElem?_set_self hci_lt chc
              have hci_stc : stc.findReceiverChainIndex x.their = some ci := by
                rw [findReceiverChainIndex_set x.st x.their ci chc ⟨ch, hch, rfl⟩]
                exact hci
              have hm1 : (x.model F).1 = .ok (ckc.messageKeys F) := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
              have hm2 : (x.model F).2 =
                  { stc with
                    receiverChains := stc.receiverChains.set ci
                      { chc with chainKey := some (chainStepN F 1 ckc) } } := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
                dsimp only [stc, chc]
                rw [set_set_same]
              have htouch : x.touched F = some ci := by
                unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
              exact hs4 hA hfind hhmac x G2 stc ckc ci chc R s0 s2
                hck_end hc_max hci_stc hchc_get hG2 hm1 hm2 htouch hst2
          · exact reaches_outcome_steps (hsteps1.trans hsteps2) (reaches_outcome_refl_panic hpan2 hq2)
      · simp only [hck_lt, ↓reduceIte] at hst1
        have hck_eq : x.ck.index = x.counter :=
          BitVec.le_antisymm hle (BitVec.not_lt.mp hck_lt)
        by_cases hpan_cond : x.counter = BitVec.allOnes 32 ∨ x.st.findReceiverChainIndex x.their = none
        · have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, hpan_cond⟩
          exact reaches_outcome_steps hsteps1
            (hs5_ep hexp hovf hfind hhmac x x.G x.st x.ck R s0 s1 hck_eq hpan_cond hpan_model hst1)
        · rw [not_or] at hpan_cond
          rcases hpan_cond with ⟨hc_max, hci_ne⟩
          obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hci_ne
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨ch', hch', hmodel⟩ :=
            consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
          rw [hch] at hch'; cases hch'
          have hn0 : (x.counter - x.ck.index).toNat = 0 := by rw [hck_eq, BitVec.sub_self]; rfl
          have htake : ch.messageKeys.take maxMessageKeys = ch.messageKeys :=
            List.take_of_length_le (hok ch (List.mem_of_getElem? hch)).1
          have hm1 : (x.model F).1 = .ok (x.ck.messageKeys F) := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]; simp [hn0, chainStepN]
          have hm2 : (x.model F).2 =
              { x.st with
                receiverChains := x.st.receiverChains.set ci
                  { ch with chainKey := some (chainStepN F 1 x.ck) } } := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]
            simp [hn0, chainStepN, skippedKeys, htake]
          have htouch : x.touched F = some ci := by
            unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
          exact reaches_outcome_steps hsteps1
            (hs4 hA hfind hhmac x x.G x.st x.ck ci ch R s0 s1
              hck_eq hc_max hci hch (RatchetGhost.AgreeExcept.refl x.G (some ci))
              hm1 hm2 htouch hst1)
    · have hj_gt : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat := Nat.lt_of_not_ge hj
      obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
        hs0_tooFar x R s0 hpc hrun hsp hpre hle hL
      have hro1 : LibsignalRoLoaded lsmpl s1.mem :=
        libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen
      have hst1_ro : CmkTooFarState_placed A x ((lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s1 := by
        rcases hst1 with ⟨hpc1, hframe1, hregs1, hmem1⟩
        refine ⟨hpc1, hframe1, hregs1, ?_⟩
        have hm := TooFarPath.rodata_placed_tooFarInFuture_intro hro1 hmem1
        have heq : (lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ (cmkPreLoopHeap_placed A x s0 ∗ R) =
            cmkPreLoopHeap_placed A x s0 ∗ ((lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) := by ac_rfl
        rwa [heq] at hm
      exact reaches_outcome_steps hsteps1 (hs2 hA x R s0 s1 hle hj_gt hst1_ro)

/-- Block 24 satisfies `CmkPlacedRunStmt` given `FindIndexPlacedOk`, `HmacPlacedOk`, and `GrowOnePlacedOk`. -/
theorem consume_message_key_placed_run_of [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A) :
    CmkPlacedRunStmt F A H :=
  cmk_placed_of_seams hfind hhmac hgrow
    (prologueSplit_past_placed_ok F A H) (prologueSplit_tooFar_placed_ok F A H) (prologueSplit_advance_placed_ok F A H)
    (takePath_placed_ok F A H) (tooFarPath_placed_ok F A H) (storeLoop_iter_placed_ok F A H)
    (advanceEpilogue_placed_ok F A H)
    (loopNoChainPanic_placed_ok F A H) (epiloguePanic_placed_ok F A H)

theorem storeLoop_iter_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    StoreLoopIterPlacedRoSpec F A H :=
  StoreLoop.storeLoop_iter_placed_ro_of_parts
    (StoreLoop.deriveSeed_placed_ro_ok F A H)
    (StoreLoop.insertKey_placed_ok F A H)
    StoreLoop.evictOldestKey_placed_ok
    (StoreLoop.advanceChainKey_placed_ro_ok F A H)

theorem cmk_placed_ro_of_seams [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hfind : FindIndexPlacedOk H A)
    (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A)
    (hs0_past : ProloguePastPlacedSpec F A H)
    (hs0_tooFar : PrologueTooFarPlacedSpec F A H)
    (hs0_adv : PrologueAdvanceEntryPlacedSpec F A H)
    (hs1 : TakePath.TakePathPlacedSpec F A H)
    (hs2 : TooFarPathPlacedSpec F A H)
    (hs3_iter : StoreLoopIterPlacedRoSpec F A H)
    (hs4 : AdvanceEpiloguePlacedRoSpec F A H)
    (hs5_loop : LoopNoChainPanicPlacedRoSpec F A H)
    (hs5_ep : EpiloguePanicPlacedRoSpec F A H) :
    CmkPlacedRunStmt F A H := by
  intro hA hmm
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre_ro hsp
  have hpre_split : s0.mem ⊨ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A).pre x s0 ∗ R) := by
    dsimp only [cmkPlacedRoSpec] at hpre_ro
    have heq : ((cmkPlacedSpec F A).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A).pre x s0 ∗ R) := by ac_rfl
    rwa [heq] at hpre_ro
  rw [satisfies_pure_sepConj] at hpre_split
  rcases hpre_split with ⟨hro, hpre⟩
  have hexp : H cmkExpectFailedSym = some Rust.panicked := hA.2.2.2.2.1
  have hovf : H cmkPanicAddOverflowSym = some Rust.panicked := hA.2.2.2.2.2
  suffices h_out : reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s0 from
    h_out.mono_outcome fun _ hout => hout
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hratchet : s0.mem ⊨ ratchetAt A x.self x.G x.st ∗
      (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
       ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStack ∗ A.pool ∗ R) := by
    simp only [cmkPlacedSpec, withLsCodeLoaded] at hpre
    exact Satisfies.of_eq hpre
  have hok : ChainsOk x.st := chainsOk_of_ratchetAt hratchet
  by_cases hlt : x.counter < x.ck.index
  · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
      hs0_past x R s0 hpc hrun hsp hpre hlt hL
    exact reaches_outcome_steps hsteps1 (hs1 hA hmm hfind x R s0 s1 hlt hst1)
  · have hle : x.ck.index ≤ x.counter := BitVec.not_lt.mp hlt
    by_cases hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps
    · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
        hs0_adv x R s0 hpc hrun hsp hpre hle hj hL
      have hL1 := hsteps1.codeLoaded hL
      have hro1 : LibsignalRoLoaded lsmpl s1.mem :=
        libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen
      by_cases hck_lt : x.ck.index < x.counter
      · simp only [hck_lt, ↓reduceIte] at hst1
        cases hci : x.st.findReceiverChainIndex x.their with
        | none =>
          have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, Or.inr hci⟩
          exact reaches_outcome_steps hsteps1
            (hs5_loop hA hfind hhmac x R s0 s1 hck_lt hci hpan_model hst1 hro1)
        | some ci =>
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | ⟨hpan2, hq2⟩⟩ :=
            storeLoop_placed_ro_of_iter hs3_iter hA hmm hfind hhmac hgrow x x.G x.st x.ck ci ch R s0 s1
              hck_lt hci hch hst1 hL1 hro1
          · refine reaches_outcome_steps (hsteps1.trans hsteps2) ?_
            have hro2 : LibsignalRoLoaded lsmpl s2.mem :=
              libsignalRoLoaded_of_keepsFrozen hro1 hsteps2.keepsFrozen
            let n := (x.counter - x.ck.index).toNat
            let ckc := chainStepN F n x.ck
            let chc : ReceiverChain :=
              { ch with messageKeys := (skippedKeys F n x.ck ++ ch.messageKeys).take maxMessageKeys }
            let stc : RatchetState := { x.st with receiverChains := x.st.receiverChains.set ci chc }
            by_cases hc_max : x.counter = BitVec.allOnes 32
            · have hpan_model : (x.model F).1 = .error .panic :=
                (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
                  ⟨hle, hj, Or.inl hc_max⟩
              exact hs5_ep hexp hovf hfind hhmac x G2 stc ckc R s0 s2 hck_end (Or.inl hc_max) hpan_model hst2 hro2
            · obtain ⟨ch', hch', hmodel⟩ :=
                consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
              rw [hch] at hch'; cases hch'
              have hci_lt : ci < x.st.receiverChains.length := (List.getElem?_eq_some_iff.mp hch).1
              have hchc_get : stc.receiverChains[ci]? = some chc := getElem?_set_self hci_lt chc
              have hci_stc : stc.findReceiverChainIndex x.their = some ci := by
                rw [findReceiverChainIndex_set x.st x.their ci chc ⟨ch, hch, rfl⟩]; exact hci
              have hm1 : (x.model F).1 = .ok (ckc.messageKeys F) := by unfold ConsumeMessageKeyGhost.model; rw [hmodel]
              have hm2 : (x.model F).2 =
                  { stc with
                    receiverChains := stc.receiverChains.set ci
                      { chc with chainKey := some (chainStepN F 1 ckc) } } := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]; dsimp only [stc, chc]; rw [set_set_same]
              have htouch : x.touched F = some ci := by unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
              exact hs4 hA hfind hhmac x G2 stc ckc ci chc R s0 s2
                hck_end hc_max hci_stc hchc_get hG2 hm1 hm2 htouch hst2 hro2
          · exact reaches_outcome_steps (hsteps1.trans hsteps2) (reaches_outcome_refl_panic hpan2 hq2)
      · simp only [hck_lt, ↓reduceIte] at hst1
        have hck_eq : x.ck.index = x.counter := BitVec.le_antisymm hle (BitVec.not_lt.mp hck_lt)
        by_cases hpan_cond : x.counter = BitVec.allOnes 32 ∨ x.st.findReceiverChainIndex x.their = none
        · have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr ⟨hle, hj, hpan_cond⟩
          exact reaches_outcome_steps hsteps1
            (hs5_ep hexp hovf hfind hhmac x x.G x.st x.ck R s0 s1 hck_eq hpan_cond hpan_model hst1 hro1)
        · rw [not_or] at hpan_cond
          rcases hpan_cond with ⟨hc_max, hci_ne⟩
          obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hci_ne
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨ch', hch', hmodel⟩ :=
            consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
          rw [hch] at hch'; cases hch'
          have hn0 : (x.counter - x.ck.index).toNat = 0 := by rw [hck_eq, BitVec.sub_self]; rfl
          have htake : ch.messageKeys.take maxMessageKeys = ch.messageKeys :=
            List.take_of_length_le (hok ch (List.mem_of_getElem? hch)).1
          have hm1 : (x.model F).1 = .ok (x.ck.messageKeys F) := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]; simp [hn0, chainStepN]
          have hm2 : (x.model F).2 =
              { x.st with
                receiverChains := x.st.receiverChains.set ci
                  { ch with chainKey := some (chainStepN F 1 x.ck) } } := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]; simp [hn0, chainStepN, skippedKeys, htake]
          have htouch : x.touched F = some ci := by unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
          exact reaches_outcome_steps hsteps1
            (hs4 hA hfind hhmac x x.G x.st x.ck ci ch R s0 s1
              hck_eq hc_max hci hch (RatchetGhost.AgreeExcept.refl x.G (some ci))
              hm1 hm2 htouch hst1 hro1)
    · have hj_gt : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat := Nat.lt_of_not_ge hj
      obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
        hs0_tooFar x R s0 hpc hrun hsp hpre hle hL
      have hro1 : LibsignalRoLoaded lsmpl s1.mem :=
        libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen
      have hst1_ro : CmkTooFarState_placed A x ((lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s1 := by
        rcases hst1 with ⟨hpc1, hframe1, hregs1, hmem1⟩
        refine ⟨hpc1, hframe1, hregs1, ?_⟩
        have hm := TooFarPath.rodata_placed_tooFarInFuture_intro hro1 hmem1
        have heq : (lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ (cmkPreLoopHeap_placed A x s0 ∗ R) =
            cmkPreLoopHeap_placed A x s0 ∗ ((lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) := by ac_rfl
        rwa [heq] at hm
      exact reaches_outcome_steps hsteps1 (hs2 hA x R s0 s1 hle hj_gt hst1_ro)

theorem consume_message_key_placed_ro_run_of [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A) :
    CmkPlacedRunStmt F A H :=
  cmk_placed_ro_of_seams hfind hhmac hgrow
    (prologueSplit_past_placed_ok F A H) (prologueSplit_tooFar_placed_ok F A H) (prologueSplit_advance_placed_ok F A H)
    (takePath_placed_ok F A H) (tooFarPath_placed_ok F A H) (storeLoop_iter_placed_ro_ok F A H)
    (advanceEpilogue_placed_ro_ok F A H)
    (loopNoChainPanic_placed_ro_ok F A H) (epiloguePanic_placed_ro_ok F A H)

end CryptoVerification.LibsignalSession
