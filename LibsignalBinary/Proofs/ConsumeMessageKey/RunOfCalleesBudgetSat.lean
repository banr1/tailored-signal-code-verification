/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CoreBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplitBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKeyBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeedBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKeyBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKeyBudgetSat
import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.CoreBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `HookSat` Sibling of `RunOfCalleesBudget`
(`LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat`)

Additive `HookSat` sibling of `LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget`,
weakening `H "memmove" = some hookMemmove` to
`HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096)` across:
- `storeLoop_iter_placed_ok_sat` / `storeLoop_iter_placed_ro_ok_sat`
- `cmk_placed_of_seams_sat` / `consume_message_key_placed_run_of_sat`
- `cmk_placed_ro_of_seams_sat` / `consume_message_key_placed_ro_run_of_sat`
with corollaries for unbounded `sessionMemmoveBudgetSpec 4096` and exact `hookMemmove`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (
  ChainKey RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPl_24 libsignalRoLoaded_of_keepsFrozen
  lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (
  RatchetGhost chainKeyBytes msgTypeByte ratchetAt tooFarInFutureStr
)
open CryptoVerification.SessionModel (
  ChainsOk chainStepN consumeMessageKey_advance consumeMessageKey_panic_iff
  findReceiverChainIndex_set skippedKeys
)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost chainsOk_of_ratchetAt cmkEpiloguePC_placed cmkExpectFailedSym
  cmkLoopPC_placed cmkPanicAddOverflowSym cmkPreLoopHeap_placed cmkStack
  findReceiverChainIndex_some_getElem?
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemmoveBudgetSpec
)
open CryptoVerification.LibsignalSession.TakePath (cmkMemmoveSym)
open CryptoVerification.LibsignalSession.TooFarPath (
  cmkTooFarStrSym rodata_placed_tooFarInFuture_intro
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOnePlacedOk)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  AdvanceEpiloguePlacedRoSpec AdvanceEpiloguePlacedSpec
  CmkAllocHooks CmkEnv CmkEpilogueEvs CmkLoopState_placed CmkTooFarState_placed
  EpiloguePanicPlacedRoSpec EpiloguePanicPlacedSpec
  FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk
  LoopNoChainPanicPlacedRoSpec LoopNoChainPanicPlacedSpec
  PrologueAdvanceEntryPlacedSpec ProloguePastPlacedSpec PrologueTooFarPlacedSpec
  TooFarPathPlacedSpec cmkPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (
  CmkPlacedRunStmt cmkPlacedRoSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CoreBudgetSat (
  TakePathPlacedSpecSat takePath_placed_ok_thm_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.PrologueSplitBudget (
  prologueSplit_advance_placed_ok prologueSplit_past_placed_ok prologueSplit_tooFar_placed_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.CoreBudget (tooFarPath_placed_ok')
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueBudget (
  advanceEpilogue_placed_ok advanceEpilogue_placed_ro_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsBudget (
  epiloguePanic_placed_ok epiloguePanic_placed_ro_ok
  loopNoChainPanic_placed_ok loopNoChainPanic_placed_ro_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  cmkEnv_advance_chain_iff cmkLoopAdvanceEvs_zero_iff
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudgetSat (
  StoreLoopIterPlacedRoSpecSat StoreLoopIterPlacedSpecSat
  storeLoop_iter_placed_of_parts_sat storeLoop_iter_placed_ro_of_parts_sat
  storeLoop_placed_of_iter_sat storeLoop_placed_ro_of_iter_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeedBudget (
  deriveSeed_placed_ok deriveSeed_placed_ro_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKeyBudgetSat (
  insertKey_placed_ok_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKeyBudget (
  evictOldestKey_placed_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKeyBudget (
  advanceChainKey_placed_ok advanceChainKey_placed_ro_ok
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (
  hookSat_sessionMemmoveBoundedBudget_of_exact
  hookSat_sessionMemmoveBoundedBudget_of_unbounded
  sessionMemmoveBoundedBudgetSpec
)

private theorem set_set_same {α : Type} (xs : List α) (i : Nat) (a b : α) :
    (xs.set i a).set i b = xs.set i b := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem getElem?_set_self {α : Type} {xs : List α} {i : Nat}
    (hi : i < xs.length) (a : α) :
    (xs.set i a)[i]? = some a := by
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_set_self]

/-- Budget-threaded relocatable headline statement for `RatchetState::consume_message_key`
    (Block `24`) under `HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096)`. -/
@[expose] def CmkPlacedRunStmtSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
  HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096) →
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base (cmkPlacedRoSpec F A lim)

/-- Variant of `CmkPlacedRunStmtSat` taking unbounded `sessionMemmoveBudgetSpec 4096`. -/
@[expose] def CmkPlacedRunStmtUnboundedSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
  HookSat H "memmove" (sessionMemmoveBudgetSpec 4096) →
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base (cmkPlacedRoSpec F A lim)

theorem storeLoop_iter_placed_ok_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    StoreLoopIterPlacedSpecSat F A lim H :=
  storeLoop_iter_placed_of_parts_sat
    (deriveSeed_placed_ok F A lim H)
    (insertKey_placed_ok_sat F A lim H)
    evictOldestKey_placed_ok
    (advanceChainKey_placed_ok F A lim H)

theorem storeLoop_iter_placed_ro_ok_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    StoreLoopIterPlacedRoSpecSat F A lim H :=
  storeLoop_iter_placed_ro_of_parts_sat
    (deriveSeed_placed_ro_ok F A lim H)
    (insertKey_placed_ok_sat F A lim H)
    evictOldestKey_placed_ok
    (advanceChainKey_placed_ro_ok F A lim H)

/-- **Top-level composition of S0–S5 (placed, budget-threaded, `HookSat` on `memmove`).** -/
theorem cmk_placed_of_seams_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hfind : FindIndexPlacedOk H A)
    (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A lim)
    (hs0_past : ProloguePastPlacedSpec F A lim H)
    (hs0_tooFar : PrologueTooFarPlacedSpec F A lim H)
    (hs0_adv : PrologueAdvanceEntryPlacedSpec F A lim H)
    (hs1 : TakePathPlacedSpecSat F A lim H)
    (hs2 : TooFarPathPlacedSpec F A lim H)
    (hs3_iter : StoreLoopIterPlacedSpecSat F A lim H)
    (hs4 : AdvanceEpiloguePlacedSpec F A lim H)
    (hs5_loop : LoopNoChainPanicPlacedSpec F A lim H)
    (hs5_ep : EpiloguePanicPlacedSpec F A lim H) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  have hmm_s1 : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack) := by
    simpa [cmkMemmoveSym, allocHookStack] using hmm
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre_ro hsp
  have hpre_split :
      s0.mem ⊨ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) := by
    dsimp only [cmkPlacedRoSpec] at hpre_ro
    have heq :
        ((cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗ R =
          ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) := by
      sep_ac_rfl
    rwa [heq] at hpre_ro
  rw [satisfies_pure_sepConj] at hpre_split
  rcases hpre_split with ⟨hro, hpre⟩
  have hexp : H cmkExpectFailedSym = some Rust.panicked := hA.2.2.2.2.1
  have hovf : H cmkPanicAddOverflowSym = some Rust.panicked := hA.2.2.2.2.2
  suffices h_out :
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s0 from
    h_out.mono_outcome fun _ hout => hout
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hratchet : s0.mem ⊨ ratchetAt (A.atState lim st_init s0) x.self x.G x.st ∗
      (⌜FitsEnv M lim st_init (CmkEnv x)⌝ ∗
       ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
       ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp cmkStack ∗ (A.atState lim st_init s0).pool ∗ R) := by
    dsimp only [cmkPlacedSpec, CryptoVerification.LibsignalSession.cmkPlacedSpec,
      withLsCodeLoaded] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hok : ChainsOk x.st := chainsOk_of_ratchetAt hratchet
  by_cases hlt : x.counter < x.ck.index
  · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
      hs0_past x st_init R s0 hpc hrun hsp hpre hlt hL
    swap; · exact hoom.elim
    exact reaches_outcome_steps hsteps1 (hs1 hA hmm_s1 hfind x st_init st_init R s0 s1 hlt hst1)
  · have hle : x.ck.index ≤ x.counter := BitVec.not_lt.mp hlt
    by_cases hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps
    · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
        hs0_adv x st_init R s0 hpc hrun hsp hpre hle hj hL
      swap; · exact hoom.elim
      have hL1 := hsteps1.codeLoaded hL
      by_cases hck_lt : x.ck.index < x.counter
      · simp only [hck_lt, ↓reduceIte] at hst1
        cases hci : x.st.findReceiverChainIndex x.their with
        | none =>
          have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, Or.inr hci⟩
          have hst1_pan :
              CmkLoopState_placed A lim x st_init st_init
                (fun evs => evs = [] ∨ evs = rustAllocEvents 32 1)
                x.G x.st x.ck R cmkLoopPC_placed s0 s1 :=
            ⟨hst1.1.weaken fun evs hevs => by
              simpa only [CmkEnv, hlt, hj, hci, hck_lt, ↓reduceIte] using hevs, hst1.2⟩
          exact reaches_outcome_steps hsteps1
            (hs5_loop hA hfind hhmac x st_init st_init R s0 s1 hck_lt hci hpan_model hst1_pan)
        | some ci =>
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          have hst1_adv :
              CmkLoopState_placed A lim x st_init st_init
                (AdvanceEpilogueProofs.FetchBudget.CmkLoopAdvanceEvs
                  (x.counter - x.ck.index).toNat
                  ((x.G.chains[ci]?.map (·.mkCap)).getD 0#64)
                  ch.messageKeys.length
                  (x.counter == BitVec.allOnes 32))
                x.G x.st x.ck R cmkLoopPC_placed s0 s1 :=
            ⟨hst1.1.weaken fun _ hevs => (cmkEnv_advance_chain_iff hle hj hci hch).mpr hevs, hst1.2⟩
          obtain ⟨s2, hsteps2, ⟨hck_end, st2_b, G2, hG2, hst2⟩ | ⟨hpan2, hq2⟩⟩ :=
            storeLoop_placed_of_iter_sat hs3_iter hA hmm hfind hhmac hgrow x st_init st_init
              (x.counter == BitVec.allOnes 32) x.G x.st x.ck ci ch R s0 s1
              hck_lt hci hch hst1_adv hL1
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
              exact hs5_ep hexp hovf hfind hhmac x st_init st2_b
                (CmkEpilogueEvs (x.counter == BitVec.allOnes 32))
                G2 stc ckc R s0 s2 hck_end (Or.inl hc_max) hpan_model hst2
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
              have hbeq_f : (x.counter == BitVec.allOnes 32) = false :=
                beq_eq_false_iff_ne.mpr hc_max
              rw [hbeq_f] at hst2
              exact hs4 hA hfind hhmac x st_init st2_b G2 stc ckc ci chc R s0 s2
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
            (hs5_ep hexp hovf hfind hhmac x st_init st_init (CmkEnv x)
              x.G x.st x.ck R s0 s1 hck_eq hpan_cond hpan_model hst1)
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
          have hbeq_f : (x.counter == BitVec.allOnes 32) = false :=
            beq_eq_false_iff_ne.mpr hc_max
          have hst1_ep :
              CmkLoopState_placed A lim x st_init st_init (CmkEpilogueEvs false)
                x.G x.st x.ck R cmkEpiloguePC_placed s0 s1 :=
            ⟨hst1.1.weaken fun _ hevs =>
              (cmkEnv_advance_chain_iff hle hj hci hch).mpr
                (by rw [hn0, hbeq_f]; exact cmkLoopAdvanceEvs_zero_iff.mpr hevs), hst1.2⟩
          exact reaches_outcome_steps hsteps1
            (hs4 hA hfind hhmac x st_init st_init x.G x.st x.ck ci ch R s0 s1
              hck_eq hc_max hci hch (RatchetGhost.AgreeExcept.refl x.G (some ci))
              hm1 hm2 htouch hst1_ep)
    · have hj_gt : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat := Nat.lt_of_not_ge hj
      obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
        hs0_tooFar x st_init R s0 hpc hrun hsp hpre hle hj_gt hL
      swap; · exact hoom.elim
      have hro1 : LibsignalRoLoaded lsmpl s1.mem :=
        libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen
      have hst1_ro :
          CmkTooFarState_placed A lim x st_init st_init
            ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s1 := by
        rcases hst1 with ⟨hsb1, hpc1, hframe1, hregs1, hmem1⟩
        refine ⟨hsb1, hpc1, hframe1, hregs1, ?_⟩
        have hm := rodata_placed_tooFarInFuture_intro hro1 hmem1
        have heq :
            (lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗
              (cmkPreLoopHeap_placed (A.atState lim st_init s1) x s0 ∗ R) =
            cmkPreLoopHeap_placed (A.atState lim st_init s1) x s0 ∗
              ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) := by sep_ac_rfl
        rwa [heq] at hm
      exact reaches_outcome_steps hsteps1 (hs2 hA x st_init st_init R s0 s1 hle hj_gt hst1_ro)

theorem consume_message_key_placed_run_of_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A lim) :
    CmkPlacedRunStmtSat F A lim H :=
  cmk_placed_of_seams_sat hfind hhmac hgrow
    (prologueSplit_past_placed_ok F A lim H)
    (prologueSplit_tooFar_placed_ok F A lim H)
    (prologueSplit_advance_placed_ok F A lim H)
    (takePath_placed_ok_thm_sat F A lim H)
    (tooFarPath_placed_ok' F A lim H)
    (storeLoop_iter_placed_ok_sat F A lim H)
    (advanceEpilogue_placed_ok F A lim H)
    (loopNoChainPanic_placed_ok F A lim H)
    (epiloguePanic_placed_ok F A lim H)

/-- **Top-level composition of S0–S5 with `.rodata` (`LibsignalRoLoaded lsmpl`, budget-threaded, `HookSat` on `memmove`).** -/
theorem cmk_placed_ro_of_seams_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hfind : FindIndexPlacedOk H A)
    (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A lim)
    (hs0_past : ProloguePastPlacedSpec F A lim H)
    (hs0_tooFar : PrologueTooFarPlacedSpec F A lim H)
    (hs0_adv : PrologueAdvanceEntryPlacedSpec F A lim H)
    (hs1 : TakePathPlacedSpecSat F A lim H)
    (hs2 : TooFarPathPlacedSpec F A lim H)
    (hs3_iter : StoreLoopIterPlacedRoSpecSat F A lim H)
    (hs4 : AdvanceEpiloguePlacedRoSpec F A lim H)
    (hs5_loop : LoopNoChainPanicPlacedRoSpec F A lim H)
    (hs5_ep : EpiloguePanicPlacedRoSpec F A lim H) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  have hmm_s1 : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack) := by
    simpa [cmkMemmoveSym, allocHookStack] using hmm
  refine Arm64.subroutine_ok_outcome_intro ?_
  rintro ⟨x, st_init⟩ R s0 hpc hrun hpre_ro hsp
  have hpre_split :
      s0.mem ⊨ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) := by
    dsimp only [cmkPlacedRoSpec] at hpre_ro
    have heq :
        ((cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗ R =
          ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) := by
      sep_ac_rfl
    rwa [heq] at hpre_ro
  rw [satisfies_pure_sepConj] at hpre_split
  rcases hpre_split with ⟨hro, hpre⟩
  have hexp : H cmkExpectFailedSym = some Rust.panicked := hA.2.2.2.2.1
  have hovf : H cmkPanicAddOverflowSym = some Rust.panicked := hA.2.2.2.2.2
  suffices h_out :
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s0 from
    h_out.mono_outcome fun _ hout => hout
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  have hratchet : s0.mem ⊨ ratchetAt (A.atState lim st_init s0) x.self x.G x.st ∗
      (⌜FitsEnv M lim st_init (CmkEnv x)⌝ ∗
       ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
       ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp cmkStack ∗ (A.atState lim st_init s0).pool ∗ R) := by
    dsimp only [cmkPlacedSpec, CryptoVerification.LibsignalSession.cmkPlacedSpec,
      withLsCodeLoaded] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hok : ChainsOk x.st := chainsOk_of_ratchetAt hratchet
  by_cases hlt : x.counter < x.ck.index
  · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
      hs0_past x st_init R s0 hpc hrun hsp hpre hlt hL
    swap; · exact hoom.elim
    exact reaches_outcome_steps hsteps1 (hs1 hA hmm_s1 hfind x st_init st_init R s0 s1 hlt hst1)
  · have hle : x.ck.index ≤ x.counter := BitVec.not_lt.mp hlt
    by_cases hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps
    · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
        hs0_adv x st_init R s0 hpc hrun hsp hpre hle hj hL
      swap; · exact hoom.elim
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
          have hst1_pan :
              CmkLoopState_placed A lim x st_init st_init
                (fun evs => evs = [] ∨ evs = rustAllocEvents 32 1)
                x.G x.st x.ck R cmkLoopPC_placed s0 s1 :=
            ⟨hst1.1.weaken fun evs hevs => by
              simpa only [CmkEnv, hlt, hj, hci, hck_lt, ↓reduceIte] using hevs, hst1.2⟩
          exact reaches_outcome_steps hsteps1
            (hs5_loop hA hfind hhmac x st_init st_init R s0 s1 hck_lt hci hpan_model hst1_pan hro1)
        | some ci =>
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          have hst1_adv :
              CmkLoopState_placed A lim x st_init st_init
                (AdvanceEpilogueProofs.FetchBudget.CmkLoopAdvanceEvs
                  (x.counter - x.ck.index).toNat
                  ((x.G.chains[ci]?.map (·.mkCap)).getD 0#64)
                  ch.messageKeys.length
                  (x.counter == BitVec.allOnes 32))
                x.G x.st x.ck R cmkLoopPC_placed s0 s1 :=
            ⟨hst1.1.weaken fun _ hevs => (cmkEnv_advance_chain_iff hle hj hci hch).mpr hevs, hst1.2⟩
          obtain ⟨s2, hsteps2, ⟨hck_end, st2_b, G2, hG2, hst2⟩ | ⟨hpan2, hq2⟩⟩ :=
            storeLoop_placed_ro_of_iter_sat hs3_iter hA hmm hfind hhmac hgrow x st_init st_init
              (x.counter == BitVec.allOnes 32) x.G x.st x.ck ci ch R s0 s1
              hck_lt hci hch hst1_adv hL1 hro1
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
              exact hs5_ep hexp hovf hfind hhmac x st_init st2_b
                (CmkEpilogueEvs (x.counter == BitVec.allOnes 32))
                G2 stc ckc R s0 s2 hck_end (Or.inl hc_max) hpan_model hst2 hro2
            · obtain ⟨ch', hch', hmodel⟩ :=
                consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
              rw [hch] at hch'; cases hch'
              have hci_lt : ci < x.st.receiverChains.length := (List.getElem?_eq_some_iff.mp hch).1
              have hchc_get : stc.receiverChains[ci]? = some chc := getElem?_set_self hci_lt chc
              have hci_stc : stc.findReceiverChainIndex x.their = some ci := by
                rw [findReceiverChainIndex_set x.st x.their ci chc ⟨ch, hch, rfl⟩]; exact hci
              have hm1 : (x.model F).1 = .ok (ckc.messageKeys F) := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
              have hm2 : (x.model F).2 =
                  { stc with
                    receiverChains := stc.receiverChains.set ci
                      { chc with chainKey := some (chainStepN F 1 ckc) } } := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
                dsimp only [stc, chc]; rw [set_set_same]
              have htouch : x.touched F = some ci := by
                unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
              have hbeq_f : (x.counter == BitVec.allOnes 32) = false :=
                beq_eq_false_iff_ne.mpr hc_max
              rw [hbeq_f] at hst2
              exact hs4 hA hfind hhmac x st_init st2_b G2 stc ckc ci chc R s0 s2
                hck_end hc_max hci_stc hchc_get hG2 hm1 hm2 htouch hst2 hro2
          · exact reaches_outcome_steps (hsteps1.trans hsteps2) (reaches_outcome_refl_panic hpan2 hq2)
      · simp only [hck_lt, ↓reduceIte] at hst1
        have hck_eq : x.ck.index = x.counter := BitVec.le_antisymm hle (BitVec.not_lt.mp hck_lt)
        by_cases hpan_cond : x.counter = BitVec.allOnes 32 ∨ x.st.findReceiverChainIndex x.their = none
        · have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, hpan_cond⟩
          exact reaches_outcome_steps hsteps1
            (hs5_ep hexp hovf hfind hhmac x st_init st_init (CmkEnv x)
              x.G x.st x.ck R s0 s1 hck_eq hpan_cond hpan_model hst1 hro1)
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
          have hbeq_f : (x.counter == BitVec.allOnes 32) = false :=
            beq_eq_false_iff_ne.mpr hc_max
          have hst1_ep :
              CmkLoopState_placed A lim x st_init st_init (CmkEpilogueEvs false)
                x.G x.st x.ck R cmkEpiloguePC_placed s0 s1 :=
            ⟨hst1.1.weaken fun _ hevs =>
              (cmkEnv_advance_chain_iff hle hj hci hch).mpr
                (by rw [hn0, hbeq_f]; exact cmkLoopAdvanceEvs_zero_iff.mpr hevs), hst1.2⟩
          exact reaches_outcome_steps hsteps1
            (hs4 hA hfind hhmac x st_init st_init x.G x.st x.ck ci ch R s0 s1
              hck_eq hc_max hci hch (RatchetGhost.AgreeExcept.refl x.G (some ci))
              hm1 hm2 htouch hst1_ep hro1)
    · have hj_gt : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat := Nat.lt_of_not_ge hj
      obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, hoom⟩⟩ :=
        hs0_tooFar x st_init R s0 hpc hrun hsp hpre hle hj_gt hL
      swap; · exact hoom.elim
      have hro1 : LibsignalRoLoaded lsmpl s1.mem :=
        libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen
      have hst1_ro :
          CmkTooFarState_placed A lim x st_init st_init
            ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s1 := by
        rcases hst1 with ⟨hsb1, hpc1, hframe1, hregs1, hmem1⟩
        refine ⟨hsb1, hpc1, hframe1, hregs1, ?_⟩
        have hm := rodata_placed_tooFarInFuture_intro hro1 hmem1
        have heq :
            (lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗
              (cmkPreLoopHeap_placed (A.atState lim st_init s1) x s0 ∗ R) =
            cmkPreLoopHeap_placed (A.atState lim st_init s1) x s0 ∗
              ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) := by sep_ac_rfl
        rwa [heq] at hm
      exact reaches_outcome_steps hsteps1 (hs2 hA x st_init st_init R s0 s1 hle hj_gt hst1_ro)

theorem consume_message_key_placed_ro_run_of_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A lim) :
    CmkPlacedRunStmtSat F A lim H :=
  cmk_placed_ro_of_seams_sat hfind hhmac hgrow
    (prologueSplit_past_placed_ok F A lim H)
    (prologueSplit_tooFar_placed_ok F A lim H)
    (prologueSplit_advance_placed_ok F A lim H)
    (takePath_placed_ok_thm_sat F A lim H)
    (tooFarPath_placed_ok' F A lim H)
    (storeLoop_iter_placed_ro_ok_sat F A lim H)
    (advanceEpilogue_placed_ro_ok F A lim H)
    (loopNoChainPanic_placed_ro_ok F A lim H)
    (epiloguePanic_placed_ro_ok F A lim H)

theorem consume_message_key_placed_run_of_unbounded_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A lim) :
    CmkPlacedRunStmtUnboundedSat F A lim H :=
  fun hA hmm =>
    consume_message_key_placed_run_of_sat F A lim H hfind hhmac hgrow hA
      (hookSat_sessionMemmoveBoundedBudget_of_unbounded 4096 hmm)

theorem consume_message_key_placed_ro_run_of_unbounded_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A lim) :
    CmkPlacedRunStmtUnboundedSat F A lim H :=
  fun hA hmm =>
    consume_message_key_placed_ro_run_of_sat F A lim H hfind hhmac hgrow hA
      (hookSat_sessionMemmoveBoundedBudget_of_unbounded 4096 hmm)

theorem consume_message_key_placed_run_of_exact [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A lim) :
    CmkPlacedRunStmt F A lim H :=
  fun hA hmm =>
    consume_message_key_placed_run_of_sat F A lim H hfind hhmac hgrow hA
      (hookSat_sessionMemmoveBoundedBudget_of_exact 4096 hmm)

theorem consume_message_key_placed_ro_run_of_exact [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A lim) :
    CmkPlacedRunStmt F A lim H :=
  fun hA hmm =>
    consume_message_key_placed_ro_run_of_sat F A lim H hfind hhmac hgrow hA
      (hookSat_sessionMemmoveBoundedBudget_of_exact 4096 hmm)

end LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat
