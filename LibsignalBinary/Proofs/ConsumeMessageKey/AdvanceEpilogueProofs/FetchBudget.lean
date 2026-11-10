/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
public import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Budget-Threaded Checkpoint States, Envelope, and Segment Contracts for `consume_message_key`

Defines `VmPreserved`-lifted callee contracts, the stack-independent `AllocEvent` envelope `CmkEnv`,
`SeamBudget`-threaded intermediate checkpoint states, and segment specifications for Block 24.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (
  ChainKey RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalPlacement LibsignalRoLoaded lsmpl lsρ withLsCodeLoaded
  blkPC_24 blkPl_24
)
open CryptoVerification.LibsignalSessionRepr (
  RatchetGhost tooFarInFutureStr
)
open CryptoVerification.SessionModel (chainStepN)
open CryptoVerification.LibsignalSession (
  FindIndexGhost ConsumeMessageKeyGhost
  cmkRustAllocSym cmkRustDeallocSym cmkRustNoAllocShimSym
  cmkHandleErrorSym cmkExpectFailedSym cmkPanicAddOverflowSym
  cmkEntry_placed cmkTakePC_placed cmkTooFarPC_placed
  cmkLoopPC_placed cmkEpiloguePC_placed
)
open CryptoVerification.LibsignalSession.TooFarPath (cmkTooFarStrSym)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv FreeOnlyEvs
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (
  hmacSpec GrowOneEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)

/-! ## Budget-Threaded Extern and Callee Contracts -/

def cmkShimSpec : Spec Unit :=
  withVmPreserved CryptoVerification.LibsignalSession.cmkShimSpec

/-- Budget-threaded allocator and panic hook assumptions for `consume_message_key`. -/
def CmkAllocHooks [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  HookSat H cmkRustAllocSym (rustCliAllocBudgetSpec M A lim false) ∧
  HookSat H cmkRustDeallocSym (rustCliDeallocBudgetSpec M A lim) ∧
  HookSat H cmkRustNoAllocShimSym cmkShimSpec ∧
  H cmkHandleErrorSym = some Rust.panicked ∧
  H cmkExpectFailedSym = some Rust.panicked ∧
  H cmkPanicAddOverflowSym = some Rust.panicked

def findIndexPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) : Spec FindIndexGhost :=
  withVmPreserved (CryptoVerification.LibsignalSession.findIndexPlacedSpec A.repAlloc)

def FindIndexPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (A : RustCliAllocBudget M) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
    (withLsCodeLoaded lsmpl (findIndexPlacedSpec A))

def HmacPlacedOk [LibsignalPlacement]
    (H : String → Option (State → State))
    (F : ShaState → List (BitVec 8) → ShaState) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73)
    (withLsCodeLoaded lsmpl (hmacSpec F))

def HmacPlacedRoOk [LibsignalPlacement]
    (H : String → Option (State → State))
    (F : ShaState → List (BitVec 8) → ShaState) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73)
    (withLsCodeLoaded lsmpl
      { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ })

/-! ## Allocation-Event Envelope `CmkEnv` -/

/-- Remaining allocation events at `cmkEpiloguePC_placed` (`+0x4dc`): `[]` on pre-allocation
panic, or two 32-byte allocations separated by an optional `chain_key` deallocation. -/
def CmkEpilogueEvs (isPanic : Bool) (evs : List AllocEvent) : Prop :=
  if isPanic then
    evs = []
  else
    ∃ evs_ck : List AllocEvent,
      FreeOnlyEvs evs_ck ∧
      evs = rustAllocEvents 32 1 ++ evs_ck ++ rustAllocEvents 32 1

/-- Remaining allocation events across `n` `StoreLoop` iterations followed by the epilogue. -/
inductive CmkLoopAdvanceEvs : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop where
  | done {cap : BitVec 64} {len : Nat} {isPanic : Bool} {evs : List AllocEvent}
      (h : CmkEpilogueEvs isPanic evs) :
      CmkLoopAdvanceEvs 0 cap len isPanic evs
  | step {n : Nat} {cap : BitVec 64} {len : Nat} {isPanic : Bool}
      {evs_grow evs_pop evs_rest : List AllocEvent}
      (hgrow : if len = cap.toNat then GrowOneEnv cap evs_grow else evs_grow = [])
      (hpop : if maxMessageKeys ≤ len then FreeOnlyEvs evs_pop else evs_pop = [])
      (hrest : CmkLoopAdvanceEvs n
        (if len = cap.toNat then BitVec.ofNat 64 (max (2 * cap.toNat) 4) else cap)
        (if maxMessageKeys ≤ len then maxMessageKeys else len + 1)
        isPanic evs_rest) :
      CmkLoopAdvanceEvs (n + 1) cap len isPanic
        (rustAllocEvents 32 1 ++ evs_grow ++ evs_pop ++ evs_rest)

/-- Full `AllocEvent` envelope for `RatchetState::consume_message_key`. -/
def CmkEnv (x : ConsumeMessageKeyGhost) (evs : List AllocEvent) : Prop :=
  if x.counter < x.ck.index then
    FreeOnlyEvs evs
  else if (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps then
    match x.st.findReceiverChainIndex x.their with
    | none =>
      if x.ck.index < x.counter then
        evs = [] ∨ evs = rustAllocEvents 32 1
      else
        evs = []
    | some ci =>
      let cap0 := (x.G.chains[ci]?.map (·.mkCap)).getD 0#64
      let len0 := (x.st.receiverChains[ci]?.map (·.messageKeys.length)).getD 0
      CmkLoopAdvanceEvs (x.counter - x.ck.index).toNat cap0 len0
        (x.counter == BitVec.allOnes 32) evs
  else
    evs = rustAllocEvents 36 1

theorem cmkEnv_tooFar {x : ConsumeMessageKeyGhost} {evs : List AllocEvent}
    (hle : x.ck.index ≤ x.counter)
    (hjump : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat) :
    CmkEnv x evs ↔ evs = rustAllocEvents 36 1 := by
  have hlt : ¬ x.counter < x.ck.index := BitVec.not_lt.mpr hle
  have hnle : ¬ (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps := Nat.not_le.mpr hjump
  simp only [CmkEnv, hlt, hnle, ↓reduceIte]

/-! ## Budget-Threaded Specification and Seam States -/

/-- Budget-threaded relocatable `consume_message_key` specification with `.OutOfMemory` ruled out. -/
def cmkPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ConsumeMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (CmkEnv x)⌝ ∗
      (CryptoVerification.LibsignalSession.cmkPlacedSpec F (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜CmkEnv x evs⌝ ∗
        (CryptoVerification.LibsignalSession.cmkPlacedSpec
          F (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜(x.model F).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def CmkTakeState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (R : SepProp)
    (s0 s : State) : Prop :=
  SeamBudget M lim (CmkEnv x) st_init st FreeOnlyEvs ∧
  CryptoVerification.LibsignalSession.CmkTakeState_placed (A.atState lim st s) x R s0 s

def CmkTooFarState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (R : SepProp)
    (s0 s : State) : Prop :=
  SeamBudget M lim (CmkEnv x) st_init st (fun evs => evs = rustAllocEvents 36 1) ∧
  CryptoVerification.LibsignalSession.CmkTooFarState_placed (A.atState lim st s) x R s0 s

def CmkLoopState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (remEnv : List AllocEvent → Prop)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (R : SepProp)
    (pc : BitVec 64) (s0 s : State) : Prop :=
  SeamBudget M lim (CmkEnv x) st_init st remEnv ∧
  CryptoVerification.LibsignalSession.CmkLoopState_placed (A.atState lim st s) x Gc stc ckc R pc s0 s

/-! ## Budget-Threaded Segment Contracts -/

def ProloguePastPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : ConsumeMessageKeyGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    s0.pc = cmkEntry_placed → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) →
    x.counter < x.ck.index →
    reaches_pc ((blkPC_24).rebase (blkPl_24).base H) cmkTakePC_placed s0
      (CmkTakeState_placed A lim x st_init st_init R s0)

def PrologueTooFarPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : ConsumeMessageKeyGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    s0.pc = cmkEntry_placed → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) →
    x.ck.index ≤ x.counter →
    x.st.maxForwardJumps < (x.counter - x.ck.index).toNat →
    reaches_pc ((blkPC_24).rebase (blkPl_24).base H) cmkTooFarPC_placed s0
      (CmkTooFarState_placed A lim x st_init st_init R s0)

def PrologueAdvanceEntryPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : ConsumeMessageKeyGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    s0.pc = cmkEntry_placed → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cmkPlacedSpec F A lim).pre (x, st_init) s0 ∗ R) →
    x.ck.index ≤ x.counter →
    (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps →
    let targetPC := if x.ck.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    reaches_pc ((blkPC_24).rebase (blkPl_24).base H) targetPC s0
      (CmkLoopState_placed A lim x st_init st_init (CmkEnv x) x.G x.st x.ck R targetPC s0)

def TooFarPathPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
      x.ck.index ≤ x.counter →
      x.st.maxForwardJumps < (x.counter - x.ck.index).toNat →
      CmkTooFarState_placed A lim x st_init st
        ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

def AdvanceEpiloguePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H → FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      x.counter ≠ BitVec.allOnes 32 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      x.G.AgreeExcept Gc (some ci) →
      (x.model F).1 = .ok (ckc.messageKeys F) →
      (x.model F).2 =
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with chainKey := some (chainStepN F 1 ckc) } } →
      x.touched F = some ci →
      CmkLoopState_placed A lim x st_init st (CmkEpilogueEvs false)
        Gc stc ckc R cmkEpiloguePC_placed s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

def LoopNoChainPanicPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H → FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
      x.ck.index < x.counter →
      x.st.findReceiverChainIndex x.their = none →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A lim x st_init st (fun evs => evs = [] ∨ evs = rustAllocEvents 32 1)
        x.G x.st x.ck R cmkLoopPC_placed s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

def EpiloguePanicPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  H cmkExpectFailedSym = some Rust.panicked →
    H cmkPanicAddOverflowSym = some Rust.panicked →
    FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (remEnv : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      (x.counter = BitVec.allOnes 32 ∨ stc.findReceiverChainIndex x.their = none) →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A lim x st_init st remEnv Gc stc ckc R cmkEpiloguePC_placed s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

def AdvanceEpiloguePlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H → FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      x.counter ≠ BitVec.allOnes 32 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      x.G.AgreeExcept Gc (some ci) →
      (x.model F).1 = .ok (ckc.messageKeys F) →
      (x.model F).2 =
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with chainKey := some (chainStepN F 1 ckc) } } →
      x.touched F = some ci →
      CmkLoopState_placed A lim x st_init st (CmkEpilogueEvs false)
        Gc stc ckc R cmkEpiloguePC_placed s0 s →
      LibsignalRoLoaded lsmpl s.mem →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

def LoopNoChainPanicPlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H → FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
      x.ck.index < x.counter →
      x.st.findReceiverChainIndex x.their = none →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A lim x st_init st (fun evs => evs = [] ∨ evs = rustAllocEvents 32 1)
        x.G x.st x.ck R cmkLoopPC_placed s0 s →
      LibsignalRoLoaded lsmpl s.mem →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

def EpiloguePanicPlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  H cmkExpectFailedSym = some Rust.panicked →
    H cmkPanicAddOverflowSym = some Rust.panicked →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (remEnv : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      (x.counter = BitVec.allOnes 32 ∨ stc.findReceiverChainIndex x.their = none) →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A lim x st_init st remEnv Gc stc ckc R cmkEpiloguePC_placed s0 s →
      LibsignalRoLoaded lsmpl s.mem →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s

end LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
