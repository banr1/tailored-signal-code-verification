/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Definitions and Composition for `StoreLoop` (Block 24)

Defines per-iteration `AllocEvent` envelopes (`ConcatEnv`, `CmkAfterSeedEvs`, `CmkAfterGrowEvs`),
`SeamBudget`-threaded store-loop checkpoint states, and sub-segment composition
`storeLoop_iter_placed_of_parts`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (chainHmac chainKeySeed)
open CryptoGames.LibsignalSession (
  ChainKey RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPl_24 libsignalRoLoaded_of_keepsFrozen lsLogFilterAddr lsmpl
)
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost RatchetGhost chainAt)
open CryptoVerification.SessionModel (chainStepN findReceiverChainIndex_set skippedKeys)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkEpiloguePC_placed cmkLoopPC_placed
)
open CryptoVerification.LibsignalSession.StoreLoop (
  introduce_withLsCodeLoaded updatedRatchetState
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (
  GrowOneEnv GrowOnePlacedOk growOneEnv_events growOneEvents hmacSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEnv CmkEpilogueEvs CmkLoopAdvanceEvs CmkLoopState_placed
  FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk cmkPlacedSpec findIndexPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)

/-! ## Per-Iteration Capacity, Length, and `AllocEvent` Envelopes -/

/-- Exact sequential concatenation of two `AllocEvent` predicates (without prefix truncation). -/
def ConcatEnv (E₁ E₂ : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  ∃ evs₁ evs₂, evs = evs₁ ++ evs₂ ∧ E₁ evs₁ ∧ E₂ evs₂

/-- Deterministic `mkCap` after one `InsertKey` step (`grow_one` iff `len = cap.toNat`). -/
def cmkNextCap (cap : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = cap.toNat then BitVec.ofNat 64 (max (2 * cap.toNat) 4) else cap

/-- Deterministic `messageKeys.length` after inserting one key and capping at `maxMessageKeys`. -/
def cmkNextLen (len : Nat) : Nat :=
  if maxMessageKeys ≤ len then maxMessageKeys else len + 1

theorem cmkNextLen_eq_take {α : Type} (a : α) (l : List α) :
    cmkNextLen l.length = ((a :: l).take maxMessageKeys).length := by
  unfold cmkNextLen
  rw [List.length_take, List.length_cons]
  by_cases h : maxMessageKeys ≤ l.length
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

/-- Events emitted by the optional `RawVec<MessageKey>::grow_one` inside `InsertKey`. -/
def CmkGrowOptEvs (cap : BitVec 64) (len : Nat) (evs : List AllocEvent) : Prop :=
  if len = cap.toNat then GrowOneEnv cap evs else evs = []

/-- Events emitted by the optional 2001st-key eviction inside `EvictOldestKey`. -/
def CmkPopOptEvs (len : Nat) (evs : List AllocEvent) : Prop :=
  if maxMessageKeys ≤ len then FreeOnlyEvs evs else evs = []

def CmkIterPostEvs (k : Nat) (cap : BitVec 64) (len : Nat) (isPanic : Bool) :
    List AllocEvent → Prop :=
  CmkLoopAdvanceEvs k (cmkNextCap cap len) (cmkNextLen len) isPanic

def CmkAfterGrowEvs (k : Nat) (cap : BitVec 64) (len : Nat) (isPanic : Bool) :
    List AllocEvent → Prop :=
  ConcatEnv (CmkPopOptEvs len) (CmkIterPostEvs k cap len isPanic)

def CmkAfterSeedEvs (k : Nat) (cap : BitVec 64) (len : Nat) (isPanic : Bool) :
    List AllocEvent → Prop :=
  ConcatEnv (CmkGrowOptEvs cap len) (CmkAfterGrowEvs k cap len isPanic)

theorem cmkEpilogueEvs_nonempty (isPanic : Bool) :
    ∃ evs, CmkEpilogueEvs isPanic evs := by
  cases isPanic
  · exact ⟨rustAllocEvents 32 1 ++ [] ++ rustAllocEvents 32 1, [], FreeOnlyEvs.nil, rfl⟩
  · exact ⟨[], rfl⟩

theorem cmkLoopAdvanceEvs_nonempty :
    ∀ (n : Nat) (cap : BitVec 64) (len : Nat) (isPanic : Bool),
      ∃ evs, CmkLoopAdvanceEvs n cap len isPanic evs
  | 0, _, _, isPanic => by
    rcases cmkEpilogueEvs_nonempty isPanic with ⟨evs, h⟩
    exact ⟨evs, .done h⟩
  | n + 1, cap, len, isPanic => by
    rcases cmkLoopAdvanceEvs_nonempty n (cmkNextCap cap len) (cmkNextLen len) isPanic with
      ⟨evs_rest, hrest⟩
    let evs_grow : List AllocEvent := if len = cap.toNat then growOneEvents cap else []
    have hgrow : if len = cap.toNat then GrowOneEnv cap evs_grow else evs_grow = [] := by
      by_cases hc : len = cap.toNat <;> simp [evs_grow, hc, growOneEnv_events]
    let evs_pop : List AllocEvent := []
    have hpop : if maxMessageKeys ≤ len then FreeOnlyEvs evs_pop else evs_pop = [] := by
      by_cases hm : maxMessageKeys ≤ len <;> simp [evs_pop, hm, FreeOnlyEvs.nil]
    exact ⟨rustAllocEvents 32 1 ++ evs_grow ++ evs_pop ++ evs_rest, .step hgrow hpop hrest⟩

theorem cmkGrowOptEvs_nonempty (cap : BitVec 64) (len : Nat) :
    ∃ evs, CmkGrowOptEvs cap len evs := by
  unfold CmkGrowOptEvs
  by_cases h : len = cap.toNat
  · exact ⟨growOneEvents cap, by simp [h, growOneEnv_events]⟩
  · exact ⟨[], by simp [h]⟩

theorem cmkPopOptEvs_nonempty (len : Nat) :
    ∃ evs, CmkPopOptEvs len evs := by
  unfold CmkPopOptEvs
  by_cases h : maxMessageKeys ≤ len
  · exact ⟨[], by simp [h, FreeOnlyEvs.nil]⟩
  · exact ⟨[], by simp [h]⟩

theorem cmkAfterGrowEvs_nonempty (k : Nat) (cap : BitVec 64) (len : Nat) (isPanic : Bool) :
    ∃ evs, CmkAfterGrowEvs k cap len isPanic evs := by
  rcases cmkPopOptEvs_nonempty len with ⟨e1, h1⟩
  rcases cmkLoopAdvanceEvs_nonempty k (cmkNextCap cap len) (cmkNextLen len) isPanic with ⟨e2, h2⟩
  exact ⟨e1 ++ e2, e1, e2, rfl, h1, h2⟩

theorem cmkAfterSeedEvs_nonempty (k : Nat) (cap : BitVec 64) (len : Nat) (isPanic : Bool) :
    ∃ evs, CmkAfterSeedEvs k cap len isPanic evs := by
  rcases cmkGrowOptEvs_nonempty cap len with ⟨e1, h1⟩
  rcases cmkAfterGrowEvs_nonempty k cap len isPanic with ⟨e2, h2⟩
  exact ⟨e1 ++ e2, e1, e2, rfl, h1, h2⟩

theorem cmkLoopAdvanceEvs_zero_iff {cap : BitVec 64} {len : Nat} {isPanic : Bool}
    {evs : List AllocEvent} :
    CmkLoopAdvanceEvs 0 cap len isPanic evs ↔ CmkEpilogueEvs isPanic evs :=
  ⟨fun h => by cases h with | done h' => exact h', CmkLoopAdvanceEvs.done⟩

theorem cmkLoopAdvanceEvs_of_seed_seq {k : Nat} {cap : BitVec 64} {len : Nat} {isPanic : Bool}
    {evs : List AllocEvent}
    (h : ConcatEnv (fun e => e = rustAllocEvents 32 1) (CmkAfterSeedEvs k cap len isPanic) evs) :
    CmkLoopAdvanceEvs (k + 1) cap len isPanic evs := by
  rcases h with ⟨_, _, rfl, rfl, ⟨evs_grow, _, rfl, hgrow, ⟨evs_pop, evs_rest, rfl, hpop, hrest⟩⟩⟩
  simpa only [List.append_assoc] using CmkLoopAdvanceEvs.step hgrow hpop hrest

theorem cmkEnv_advance_chain_iff {x : ConsumeMessageKeyGhost} {ci : Nat} {chc : ReceiverChain}
    {evs : List AllocEvent}
    (hle : x.ck.index ≤ x.counter)
    (hjump : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps)
    (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hchc : x.st.receiverChains[ci]? = some chc) :
    CmkEnv x evs ↔
      CmkLoopAdvanceEvs (x.counter - x.ck.index).toNat
        ((x.G.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length
        (x.counter == BitVec.allOnes 32) evs := by
  have hnlt : ¬ x.counter < x.ck.index := BitVec.not_lt.mpr hle
  unfold CmkEnv
  simp only [hnlt, hjump, hci, hchc, ↓reduceIte]
  rfl

/-! ## `VmPreserved`-Lifted Callee Wrappers -/

def hmacAtStateSpec (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, ka, key, ia, inp) s' =>
    ⌜s'.mem = s.mem ∧
      s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
      s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
      inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
  post := (hmacSpec F).post

theorem hmac_placed_ok_at_state [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {s : State}
    (hhmac : HmacPlacedOk H F)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s) := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine subroutine_ok.mono_outcome hhmac (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [hmacAtStateSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
  dsimp only [hmacSpec, LibsignalBinary.Heap.SpecBudget.withVmPreserved,
    CryptoVerification.LibsignalSession.hmacSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem hmac_placed_ro_ok_at_state [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {s : State}
    (hhmac : HmacPlacedRoOk H F)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s) := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [hmacAtStateSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hcl) ?_
  dsimp only
  rw [sepConj_assoc, sepConj_left_comm ((hmacSpec F).pre (out, ka, key, ia, inp) s0),
      satisfies_pure_sepConj]
  refine ⟨hmem ▸ hro, ?_⟩
  dsimp only [hmacSpec, LibsignalBinary.Heap.SpecBudget.withVmPreserved,
    CryptoVerification.LibsignalSession.hmacSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem findIndex_placed_ok_at_state [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {H : String → Option (State → State)} {s : State}
    (hfind : FindIndexPlacedOk H A)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A.repAlloc) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (findIndexPlacedSpec A).post } := by
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp => ?_
  refine subroutine_ok.mono_outcome hfind (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
  dsimp only [findIndexPlacedSpec, LibsignalBinary.Heap.SpecBudget.withVmPreserved,
    CryptoVerification.LibsignalSession.findIndexPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

/-! ## Budget-Threaded Seam States -/

def InsertKeyState_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (remEnv : List AllocEvent → Prop)
    (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (ci : Nat) (seedPtr : BitVec 64)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (CmkEnv x) st_init st remEnv ∧
  CryptoVerification.LibsignalSession.StoreLoop.InsertKeyState_placed
    F (A.atState lim st s) x Gc stc ckc ci seedPtr R s0 s

def EvictOldestKeyState_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (remEnv : List AllocEvent → Prop)
    (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (CmkEnv x) st_init st remEnv ∧
  CryptoVerification.LibsignalSession.StoreLoop.EvictOldestKeyState_placed
    F (A.atState lim st s) x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 s

def AdvanceChainKeyState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
    (remEnv : List AllocEvent → Prop)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (CmkEnv x) st_init st remEnv ∧
  CryptoVerification.LibsignalSession.StoreLoop.AdvanceChainKeyState_placed
    (A.atState lim st s) x G' st' ckc R s0 s

/-! ## Budget-Threaded Sub-Segment and Loop Specifications -/

def DeriveSeedPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
      (remPost : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
      (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      (∃ evs, remPost evs) →
      CmkLoopState_placed A lim x st_init st
        (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) remPost)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s sA ∧
        ((∃ stA seedPtr,
            InsertKeyState_placed F A lim x st_init stA remPost Gc stc ckc ci seedPtr R s0 sA) ∨
         (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sA ∗ R)))

def DeriveSeedPlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ)
      (remPost : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
      (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      (∃ evs, remPost evs) →
      CmkLoopState_placed A lim x st_init st
        (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) remPost)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s sA ∧
        ((∃ stA seedPtr,
            InsertKeyState_placed F A lim x st_init stA remPost Gc stc ckc ci seedPtr R s0 sA) ∨
         (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sA ∗ R)))

def InsertKeyPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  H "memmove" = some hookMemmove → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
      (remAfterGrow : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
      (seedPtr : BitVec 64) (R : SepProp) (s0 sA : State),
      stc.receiverChains[ci]? = some chc →
      (∃ evs, remAfterGrow evs) →
      InsertKeyState_placed F A lim x st_init stA
        (ConcatEnv (CmkGrowOptEvs ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length)
          remAfterGrow)
        Gc stc ckc ci seedPtr R s0 sA →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sA.mem →
      let cap1 := cmkNextCap ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length
      ∃ sB, Steps ((blkPC_24).rebase (blkPl_24).base H) sA sB ∧
        ((chc.messageKeys.length < maxMessageKeys ∧
          ∃ stB G', Gc.AgreeExcept G' (some ci) ∧
            (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = cap1 ∧
            AdvanceChainKeyState_placed A lim x st_init stB remAfterGrow
              G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB) ∨
         (∃ stB cg,
            EvictOldestKeyState_placed F A lim x st_init stB remAfterGrow
              Gc stc ckc ci chc cg cap1 (sB.readReg64 .x24) seedPtr R s0 sB) ∨
         (sB.status = .Panicked ∧ (sB.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sB ∗ R)))

def EvictOldestKeyPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    ∀ (x : ConsumeMessageKeyGhost) (st_init stB : M.σ)
      (remPost : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
      (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64)
      (R : SepProp) (s0 sB : State),
      stc.receiverChains[ci]? = some chc →
      EvictOldestKeyState_placed F A lim x st_init stB (ConcatEnv FreeOnlyEvs remPost)
        Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sB.mem →
      ∃ sC, Steps ((blkPC_24).rebase (blkPl_24).base H) sB sC ∧
        ∃ stC G', Gc.AgreeExcept G' (some ci) ∧
          (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = mkCap1 ∧
          AdvanceChainKeyState_placed A lim x st_init stC remPost
            G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC

def AdvanceChainKeyPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init stD : M.σ)
      (remPost : List AllocEvent → Prop)
      (G' : RatchetGhost) (st' : RatchetState)
      (ckc : ChainKey) (R : SepProp) (s0 sD : State),
      ckc.index < x.counter →
      AdvanceChainKeyState_placed A lim x st_init stD remPost G' st' ckc R s0 sD →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem →
      let ck' := chainStepN F 1 ckc
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
        CmkLoopState_placed A lim x st_init stD remPost G' st' ck' R nextPC s0 s'

def AdvanceChainKeyPlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (st_init stD : M.σ)
      (remPost : List AllocEvent → Prop)
      (G' : RatchetGhost) (st' : RatchetState)
      (ckc : ChainKey) (R : SepProp) (s0 sD : State),
      ckc.index < x.counter →
      AdvanceChainKeyState_placed A lim x st_init stD remPost G' st' ckc R s0 sD →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem →
      LibsignalRoLoaded lsmpl sD.mem →
      let ck' := chainStepN F 1 ckc
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
        CmkLoopState_placed A lim x st_init stD remPost G' st' ck' R nextPC s0 s'

def StoreLoopIterPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (k : Nat) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((∃ st_next G', Gc.AgreeExcept G' (some ci) ∧
            (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = cmkNextCap cap0 chc.messageKeys.length ∧
            CmkLoopState_placed A lim x st_init st_next
              (CmkIterPostEvs k cap0 chc.messageKeys.length isPanic)
              G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

def StoreLoopIterPlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (k : Nat) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((∃ st_next G', Gc.AgreeExcept G' (some ci) ∧
            (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = cmkNextCap cap0 chc.messageKeys.length ∧
            CmkLoopState_placed A lim x st_init st_next
              (CmkIterPostEvs k cap0 chc.messageKeys.length isPanic)
              G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

def StoreLoopPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (x.counter - ckc.index).toNat
          ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

def StoreLoopPlacedRoSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    H "memmove" = some hookMemmove →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (x.counter - ckc.index).toNat
          ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

/-! ## Sub-Segment Composition and Loop Induction -/

theorem storeLoop_iter_placed_of_parts [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA_part : DeriveSeedPlacedSpec F A lim H)
    (hB_part : InsertKeyPlacedSpec F A lim H)
    (hC_part : EvictOldestKeyPlacedSpec F A lim H)
    (hD_part : AdvanceChainKeyPlacedSpec F A lim H) :
    StoreLoopIterPlacedSpec F A lim H := by
  unfold StoreLoopIterPlacedSpec
  intro hA hmm hfind hhmac hgrow x st_init st k isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
  let len0 := chc.messageKeys.length
  have hstate_seq :
      CmkLoopState_placed A lim x st_init st
        (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) (CmkAfterSeedEvs k cap0 len0 isPanic))
        Gc stc ckc R cmkLoopPC_placed s0 s :=
    ⟨hstate.1.weaken fun _ h => cmkLoopAdvanceEvs_of_seed_seq h, hstate.2⟩
  obtain ⟨sA, hstepsA, ⟨stA, seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA hfind hhmac x st_init st (CmkAfterSeedEvs k cap0 len0 isPanic)
      Gc stc ckc ci chc R s0 s hlt hci hchc (cmkAfterSeedEvs_nonempty k cap0 len0 isPanic)
      hstate_seq hL
  · have hLA := hstepsA.codeLoaded hL
    obtain ⟨sB, hstepsB, ⟨hlt_max, stB, G', hG', hcap', hsD⟩ | ⟨stB, cg, hsC⟩ | hpanB⟩ :=
      hB_part hmm hgrow x st_init stA (CmkAfterGrowEvs k cap0 len0 isPanic)
        Gc stc ckc ci chc seedPtr R s0 sA hchc (cmkAfterGrowEvs_nonempty k cap0 len0 isPanic)
        hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      have hnle : ¬ maxMessageKeys ≤ len0 := Nat.not_le.mpr hlt_max
      have hsD' : AdvanceChainKeyState_placed A lim x st_init stB
          (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB :=
        ⟨hsD.1.weaken fun evs h => ⟨[], evs, rfl, by simp [CmkPopOptEvs, hnle], h⟩, hsD.2⟩
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD' hLB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨stB, G', hG', hcap', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      have hlen2000 : len0 = maxMessageKeys := hsC.2.2.2.2.2.2.1
      have hle_max : maxMessageKeys ≤ len0 := Nat.le_of_eq hlen2000.symm
      have hsC' : EvictOldestKeyState_placed F A lim x st_init stB
          (ConcatEnv FreeOnlyEvs (CmkIterPostEvs k cap0 len0 isPanic))
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB :=
        ⟨hsC.1.weaken fun _ ⟨e1, e2, heq, h1, h2⟩ =>
          ⟨e1, e2, heq, by simp [CmkPopOptEvs, hle_max, h1], h2⟩, hsC.2⟩
      obtain ⟨sC, hstepsC, stC, G', hG', hcap', hsD⟩ :=
        hC_part hA x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB hchc hsC' hLB
      have hLC := hstepsC.codeLoaded hLB
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stC (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD,
        Or.inl ⟨stC, G', hG', hcap', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

theorem storeLoop_iter_placed_ro_of_parts [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA_part : DeriveSeedPlacedRoSpec F A lim H)
    (hB_part : InsertKeyPlacedSpec F A lim H)
    (hC_part : EvictOldestKeyPlacedSpec F A lim H)
    (hD_part : AdvanceChainKeyPlacedRoSpec F A lim H) :
    StoreLoopIterPlacedRoSpec F A lim H := by
  unfold StoreLoopIterPlacedRoSpec
  intro hA hmm hfind hhmac hgrow x st_init st k isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
  let len0 := chc.messageKeys.length
  have hstate_seq :
      CmkLoopState_placed A lim x st_init st
        (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) (CmkAfterSeedEvs k cap0 len0 isPanic))
        Gc stc ckc R cmkLoopPC_placed s0 s :=
    ⟨hstate.1.weaken fun _ h => cmkLoopAdvanceEvs_of_seed_seq h, hstate.2⟩
  obtain ⟨sA, hstepsA, ⟨stA, seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA hfind hhmac x st_init st (CmkAfterSeedEvs k cap0 len0 isPanic)
      Gc stc ckc ci chc R s0 s hlt hci hchc (cmkAfterSeedEvs_nonempty k cap0 len0 isPanic)
      hstate_seq hL hro
  · have hLA := hstepsA.codeLoaded hL
    have hroA := libsignalRoLoaded_of_keepsFrozen hro hstepsA.keepsFrozen
    obtain ⟨sB, hstepsB, ⟨hlt_max, stB, G', hG', hcap', hsD⟩ | ⟨stB, cg, hsC⟩ | hpanB⟩ :=
      hB_part hmm hgrow x st_init stA (CmkAfterGrowEvs k cap0 len0 isPanic)
        Gc stc ckc ci chc seedPtr R s0 sA hchc (cmkAfterGrowEvs_nonempty k cap0 len0 isPanic)
        hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      have hroB := libsignalRoLoaded_of_keepsFrozen hroA hstepsB.keepsFrozen
      have hnle : ¬ maxMessageKeys ≤ len0 := Nat.not_le.mpr hlt_max
      have hsD' : AdvanceChainKeyState_placed A lim x st_init stB
          (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB :=
        ⟨hsD.1.weaken fun evs h => ⟨[], evs, rfl, by simp [CmkPopOptEvs, hnle], h⟩, hsD.2⟩
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD' hLB hroB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨stB, G', hG', hcap', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      have hroB := libsignalRoLoaded_of_keepsFrozen hroA hstepsB.keepsFrozen
      have hlen2000 : len0 = maxMessageKeys := hsC.2.2.2.2.2.2.1
      have hle_max : maxMessageKeys ≤ len0 := Nat.le_of_eq hlen2000.symm
      have hsC' : EvictOldestKeyState_placed F A lim x st_init stB
          (ConcatEnv FreeOnlyEvs (CmkIterPostEvs k cap0 len0 isPanic))
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB :=
        ⟨hsC.1.weaken fun _ ⟨e1, e2, heq, h1, h2⟩ =>
          ⟨e1, e2, heq, by simp [CmkPopOptEvs, hle_max, h1], h2⟩, hsC.2⟩
      obtain ⟨sC, hstepsC, stC, G', hG', hcap', hsD⟩ :=
        hC_part hA x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB hchc hsC' hLB
      have hLC := hstepsC.codeLoaded hLB
      have hroC := libsignalRoLoaded_of_keepsFrozen hroB hstepsC.keepsFrozen
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stC (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC hroC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD,
        Or.inl ⟨stC, G', hG', hcap', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

private theorem take_append_take_of_le_placed {α : Type} :
    ∀ (xs ys : List α) {m k : Nat}, m ≤ k →
      (xs ++ ys.take k).take m = (xs ++ ys).take m
  | [], ys, m, k, hmk => by simp [List.take_take, Nat.min_eq_left hmk]
  | x :: xs, ys, 0, k, _ => rfl
  | x :: xs, ys, m + 1, k, hmk => by
    simp only [List.cons_append, List.take_succ_cons]
    exact congrArg (x :: ·) (take_append_take_of_le_placed xs ys (Nat.le_of_succ_le hmk))

private theorem take_append_take_eq_placed {α : Type} (xs ys : List α) (m : Nat) :
    (xs ++ ys.take m).take m = (xs ++ ys).take m :=
  take_append_take_of_le_placed xs ys (Nat.le_refl m)

private theorem set_set_same_placed {α : Type} (xs : List α) (i : Nat) (a b : α) :
    (xs.set i a).set i b = xs.set i b := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem getElem?_set_self_placed {α : Type} {xs : List α} {i : Nat}
    (hi : i < xs.length) (a : α) :
    (xs.set i a)[i]? = some a := by
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_set_self]

private theorem storeLoop_placed_loop_ind [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hiter : StoreLoopIterPlacedSpec F A lim H)
    (hA : CmkAllocHooks A lim H) (hmm : H "memmove" = some hookMemmove)
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A lim)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (isPanic : Bool)
    (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (st : M.σ) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))
  | 0, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkEpiloguePC_placed := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨st_next, G', hG', _, hst'⟩ | hpan⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st 0 isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst'
      have hst_ep : CmkLoopState_placed A lim x st_init st_next (CmkEpilogueEvs isPanic)
          G' _ ck' R cmkEpiloguePC_placed s0 s' :=
        ⟨hst'.1.weaken fun _ h => cmkLoopAdvanceEvs_zero_iff.mpr h, hst'.2⟩
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, st_next, G', hG', ?_⟩⟩
      simpa [ck', chainStepN, skippedKeys] using hst_ep
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkLoopPC_placed := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨st1_b, G1, hG1, hcap1, hst1⟩ | hpan1⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st (k + 1) isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self_placed hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      have hlen1 : cmkNextLen chc.messageKeys.length = chc1.messageKeys.length :=
        cmkNextLen_eq_take (ckc.messageKeys F) chc.messageKeys
      have hst1' : CmkLoopState_placed A lim x st_init st1_b
          (CmkLoopAdvanceEvs (k + 1) ((G1.chains[ci]?.map (·.mkCap)).getD 0#64)
            chc1.messageKeys.length isPanic)
          G1 st1 ck' R cmkLoopPC_placed s0 s1 := by
        refine ⟨hst1.1.weaken fun _ h => ?_, hst1.2⟩
        unfold CmkIterPostEvs
        rwa [← hcap1, hlen1]
      obtain ⟨s2, hsteps2, ⟨hck_end, st2_b, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_placed_loop_ind F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
          k st1_b G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1' (hsteps1.codeLoaded hL)
      · refine ⟨s2, hsteps1.trans hsteps2,
          Or.inl ⟨hck_end, st2_b, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same_placed]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (chainHmac F ckc.key chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq_placed]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem storeLoop_placed_of_iter [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hiter : StoreLoopIterPlacedSpec F A lim H) : StoreLoopPlacedSpec F A lim H := by
  unfold StoreLoopPlacedSpec
  intro hA hmm hfind hhmac hgrow x st_init st isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 :=
    ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk] at hstate ⊢
  exact storeLoop_placed_loop_ind F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
    k st Gc stc ckc chc s hlt hk hci hchc hstate hL

private theorem storeLoop_placed_ro_loop_ind [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hiter : StoreLoopIterPlacedRoSpec F A lim H)
    (hA : CmkAllocHooks A lim H) (hmm : H "memmove" = some hookMemmove)
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A lim)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (isPanic : Bool)
    (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (st : M.σ) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))
  | 0, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL, hro => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkEpiloguePC_placed := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨st_next, G', hG', _, hst'⟩ | hpan⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st 0 isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
    · rw [hpc_eq] at hst'
      have hst_ep : CmkLoopState_placed A lim x st_init st_next (CmkEpilogueEvs isPanic)
          G' _ ck' R cmkEpiloguePC_placed s0 s' :=
        ⟨hst'.1.weaken fun _ h => cmkLoopAdvanceEvs_zero_iff.mpr h, hst'.2⟩
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, st_next, G', hG', ?_⟩⟩
      simpa [ck', chainStepN, skippedKeys] using hst_ep
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL, hro => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkLoopPC_placed := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨st1_b, G1, hG1, hcap1, hst1⟩ | hpan1⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st (k + 1) isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self_placed hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      have hlen1 : cmkNextLen chc.messageKeys.length = chc1.messageKeys.length :=
        cmkNextLen_eq_take (ckc.messageKeys F) chc.messageKeys
      have hst1' : CmkLoopState_placed A lim x st_init st1_b
          (CmkLoopAdvanceEvs (k + 1) ((G1.chains[ci]?.map (·.mkCap)).getD 0#64)
            chc1.messageKeys.length isPanic)
          G1 st1 ck' R cmkLoopPC_placed s0 s1 := by
        refine ⟨hst1.1.weaken fun _ h => ?_, hst1.2⟩
        unfold CmkIterPostEvs
        rwa [← hcap1, hlen1]
      obtain ⟨s2, hsteps2, ⟨hck_end, st2_b, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_placed_ro_loop_ind F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
          k st1_b G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1' (hsteps1.codeLoaded hL)
          (libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen)
      · refine ⟨s2, hsteps1.trans hsteps2,
          Or.inl ⟨hck_end, st2_b, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same_placed]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (chainHmac F ckc.key chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq_placed]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem storeLoop_placed_ro_of_iter [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hiter : StoreLoopIterPlacedRoSpec F A lim H) : StoreLoopPlacedRoSpec F A lim H := by
  unfold StoreLoopPlacedRoSpec
  intro hA hmm hfind hhmac hgrow x st_init st isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 :=
    ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk] at hstate ⊢
  exact storeLoop_placed_ro_loop_ind F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
    k st Gc stc ckc chc s hlt hk hci hchc hstate hL hro

end LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
