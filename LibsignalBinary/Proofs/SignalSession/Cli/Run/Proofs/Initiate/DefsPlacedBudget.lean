/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced

/-!
# Budget-Threaded Relocatable Definitions for `initiate`

Defines `RustCliAllocBudget M` counterparts of `slotFramePlaced`, `initSlotSpecPlaced`,
`sessDeserialize_false_placed_ok`, `InitExitPostPlaced`, `InitPanicPostPlaced`, and
`stage{2,3,4,5}MemPlaced` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessDeserializeSpecPlaced)

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of `RunProofs.slotFramePlaced`. -/
def slotFramePlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (x : SlotCtx) : SepProp :=
  ⌜x.coins.length < 2 ^ 63⌝ ∗
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗
    protocolAddressAt A.repAlloc x.me x.meA ∗
    coinsInstalledPlaced x.coinsP x.coins ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool lim st s

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of `RunProofs.initSlotSpecPlaced`
parameterized by `InitEnv : InitGhost → List AllocEvent → Prop`. -/
def initSlotSpecPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (InitEnv : InitGhost → List AllocEvent → Prop)
    (S : RunSem) (stk : Nat) : Spec (InitGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.peerA ∧ s.readReg64 .x1 = x.meA ∧
          s.readReg64 .x2 = x.stores + 0xf0#64 ∧ s.readReg64 .x3 = lsρ cliSessionVtSym ∧
          s.readReg64 .x4 = x.stores ∧ s.readReg64 .x5 = lsρ cliIdentityVtSym ∧
          s.readReg64 .x6 = x.bundleA ∧ s.readReg64 .x7 = 0#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧
          S.filesOk x.F x.peer.val x.me.val ∧ S.initOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat ∧ FitsEnv M lim st (InitEnv x)⌝ ∗
        slotFramePlaced A lim st s x.toSlotCtx ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Unit,
          ⌜InitEnv x evs ∧ slotTrace s0 sf ∧
            slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' e s0 sf⌝ ∗
          storesAt A.repAlloc x.stores g' ∗ initResAt A.repAlloc x.ret e ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (x, _) s0 sf =>
        ⌜S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }

/-- Vacuously discharges `SpecsPlacedBudget.sessDeserializeSpecPlaced` at empty scope `fun _ => False`. -/
theorem sessDeserialize_false_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop} :
    subroutine_ok prog entry
      (withLsRoCl lsmpl (SpecsPlacedBudget.sessDeserializeSpecPlaced (fun _ => False) A lim DeserEnv)) := by
  refine subroutine_ok_intro fun ⟨x, st⟩ R s0 _ _ hmem _ => ?_
  dsimp only [withLsRoCl, SpecsPlacedBudget.sessDeserializeSpecPlaced] at hmem
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem
  exact False.elim hmem.1.2.2.2.1

/-- Shared budget-threaded postcondition predicate for any completed exit path reaching `lr`. -/
def InitExitPostPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (InitEnv : InitGhost → List AllocEvent → Prop)
    (S : RunSem) (x : InitGhost) (st0 : M.σ) (stk : Nat) (s0 : State) :
    State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (Pf ⊢ (initSlotSpecPlaced A lim InitEnv S stk).post (x, st0) s0 sf)

/-- Shared budget-threaded panic predicate matching `initSlotSpecPlaced`. -/
def InitPanicPostPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (InitEnv : InitGhost → List AllocEvent → Prop)
    (S : RunSem) (x : InitGhost) (st0 : M.σ) (stk : Nat) (s0 : State) :
    State → SepProp → Prop :=
  fun sf Pf => Pf ⊢ (initSlotSpecPlaced A lim InitEnv S stk).onPanic (x, st0) s0 sf

theorem initPanicPostPlaced_of_false [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (S : RunSem) (x : InitGhost) (st0 : M.σ) (stk : Nat) {s0 sf : State} (F : SepProp) :
    InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf (⌜False⌝ ∗ F) :=
  Entails.pure_left False.elim

theorem initPanicPostPlaced_of_allocFailed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (S : RunSem) (x : InitGhost) (st0 : M.σ) (stk : Nat)
    {s0 s sf : State} (htr : s.trace = s0.trace) (F : SepProp) :
    InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf
      ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  dsimp only [InitPanicPostPlaced, initSlotSpecPlaced, withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hfail, _⟩ => ?_
  have hfail0 : allocFailedIn s0 sf := by simpa [allocFailedIn, htr] using hfail
  exact Entails.pure_right (Or.inr hfail0) (entails_anyHeap _)

theorem initPanicPostPlaced_of_panicked [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (S : RunSem) (x : InitGhost) (st0 : M.σ) (stk : Nat)
    {s0 s : State} (hfail : allocFailedIn s0 s) (P : SepProp) :
    InitPanicPostPlaced A lim InitEnv S x st0 stk s0 (Rust.panicked s) P := by
  dsimp only [InitPanicPostPlaced, initSlotSpecPlaced, withLsCodeRoLoaded]
  have hfail' : allocFailedIn s0 (Rust.panicked s) := by
    simpa [Rust.panicked, allocFailedIn] using hfail
  exact Entails.pure_right (Or.inr hfail') (entails_anyHeap P)

/-- Budget-threaded `stage2MemPlaced` (`BB038`, offset `0x0390`). -/
def stage2MemPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 s : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 0 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Budget-threaded `stage3MemPlaced` (`BB064b`, offset `0x0760`). -/
def stage3MemPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (stk : Nat) (s0 s : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 32 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
    memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Budget-threaded `stage4MemPlaced` (`BB129`, offset `0x10a4`). -/
def stage4MemPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk kemCtBytes hkSlotBytes : List (BitVec 8))
    (pqspkPtr kemCtPtr : BitVec 64) (opkId : BitVec 32)
    (stk : Nat) (s0 s : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  ⌜kemCtBytes.length = 1569 ∧ hkSlotBytes.length = 100⌝ ∗
    storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 160 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
    memRegion fsp 0x60 ∗
    ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
    A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ kemCtBytes) ∗
    ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
    ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗
    ((fsp + 0x930#64) ↦ₛ hkSlotBytes) ∗
    memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Budget-threaded `stage5MemPlaced` (`BB143`, offset `0x1484`). -/
def stage5MemPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (stk : Nat) (s0 s : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 192 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    sessionStateAt A.repAlloc (fsp + 0x460#64) sg ss ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget

end
