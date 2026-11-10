/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded `SessionRecord::serialize` Specifications and Stub Contracts

Defines the canonical serialization allocation envelope `SerializeEnvX`, total-correctness
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) budget-threaded specifications (`encodeChainSpecX`,
`encodeRawSpecX`, `sessionCloneSpecX`, `dropSessionStructureLocal1SpecX`, `serializeSpecX`,
`serializeCanonSpecX`), and the relocatable `[LibsignalPlacement]` stub bundle
`SerContractsXPlaced M A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl withMemEq
  lsρ lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym lsMemcpySym
)
open CryptoVerification.RustHeap (vecU8At vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost okTagVec sessionStateAt
)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost sessionStateReprAt sessionRecordAt
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionMemcpySpec
  ls_hook_ok_of_caller ls_subroutine_ok_cl_of_plain_prog ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (DropSessionStructureGhost)
open CryptoVerification.E2E.Record (lenField encodeRecord)
open CryptoVerification.E2E.Record.Serialization (
  encChainMem encSessionMem encRecordMem CanonRecord protoChainAt
  EncodeChainGhost EncodeRawGhost SessionCloneGhost SerializeGhost
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
  FitsEvents FitsEnv SeqEnv FreeOnlyEvs VmPreserved
  rustAllocEvents rustReallocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliDeallocBudgetExternSpecWithStack
  rustCliReallocBudgetExternSpecWithStack
  rustCliAllocNoOomSpecWithStack rustCliReallocNoOomExternSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyBudgetSpec sessionMemmoveBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs EncodeChainEnv EncodeRawEnv SessionCloneEnv SerializeEnv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget (Stage2ContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (
  allocContractsPlaced_of_stage2ContractsPlaced
)

/-! ## Re-exported stack budgets at `extHookStack` -/

abbrev encodeChainStackX : Nat := Proofs.libsignal.Hooks2.encodeChainStackX
abbrev encodeRawStackX : Nat := Proofs.libsignal.Hooks2.encodeRawStackX
abbrev sessionCloneStackX : Nat := Proofs.libsignal.Hooks2.sessionCloneStackX
abbrev dropSessionStructureLocal1StackX : Nat :=
  Proofs.libsignal.Hooks2.dropSessionStructureLocal1StackX
abbrev serializeStackX : Nat := Proofs.libsignal.Hooks2.serializeStackX

theorem serializeStackX_le_recordSerializeStack :
    serializeStackX ≤ CryptoVerification.E2E.Bin.recordSerializeStack :=
  Proofs.libsignal.Hooks2.serializeStackX_le_recordSerializeStack

/-! ## Canonical `SerializeEnvX` envelope -/

/-- Canonical allocation envelope for `<SessionRecord>::serialize`, composing the bounded allocation
prefix `SerializeEnv g r` with the pure-deallocation suffix `FreeOnlyEvs` emitted by
`drop_glue<SessionStructure> [local#1]` on the `Some` branch. -/
def SerializeEnvX (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (SerializeEnv g r) FreeOnlyEvs

theorem SerializeEnvX.of_serializeEnv {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {evs : List AllocEvent} (h : SerializeEnv g r evs) :
    SerializeEnvX g r evs :=
  SeqEnv.inl h

theorem SerializeEnvX.nil (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    SerializeEnvX g r [] :=
  SeqEnv.inl (BoundedRustEvs.nil _ _)

theorem SerializeEnvX.append_free {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {evs₁ evs₂ : List AllocEvent} (h1 : SerializeEnv g r evs₁) (h2 : FreeOnlyEvs evs₂) :
    SerializeEnvX g r (evs₁ ++ evs₂) :=
  SeqEnv.append h1 h2

theorem SerializeEnvX.append_free' {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {evs₁ evs₂ : List AllocEvent} (h1 : SerializeEnvX g r evs₁) (h2 : FreeOnlyEvs evs₂) :
    SerializeEnvX g r (evs₁ ++ evs₂) := by
  rcases h1 with h1 | ⟨a, b, rfl, ha, hb⟩
  · exact SeqEnv.append h1 h2
  · rw [List.append_assoc]
    exact SeqEnv.append ha (FreeOnlyEvs.append hb h2)

theorem fitsEnv_serializeEnv_of_serializeEnvX {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (h : FitsEnv M lim st (SerializeEnvX g r)) :
    FitsEnv M lim st (SerializeEnv g r) :=
  FitsEnv.seq_left h

theorem SerializeEnvX.event_bounds {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {evs : List AllocEvent} (h : SerializeEnvX g r evs) :
    ∀ ev ∈ evs,
      ev.withinMaxAlloc ∧
      ev.reqBytes ≤ 256 * ((encRecordMem g r).length + 16) ∧
      (∀ al req, ev = .aligned al req → al ≤ 16) ∧
      (∀ al o n, ev = .realloc al o n → al ≤ 16) := by
  intro ev hev
  rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
  · exact h1.2 ev hev
  · rcases List.mem_append.mp hev with hm1 | hm2
    · exact h1.2 ev hm1
    · obtain ⟨al, sz, rfl⟩ := h2 ev hm2
      refine ⟨trivial, Nat.zero_le _, ?_, ?_⟩
      · rintro _ _ ⟨⟩
      · rintro _ _ _ ⟨⟩

/-! ## Budget-threaded specifications -/

/-- Budget-threaded `encodeChainSpec` at `encodeChainStackX`. -/
def encodeChainSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 ∧
      FitsEnv M lim st (EncodeChainEnv x)⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeChainStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ EncodeChainEnv x evs⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encodeChainStackX

/-- Budget-threaded `encodeRawSpec` at `encodeRawStackX`. -/
def encodeRawSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeRawGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32 ∧
      FitsEnv M lim st (EncodeRawEnv x)⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeRawStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ EncodeRawEnv x evs⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encodeRawStackX

/-- Budget-threaded `sessionCloneSpec` at `sessionCloneStackX`. -/
def sessionCloneSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SessionCloneEnv x.G x.s)⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗ memRegion x.dst 344 ∗
      A.pool lim st s ∗ stackAt s.sp sessionCloneStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SessionCloneEnv x.G x.s evs⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A.repAlloc x.dst G' x.s) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp sessionCloneStackX

/-- Budget-threaded `drop_glue<SessionStructure> [local#1]` at `dropSessionStructureLocal1StackX`
(`FreeOnlyEvs`, `0` `FitsEnv` preconditions). -/
def dropSessionStructureLocal1SpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal1StackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal1StackX

/-- Budget-threaded memory-level `serializeSpec` at `serializeStackX` using `SerializeEnvX`. -/
def serializeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encRecordMem x.g x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializeEnvX x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializeEnvX x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encRecordMem x.g x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-- Budget-threaded canonical `serializeCanonSpec` at `serializeStackX` using `SerializeEnvX`. -/
def serializeCanonSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializeEnvX x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializeEnvX x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-! ## Relocatable `[LibsignalPlacement]` stub contracts (`SerContractsXPlaced`) -/

/-- Relocatable budget-threaded `[LibsignalPlacement]` counterpart of `SerContractsX`:
allocator / `shim` / `memmove` (`AllocContractsPlaced M A lim H` at `extHookStack`) plus
`VmPreserved`-preserving owned-source `memcpy` (`sessionMemcpyBudgetSpec extHookStack`). -/
structure SerContractsXPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : AllocContractsPlaced M A lim H
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))

/-- Construct `SerContractsXPlaced M A lim H` from block-0 `withLsCodeLoaded` contracts. -/
theorem SerContractsXPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl session2ShimBudgetSpecX))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove")
      (withLsCodeLoaded lsmpl (sessionMemmoveBudgetSpec extHookStack)))
    (hmemcpy : subroutine_ok blk0Prog (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl (sessionMemcpyBudgetSpec extHookStack))) :
    SerContractsXPlaced M A lim H where
  alloc := AllocContractsPlaced.of_block0 halloc hdealloc hrealloc hshim hmemmove
  memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy

/-- Construct `SerContractsXPlaced M A lim H` from `HookSat H` single-step hooks. -/
theorem SerContractsXPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hmemmove : HookSat H "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hmemcpy : HookSat H lsMemcpySym (sessionMemcpyBudgetSpec extHookStack)) :
    SerContractsXPlaced M A lim H where
  alloc := AllocContractsPlaced.of_hooks halloc hdealloc hrealloc hshim hmemmove
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)

theorem serContractsXPlaced_of_stage2ContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H) :
    SerContractsXPlaced M A lim H where
  alloc := allocContractsPlaced_of_stage2ContractsPlaced hC
  memcpy := hC.memcpy

/-! ## State-specialized `[LibsignalPlacement]` call helpers -/

private theorem pack_withMemEq {α : Type} {m : Memory} {S : Spec α} {x : α}
    {s0 : State} {R : SepProp} (hm : s0.mem = m) (hp : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (withMemEq m S).pre x s0 ∗ R := by
  dsimp only [withMemEq]
  rw [sepConj_assoc, sepConj_left_comm _ ⌜s0.mem = m⌝, satisfies_pure_sepConj]
  exact ⟨hm, hp⟩

theorem shim_placed_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hshim : subroutine_ok prog entry (withLsCl pl session2ShimBudgetSpecX))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (_ : Unit) s' =>
          ⌜s'.mem = s.mem⌝ ∗ stackAt s'.sp extHookStack
        post := fun (_ : Unit) s0 sf =>
          ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp extHookStack } := by
  have h0 := lscall_of_withLsCl hshim hcl
  refine subroutine_ok_mono h0 (fun _ _ s0 hp => ?_) (fun _ _ _ _ hq => ?_)
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact pack_withMemEq hp.1 (by dsimp only [session2ShimBudgetSpecX]; exact hp.2)
  · dsimp only [withMemEq, session2ShimBudgetSpecX] at hq ⊢
    exact hq

theorem alloc_placed_ok_at_stateX {pl : Obj.MultiPlacement} [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {entry : BitVec 64} {s : State}
    (halloc : subroutine_ok prog entry
      (withLsCl pl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (size, align, st) s' =>
          ⌜s'.mem = s.mem ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align ∧ LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).post
        onOom := (rustCliAllocBudgetSpecWithStack M A lim false extHookStack).onOom } := by
  have h0 := lscall_of_withLsCl halloc hcl
  refine subroutine_ok_map_oom' h0 fun ⟨size, align, st⟩ R s0 hp =>
    ⟨(size, align, st), R, ?_, fun _ hq => hq, fun _ ho => ho⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hx0, hx1, hlay, hlr⟩, hrest⟩
  refine pack_withMemEq hm ?_
  dsimp only [rustCliAllocBudgetSpecWithStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hlay, hlr⟩, hrest⟩

theorem allocNoOom_placed_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {s : State} (hA : AllocContractsPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      { pre := fun (size, align, st) s' =>
          ⌜s'.mem = s.mem ∧
            (s'.readReg64 .x0).toNat = size ∧ (s'.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align) ∧
            LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliAllocNoOomSpecWithStack M A lim false extHookStack).post } := by
  have h0 := hA.allocNoOom_call (callerProg := callerProg) hcl
  refine subroutine_ok_mono h0 (fun ⟨size, align, st⟩ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hx0, hx1, hlay, hfit, hlr⟩, hrest⟩
  refine pack_withMemEq hm ?_
  dsimp only [rustCliAllocNoOomSpecWithStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hlay, hfit, hlr⟩, hrest⟩

theorem dealloc_placed_ok_at_stateX {pl : Obj.MultiPlacement} [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hdealloc : subroutine_ok prog entry
      (withLsCl pl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (p, size, align, st) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ RustLayoutOk size align ∧
            LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack).post } := by
  have h0 := lscall_of_withLsCl hdealloc hcl
  refine subroutine_ok_mono h0 (fun ⟨p, size, align, st⟩ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hx0, hx1, hx2, hlay, hlr⟩, hrest⟩
  refine pack_withMemEq hm ?_
  dsimp only [rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2, hlay, hlr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩

theorem realloc_placed_ok_at_stateX {pl : Obj.MultiPlacement} [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hrealloc : subroutine_ok prog entry
      (withLsCl pl (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (p, old_size, align, new_size, bs, st) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = old_size ∧
            (s'.readReg64 .x2).toNat = align ∧ (s'.readReg64 .x3).toNat = new_size ∧
            RustLayoutOk old_size align ∧ RustLayoutOk new_size align ∧
            bs.length ≤ old_size ∧ bs.length ≤ new_size ∧
            LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.live p old_size align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack).post
        onOom := (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack).onOom } := by
  have h0 := lscall_of_withLsCl hrealloc hcl
  refine subroutine_ok_map_oom' h0 fun ⟨p, old_size, align, new_size, bs, st⟩ R s0 hp =>
    ⟨(p, old_size, align, new_size, bs, st), R, ?_, fun _ hq => hq, fun _ ho => ho⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hx0, hx1, hx2, hx3, hold, hnew, hbs1, hbs2, hlr⟩, hrest⟩
  refine pack_withMemEq hm ?_
  dsimp only [rustCliReallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hbs1, hbs2, hlr⟩,
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩

theorem reallocNoOom_placed_ok_at_stateX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {s : State} (hA : AllocContractsPlaced M A lim H)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      { pre := fun (p, old_size, align, new_size, bs, st) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = old_size ∧
            (s'.readReg64 .x2).toNat = align ∧ (s'.readReg64 .x3).toNat = new_size ∧
            RustLayoutOk old_size align ∧ RustLayoutOk new_size align ∧
            bs.length ≤ old_size ∧ bs.length ≤ new_size ∧
            FitsEvents M lim st (rustReallocEvents old_size new_size align) ∧
            LsRetAddr624 (s'.readReg64 .lr)⌝ ∗
          A.live p old_size align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
          A.pool lim st s' ∗ stackAt s'.sp extHookStack
        post := (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).post } := by
  have h0 := hA.reallocNoOom_call (callerProg := callerProg) hcl
  refine subroutine_ok_mono h0
    (fun ⟨p, old_size, align, new_size, bs, st⟩ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hx0, hx1, hx2, hx3, hold, hnew, hbs1, hbs2, hfit, hlr⟩, hrest⟩
  refine pack_withMemEq hm ?_
  dsimp only [rustCliReallocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hbs1, hbs2, hfit, hlr⟩,
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩

theorem memcpy_placed_ok_at_stateX {pl : Obj.MultiPlacement} {prog : Program}
    {entry : BitVec 64} {s : State}
    (hmemcpy : subroutine_ok prog entry (withLsCl pl (sessionMemcpyBudgetSpec extHookStack)))
    (hcl : LibsignalCodeLoaded pl s.mem) :
    subroutine_ok prog entry
      { pre := fun (dst, src, bs) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
            (s'.readReg64 .x2).toNat = bs.length⌝ ∗
          memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s'.sp extHookStack
        post := (sessionMemcpyBudgetSpec extHookStack).post } := by
  have h0 := lscall_of_withLsCl hmemcpy hcl
  refine subroutine_ok_mono h0 (fun ⟨dst, src, bs⟩ _ s0 hp => ?_) (fun _ _ _ _ hq => hq)
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hm, hx0, hx1, hx2⟩, hrest⟩
  refine pack_withMemEq hm ?_
  dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2⟩, hrest⟩

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
