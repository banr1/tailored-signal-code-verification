/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsCroPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Inlined `SessionStructure::decode` Loop Definitions

Input-bounded allocation envelopes (`OverDecFieldEnv`, `OverDecPrefixEnv`, `OverPrevDecodeEnv`),
budget-threaded spatial bundles (`overDecHeapBudget`), and `[LibsignalPlacement]` total-correctness
loop and step contracts on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget

open Arm64 ProofLib SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost sliceCursorAfter)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecAnyField OverDecBytesField OverDecG OverDecRecvField OverDecRegsCroPlaced
  OverDecRegsPlaced OverDecSenderField OverDecVarintField OverPrevEncOKAt
  overDecArmOff overDecScratchPostExt overDecScratchPre overDecStackX overDecWt
  overDecHeapExt overPrevElemAtExt overPrevElemRestExt
)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ prostSSGQAt ssgqOf)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  boundedRustEvs_bytesMergeEnv_of_some fitsEnv_bytesMerge_of_some
)

/-! ## Input-Bounded Allocation Envelopes and Stepping Lemmas -/

/-- Per-field allocation envelope of one inlined `SessionStructure::decode` field `fl`
(aligned with `B3DeserQ.DefsBudget.MergeFieldQEnv`). -/
def OverDecFieldEnv (fl : GenFieldQ) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * fl.enc.length) (256 * (fl.enc.length + 16)) evs

/-- Loop-prefix allocation envelope after decoding the prefix of `enc` preceding `rest`. -/
def OverDecPrefixEnv (enc rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * (enc.length - rest.length) + 32) (256 * (enc.length + 16)) evs

/-- Total allocation envelope of inlined `SessionStructure::decode` on `enc`
(`+0x1ee8 → +0x2620`). -/
def OverPrevDecodeEnv (enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * enc.length + 64) (256 * (enc.length + 16)) evs

theorem overDecFieldEnv_nil (fl : GenFieldQ) : OverDecFieldEnv fl [] :=
  BoundedRustEvs.nil _ _

theorem overDecPrefixEnv_nil (enc rest : List (BitVec 8)) : OverDecPrefixEnv enc rest [] :=
  BoundedRustEvs.nil _ _

/-- Every encoded `GenFieldQ` has at least one byte (its protobuf tag/wire-type key). -/
theorem genFieldQ_enc_pos (fl : GenFieldQ) : 1 ≤ fl.enc.length := by
  unfold GenFieldQ.enc CryptoVerification.LibsignalProtoCodec.encodeKey
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  rw [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  split <;> simp [List.length_append]

/-- On `mergeBytes x.wt x.bs = some (b, rest)` with `b.length ≤ fl.enc.length` and
`b.length < 2 ^ 32`, `BytesMergeEnv x` fits inside `OverDecFieldEnv fl`. -/
theorem overDecFieldEnv_of_bytesMerge {fl : GenFieldQ} {x : BytesMergeGhost}
    {b rest : List (BitVec 8)} {evs : List AllocEvent}
    (hm : mergeBytes x.wt x.bs = some (b, rest))
    (hb_le : b.length ≤ fl.enc.length)
    (hb_lt : b.length < 2 ^ 32)
    (hevs : BytesMergeEnv x evs) :
    OverDecFieldEnv fl evs := by
  have hpos := genFieldQ_enc_pos fl
  have hmax : 2 * b.length + 8 ≤ MallocngMaxAllocSize := by
    unfold MallocngMaxAllocSize; omega
  exact BoundedRustEvs.mono (by omega) (by omega)
    (boundedRustEvs_bytesMergeEnv_of_some hm hmax hevs)

theorem fitsEnv_bytesMerge_of_overDecField {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fl : GenFieldQ} {x : BytesMergeGhost} {b rest : List (BitVec 8)}
    (hm : mergeBytes x.wt x.bs = some (b, rest))
    (hb_le : b.length ≤ fl.enc.length)
    (hb_lt : b.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (OverDecFieldEnv fl)) :
    FitsEnv M lim st (BytesMergeEnv x) := by
  have hpos := genFieldQ_enc_pos fl
  have hmax : 2 * b.length + 8 ≤ MallocngMaxAllocSize := by
    unfold MallocngMaxAllocSize; omega
  exact fitsEnv_bytesMerge_of_some hm hmax (by omega) (by omega) hFit

theorem overDecPrefixEnv_entry (enc : List (BitVec 8)) {evs : List AllocEvent}
    (h : BoundedRustEvs 32 0 evs) : OverDecPrefixEnv enc enc evs := by
  unfold OverDecPrefixEnv
  rw [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
  exact BoundedRustEvs.mono (Nat.le_refl _) (Nat.zero_le _) h

/-- Loop-body prefix step: `OverDecPrefixEnv enc (fl.enc ++ rest)` followed by `OverDecFieldEnv fl`
yields `OverDecPrefixEnv enc rest` whenever `(fl.enc ++ rest) <:+ enc`. -/
theorem overDecPrefixEnv_step {enc rest : List (BitVec 8)} {fl : GenFieldQ}
    {evs₁ evs₂ : List AllocEvent}
    (hsuf : (fl.enc ++ rest) <:+ enc)
    (h1 : OverDecPrefixEnv enc (fl.enc ++ rest) evs₁)
    (h2 : OverDecFieldEnv fl evs₂) :
    OverDecPrefixEnv enc rest (evs₁ ++ evs₂) := by
  obtain ⟨pfx, hpfx⟩ := hsuf
  have hlen : pfx.length + fl.enc.length + rest.length = enc.length := by
    have := congrArg List.length hpfx
    rw [List.length_append, List.length_append] at this
    omega
  unfold OverDecPrefixEnv at h1 ⊢
  unfold OverDecFieldEnv at h2
  rw [List.length_append] at h1
  exact BoundedRustEvs.mono (by omega) (Nat.max_le.mpr ⟨Nat.le_refl _, by omega⟩)
    (BoundedRustEvs.append h1 h2)

theorem overDecPrefixEnv_finish {enc : List (BitVec 8)} {evs₁ evs₂ : List AllocEvent} {r₂ : Nat}
    (h1 : OverDecPrefixEnv enc [] evs₁)
    (h2 : BoundedRustEvs 32 r₂ evs₂)
    (hr2 : r₂ ≤ 256 * (enc.length + 16)) :
    OverPrevDecodeEnv enc (evs₁ ++ evs₂) := by
  unfold OverDecPrefixEnv at h1
  unfold OverPrevDecodeEnv
  simp only [List.length_nil, Nat.sub_zero] at h1
  exact BoundedRustEvs.mono (by omega) (Nat.max_le.mpr ⟨Nat.le_refl _, hr2⟩)
    (BoundedRustEvs.append h1 h2)

/-- Split `FitsEnv M lim st (OverPrevDecodeEnv enc)` into `FitsEnv M lim st (OverDecFieldEnv fl)`
whenever `(fl.enc ++ rest) <:+ enc`. -/
theorem fitsEnv_overDecField_of_total {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {enc rest : List (BitVec 8)} {fl : GenFieldQ}
    (hsuf : (fl.enc ++ rest) <:+ enc)
    (hFit : FitsEnv M lim st (OverPrevDecodeEnv enc)) :
    FitsEnv M lim st (OverDecFieldEnv fl) := by
  obtain ⟨pfx, hpfx⟩ := hsuf
  have hlen : fl.enc.length ≤ enc.length := by
    have := congrArg List.length hpfx
    rw [List.length_append, List.length_append] at this
    omega
  intro evs hevs
  exact hFit evs (BoundedRustEvs.mono (by omega) (by omega) hevs)

/-! ## Budget-Threaded Spatial Bundles and `atState` Bridges -/

/-- Archived element of `previous_sessions` at `prevPtr` under `A.repAlloc`. -/
abbrev overPrevElemAtBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) : SepProp :=
  overPrevElemAtExt A.repAlloc prevCap prevPtr encCap encPtr enc

/-- `overPrevElemAtBudget` without `encPtr ↦ₛ enc` (lent to the slice cursor during the loop). -/
abbrev overPrevElemRestBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) : SepProp :=
  overPrevElemRestExt A.repAlloc prevCap prevPtr encCap encPtr enc

/-- Closure scratch after the decode at `+0x2620` under `A.repAlloc`. -/
abbrev overDecScratchPostBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (q : BitVec 64) (v : SSGQ) : SepProp :=
  overDecScratchPostExt A.repAlloc q v

/-- Budget-threaded spatial invariant of the decode loop at undecoded suffix `rest`, partial `SSGQ`
value `v`, cost-model state `st`, and machine state `s`. -/
def overDecHeapBudget {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  overPrevElemRestBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

theorem overDecHeapBudget_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) :
    overDecHeapBudget A lim st s g rest v =
      overDecHeapExt (A.atState lim st s) g rest v :=
  rfl

/-! ## Relocatable Budget-Threaded Loop and Step Contracts -/

/-- Lift any `SepWPp` by threading `LibsignalCodeRoLoaded lsmpl` via `Steps.keepsFrozen`. -/
theorem sepWPp_lift_cro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P
      (fun sf P_f => LibsignalCodeRoLoaded lsmpl sf.mem ∧ Q sf P_f) Qp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.sepWPp_lift_cro hcro hwp

theorem sepWPp_lift_cro_regs [LibsignalPlacement] {ext : String → Option (State → State)}
    {ret off : BitVec 64} {s0 s : State} {g : OverDecG} {P : SepProp}
    {Rpost : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp (lsProg_518 ext) ret s P
      (fun sf P_f => OverDecRegsPlaced ext s0 g off sf ∧ Rpost sf P_f)
      (fun _ _ => False)) :
    SepWPp (lsProg_518 ext) ret s P
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g off sf ∧ Rpost sf P_f)
      (fun _ _ => False) := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hregs, hR⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, .inl ⟨hpc, hrun, P_f, hmf,
      ⟨hcro.of_keepsFrozen hsteps.keepsFrozen, hregs⟩, hR⟩⟩
  · exact ⟨sf, hsteps, .inr hpan⟩

/-- Fixed-`ext` `[LibsignalPlacement]` budget-threaded inlined `SessionStructure::decode` of `enc`
(`(blkPl_518).base + 0x1ee8 → (blkPl_518).base + 0x2620`, closure frame `s.sp`) on `lsProg_518 ext`
under `LibsignalCodeRoLoaded lsmpl`. -/
def OverPrevDecodeCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st0 : M.σ) (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8))),
    OverPrevEncOKAt enc sess →
    FitsEnv M lim st0 (OverPrevDecodeEnv enc) →
    LibsignalCodeRoLoaded lsmpl s.mem →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x21 = s.sp + 0x930#64 →
    s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 →
    s.readReg64 .x27 = prevPtr →
    s.readReg64 .x29 = s.sp + 0xc70#64 →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        A.pool lim st0 s)
      (fun sf P_f =>
        (∃ evs, OverPrevDecodeEnv enc evs ∧
          (P_f ⊢ overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
              overDecScratchPostBudget A s.sp (ssgqOf sess) ∗
              stackAt s.sp overDecStackX ∗
              A.pool lim (M.stepEvents evs st0) sf ∗ anyHeap)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False)

/-- Relocatable `[LibsignalPlacement]` budget-threaded inlined `SessionStructure::decode` of `enc`
quantified over `ext`. -/
def OverPrevDecodePlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ (ext : String → Option (State → State)), OverPrevDecodeCroPlacedAt A lim ext

/-- Relocatable `[LibsignalPlacement]` budget-threaded Entry (`+0x1ee8 → +0x216c`, `0` allocations). -/
def OverDecEntryPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ (ext : String → Option (State → State)) (st : M.σ) (s0 s : State) (g : OverDecG),
    g.enc ≠ [] → g.enc.length < 2 ^ 62 →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running → s.sp = g.q → (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x19 = g.r19 → s.readReg64 .x20 = g.r20 → s.readReg64 .x26 = g.r26 →
    s.readReg64 .x21 = g.q + 0x930#64 → s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 → s.readReg64 .x27 = g.prevPtr →
    s.readReg64 .x29 = g.q + 0xc70#64 →
    calleeSavedVRegs s = calleeSavedVRegs g.sv →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overPrevElemAtBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        overDecScratchPre g.q ∗ stackAt g.q overDecStackX ∗ A.pool lim st s)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g g.enc SSGQ.empty))
      (fun _ _ => False)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded Entry (`+0x1ee8 → +0x216c`, `0` allocations). -/
def OverDecEntryCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG),
    g.enc ≠ [] → g.enc.length < 2 ^ 62 →
    LibsignalCodeRoLoaded lsmpl s.mem →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running → s.sp = g.q → (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x19 = g.r19 → s.readReg64 .x20 = g.r20 → s.readReg64 .x26 = g.r26 →
    s.readReg64 .x21 = g.q + 0x930#64 → s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 → s.readReg64 .x27 = g.prevPtr →
    s.readReg64 .x29 = g.q + 0xc70#64 →
    calleeSavedVRegs s = calleeSavedVRegs g.sv →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overPrevElemAtBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        overDecScratchPre g.q ∗ stackAt g.q overDecStackX ∗ A.pool lim st s)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g g.enc SSGQ.empty))
      (fun _ _ => False)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded one-field step (`+0x216c → +0x2160`)
restricted by `P`. -/
def OverDecFieldCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (P : GenFieldQ → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    FitsEnv M lim st (OverDecFieldEnv fl) →
    OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeapBudget A lim st s g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        ∃ evs, OverDecFieldEnv fl evs ∧
          (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest (v.apply fl)))
      (fun _ _ => False)

/-- Relocatable `[LibsignalPlacement]` budget-threaded one-field step (`+0x216c → +0x2160`)
quantified over `ext`. -/
def OverDecFieldPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (P : GenFieldQ → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)), OverDecFieldCroPlacedAt A lim ext P

/-- Relocatable `[LibsignalPlacement]` budget-threaded loop head (`+0x2160 → +0x216c`) when
`rest ≠ []` (`0` allocations). -/
def OverDecHeadConsPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ (ext : String → Option (State → State)) (st : M.σ) (s0 s : State)
    (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8)),
    rest ≠ [] → rest <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overDecHeapBudget A lim st s g rest v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g rest v))
      (fun _ _ => False)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded loop head (`+0x2160 → +0x216c`) when
`rest ≠ []` (`0` allocations). -/
def OverDecHeadConsCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8)),
    rest ≠ [] → rest <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overDecHeapBudget A lim st s g rest v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g rest v))
      (fun _ _ => False)

/-- Relocatable `[LibsignalPlacement]` budget-threaded loop head (`+0x2160 → +0x2620`) when
`rest = []` (`0` allocations). -/
def OverDecHeadNilPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ (ext : String → Option (State → State)) (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ),
    g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overDecHeapBudget A lim st s g [] v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g [] v))
      (fun _ _ => False)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded loop head (`+0x2160 → +0x2620`) when
`rest = []` (`0` allocations). -/
def OverDecHeadNilCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ),
    g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overDecHeapBudget A lim st s g [] v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g [] v))
      (fun _ _ => False)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded Key dispatch (`+0x216c → overDecArmOff fl`,
`0` allocations on `OverDecAnyField fl` + `fl.Ok`). -/
def OverDecKeyCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    OverDecAnyField fl → fl.Ok →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + overDecArmOff fl) s
      (overDecHeapBudget A lim st s g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) sf ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g (fl.payload ++ rest) v))
      (fun _ _ => False)

/-- Relocatable `[LibsignalPlacement]` budget-threaded Key dispatch quantified over `ext`. -/
def OverDecKeyPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ (ext : String → Option (State → State)), OverDecKeyCroPlacedAt A lim ext

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded Arm contract
(`overDecArmOff fl → +0x2160`). -/
def OverDecArmCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (P : GenFieldQ → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    FitsEnv M lim st (OverDecFieldEnv fl) →
    OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) s →
    s.readReg64 .x0 = overDecWt fl →
    s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeapBudget A lim st s g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        ∃ evs, OverDecFieldEnv fl evs ∧
          (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest (v.apply fl)))
      (fun _ _ => False)

/-- Relocatable `[LibsignalPlacement]` budget-threaded Arm contract quantified over `ext`. -/
def OverDecArmPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (P : GenFieldQ → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)), OverDecArmCroPlacedAt A lim ext P

abbrev OverDecArmCroPlacedAtTR [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (P : GenFieldQ → Prop) : Prop :=
  OverDecArmCroPlacedAt A lim ext P

abbrev OverDecArmPlacedStmtTR [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (P : GenFieldQ → Prop) : Prop :=
  OverDecArmPlacedStmt A lim P

theorem OverDecArmPlacedStmt.toTR [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : GenFieldQ → Prop}
    (h : OverDecArmPlacedStmt A lim P) : OverDecArmPlacedStmtTR A lim P := h

theorem overDecEntry_cro_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : OverDecEntryPlacedStmt A lim)
    (ext : String → Option (State → State)) : OverDecEntryCroPlacedAt A lim ext := by
  intro st s0 s g hne hlen hcro hcl hpc hrun hsp hal htr h19 h20 h26 h21 h24 h25 h27 h29 hv
  exact sepWPp_lift_cro_regs hcro
    (h ext st s0 s g hne hlen hcl hpc hrun hsp hal htr h19 h20 h26 h21 h24 h25 h27 h29 hv)

theorem overDecHeadCons_cro_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : OverDecHeadConsPlacedStmt A lim)
    (ext : String → Option (State → State)) : OverDecHeadConsCroPlacedAt A lim ext := by
  intro st s0 s g v rest hne hsuf hlen ⟨hcro, hregs⟩
  exact sepWPp_lift_cro_regs hcro (h ext st s0 s g v rest hne hsuf hlen hregs)

theorem overDecHeadNil_cro_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : OverDecHeadNilPlacedStmt A lim)
    (ext : String → Option (State → State)) : OverDecHeadNilCroPlacedAt A lim ext := by
  intro st s0 s g v hlen ⟨hcro, hregs⟩
  exact sepWPp_lift_cro_regs hcro (h ext st s0 s g v hlen hregs)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
