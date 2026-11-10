/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Envelopes and Definitions for `SessionRecord::deserialize`

Input-length-bounded allocation envelopes (`ChainMergeGenEnv`, `MergeFieldGenEnv`,
`DeserializeGenEnv` via `BoundedRustEvs`), `RustCliAllocBudget`-threaded raw and
`[LibsignalPlacement]` specifications, loop invariants, and cross-block call helpers for Blocks
`11`, `15`, and `46`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget

open Arm64 ProofLib SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded withLsCl
  blkPC_1 blkPl_1 blkPC_7 blkPl_7 blkPC_8 blkPl_8 blkPC_76 blkPl_76
)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalProtoCodec (
  WireType decodeVarint encodeVarint mergeUint32 mergeBytes
)
open CryptoVerification.LibsignalTripleRatchet (
  reserveCap extHookStack LibsignalCodeRoLoaded withLsCodeRoLoaded
  extract_withLsCodeRoLoaded sepWP_seq_lscro
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  sliceCursorAt sliceCursorAfter
  DecodeVarintSliceGhost Int32MergeGhost BytesMergeGhost
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (
  decodeVarintSliceStackW int32MergeStackW bytesMergeStackW
)
open CryptoVerification.E2E.Record (
  encodeRecord recDeserializeStack pbVarintBody
)
open CryptoVerification.E2E.Record.Placed (
  blkPC_11 blkPl_11 blkPC_15 blkPl_15 blkPC_46 blkPl_46
  lsProg_11 lsProg_15 lsProg_46
)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.E2E.Record.DeserializeSeed (
  deserCalleeStack deserSpL deserSaved deserPlacedPC
  ls_call_ro_of_block ls_call_ro_of_cl
  chainMergeSavedRegs sp_sub_256_aligned_seedChain
  mergeBytes_lt128_seedChain mergeUint32_pbVarintBody_seedChain
  sliceCursorAfter_append_eq_seedChain
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  SSG ChainG ChainField GenField DeserializeScope recFields
  ssgAfter chainGAfter prostSSGAt prostChainGAt
  MergeFieldGenGhost ChainMergeGenGhost DeserializeGenGhost SegStepG
  encodeRecord_eq_recFields chainG_enc_eq_fields
)
open Proofs.libsignal.Hooks2 (
  mergeFieldStackX chainMergeStackX chainMergeSubStackX chainPlacedPC
  deserLocalsGA deserOutRecordGA
  stackAt_sub_to_bytesMerge_seedChainW stackAt_sub_to_int32Merge_seedChainW
)
open Proofs.libsignal.Stage1X (growOneChainStackX finishGrowStackX)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv fitsEvents_append
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents Int32MergeEnv int32MergeEvents
  int32MergeSpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  doReserveClearEvents bytesMergeEventsCore BytesMergeEnv
  bytesMergeRawSpecGen bmPreBoundBudget bmPostVec
)
open LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget (
  decodeVarintSliceSpecW int32MergeSpecW bytesMergeRawSpecW bytesMergePlacedSpecW
  bytesMergeStackW_eq_gen int32MergeStackW_eq_gen
  DecodeVarintSlicePlacedOkW Int32MergePlacedOkW BytesMergePlacedOkW
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env growOne104Events growOne104SpecX growOneChainSpecX GrowOneChainPlacedOkX
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem DDXB1 : True := trivial

/-! ## 1. Input-Bounded Allocation Envelopes & `FitsEnv` / `BoundedRustEvs` Lemmas -/

/-- Prefix allocation envelope after `k` fields of `message::merge<Chain>` on `c`. -/
def ChainPrefixEnv (c : ChainG) (k : Nat) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * ((c.fields.take k).flatMap ChainField.enc).length + 4)
    (256 * (c.payload.length + 16)) evs

/-- Total allocation envelope of `message::merge<Chain>` on `x`. -/
def ChainMergeGenEnv (x : ChainMergeGenGhost) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * x.c.payload.length + 4) (256 * (x.c.payload.length + 16)) evs

/-- Total allocation envelope of `SessionStructure::merge_field` on `x`. -/
def MergeFieldGenEnv (x : MergeFieldGenGhost) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * x.fld.enc.length) (256 * (x.fld.enc.length + 16)) evs

/-- Prefix allocation envelope after `k` outer fields of `SessionRecord::deserialize` on `r`. -/
def DeserPrefixEnv (r : SessionRecord (List (BitVec 8))) (k : Nat)
    (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * (((recFields r).take k).flatMap GenField.enc).length + 32)
    (256 * ((encodeRecord r).length + 16)) evs

/-- Total allocation envelope of `SessionRecord::deserialize` on `x`
    (`= RecordDeserializeEnv (encodeRecord x.r)` by `rfl`). -/
def DeserializeGenEnv (x : DeserializeGenGhost) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * (encodeRecord x.r).length + 64)
    (256 * ((encodeRecord x.r).length + 16)) evs

/-- Step a `FitsEnv M lim st (BoundedRustEvs c r)` budget across an already-emitted prefix
    `evs₁` satisfying `BoundedRustEvs c₁ r₁ evs₁` when `c₁ + c₂ ≤ c`, `r₁ ≤ r`, `r₂ ≤ r`. -/
theorem fitsEnv_step_boundedRustEvs {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {c₁ c₂ c r₁ r₂ r : Nat} {evs₁ : List AllocEvent}
    (h1 : BoundedRustEvs c₁ r₁ evs₁)
    (hc : c₁ + c₂ ≤ c) (hr1 : r₁ ≤ r) (hr2 : r₂ ≤ r)
    (hFit : FitsEnv M lim st (BoundedRustEvs c r)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (BoundedRustEvs c₂ r₂) := by
  intro evs₂ h2
  have happ : BoundedRustEvs c r (evs₁ ++ evs₂) :=
    BoundedRustEvs.mono hc (Nat.max_le.mpr ⟨hr1, hr2⟩) (BoundedRustEvs.append h1 h2)
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) happ)).2

/-- Specialize `fitsEnv_step_boundedRustEvs` to a concrete callee envelope `E`. -/
theorem fitsEnv_step_of_sub {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {c₁ c₂ c r₁ r₂ r : Nat} {evs₁ : List AllocEvent} {E : List AllocEvent → Prop}
    (h1 : BoundedRustEvs c₁ r₁ evs₁)
    (hsub : ∀ evs₂, E evs₂ → BoundedRustEvs c₂ r₂ evs₂)
    (hc : c₁ + c₂ ≤ c) (hr1 : r₁ ≤ r) (hr2 : r₂ ≤ r)
    (hFit : FitsEnv M lim st (BoundedRustEvs c r)) :
    FitsEnv M lim (M.stepEvents evs₁ st) E :=
  FitsEnv.mono hsub (fitsEnv_step_boundedRustEvs h1 hc hr1 hr2 hFit)

/-- Specialize `fitsEnv_step_of_sub` at the initial state `st` (`evs₁ = []`). -/
theorem fitsEnv_head_of_sub {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {c₂ c r₂ r : Nat} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → BoundedRustEvs c₂ r₂ evs)
    (hc : c₂ ≤ c) (hr : r₂ ≤ r)
    (hFit : FitsEnv M lim st (BoundedRustEvs c r)) :
    FitsEnv M lim st E :=
  FitsEnv.mono (fun evs he => BoundedRustEvs.mono hc hr (hsub evs he)) hFit

/-- `rustDeallocEvents sz align` always fits in `BoundedRustEvs 1 0`. -/
theorem boundedRustEvs_rustDeallocEvents (sz align : Nat) :
    BoundedRustEvs 1 0 (rustDeallocEvents sz align) := by
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  subst hev
  exact ⟨trivial, Nat.le_refl 0, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- `rustAllocEvents sz align` fits in `BoundedRustEvs 1 sz` when `align ≤ 16`, `align ≤ sz`,
    and `sz ≤ MallocngMaxAllocSize`. -/
theorem boundedRustEvs_rustAllocEvents {sz align : Nat}
    (hal16 : align ≤ 16) (halsz : align ≤ sz) (hmax : sz ≤ MallocngMaxAllocSize) :
    BoundedRustEvs 1 sz (rustAllocEvents sz align) := by
  unfold rustAllocEvents
  simp only [hal16, halsz, and_self, ↓reduceIte]
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax, Nat.le_refl sz, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- `rustReallocEvents old new align` fits in `BoundedRustEvs 1 new` when `align ≤ 16`,
    `align ≤ new`, and `new ≤ MallocngMaxAllocSize`. -/
theorem boundedRustEvs_rustReallocEvents (old : Nat) {new align : Nat}
    (hal16 : align ≤ 16) (halnew : align ≤ new) (hmax : new ≤ MallocngMaxAllocSize) :
    BoundedRustEvs 1 new (rustReallocEvents old new align) := by
  unfold rustReallocEvents
  simp only [hal16, halnew, and_self, ↓reduceIte]
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  refine ⟨hmax, Nat.le_refl new, (fun _ _ h => nomatch h), ?_⟩
  intro al _ _ h
  cases h
  exact hal16

/-- Every `DecodeVarintSliceEnv bs` execution emits at most 1 event of size `≤ 72`. -/
theorem boundedRustEvs_decodeVarintSliceEnv {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DecodeVarintSliceEnv bs evs) :
    BoundedRustEvs 1 72 evs := by
  subst h
  unfold decodeVarintSliceEvents
  cases decodeVarint bs with
  | some _ => exact BoundedRustEvs.nil 1 72
  | none =>
    exact boundedRustEvs_rustAllocEvents (by decide) (by decide) (by decide)

/-- On `decodeVarint bs = some p`, `DecodeVarintSliceEnv bs` emits `[]`. -/
theorem decodeVarintSliceEnv_eq_nil {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    {evs : List AllocEvent} (hdec : decodeVarint bs = some p) (hevs : DecodeVarintSliceEnv bs evs) :
    evs = [] := by
  rw [hevs, decodeVarintSliceEvents, hdec]

/-- Every `Int32MergeEnv x` execution emits at most 1 event of size `≤ 72`. -/
theorem boundedRustEvs_int32MergeEnv {x : Int32MergeGhost} {evs : List AllocEvent}
    (h : Int32MergeEnv x evs) :
    BoundedRustEvs 1 72 evs := by
  subst h
  unfold int32MergeEvents
  cases mergeUint32 x.wt x.bs with
  | some _ => exact BoundedRustEvs.nil 1 72
  | none =>
    exact boundedRustEvs_rustAllocEvents (by decide) (by decide) (by decide)

/-- On `mergeUint32 x.wt x.bs = some p`, `Int32MergeEnv x` emits `[]`. -/
theorem int32MergeEnv_eq_nil {x : Int32MergeGhost} {p : BitVec 32 × List (BitVec 8)}
    {evs : List AllocEvent} (hm : mergeUint32 x.wt x.bs = some p) (hevs : Int32MergeEnv x evs) :
    evs = [] := by
  rw [hevs, int32MergeEvents, hm]

/-- `doReserveClearEvents cap vLen` fits in `BoundedRustEvs 1 (2 * vLen + 8)` whenever
    `2 * vLen + 8 ≤ MallocngMaxAllocSize` (independent of `cap`, since `vLen ≤ cap` emits `[]`). -/
theorem boundedRustEvs_doReserveClearEvents (cap vLen : Nat)
    (hmax : 2 * vLen + 8 ≤ MallocngMaxAllocSize) :
    BoundedRustEvs 1 (2 * vLen + 8) (doReserveClearEvents cap vLen) := by
  unfold doReserveClearEvents
  split
  · exact BoundedRustEvs.nil 1 (2 * vLen + 8)
  · rename_i hlt
    have hcap_lt : cap < vLen := by omega
    have hrc_ge : 1 ≤ reserveCap cap 0 vLen := by
      unfold reserveCap; omega
    have hrc_le : reserveCap cap 0 vLen ≤ 2 * vLen + 8 := by
      unfold reserveCap; omega
    have hrc_max : reserveCap cap 0 vLen ≤ MallocngMaxAllocSize :=
      Nat.le_trans hrc_le hmax
    split
    · exact BoundedRustEvs.mono (Nat.le_refl 1) hrc_le
        (boundedRustEvs_rustAllocEvents (by decide) hrc_ge hrc_max)
    · exact BoundedRustEvs.mono (Nat.le_refl 1) hrc_le
        (boundedRustEvs_rustReallocEvents cap (by decide) hrc_ge hrc_max)

/-- On `mergeBytes x.wt x.bs = some (v, rest)`, `BytesMergeEnv x` emits at most 3 events of
    request size `≤ 2 * v.length + 8` (for ANY initial `x.valCap`). -/
theorem boundedRustEvs_bytesMergeEnv_of_some {x : BytesMergeGhost}
    {v rest : List (BitVec 8)} {evs : List AllocEvent}
    (hm : mergeBytes x.wt x.bs = some (v, rest))
    (hmax : 2 * v.length + 8 ≤ MallocngMaxAllocSize)
    (hevs : BytesMergeEnv x evs) :
    BoundedRustEvs 3 (2 * v.length + 8) evs := by
  unfold BytesMergeEnv at hevs
  rw [hevs]
  unfold bytesMergeEventsCore
  rw [hm]
  dsimp only
  split
  · exact BoundedRustEvs.nil 3 (2 * v.length + 8)
  · rename_i hne
    have hv_pos : 1 ≤ v.length := by omega
    have hv_le : v.length ≤ 2 * v.length + 8 := by omega
    have h1 : BoundedRustEvs 1 (2 * v.length + 8) (rustAllocEvents v.length 1) :=
      BoundedRustEvs.mono (Nat.le_refl 1) hv_le
        (boundedRustEvs_rustAllocEvents (by decide) hv_pos (Nat.le_trans hv_le hmax))
    have h2 : BoundedRustEvs 1 (2 * v.length + 8)
        (doReserveClearEvents x.valCap.toNat v.length) :=
      boundedRustEvs_doReserveClearEvents x.valCap.toNat v.length hmax
    have h3 : BoundedRustEvs 1 (2 * v.length + 8) (rustDeallocEvents v.length 1) :=
      BoundedRustEvs.mono (Nat.le_refl 1) (Nat.zero_le _)
        (boundedRustEvs_rustDeallocEvents v.length 1)
    have h12 := BoundedRustEvs.append h1 h2
    rw [Nat.max_self] at h12
    have h123 := BoundedRustEvs.append h12 h3
    rw [Nat.max_self] at h123
    exact BoundedRustEvs.mono (by decide) (Nat.le_refl _) h123

/-- Even before branching on `Ok` vs `Err`, if `mergeBytes x.wt x.bs = some (v, rest)`, then
    `FitsEnv M lim st (BoundedRustEvs c r)` implies `FitsEnv M lim st (BytesMergeEnv x)` when
    `3 ≤ c`, `2 * v.length + 8 ≤ r`, and `2 * v.length + 8 ≤ MallocngMaxAllocSize`. -/
theorem fitsEnv_bytesMerge_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : BytesMergeGhost} {v rest : List (BitVec 8)} {c r : Nat}
    (hm : mergeBytes x.wt x.bs = some (v, rest))
    (hmax : 2 * v.length + 8 ≤ MallocngMaxAllocSize)
    (hc : 3 ≤ c) (hr : 2 * v.length + 8 ≤ r)
    (hFit : FitsEnv M lim st (BoundedRustEvs c r)) :
    FitsEnv M lim st (BytesMergeEnv x) :=
  fitsEnv_head_of_sub (fun _ h => boundedRustEvs_bytesMergeEnv_of_some hm hmax h) hc hr hFit

/-- `GrowOne104Env cap` emits 1 event of request size `max (2 * cap.toNat) 4 * 104`. -/
theorem boundedRustEvs_growOne104Env {cap : BitVec 64} {evs : List AllocEvent}
    (hmax : max (2 * cap.toNat) 4 * 104 ≤ MallocngMaxAllocSize)
    (hevs : GrowOne104Env cap evs) :
    BoundedRustEvs 1 (max (2 * cap.toNat) 4 * 104) evs := by
  rw [hevs]
  unfold growOne104Events LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents
  have hge8 : 8 ≤ max (2 * cap.toNat) 4 * 104 := by omega
  split
  · exact boundedRustEvs_rustAllocEvents (by decide) hge8 hmax
  · exact boundedRustEvs_rustReallocEvents (cap.toNat * 104) (by decide) hge8 hmax

/-- Prefix length identity for `take (k + 1)` under `flatMap`. -/
theorem flatMap_take_succ_length {α β : Type} (f : α → List β) (xs : List α)
    {k : Nat} (hk : k < xs.length) :
    (((xs.take (k + 1)).flatMap f).length) =
      ((xs.take k).flatMap f).length + (f xs[k]).length := by
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.length_append,
    List.flatMap_singleton]

/-- Prefix `flatMap` length is bounded by full `flatMap` length. -/
theorem flatMap_take_length_le {α β : Type} (f : α → List β) (xs : List α) (k : Nat) :
    ((xs.take k).flatMap f).length ≤ (xs.flatMap f).length := by
  have hsplit : xs = xs.take k ++ xs.drop k := (List.take_append_drop k xs).symm
  conv => rhs; rw [hsplit, List.flatMap_append, List.length_append]
  omega

theorem chainPrefixEnv_zero (c : ChainG) : ChainPrefixEnv c 0 [] :=
  BoundedRustEvs.nil _ _

theorem chainPrefixEnv_at_length {x : ChainMergeGenGhost} {evs : List AllocEvent} :
    ChainPrefixEnv x.c x.c.fields.length evs → ChainMergeGenEnv x evs := by
  intro h
  have hle : ((x.c.fields.take x.c.fields.length).flatMap ChainField.enc).length ≤
      x.c.payload.length := by
    rw [List.take_length, ← chainG_enc_eq_fields]
    unfold ChainG.payload
    rw [List.length_append]
    omega
  exact BoundedRustEvs.mono (by omega) (Nat.le_refl _) h

theorem deserPrefixEnv_zero (r : SessionRecord (List (BitVec 8))) :
    DeserPrefixEnv r 0 [] :=
  BoundedRustEvs.nil _ _

theorem recFields_flatMap_length_le_encodeRecord (r : SessionRecord (List (BitVec 8)))
    (hr : DeserializeScope r) :
    ((recFields r).flatMap GenField.enc).length ≤ (encodeRecord r).length := by
  rw [encodeRecord_eq_recFields r hr, List.length_append, List.length_append]
  omega

theorem deserPrefixEnv_at_length {x : DeserializeGenGhost} (hr : DeserializeScope x.r)
    {evs : List AllocEvent} :
    DeserPrefixEnv x.r (recFields x.r).length evs → DeserializeGenEnv x evs := by
  intro h
  have h1 := flatMap_take_length_le GenField.enc (recFields x.r) (recFields x.r).length
  have h2 := recFields_flatMap_length_le_encodeRecord x.r hr
  exact BoundedRustEvs.mono (by omega) (Nat.le_refl _) h

/-! ## 2. Budget-Threaded Raw & `[LibsignalPlacement]` Specifications -/

/-- Image-free budget-threaded contract of `SessionStructure::merge_field` (block `15`) on one
    in-scope field restricted by `P`, at `mergeFieldStackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def mergeFieldGenRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : GenField → Prop) : Spec (MergeFieldGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEnv M lim st (MergeFieldGenEnv x)⌝ ∗
      prostSSGAt A.repAlloc x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp mergeFieldStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64 ∧ MergeFieldGenEnv x evs⌝ ∗
        prostSSGAt A.repAlloc x.ss (x.v.apply x.fld) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp mergeFieldStackX

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract of `SessionStructure::merge_field`
    (block `15`) at `mergeFieldStackX`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev mergeFieldGenPlacedSpecW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (P : GenField → Prop) :
    Spec (MergeFieldGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (mergeFieldGenRawSpecW M A lim P)

/-- Image-free budget-threaded contract of `message::merge<Chain>` (block `11`) on one in-scope
    chain into a default chain, at `chainMergeStackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainMergeGenRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧
      (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEnv M lim st (ChainMergeGenEnv x)⌝ ∗
      prostChainGAt A.repAlloc x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp chainMergeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64 ∧ ChainMergeGenEnv x evs⌝ ∗
        prostChainGAt A.repAlloc x.a x.c ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainMergeStackX

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract of `message::merge<Chain>`
    (block `11`) at `chainMergeStackX`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev chainMergeGenPlacedSpecW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ChainMergeGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (chainMergeGenRawSpecW M A lim)

/-- Image-free budget-threaded contract of `SessionRecord::deserialize` (block `46`) on a general
    record (`DeserializeScope`), with `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`. -/
noncomputable def deserializeGenRawSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeserializeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScope x.r ∧
      FitsEnv M lim st (DeserializeGenEnv x)⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗
      memRegion x.out 368 ∗ A.pool lim st s ∗ stackAt s.sp recDeserializeStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ DeserializeGenEnv x evs⌝ ∗
        (x.p ↦ₛ encodeRecord x.r) ∗
        (∃∗ g : RecordGhost, ⌜CanonRecord g x.r⌝ ∗ sessionRecordAt A.repAlloc x.out g x.r) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp recDeserializeStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract of `SessionRecord::deserialize`
    (block `46`) on a general record (`DeserializeScope`), carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeGenPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DeserializeGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (deserializeGenRawSpec M A lim)

/-- Raw loop-exit postcondition of `SessionRecord::deserialize` before lifting `deserOutRecordGA`
    to `sessionRecordAt`. -/
def deserOutRawGBudget (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (st : M.σ) (s0 sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜sf.trace = s0.trace ∧ DeserializeGenEnv x evs⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗
      deserOutRecordGA A.repAlloc x.out x.r ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp recDeserializeStack

/-! ## 3. Callee Bundles, Loop Invariants, Segment Steps, and Return Predicates -/

/-- Relocatable `[LibsignalPlacement]` budget-threaded X-stack callee bundle for `deserialize`
    and `merge_field`. -/
def DeserializeCalleesPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  DecodeVarintSlicePlacedOkW A lim H ∧
    Int32MergePlacedOkW A lim H ∧
    BytesMergePlacedOkW A lim H ∧
    GrowOneChainPlacedOkX A lim H

/-- Relocatable budget-threaded `merge_field` (block `15`) contract restricted by `P`. -/
def MergeFieldGenPlacedOkW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (P : GenField → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldGenPlacedSpecW M A lim P)

/-- Relocatable budget-threaded `message::merge<Chain>` (block `11`) contract. -/
def ChainMergeGenPlacedOkW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_11 H) (blkPl_11).base (chainMergeGenPlacedSpecW M A lim)

/-- One segment step of relocatable budget-threaded `message::merge<Chain>` on `lsProg_11 H`. -/
abbrev ChainStepGPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_11 H) (chainMergeGenPlacedSpecW M A lim) (x, st) R s0 s Q

/-- Return state of relocatable budget-threaded `message::merge<Chain>` on `lsProg_11 H`. -/
def ChainRetGPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMergeGenPlacedSpecW M A lim).post (x, st) s0 sf ∗ R)

/-- Field-loop head `(blkPl_11).base + 0x120` after `k` fields of `message::merge<Chain>` at
    `chainMergeSubStackX`, threading `FitsEnv M lim st (ChainMergeGenEnv x)` and accumulated
    `ChainPrefixEnv x.c k evs`. -/
def ChainLoopGPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chainPlacedPC 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    FitsEnv M lim st (ChainMergeGenEnv x) ∧
    ∃ evs : List AllocEvent,
      ChainPrefixEnv x.c k evs ∧
      (s.mem ⊨ prostChainGAt A.repAlloc x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
          (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

/-- One segment step of relocatable budget-threaded `SessionRecord::deserialize` on `lsProg_46 H`. -/
abbrev DeserStepGPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (x : DeserializeGenGhost) (st : M.σ) (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_46 H) (deserializeGenPlacedSpec M A lim) (x, st) R s0 s Q

/-- Raw return state of relocatable budget-threaded `SessionRecord::deserialize` on `lsProg_46 H`. -/
def DeserRetGPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (st : M.σ) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ deserOutRawGBudget M A lim x st s0 sf ∗ R)

/-- Field-loop head `(blkPl_46).base + 0x254` after `k` outer fields of
    `SessionRecord::deserialize`, threading `FitsEnv M lim st (DeserializeGenEnv x)` and
    accumulated `DeserPrefixEnv x.r k evs`. -/
def DeserLoopGPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (st : M.σ) (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPlacedPC 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    FitsEnv M lim st (DeserializeGenEnv x) ∧
    ∃ evs : List AllocEvent,
      DeserPrefixEnv x.r k evs ∧
      (s.mem ⊨ deserLocalsGA A.repAlloc (deserSpL s0.sp) x.p (encodeRecord x.r)
          (((recFields x.r).drop k).flatMap GenField.enc) (ssgAfter x.r k) ∗
        memRegion x.out 368 ∗ A.pool lim (M.stepEvents evs st) s ∗
        stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

/-- Convert a non-panicking, non-OOM `SepWP` step directly into `SegStepG`. -/
theorem segStepG_of_sepWP {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R P : SepProp} {target : BitVec 64} {s0 s : State} {Q : State → Prop}
    (hmem : s.mem ⊨ P ∗ R)
    (hwp : SepWP prog target s P (fun s' P' => (s'.mem ⊨ P' ∗ R) → Q s')) :
    SegStepG prog spec x R s0 s Q := by
  unfold SegStepG
  intro hL
  obtain ⟨s', hsteps, ⟨_, _, P', hm', hq⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · exact ⟨s', hsteps, Or.inl (hq hm')⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 4. Cross-Block Callee Transfers & `growOne` / `chainMerge` Call Helpers -/

theorem bytesMerge_placed_ok_sub_seedChainW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : BytesMergePlacedOkW A lim H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 7) (bytesMergePlacedSpecW A lim) :=
  ls_call_ro_of_block (callerProg := lsProg_11 H) h

theorem int32Merge_placed_ok_sub_seedChainW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : Int32MergePlacedOkW A lim H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 8)
      (withLsCodeRoLoaded lsmpl (int32MergeSpecW A lim)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

theorem decodeVarintSlice_placed_ok_sub_cmeW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : DecodeVarintSlicePlacedOkW A lim H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecW A lim)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

theorem growOneChain_placed_ok_sub_seedChainW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : GrowOneChainPlacedOkX A lim H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

theorem growOne_placed_pre_eq_extW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) :
    (growOneChainSpecX M A lim).pre ((v, cap, ptr, bs), st) s =
    ⌜bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (GrowOne104Env cap)⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool lim st s ∗ stackAt sp growOneChainStackX) := by
  unfold growOneChainSpecX growOne104SpecX
  dsimp only
  have hpure :
      (s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (GrowOne104Env cap)) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (GrowOne104Env cap)) :=
    propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h3, by omega, h5⟩,
             fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h3, by omega, h5⟩⟩
  rw [hpure, hsp]

theorem growOne_placed_post_elim_sp_extW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp)
    (hfull : n = cap.toNat) (hbs : bs.length = n * 104)
    (hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    (growOneChainSpecX M A lim).post ((v, cap, ptr, bs), st) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ evs : List AllocEvent, ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜GrowOne104Env cap evs ∧ n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        (v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt sp growOneChainStackX := by
  unfold growOneChainSpecX growOne104SpecX
  dsimp only
  rw [hsp]
  apply Entails.pure_left; intro htr; refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  let evs : List AllocEvent := growOne104Events cap
  let cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  refine Entails.sepExists_right evs
    (Entails.sepExists_right cap' (Entails.sepExists_right p' ?_))
  have hevs : GrowOne104Env cap evs := rfl
  have hmax_lt64 : max (2 * cap.toNat) 4 < 2 ^ 64 := by omega
  have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
    change (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt64]
  have hcap'_le : n + 1 ≤ cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  have hmul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 =
      104 + (cap'.toNat - (n + 1)) * 104 := by omega
  have hsplit := memRegion_split (p' + BitVec.ofNat 64 (n * 104))
    104 ((cap'.toNat - (n + 1)) * 104) (by omega)
  have haddr : p' + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 =
      p' + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [haddr] at hsplit
  have hlive : max (2 * cap.toNat) 4 * 104 = cap'.toNat * 104 := by omega
  rw [hbs, hmul, hsplit, hlive]
  have hpurePull :
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        (memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
          memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104)) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt sp (464 + Stage1X.GrowOneXBudget.finishGrowStackX) =
      ⌜p' ≠ 0#64⌝ ∗
        ((v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (cap'.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
          memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp growOneChainStackX) := by
    change _ = _ ∗ (_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ stackAt sp (464 + Stage1X.GrowOneXBudget.finishGrowStackX))
    sep_ac_rfl
  rw [hpurePull]
  apply Entails.pure_left; intro hp'
  exact Entails.pure_right ⟨hevs, hcap'_le, hcap'_lt, hp'⟩ (Entails.refl _)

private theorem align_pre_gen {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog target s P' Q) :
    SepWP prog target s P Q :=
  heq ▸ h

/-- Call a `withLsCodeRoLoaded lsmpl spec` subroutine inside a `SepWP` proof when `spec` has
    `onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, and `onOom = ⌜False⌝`. -/
theorem sepWP_call_lscro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret : BitVec 64} {spec : Spec α} {x : α}
    (hsub : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpan : ∀ x' s0 sf, spec.onPanic x' s0 sf = ⌜False⌝)
    (hoom : ∀ x' s0 sf, spec.onOom x' s0 sf = ⌜False⌝)
    {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hnext : ∀ sm,
      sm.pc = s.readReg64 .lr →
      sm.status = .Running →
      sm.sp = s.sp →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      CalleeSavedPreserved s sm →
      SepWP prog ret sm (spec.post x s sm ∗ F) Q)
    (hex : ∀ x' code s0 sf, spec.onExit x' code s0 sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog ret s P Q := by
  apply sepWP_seq_lscro hcrl (mid := s.readReg64 .lr)
  refine SepWP.call_subroutine_frame (x := x) (F := F) hsub hpc hrun hal rfl ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hm1 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hpre) hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm1⟩
  · intro R' sf _
    dsimp only [withLsCodeRoLoaded]
    rw [hpan]
    exact not_satisfies_false_sepConj
  · intro R' code sf _
    dsimp only [withLsCodeRoLoaded]
    rw [hex]
    exact not_satisfies_false_sepConj
  · intro sm hpcm hrunm hspm hcsm
    exact SepWP.done hpcm hrunm fun hcrlm => hnext sm hpcm hrunm hspm hcrlm hcsm
  · intro R' sf _ ho
    dsimp only [withLsCodeRoLoaded] at ho
    rw [hoom] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-- Step a `bl bytes::merge` (`lsmpl.base 7`) call inside `message::merge<Chain>` (`lsProg_11 H`)
    on a `< 128`-byte field `[BitVec.ofNat 8 b.length] ++ b`, threading `A.pool lim st s` and
    producing `evs_bm` with `BoundedRustEvs 3 (2 * b.length + 8) evs_bm`. -/
theorem step_chainMerge_bytesMerge_placedW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hBM : BytesMergePlacedOkW A lim H)
    (st : M.σ) (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    (hFit : FitsEnv M lim st (BoundedRustEvs 3 (2 * b.length + 8)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 7)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A.repAlloc v bs0 ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      A.pool lim st s ∗
      stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (evs_bm : List AllocEvent),
      BoundedRustEvs 3 (2 * b.length + 8) evs_bm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWP (lsProg_11 H) ret sm
        ((vecU8 A.repAlloc v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents evs_bm st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_11 H) ret s P Q := by
  have hcall := bytesMerge_placed_ok_sub_seedChainW hBM
  rw [hP]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun cap0 => SepWP.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  let xg : BytesMergeGhost :=
    BytesMergeGhost.mk .lengthDelimited v cap0 ptr0 bs0 bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest)
  have hmB : mergeBytes xg.wt xg.bs = some (b, rest) := mergeBytes_lt128_seedChain b rest hb
  have hb_max : 2 * b.length + 8 ≤ MallocngMaxAllocSize := by
    unfold MallocngMaxAllocSize; omega
  have hFit_xg : FitsEnv M lim st (BytesMergeEnv xg) :=
    fitsEnv_bytesMerge_of_some hmB hb_max (Nat.le_refl 3) (Nat.le_refl _) hFit
  refine sepWP_call_lscro (x := (xg, st))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
      (chainMergeSubStackX - bytesMergeStackW) ∗ F)
    hcall (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpc hrun hsp_aligned hcrl ?_ ?_
  · rw [stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)]
    dsimp only [bytesMergeRawSpecW, bytesMergeRawSpecGen, bmPreBoundBudget, xg]
    rw [hsp, bytesMergeStackW_eq_gen]
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.pure_right ⟨hx0, hx1, hx2, hlen_lt, hFit_xg⟩ (Entails.refl _)))
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hpcm hrunm hspm hcrlm hcsm
    rw [hlr] at hpcm
    rw [hsp] at hspm
    dsimp only [bytesMergeRawSpecW, bytesMergeRawSpecGen, bmPostVec]
    rw [hmB, hsp, bytesMergeStackW_eq_gen]
    dsimp only
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun cap' =>
      SepWP.exists_elim fun ptr' => SepWP.exists_elim fun evs_bm => ?_
    refine align_pre_gen
      (P' := ⌜sm.trace = s.trace⌝ ∗ ⌜BytesMergeEnv xg evs_bm⌝ ∗ ⌜sm.readReg64 .x0 = 0#64⌝ ∗
        (vecU8At A.repAlloc v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            sliceCursorAfter slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) rest ∗
            A.pool lim (M.stepEvents evs_bm st) sm ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - bytesMergeStackW) ∗
              stackAt (sp0 - 256#64) bytesMergeStackW) ∗ F)))
      (by dsimp only [xg]; sep_ac_rfl) ?_
    refine SepWP.pure_elim fun htrm =>
      SepWP.pure_elim fun hevs_bm =>
      SepWP.pure_elim fun hx0m => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A.repAlloc v cap' ptr' b ⊢ vecU8 A.repAlloc v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    have hbnd := boundedRustEvs_bytesMergeEnv_of_some hmB hb_max hevs_bm
    refine SepWP.weaken_pre ?_
      (hnext sm evs_bm hbnd hpcm hrunm hspm hcrlm (htrm.trans htr) hcsm hx0m)
    rw [hcur, stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)]
    refine Entails.trans (sepConj_mono_left hv) ?_
    exact Entails.of_eq (by sep_ac_rfl)

/-- Step a `bl int32::merge` (`lsmpl.base 8`) call inside `message::merge<Chain>` (`lsProg_11 H`)
    on `pbVarintBody 5 i.toNat ++ rest` (`0` allocator events emitted on `Ok`). -/
theorem step_chainMerge_int32Merge_placedW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hIM : Int32MergePlacedOkW A lim H)
    (st : M.σ) (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 : BitVec 32)
    (i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 8)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗
      A.pool lim st s ∗
      stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWP (lsProg_11 H) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q) :
    SepWP (lsProg_11 H) ret s P Q := by
  have hcall := int32Merge_placed_ok_sub_seedChainW hIM
  have hlen_lt63 : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 63 :=
    Nat.lt_trans hlen_lt (by decide)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  let xg : Int32MergeGhost :=
    Int32MergeGhost.mk .varint dst bufRef slot curPtr (pbVarintBody 5 i.toNat ++ rest)
  have hmI : mergeUint32 xg.wt xg.bs = some (i, rest) := mergeUint32_pbVarintBody_seedChain i rest
  have hFit_xg : FitsEnv M lim st (Int32MergeEnv xg) := by
    intro evs hevs
    rw [int32MergeEnv_eq_nil hmI hevs]
    trivial
  refine sepWP_call_lscro (x := (xg, st))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
      (chainMergeSubStackX - int32MergeStackW) ∗ F)
    hcall (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpc hrun hsp_aligned hcrl ?_ ?_
  · rw [hP, stackAt_sub_to_int32Merge_seedChainW (sp0 - 256#64)]
    have hcell : (dst ↦₃₂ w0) ⊢ memRegion dst 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right w0 (Entails.refl _)
    dsimp only [int32MergeSpecW, int32MergeSpecGen, xg]
    rw [hsp, int32MergeStackW_eq_gen]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left hcell)) ?_
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.pure_right ⟨hx0, hx1, hx2, hlen_lt63, hFit_xg⟩ (Entails.refl _)))
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hpcm hrunm hspm hcrlm hcsm
    rw [hlr] at hpcm
    rw [hsp] at hspm
    dsimp only [int32MergeSpecW, int32MergeSpecGen]
    rw [hmI, hsp, int32MergeStackW_eq_gen]
    dsimp only
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun evs_im => ?_
    refine align_pre_gen
      (P' := ⌜sm.trace = s.trace⌝ ∗ ⌜Int32MergeEnv xg evs_im⌝ ∗ ⌜sm.readReg64 .x0 = 0#64⌝ ∗
        ((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          A.pool lim (M.stepEvents evs_im st) sm ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - int32MergeStackW) ∗
            stackAt (sp0 - 256#64) int32MergeStackW) ∗ F))
      (by dsimp only [xg]; sep_ac_rfl) ?_
    refine SepWP.pure_elim fun htrm =>
      SepWP.pure_elim fun hevs_im =>
      SepWP.pure_elim fun hx0m => ?_
    rw [int32MergeEnv_eq_nil hmI hevs_im, AllocCostModel.stepEvents_nil]
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr (pbVarintBody 5 i.toNat) rest
    have hGoalEq :
        ((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          A.pool lim st sm ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - int32MergeStackW) ∗
            stackAt (sp0 - 256#64) int32MergeStackW) ∗ F) =
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChainW (sp0 - 256#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm hcrlm (htrm.trans htr) hcsm hx0m

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget
