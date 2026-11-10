/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymC
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop

/-!
# Budget-Threaded Signed and Kyber Pre-Key Decoder Envelopes and Contracts

`RustCliAllocBudget`-threaded prost callee specifications, slice-budgeted loop/epilogue allocation
envelopes (`SpkLoopBoundedEnv`, `SpkDecodeEnv`, `KyberDecodeEnv`), relocatable
`[LibsignalPlacement]` contracts (`SignedHooksPlaced`, `SignedPortDepsPlaced`), Block `555`
`drop_glue::<DecodeError>` verification, and `FitsEnv fineCostModel` non-vacuity witnesses.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open CryptoVerification.LibsignalTripleRatchet.Prost
open LibsignalBinary.Heap
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification.RecordCodecsBinary (DecodeGhost SignedHooks SignedPortDeps kyberPreKeyResultAt signedDecodeResultAt signedDecodeStack signedPreKeyResultAt)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## 1. Budgeted Prost Callee Envelopes and Contracts -/

export LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv decodeErrorFromBudgetSpec
)

/-- Bounded `<DecodeError>::push` envelope matching `SpqrV1.Alloc.newCap32` (`max (2 * n) 4`). -/
def DecodeErrorPushBoundedEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ evs = rustAllocEvents 128 8) ∨
  (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)

/-- Bounded budget-threaded counterpart of `decodeErrorPushSpec`. -/
def decodeErrorPushBoundedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32 ∧ FitsEnv M lim st (DecodeErrorPushBoundedEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp decodeErrorHookStack
  post := fun (d, e, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushBoundedEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeErrorHookStack

/-- Deterministic allocator events of `decode_varint::<&mut &[u8]>` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
def decodeVarint2Events (bs : List (BitVec 8)) : List AllocEvent :=
  match CryptoVerification.LibsignalProtoCodec.decodeVarint bs with
  | some _ => []
  | none => rustAllocEvents 72 8

/-- Callee-fixed event envelope of `decode_varint::<&mut &[u8]>`. -/
def DecodeVarint2Env (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = decodeVarint2Events bs

/-- Budget-threaded counterpart of `CryptoVerification.SpqrV1.Varint.decodeVarint2Spec`. -/
def decodeVarint2BudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarint2Env x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp CryptoVerification.SpqrV1.Varint.decodeVarint2Stack
  post := fun (x, st) s0 sf =>
    (match CryptoVerification.LibsignalProtoCodec.decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp CryptoVerification.SpqrV1.Varint.decodeVarint2Stack ∗
      match CryptoVerification.LibsignalProtoCodec.decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Deterministic allocator events of `skip_field::<&mut &[u8]>` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
def skipField3EventsCore (depth tag : Nat) (wt : CryptoVerification.LibsignalProtoCodec.WireType)
    (bs : List (BitVec 8)) : List AllocEvent :=
  match CryptoVerification.LibsignalProtoCodec.skipField (2 * bs.length + 2) depth tag wt bs with
  | some _ => []
  | none => rustAllocEvents 72 8

/-- Callee-fixed event envelope of `skip_field::<&mut &[u8]>`. -/
def SkipField3Env (x : SkipFieldGhost) (evs : List AllocEvent) : Prop :=
  evs = skipField3EventsCore x.depth x.tag x.wt x.bs

/-- Budget-threaded counterpart of `CryptoVerification.SpqrV1.Varint.skipField3Spec`. -/
def skipField3BudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SkipFieldGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipField3Env x)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (CryptoVerification.SpqrV1.Varint.skipField3Stack x.depth)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipField3Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (CryptoVerification.SpqrV1.Varint.skipField3Stack x.depth) ∗
      match CryptoVerification.LibsignalProtoCodec.skipField
          (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Deterministic `Vec<u8>` post-capacity after `prost::encoding::bytes::merge::<Vec<u8>, _>`
succeeds with slice `v` (`v.length ≤ cap` overwrites in place; `cap < v.length` reserves
`reserveCap cap 0 v.length`). -/
def bmNextCap (cap vLen : Nat) : Nat :=
  if vLen ≤ cap then cap else reserveCap cap 0 vLen

/-- Pointer-independent event envelope of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`. -/
def BytesMerge3EnvCore (wt : CryptoVerification.LibsignalProtoCodec.WireType)
    (valCap : BitVec 64) (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = bytesMergeEventsCore wt valCap bs

/-- Callee-fixed event envelope of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`. -/
abbrev BytesMerge3Env (x : BytesMergeGhost) : List AllocEvent → Prop :=
  BytesMerge3EnvCore x.wt x.valCap x.bs

/-- Budget-threaded counterpart of `CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec`. -/
def bytesMerge3RawBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (BytesMerge3Env x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMerge3Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3Stack ∗
      match CryptoVerification.LibsignalProtoCodec.mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length ∧ cap'.toNat = bmNextCap x.valCap.toNat v.length⌝ ∗
              vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Callee-fixed event envelope of `drop_glue::<prost::error::DecodeError>`:
frees optional stack buffer `(cap * 32, 8)` then box `(72, 8)`. -/
def DropDecodeErrorEnv (evs : List AllocEvent) : Prop :=
  evs = rustDeallocEvents 72 8 ∨
  ∃ c : Nat, 0 < c ∧ c * 32 < 2 ^ 63 ∧
    evs = rustDeallocEvents (c * 32) 8 ++ rustDeallocEvents 72 8

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Budget-threaded counterpart of `dropDecodeErrorSpecGen`. -/
def dropDecodeErrorBudgetSpecGenBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (dStack : Nat) : Spec (BitVec 64 × M.σ) where
  pre := fun (e, st) s =>
    ⌜s.readReg64 .x0 = e⌝ ∗ decodeErrorAt A.repAlloc e ∗ A.pool lim st s ∗
      stackAt s.sp (0x20 + dStack)
  post := fun (_, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜DropDecodeErrorEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x20 + dStack)

def dropDecodeErrorBudgetSpecGen [CryptoVerification.LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (dStack : Nat) : Spec (BitVec 64 × M.σ) where
  pre := fun (e, st) s =>
    ⌜s.readReg64 .x0 = e ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ decodeErrorAt A.repAlloc e ∗ A.pool lim st s ∗
      stackAt s.sp (0x20 + dStack)
  post := fun (_, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜DropDecodeErrorEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x20 + dStack)

/-- Budget-threaded counterpart of `Prost.dropDecodeErrorSpec`. -/
abbrev dropDecodeErrorBudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) :=
  dropDecodeErrorBudgetSpecGenBase M A lim allocHookStack

abbrev dropDecodeErrorBudgetSpec [CryptoVerification.LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) :=
  dropDecodeErrorBudgetSpecGen M A lim allocHookStack

/-! ## 2. Loop and Epilogue Envelopes -/

/-- Length-delimited `SignedPreKeyRecordStructure` `Vec<u8>` field selector. -/
inductive SpkField where
  | pub | priv | sig

/-- Per-field `Vec<u8>` capacities tracked across `SignedPreKeyRecordStructure::decode`'s loop. -/
structure SpkCaps where
  pub : Nat
  priv : Nat
  sig : Nat

def SpkCaps.zero : SpkCaps := ⟨0, 0, 0⟩

def SpkCaps.get (c : SpkCaps) : SpkField → Nat
  | .pub => c.pub | .priv => c.priv | .sig => c.sig

def SpkCaps.set (c : SpkCaps) : SpkField → Nat → SpkCaps
  | .pub, v => { c with pub := v }
  | .priv, v => { c with priv := v }
  | .sig, v => { c with sig := v }

/-- Terminal allocator event envelope at `SignedPreKeyRecordStructure::decode` loop exit
(`Ok` `[]`, `DecodeError::from` only, or `DecodeError::from` followed by `<DecodeError>::push`
at `stack.len = 0`). -/
inductive SpkErrTailEnv : List AllocEvent → Prop where
  | nil : SpkErrTailEnv []
  | fromOnly : SpkErrTailEnv (rustAllocEvents 72 8)
  | fromPush {evs_p : List AllocEvent} :
      DecodeErrorPushBoundedEnv 0 evs_p →
      SpkErrTailEnv (rustAllocEvents 72 8 ++ evs_p)

/-- Slice-budgeted protobuf decode loop envelope for `SignedPreKeyRecordStructure::decode`:
indexed by remaining input byte count `rem` and the 3 `Vec<u8>` field capacities
`(pub, priv, sig)`. -/
inductive SpkLoopBoundedEnv : Nat → SpkCaps → List AllocEvent → Prop where
  | done {rem : Nat} {caps : SpkCaps} {evs : List AllocEvent} :
      SpkErrTailEnv evs →
      SpkLoopBoundedEnv rem caps evs
  | skipStep {rem rem' : Nat} {caps : SpkCaps} {evs : List AllocEvent} :
      rem' < rem →
      SpkLoopBoundedEnv rem' caps evs →
      SpkLoopBoundedEnv rem caps evs
  | bytesStep (f : SpkField) {rem rem' : Nat} {caps : SpkCaps}
      (wt : WireType) (bs v rest : List (BitVec 8)) {evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ rem →
      rem' + v.length + 1 ≤ rem →
      caps.get f < 2 ^ 63 →
      SpkLoopBoundedEnv rem'
        (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
        evs₂ →
      SpkLoopBoundedEnv rem caps
        (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂)

/-- Top-level loop envelope starting from zero-capacity `Vec<u8>` fields on an input slice of
`rem` bytes (retaining the legacy `_fuel` parameter solely for caller signature compatibility). -/
abbrev SpkLoopEnv (_fuel rem : Nat) : List AllocEvent → Prop :=
  SpkLoopBoundedEnv rem SpkCaps.zero

/-- `mergeBytes wt bs = some (v, rest)` consumes at least `1 + v.length` bytes (`1 ≤ k_varint`). -/
theorem mergeBytes_progress {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    rest.length + v.length + 1 ≤ bs.length := by
  unfold mergeBytes at h
  split_ifs at h
  cases hd : decodeVarint bs with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨len, r1⟩
    simp only [hd] at h
    split_ifs at h with hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨k1, hk1_pos, hk1_le, hr1⟩ :=
      CryptoVerification.LibsignalTripleRatchet.Wire.decodeVarint_suffix hd
    have hr1_len : r1.length = bs.length - k1 := by simp [hr1]
    have hv_len : (r1.take len.toNat).length = len.toNat := by simp; omega
    have hrest_len : (r1.drop len.toNat).length = r1.length - len.toNat := by simp
    omega

theorem bmNextCap_lt_two_pow_63 {cap0 : BitVec 64} {wt : WireType} {bs v rest : List (BitVec 8)}
    (hcap0_ok : BytesMergeCapOk cap0 bs.length) (hcap0_lt : cap0.toNat < 2 ^ 63)
    (hbs_lt : bs.length < 2 ^ 63) (hm : mergeBytes wt bs = some (v, rest)) :
    bmNextCap cap0.toNat v.length < 2 ^ 63 := by
  unfold bmNextCap
  split_ifs with hle
  · exact hcap0_lt
  · have hprog := mergeBytes_progress hm
    have hb := bytesMergeCapOk_reserveCap_bound (vLen := v.length) (restLen := rest.length)
      hcap0_ok (by omega) (by omega) hbs_lt
    omega

theorem SpkLoopBoundedEnv.mono_rem {rem₁ rem₂ : Nat} {caps : SpkCaps}
    {evs : List AllocEvent} (hle : rem₁ ≤ rem₂)
    (h : SpkLoopBoundedEnv rem₁ caps evs) :
    SpkLoopBoundedEnv rem₂ caps evs := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact h
  · exact .skipStep hlt h

theorem SpkErrTailEnv.of_decodeErrorFrom {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) : SpkErrTailEnv evs := by
  rw [h]; exact .fromOnly

theorem SpkErrTailEnv.of_decodeVarint2 {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DecodeVarint2Env bs evs) : SpkErrTailEnv evs := by
  rw [h]; unfold decodeVarint2Events
  cases decodeVarint bs
  · exact .fromOnly
  · exact .nil

theorem SpkErrTailEnv.of_skipField3 {x : SkipFieldGhost} {evs : List AllocEvent}
    (h : SkipField3Env x evs) : SpkErrTailEnv evs := by
  rw [h]; unfold skipField3EventsCore
  cases CryptoVerification.LibsignalProtoCodec.skipField
    (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs
  · exact .fromOnly
  · exact .nil

theorem fitsEnv_spkLoop_errTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SpkCaps} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → SpkErrTailEnv evs)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (.done (hsub evs he))

theorem fitsEnv_spkLoop_pushAfterFrom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SpkCaps}
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    FitsEnv M lim (M.stepEvents (rustAllocEvents 72 8) st) (DecodeErrorPushBoundedEnv 0) :=
  fun evs_p hp =>
    ((fitsEvents_append M lim (rustAllocEvents 72 8) evs_p st).mp
      (hFit (rustAllocEvents 72 8 ++ evs_p) (.done (.fromPush hp)))).2

theorem fitsEnv_spkLoop_bytesMerge {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (f : SpkField) {rem : Nat} {caps : SpkCaps} {x : BytesMergeGhost}
    (hcap_eq : x.valCap = BitVec.ofNat 64 (caps.get f))
    (hcap_lt : caps.get f < 2 ^ 63)
    (hbs_le : x.bs.length ≤ rem)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    FitsEnv M lim st (BytesMerge3Env x) := by
  intro evs hevs
  rw [BytesMerge3Env, BytesMerge3EnvCore, hcap_eq] at hevs
  subst hevs
  cases hm : mergeBytes x.wt x.bs with
  | none =>
    have heq : bytesMergeEventsCore x.wt (BitVec.ofNat 64 (caps.get f)) x.bs =
        rustAllocEvents 72 8 := by simp [bytesMergeEventsCore, hm]
    rw [heq]
    exact hFit _ (.done .fromOnly)
  | some p =>
    rcases p with ⟨v, rest⟩
    have hprog := mergeBytes_progress hm
    have hstep : SpkLoopBoundedEnv rem caps
        (bytesMergeEventsCore x.wt (BitVec.ofNat 64 (caps.get f)) x.bs ++ []) :=
      .bytesStep f (rem' := rest.length) x.wt x.bs v rest hm hbs_le (by omega) hcap_lt (.done .nil)
    rw [List.append_nil] at hstep
    exact hFit _ hstep

theorem fitsEnv_spkLoop_bytesTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (f : SpkField) {rem rem' : Nat} {caps : SpkCaps}
    {wt : WireType} {bs v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest))
    (hbs_le : bs.length ≤ rem)
    (hprog : rem' + v.length + 1 ≤ rem)
    (hcap_lt : caps.get f < 2 ^ 63)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    FitsEnv M lim (M.stepEvents evs₁ st)
      (SpkLoopBoundedEnv rem' (caps.set f (bmNextCap (caps.get f) v.length))) := by
  subst hevs₁
  intro evs₂ h2
  exact ((fitsEvents_append M lim _ evs₂ st).mp
    (hFit _ (.bytesStep f wt bs v rest hm hbs_le hprog hcap_lt h2))).2

theorem fitsEnv_spkLoop_skipStep {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem rem' : Nat} {caps : SpkCaps} (hlt : rem' < rem)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem caps)) :
    FitsEnv M lim st (SpkLoopBoundedEnv rem' caps) :=
  fun evs h => hFit evs (.skipStep hlt h)

theorem fitsEnv_spkLoop_mono_rem {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem₁ rem₂ : Nat} {caps : SpkCaps} (hle : rem₁ ≤ rem₂)
    (hFit : FitsEnv M lim st (SpkLoopBoundedEnv rem₂ caps)) :
    FitsEnv M lim st (SpkLoopBoundedEnv rem₁ caps) :=
  fun evs h => hFit evs (h.mono_rem hle)

/-- Optional `Vec<u8>` buffer deallocation in the `Err` epilogue (`cap = 0` or `dealloc(ptr, cap, 1)`). -/
def OptByteFreeEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ∃ cap : Nat, 0 < cap ∧ cap + 1 ≤ 2 ^ 63 ∧ evs = rustDeallocEvents cap 1

/-- Up to three `Vec<u8>` buffer deallocations (`public_key`, `private_key`, `signature`) on `Err`. -/
def SpkEpilogueFreeEnv (evs : List AllocEvent) : Prop :=
  ∃ e1 e2 e3 : List AllocEvent,
    OptByteFreeEnv e1 ∧ OptByteFreeEnv e2 ∧ OptByteFreeEnv e3 ∧ evs = e1 ++ e2 ++ e3

/-- Callee-fixed event envelope of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`. -/
def SpkDecodeEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  SpkLoopEnv (2 * len + 3) len evs ∨
  ∃ evsL evsF : List AllocEvent,
    SpkLoopEnv (2 * len + 3) len evsL ∧ SpkEpilogueFreeEnv evsF ∧ evs = evsL ++ evsF

/-- Callee-fixed event envelope of `decode_kyber_pre_key` / `decode_signed_pre_key`
(`signedDecode` followed on `Err` by `drop_glue::<DecodeError>`). -/
def KyberDecodeEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  SpkDecodeEnv len evs ∨
  ∃ evs₁ evs₂ : List AllocEvent,
    SpkDecodeEnv len evs₁ ∧ DropDecodeErrorEnv evs₂ ∧ evs = evs₁ ++ evs₂

/-! ## 3. Relocatable `[LibsignalPlacement]` Decoder Contracts -/

/-- Image-free raw budget-threaded contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`. -/
def signedDecodeRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧
      0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜SpkDecodeEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      signedDecodeResultAt A.repAlloc x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(block `562`), carrying `LibsignalCodeRoLoaded lsmpl` for transitive `bytes::merge` vtable reads. -/
abbrev signedDecodePlacedSpec [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeRawSpec A lim)

/-- Image-free raw budget-threaded contract of `signal_session::stores::decode_kyber_pre_key`. -/
def decodeKyberPreKeyRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧
      0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp smallRootStack ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜KyberDecodeEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      kyberPreKeyResultAt A.repAlloc x.ret (KyberPreKeyRecord.deserialize x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` contract of `decode_kyber_pre_key` (block `595`). -/
abbrev decodeKyberPreKeyPlacedSpec [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (decodeKyberPreKeyRawSpec A lim)

/-- Image-free raw budget-threaded contract of `decode_kyber_pre_key` called as `decode_signed_pre_key`. -/
def decodeSignedPreKeyRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧
      0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp smallRootStack ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜KyberDecodeEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      signedPreKeyResultAt A.repAlloc x.ret (SignedPreKeyRecord.deserialize x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` contract of `decode_signed_pre_key` (block `595`). -/
abbrev decodeSignedPreKeyPlacedSpec [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (decodeSignedPreKeyRawSpec A lim)

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` counterpart of `SignedHooks`: `__rust_dealloc`,
`DecodeError::from` (block `261`), and `DecodeError::push` (block `257`). -/
structure SignedHooksPlaced [CryptoVerification.LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  decodeErrorFrom :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim))
  decodeErrorPush :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBoundedSpec M A lim))

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` counterpart of `SignedPortDeps`: the CLI-instantiated `[local#...]`
prost callees (`559`, `546`, `558`, `555`). -/
structure SignedPortDepsPlaced [CryptoVerification.LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  /-- `decode_varint [local#5]` (block `559`). -/
  decodeVarint6 :
    subroutine_ok (lsProg_559 H) (blkPl_559).base
      (withLsCodeLoaded lsmpl (decodeVarint2BudgetSpec M A lim))
  /-- `skip_field [local#6]` (block `546`). -/
  skipField7 :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim))
  /-- `bytes::merge [local#6]` (block `558`). -/
  bytesMerge7 :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim))
  /-- `drop_glue::<DecodeError> [local#3]` (block `555`). -/
  dropDecodeError3 :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorBudgetSpec M A lim)

section DropDecodeError3Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit

private theorem dropDecodeErrorPool_zero {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sf : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents 72 8) st) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜DropDecodeErrorEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf :=
  Entails.sepExists_right (rustDeallocEvents 72 8)
    (Entails.pure_right (Or.inl rfl) (Entails.refl _))

private theorem dropDecodeErrorPool_nonzero {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (c : Nat) (hpos : 0 < c) (hlt : c * 32 < 2 ^ 63)
    (sf : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents 72 8)
        (M.stepEvents (rustDeallocEvents (c * 32) 8) st)) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜DropDecodeErrorEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf := by
  rw [← M.stepEvents_append]
  exact Entails.sepExists_right _
    (Entails.pure_right (Or.inr ⟨c, hpos, hlt, rfl⟩) (Entails.refl _))

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` verification of `core::ptr::drop_glue::<prost::error::DecodeError> [local#3]`
(block `555`, 41 instructions), parameterized by `dStack`. -/
theorem drop_decode_error_3_placed_ok_gen [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok (lsProg_551 H) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetExternSpecWithStack M A lim dStack)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorBudgetSpecGen M A lim dStack) := by
  simp only [dropDecodeErrorBudgetSpecGen, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, RustCliAllocBudget.repAlloc_live, stackAt_dropDecodeErrorGen hd,
    sepExists_sepConj_left, sepExists_sepConj_right, List.length_replicate]
  simp only [rustCliDeallocBudgetExternSpecWithStack, RustLayoutOk, LayoutOk] at hdealloc
  wp_init x s0
  obtain ⟨e, st⟩ := x
  dsimp only at *
  have hkv : KindNoHeap v_stk_5 := by assumption
  have hbr := kindNoHeap_branch_false hkv
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hal8 : 8 ≤ 2 ^ 31 := by decide
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by assumption
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8, st)
    apply SepWP.fold (dropDecodeErrorPool_zero A lim st _) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    have hpos_vec : 0 < v_stk_6.toNat * 32 := hlay_vec.1
    have hsum_vec : v_stk_6.toNat * 32 + 8 ≤ 2 ^ 63 := hlay_vec.2.2
    have hpos_cap : 0 < v_stk_6.toNat :=
      Nat.pos_of_ne_zero fun h0 => hcap0 (BitVec.eq_of_toNat_eq h0)
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8, st)
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8, M.stepEvents (rustDeallocEvents (v_stk_6.toNat * 32) 8) st)
    apply SepWP.fold (dropDecodeErrorPool_nonzero A lim st v_stk_6.toNat hpos_cap h_cap_lt _)
      (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` verification of `drop_glue::<DecodeError> [local#3]`
(block `555`) against `dropDecodeErrorBudgetSpec M A lim` directly from `HookSat H lsRustDeallocSym`. -/
theorem drop_decode_error_3_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorBudgetSpec M A lim) := by
  refine drop_decode_error_3_placed_ok_gen (dStack := allocHookStack) (by decide) ?_
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem (a := lsRustDeallocSym)
    (l := libsignalSessionExterns) (by decide)
  exact subroutine_ok_rustCliDeallocBudget_externWithStack (stk := allocHookStack)
    (by decide) (by decide)
    (ls_hook_ok (prog := lsProg_551 H) (i := 551) (k := k)
      (by rw [List.getElem?_eq_getElem hlt, hk]) hdealloc)

end DropDecodeError3Placed

/-- Smart constructor for `SignedPortDepsPlaced` discharging `dropDecodeError3` (block `555`)
automatically from `hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)`. -/
theorem SignedPortDepsPlaced.of_prost [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hVarint : subroutine_ok (lsProg_559 H) (blkPl_559).base
      (withLsCodeLoaded lsmpl (decodeVarint2BudgetSpec M A lim)))
    (hSkip : subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (hBytes : subroutine_ok (lsProg_558 H) (blkPl_558).base
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim))) :
    SignedPortDepsPlaced M A lim H :=
  ⟨hVarint, hSkip, hBytes, drop_decode_error_3_placed_ok hdealloc⟩

/-! ## 4. `FitsEnv fineCostModel` Non-Vacuity Witnesses (`1 GiB`) -/

/-- Concrete `1 GiB` (`physCap = 2 ^ 30`) `BudgetLimits` for the `FitsEnv fineCostModel` non-vacuity witnesses. -/
def spkNonVacLimits : BudgetLimits where
  staticCount := 16
  staticBytes := 16 * 1024 * 1024
  physCap := 2 ^ 30
  enforced := true

private def SpkCaps.MaxLe (caps : SpkCaps) (B : Nat) : Prop :=
  caps.pub ≤ B ∧ caps.priv ≤ B ∧ caps.sig ≤ B

private theorem SpkCaps.get_le_of_maxLe {caps : SpkCaps} {B : Nat}
    (h : caps.MaxLe B) (f : SpkField) : caps.get f ≤ B := by
  rcases h with ⟨hpub, hpriv, hsig⟩
  cases f <;> simp only [SpkCaps.get] <;> omega

private theorem SpkCaps.maxLe_set {caps : SpkCaps} {B v : Nat}
    (h : caps.MaxLe B) (hv : v ≤ B) (f : SpkField) :
    (caps.set f v).MaxLe B := by
  rcases h with ⟨hpub, hpriv, hsig⟩
  cases f <;> exact ⟨by simpa [SpkCaps.set], by simpa [SpkCaps.set], by simpa [SpkCaps.set]⟩

private theorem decodeErrorPushBounded0_phaseCredit :
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
      fineCostModel (DecodeErrorPushBoundedEnv 0) 9795 0 0 128 := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  open LibsignalBinary.Heap.Fine.ClientBounds in
  have hmax : 128 ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h128 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 128 8) 9795 0 0 128 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 128)
      (by decide) hmax).mono
      (Nat.le_trans (smallAllocCost_le_two_mul_add 128) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 9795 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  exact (hnil.or h128).of_imp fun evs hp => by
    rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega

private theorem spkErrTail_phaseCredit :
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
      fineCostModel SpkErrTailEnv 19590 0 0 128 := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  open LibsignalBinary.Heap.Fine.ClientBounds in
  have hmax : 128 ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h72 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 9683 0 0 72 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 72)
      (by decide) (by omega)).mono
      (Nat.le_trans (smallAllocCost_le_two_mul_add 72) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
  have hfp : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents 72 8) (DecodeErrorPushBoundedEnv 0)) 19590 0 0 128 :=
    (h72.concat decodeErrorPushBounded0_phaseCredit).mono
      (by decide) (by decide) (by decide) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 19590 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  have h72' : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 19590 0 0 128 :=
    h72.mono (by decide) (by decide) (by decide) (by decide)
  exact ((hnil.or h72').or hfp).of_imp fun evs he => by
    cases he with
    | nil => exact Or.inl (Or.inl rfl)
    | fromOnly => exact Or.inl (Or.inr rfl)
    | fromPush hp => exact Or.inr (ConcatEnv.append rfl hp)

private theorem spkBytesMergeStep_small_phaseCredit {wt : WireType} {bs v rest : List (BitVec 8)}
    {c : Nat} (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 63) (hc : c ≤ 128) :
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
      fineCostModel (· = bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs) 19590 0 0 128 := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  open LibsignalBinary.Heap.Fine.ClientBounds in
  have hmax : 128 ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcore : bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs =
      if v.length = 0 then []
      else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
        rustDeallocEvents v.length 1 := by
    simp [bytesMergeEventsCore, hm, hc_toNat]
  rw [show (· = bytesMergeEventsCore wt (BitVec.ofNat 64 c) bs) =
      (· = if v.length = 0 then []
        else rustAllocEvents v.length 1 ++ doReserveClearEvents c v.length ++
          rustDeallocEvents v.length 1) by rw [hcore]]
  split_ifs with hv0
  · exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  · have hv_pos : 0 < v.length := by omega
    have halloc : PhaseCreditSpec fineCostModel (· = rustAllocEvents v.length 1) 9665 0 0 128 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
        (by decide) (by omega)).mono
        (Nat.le_trans (smallAllocCost_le_two_mul_add v.length) (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    have hres : PhaseCreditSpec fineCostModel (· = doReserveClearEvents c v.length) 9795 0 0 128 := by
      unfold doReserveClearEvents
      split_ifs with hle hc0
      · exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
      · have hnc_le : reserveCap c 0 v.length ≤ 128 := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1)
          (req := reserveCap c 0 v.length) (by decide) (by omega)).mono
          (Nat.le_trans (smallAllocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hnc_le : reserveCap c 0 v.length ≤ 128 := by
          dsimp only [reserveCap]; omega
        have hnc_pos : 1 ≤ reserveCap c 0 v.length := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := c)
          (new := reserveCap c 0 v.length) (al := 1) (by decide) hnc_pos (by omega) (by omega)
          hnc_pos (by omega)).mono
          (Nat.le_trans (smallReallocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    exact (((halloc.concat hres).concat hfree).mono
      (by decide) (by decide) (by decide) (by decide)).of_imp fun evs he => by
        subst he
        exact ConcatEnv.append (ConcatEnv.append rfl rfl) rfl

private theorem spkLoop_small_phaseCredit :
    ∀ (rem : Nat) {caps : SpkCaps},
      rem ≤ 64 → caps.MaxLe 128 →
      LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.PhaseCreditSpec
        fineCostModel (SpkLoopBoundedEnv rem caps) (19590 * (rem + 1)) 0 0 128 := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro caps hrem hcaps
    open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit in
    refine {
      req_align := fun evs he => ?_
      credit_le := fun st0 {_} he => ?_
    }
    · cases he with
      | done herr => exact spkErrTail_phaseCredit.req_align evs herr
      | @skipStep _ rem' _ _ hlt hnext =>
        exact (ih rem' hlt (by omega) hcaps).req_align evs hnext
      | @bytesStep f _ rem' _ wt bs v rest evs₂ hm hbs_le hprog _ hnext =>
        have hc : caps.get f ≤ 128 := SpkCaps.get_le_of_maxLe hcaps f
        have hnc : (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length) ≤ 128 := by
          split_ifs
          · exact hc
          · dsimp only [reserveCap]; omega
        have h1 := spkBytesMergeStep_small_phaseCredit hm (by omega) hc
        have h2 := ih rem' (by omega) (by omega) (SpkCaps.maxLe_set hcaps hnc f)
        exact (h1.concat h2).req_align _ (ConcatEnv.append rfl hnext)
    · cases he with
      | done herr =>
        exact (spkErrTail_phaseCredit.mono
          (Nat.le_mul_of_pos_right 19590 (Nat.succ_pos rem))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)).credit_le st0 herr
      | @skipStep _ rem' _ _ hlt hnext =>
        have hmul : 19590 * (rem' + 1) ≤ 19590 * (rem + 1) :=
          Nat.mul_le_mul_left 19590 (by omega)
        exact ((ih rem' hlt (by omega) hcaps).mono
          hmul (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)).credit_le st0 hnext
      | @bytesStep f _ rem' _ wt bs v rest evs₂ hm hbs_le hprog _ hnext =>
        have hc : caps.get f ≤ 128 := SpkCaps.get_le_of_maxLe hcaps f
        have hnc : (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length) ≤ 128 := by
          split_ifs
          · exact hc
          · dsimp only [reserveCap]; omega
        have h1 := spkBytesMergeStep_small_phaseCredit hm (by omega) hc
        have h2 := ih rem' (by omega) (by omega) (SpkCaps.maxLe_set hcaps hnc f)
        have hmul : 19590 + 19590 * (rem' + 1) ≤ 19590 * (rem + 1) := by
          calc 19590 + 19590 * (rem' + 1) = 19590 * (rem' + 1) + 19590 := Nat.add_comm _ _
            _ = 19590 * (rem' + 2) := (Nat.mul_succ 19590 (rem' + 1)).symm
            _ ≤ 19590 * (rem + 1) := Nat.mul_le_mul_left 19590 (by omega)
        exact ((h1.concat h2).mono
          hmul (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)).credit_le st0
          (ConcatEnv.append rfl hnext)

/-- Non-trivial inhabitation witness: `DecodeErrorPushBoundedEnv 0` admits the initial
`128`-byte stack allocation (`rustAllocEvents 128 8`). -/
theorem decodeErrorPushBoundedEnv_inhabited_nontrivial :
    ∃ evs : List AllocEvent, DecodeErrorPushBoundedEnv 0 evs ∧ evs.length = 1 :=
  ⟨rustAllocEvents 128 8, Or.inr (Or.inl ⟨rfl, rfl⟩), rfl⟩

/-- Non-vacuity witness: `DecodeErrorPushBoundedEnv 0` satisfies
`FitsEnv fineCostModel` from `fineCostModel.init` under `spkNonVacLimits` (`1 GiB`). -/
theorem decodeErrorPushBoundedEnv_fitsEnv_witness :
    FitsEnv fineCostModel spkNonVacLimits fineCostModel.init (DecodeErrorPushBoundedEnv 0) := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  exact fitsEnv_fineCostModel_of_phaseCredit decodeErrorPushBounded0_phaseCredit
    (by decide) rfl (by decide) (by decide)

/-- Non-empty allocating sample `BytesMergeGhost` (`valCap = 0`, 4-byte length-delimited payload). -/
def spkSampleBytesMergeGhost : BytesMergeGhost where
  wt := .lengthDelimited
  valPtr := 0#64
  valCap := 0#64
  valBuf := 1#64
  valBs := []
  bufRef := 0#64
  slot := 0#64
  ptr := 0#64
  bs := [4#8, 1#8, 2#8, 3#8, 4#8]

/-- Non-trivial inhabitation witness: `BytesMerge3Env spkSampleBytesMergeGhost` emits `3`
allocator events (`alloc(4, 1)`, `alloc(8, 1)`, `dealloc(4, 1)`). -/
theorem bytesMerge3Env_inhabited_nontrivial :
    ∃ evs : List AllocEvent, BytesMerge3Env spkSampleBytesMergeGhost evs ∧ evs.length = 3 :=
  ⟨bytesMergeEventsCore .lengthDelimited 0#64 [4#8, 1#8, 2#8, 3#8, 4#8], rfl, rfl⟩

/-- Non-vacuity witness: `BytesMerge3Env spkSampleBytesMergeGhost` satisfies
`FitsEnv fineCostModel` from `fineCostModel.init` under `spkNonVacLimits` (`1 GiB`). -/
theorem bytesMerge3Env_fitsEnv_witness :
    FitsEnv fineCostModel spkNonVacLimits fineCostModel.init
      (BytesMerge3Env spkSampleBytesMergeGhost) := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  have hm : mergeBytes .lengthDelimited [4#8, 1#8, 2#8, 3#8, 4#8] =
      some ([1#8, 2#8, 3#8, 4#8], []) := rfl
  have hspec := spkBytesMergeStep_small_phaseCredit (c := 0) hm (by decide) (by decide)
  exact fitsEnv_fineCostModel_of_phaseCredit hspec (by decide) rfl (by decide) (by decide)

/-- Non-trivial inhabitation witness: `SpkLoopEnv 131 64` admits a non-empty `bytesStep`
trace (`mergeBytes .lengthDelimited [1, 42] = some ([42], [])`, `3` allocator events). -/
theorem spkLoopEnv_inhabited_nontrivial :
    ∃ evs : List AllocEvent, SpkLoopEnv 131 64 evs ∧ evs.length = 3 := by
  have hm : mergeBytes .lengthDelimited [1#8, 42#8] = some ([42#8], []) := rfl
  refine ⟨bytesMergeEventsCore .lengthDelimited 0#64 [1#8, 42#8] ++ [],
    SpkLoopBoundedEnv.bytesStep .pub (rem' := 0) .lengthDelimited [1#8, 42#8] [42#8] []
      hm (by decide) (by decide) (by decide) (.done .nil), ?_⟩
  decide

/-- Non-vacuity witness: `SpkLoopEnv 131 64` satisfies `FitsEnv fineCostModel`
from `fineCostModel.init` under `spkNonVacLimits` (`1 GiB` RAM cap). -/
theorem spkLoopEnv_fitsEnv_witness :
    FitsEnv fineCostModel spkNonVacLimits fineCostModel.init (SpkLoopEnv 131 64) := by
  open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas in
  have hspec := spkLoop_small_phaseCredit 64 (caps := SpkCaps.zero) (by decide)
    ⟨by decide, by decide, by decide⟩
  exact fitsEnv_fineCostModel_of_phaseCredit hspec (by decide) rfl (by decide) (by decide)

end LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
