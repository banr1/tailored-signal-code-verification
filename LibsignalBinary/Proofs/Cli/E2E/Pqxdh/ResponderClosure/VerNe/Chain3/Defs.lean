/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs

/-!
# `message::merge<Chain> [local#5]` Definitions and Loop Assembly

Defines the intermediate chain representation `chain3GAt`, top-level specification
`chainMerge3SpecAtWExt` (`Chain3OkAtWExt`), loop invariant `Chain3LoopAtWExt`, per-field slice
statements (`Chain3EntryStmtExt`, `Chain3SrkStmtExt`, `Chain3ChainKeyStmtExt`,
`Chain3MessageKeysStmtExt`, `Chain3ExitStmtExt`), and loop induction `chainMerge3W_ok_ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

/-! ## 1. Stack Budgets -/


/-- Callee budget below the `0xf0` frame: `bytes::merge [local#4]`'s `bytesMerge3Stack` (`33120` B),
the largest in-scope callee (`decode_varint [local#3]`: `32896` B, `grow_one`: `16896` B). -/
abbrev chainMerge3SubStackX : Nat := bytesMerge3Stack

/-- Stack budget of `message::merge<Chain> [local#3]`: frame `0xf0` + `chainMerge3SubStackX`
(`33360` B). -/
abbrev chainMerge3StackX : Nat := 0xf0 + chainMerge3SubStackX

theorem chainMerge3SubStackX_eq : chainMerge3SubStackX = 33120 := rfl

theorem chainMerge3StackX_eq : chainMerge3StackX = 33360 := rfl

/-! ## 2. Chain Layout (`chain3GAt`) During Merge -/

/-- A `Vec<u8>` at `v` holding `bs`, with capacity 0 while `bs` is empty (the `Vec::new()` of
`Chain::default()`), so that `bytes::merge [local#4]`'s `BytesMergeCapOk` holds at the merge. -/
def chain3VecAt (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜bs = [] → cap = 0#64⌝ ∗ vecU8At A v cap ptr bs

/-- The `message_keys` and `chain_key` fields of `prostChainGAt A a c` (a literal copy of its
tail). -/
def chainGRest (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

/-- Chain layout at `a` during `message::merge<Chain>`, representing `srk` and `priv` via `chain3VecAt`. -/
def chain3GAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) c.priv ∗ chainGRest A a c

theorem prostChainGAt_eq_rest (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c = vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗ chainGRest A a c := by
  unfold prostChainGAt chainGRest
  rfl

theorem chain3VecAt_entails_vecU8 (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    chain3VecAt A v bs ⊢ vecU8 A v bs := by
  unfold chain3VecAt vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem chain3GAt_entails_prostChainGAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    chain3GAt A a c ⊢ prostChainGAt A a c := by
  rw [prostChainGAt_eq_rest]
  unfold chain3GAt
  exact sepConj_mono (chain3VecAt_entails_vecU8 A a c.srk)
    (sepConj_mono_left (chain3VecAt_entails_vecU8 A (a + 0x18#64) c.priv))

/-- A non-empty `Vec<u8>` is a `chain3VecAt` (the pure side condition is vacuous). -/
theorem chain3VecAt_of_ne_nil (A : RustAlloc) (v cap ptr : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs ≠ []) :
    vecU8At A v cap ptr bs ⊢ chain3VecAt A v bs := by
  unfold chain3VecAt
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.pure_right (fun h => absurd h hbs) (Entails.refl _)))

/-- An empty `chain3VecAt` has capacity 0. -/
theorem chain3VecAt_nil_elim (A : RustAlloc) (v : BitVec 64) :
    chain3VecAt A v [] ⊢ ∃∗ ptr : BitVec 64, vecU8At A v 0#64 ptr [] := by
  unfold chain3VecAt
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun h => ?_
  rw [h rfl]
  exact Entails.sepExists_right ptr (Entails.refl _)

theorem chain3VecAt_nil_intro (A : RustAlloc) (v ptr : BitVec 64) :
    vecU8At A v 0#64 ptr [] ⊢ chain3VecAt A v [] := by
  unfold chain3VecAt
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right ptr
    (Entails.pure_right (fun _ => rfl) (Entails.refl _)))

/-- `Chain::default()`'s cells at `v` (`cap = 0`, `ptr = 1`, `len = 0`) are an empty `chain3VecAt`. -/
theorem default_cells_entail_chain3VecAt (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ chain3VecAt A v [] := by
  refine Entails.trans ?_ (chain3VecAt_nil_intro A v 1#64)
  unfold vecU8At vecHeader
  have hp : (⌜([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj, List.length_nil]
  exact Entails.of_eq (by simp)

/-- `Chain::default()`'s empty `Vec<MessageKey>` cells at `v` (`cap = 0`, `ptr = 8`, `len = 0`). -/
theorem default_cells_entail_c3Keys (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) v [] := by
  unfold RustHeap.vecOf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  unfold RustHeap.vecAt vecHeader RustHeap.vecBuf
  have hp : (⌜([] : List MessageKeyGenerator).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

/-- `Chain::default()` cells at `a` form `chain3GAt A a ChainG.empty` (used at both tag-6 `ss + 0x90`
and tag-7 `sp0 - 232` call sites). -/
theorem default_cells_entail_chain3GAt (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
    ((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ 1#64) ∗ ((a + 0x28#64) ↦₆₄ 0#64) ∗
    ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ 8#64) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
    ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 ⊢
      chain3GAt A a ChainG.empty := by
  have h1 : a + 0x18#64 + 8#64 = a + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have h2 : a + 0x18#64 + 16#64 = a + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  have h3 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have h4 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hv1 := default_cells_entail_chain3VecAt A a
  have hv2 := default_cells_entail_chain3VecAt A (a + 0x18#64)
  have hv3 := default_cells_entail_c3Keys A (a + 0x30#64)
  rw [h1, h2] at hv2
  rw [h3, h4] at hv3
  unfold chain3GAt chainGRest ChainG.empty
  dsimp only
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv3)))
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Top-Level Contract -/

/-- Contract of `message::merge<Chain> [local#5]` into a default `Chain` at `x.a` under stack budget
`chainMerge3StackX`, parameterized over `A : RustAlloc`. -/
def chainMerge3SpecAtWExt (A : RustAlloc) (img : Obj.Image) : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      chain3GAt A x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool ∗ stackAt s.sp chainMerge3StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp chainMerge3StackX
  onPanic := Serialization.allocPanic

def chainMerge3SpecAtW (img : Obj.Image) : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      chain3GAt A0 x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      stackAt s.sp chainMerge3StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      stackAt s0.sp chainMerge3StackX
  onPanic := Serialization.allocPanic

theorem chainMerge3SpecAtWExt_A0 (img : Obj.Image) :
    chainMerge3SpecAtWExt A0 img = chainMerge3SpecAtW img := by
  unfold chainMerge3SpecAtWExt chainMerge3SpecAtW
  have hp : A0.pool = emp := rfl
  simp only [hp, emp_sepConj]

/-- Satisfaction of `chainMerge3SpecAtWExt A img` on `SP2Ext img.base ext`. -/
def Chain3OkAtWExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  OkAtX img.base ext chainMerge3Name (chainMerge3SpecAtWExt A img)

def Chain3OkAtW (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  OkAtX img.base ext chainMerge3Name (chainMerge3SpecAtW img)

theorem Chain3OkAtWExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3OkAtWExt A0 img ext = Chain3OkAtW img ext := by
  unfold Chain3OkAtWExt Chain3OkAtW
  rw [chainMerge3SpecAtWExt_A0]

abbrev chainMerge5SubStackX : Nat := chainMerge3SubStackX
abbrev chainMerge5StackX : Nat := chainMerge3StackX
abbrev chainMerge5SpecAtWExt (A : RustAlloc) (img : Obj.Image) : Spec ChainMergeGenGhost :=
  chainMerge3SpecAtWExt A img
abbrev chainMerge5SpecAtW (img : Obj.Image) : Spec ChainMergeGenGhost := chainMerge3SpecAtW img
abbrev Chain5OkAtWExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3OkAtWExt A img ext
abbrev Chain5OkAtW (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3OkAtW img ext

/-! ## 4. Callee Contracts -/

/-- The callee contracts the in-scope run of `[local#3]` uses, parameterized over `A : RustAlloc`. -/
structure Chain3CalleesWExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop where
  dv : OkAtX img.base ext c3DecodeVarintName
    ((decodeVarint2SpecX A).inImage img)
  bm : OkAtX img.base ext c3BytesMergeName
    (bytesMerge3Spec A img)
  grow : OkAtX img.base ext c3GrowOneName
    ((Proofs.libsignal.Stage1X.growOneChainSpecX A).inImage img)

abbrev Chain3CalleesW (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A0 img ext

/-! ## 5. Loop Invariant and Segment Steps -/

/-- `message::merge<Chain> [local#3] + off` in `SP2Ext img.base ext`. -/
noncomputable abbrev chain3PCAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (off : BitVec 64) : BitVec 64 :=
  (SP2Ext img.base ext).fnAddr chainMerge3Name + off

/-- One segment step of `[local#3]` (ends in `Q` or panics with `allocPanic`), at allocator `A`. -/
abbrev Chain3StepAtWExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (chainMerge3SpecAtWExt A img) x R s0 s Q

abbrev Chain3StepAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (chainMerge3SpecAtW img) x R s0 s Q

/-- The 160-byte local frame `[sp0 - 0xf0, sp0 - 0x50)` and the 9 register words saved by the
prologue (`+0x004..+0x014`) at `[sp0 - 0x50, sp0)`, with the 8-byte hole at `sp0 - 0x38`. -/
def chain3SavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  memRegion (sp0 - 0xf0#64) 160 ∗
  ((sp0 - 0x50#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 0x48#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 0x40#64) ↦₆₄ s0.readReg64 .x25) ∗
  memRegion (sp0 - 0x38#64) 8 ∗
  ((sp0 - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 0x8#64) ↦₆₄ s0.readReg64 .x19)

/-- Field-loop invariant at `+0x0a8` parameterized over `A : RustAlloc`. -/
def Chain3LoopAtWExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chain3PCAtW img ext 0xa8#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = s0.sp - 0xf0#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x50#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x21 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x22 = s0.sp - 0xe8#64 ∧ s.readReg64 .x23 = 1#64 ∧ s.readReg64 .x24 = 104#64 ∧
    s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
    s.readReg64 .x28 = s0.readReg64 .x28 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    (s.mem ⊨ chain3GAt A x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R)

def Chain3LoopAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chain3PCAtW img ext 0xa8#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = s0.sp - 0xf0#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x50#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x21 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x22 = s0.sp - 0xe8#64 ∧ s.readReg64 .x23 = 1#64 ∧ s.readReg64 .x24 = 104#64 ∧
    s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
    s.readReg64 .x28 = s0.readReg64 .x28 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    (s.mem ⊨ chain3GAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R)

theorem Chain3LoopAtWExt_A0 (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) :
    Chain3LoopAtWExt A0 img ext x R s0 k = Chain3LoopAtW img ext x R s0 k := by
  funext s
  unfold Chain3LoopAtWExt Chain3LoopAtW
  have hp : A0.pool = emp := rfl
  simp only [hp, emp_sepConj]

/-- Return state of `[local#3]` with `(chainMerge3SpecAtWExt A img).post`. -/
def Chain3RetAtWExt (A : RustAlloc) (img : Obj.Image) (x : ChainMergeGenGhost) (R : SepProp)
    (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMerge3SpecAtWExt A img).post x s0 sf ∗ R)

def Chain3RetAtW (img : Obj.Image) (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMerge3SpecAtW img).post x s0 sf ∗ R)

theorem Chain3RetAtWExt_A0 (img : Obj.Image) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) :
    Chain3RetAtWExt A0 img x R s0 = Chain3RetAtW img x R s0 := by
  funext sf
  unfold Chain3RetAtWExt Chain3RetAtW
  rw [chainMerge3SpecAtWExt_A0]

/-! ## 6. Slice Statements -/

/-- Entry slice statement (`+0x000 → +0x0a8`, `k = 0`) at allocator `A`. -/
def Chain3EntryStmtExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name →
    s0.status = .Running →
    (s0.mem ⊨ (chainMerge3SpecAtWExt A img).pre x s0 ∗ R) →
    s0.spAligned = true →
    Chain3StepAtWExt A img ext x R s0 s0 (Chain3LoopAtWExt A img ext x R s0 0)

def Chain3EntryStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name →
    s0.status = .Running →
    (s0.mem ⊨ (chainMerge3SpecAtW img).pre x s0 ∗ R) →
    s0.spAligned = true →
    Chain3StepAtW img ext x R s0 s0 (Chain3LoopAtW img ext x R s0 0)

theorem Chain3EntryStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3EntryStmtExt A0 img ext = Chain3EntryStmt img ext := by
  unfold Chain3EntryStmtExt Chain3EntryStmt Chain3StepAtWExt Chain3StepAtW Chain3CalleesW
  simp only [chainMerge3SpecAtWExt_A0, Chain3LoopAtWExt_A0]

/-- SRK slice statement (tags 1 and 2: `sender_ratchet_key` and `sender_ratchet_key_private`) at allocator `A`. -/
def Chain3SrkStmtExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    Chain3LoopAtWExt A img ext x R s0 k s →
    Chain3StepAtWExt A img ext x R s0 s (Chain3LoopAtWExt A img ext x R s0 (k + 1))

def Chain3SrkStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    Chain3LoopAtW img ext x R s0 k s →
    Chain3StepAtW img ext x R s0 s (Chain3LoopAtW img ext x R s0 (k + 1))

theorem Chain3SrkStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3SrkStmtExt A0 img ext = Chain3SrkStmt img ext := by
  unfold Chain3SrkStmtExt Chain3SrkStmt Chain3StepAtWExt Chain3StepAtW Chain3CalleesW
  simp only [chainMerge3SpecAtWExt_A0, Chain3LoopAtWExt_A0]

/-- ChainKey slice statement (tag 3) at allocator `A`. -/
def Chain3ChainKeyStmtExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    Chain3LoopAtWExt A img ext x R s0 k s →
    Chain3StepAtWExt A img ext x R s0 s (Chain3LoopAtWExt A img ext x R s0 (k + 1))

def Chain3ChainKeyStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    Chain3LoopAtW img ext x R s0 k s →
    Chain3StepAtW img ext x R s0 s (Chain3LoopAtW img ext x R s0 (k + 1))

theorem Chain3ChainKeyStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3ChainKeyStmtExt A0 img ext = Chain3ChainKeyStmt img ext := by
  unfold Chain3ChainKeyStmtExt Chain3ChainKeyStmt Chain3StepAtWExt Chain3StepAtW Chain3CalleesW
  simp only [chainMerge3SpecAtWExt_A0, Chain3LoopAtWExt_A0]

/-- MessageKeys slice statement (tag 4) at allocator `A`. -/
def Chain3MessageKeysStmtExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    Chain3LoopAtWExt A img ext x R s0 k s →
    Chain3StepAtWExt A img ext x R s0 s (Chain3LoopAtWExt A img ext x R s0 (k + 1))

def Chain3MessageKeysStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    Chain3LoopAtW img ext x R s0 k s →
    Chain3StepAtW img ext x R s0 s (Chain3LoopAtW img ext x R s0 (k + 1))

theorem Chain3MessageKeysStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MessageKeysStmtExt A0 img ext = Chain3MessageKeysStmt img ext := by
  unfold Chain3MessageKeysStmtExt Chain3MessageKeysStmt Chain3StepAtWExt Chain3StepAtW Chain3CalleesW
  simp only [chainMerge3SpecAtWExt_A0, Chain3LoopAtWExt_A0]

/-- Exit slice statement (`k = fields.length`) at allocator `A`. -/
def Chain3ExitStmtExt (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    Chain3LoopAtWExt A img ext x R s0 x.c.fields.length s →
    Chain3StepAtWExt A img ext x R s0 s (Chain3RetAtWExt A img x R s0)

def Chain3ExitStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    Chain3LoopAtW img ext x R s0 x.c.fields.length s →
    Chain3StepAtW img ext x R s0 s (Chain3RetAtW img x R s0)

theorem Chain3ExitStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3ExitStmtExt A0 img ext = Chain3ExitStmt img ext := by
  unfold Chain3ExitStmtExt Chain3ExitStmt Chain3StepAtWExt Chain3StepAtW
  simp only [chainMerge3SpecAtWExt_A0, Chain3LoopAtWExt_A0, Chain3RetAtWExt_A0]

/-! ## 7. Loop Induction and Assembly -/

/-- Induction over the remaining `m` fields of `x.c.fields` at allocator `A`. -/
theorem chain3Loop_run_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Chain3CalleesWExt A img ext)
    (hSrk : Chain3SrkStmtExt A img ext) (hCk : Chain3ChainKeyStmtExt A img ext)
    (hMk : Chain3MessageKeysStmtExt A img ext) (hExit : Chain3ExitStmtExt A img ext)
    {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      Chain3LoopAtWExt A img ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (chainMerge3SpecAtWExt A img) x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hExit x R s0 s hs) fun sf ⟨hret, hcc, hmem⟩ => ?_
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', Chain3LoopAtWExt A img ext x R s0 (k + 1) s' →
        reaches_outcome (SP2Ext img.base ext) (chainMerge3SpecAtWExt A img) x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hSrk hC x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hCk hC x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hMk hC x R s0 k s hlt h4 hs) next

theorem chain3Loop_run (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Chain3CalleesW img ext)
    (hSrk : Chain3SrkStmt img ext) (hCk : Chain3ChainKeyStmt img ext)
    (hMk : Chain3MessageKeysStmt img ext) (hExit : Chain3ExitStmt img ext)
    {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      Chain3LoopAtW img ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (chainMerge3SpecAtW img) x R s0 s := by
  rw [← Chain3SrkStmtExt_A0] at hSrk
  rw [← Chain3ChainKeyStmtExt_A0] at hCk
  rw [← Chain3MessageKeysStmtExt_A0] at hMk
  rw [← Chain3ExitStmtExt_A0] at hExit
  rw [← chainMerge3SpecAtWExt_A0]
  intro m k s hk hs
  rw [← Chain3LoopAtWExt_A0] at hs
  exact chain3Loop_run_ext img ext hC hSrk hCk hMk hExit m k s hk hs

/-- Assembles the five slice statements and callee contracts into `Chain3OkAtWExt A`. -/
theorem chainMerge3W_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Chain3CalleesWExt A img ext)
    (hEntry : Chain3EntryStmtExt A img ext) (hSrk : Chain3SrkStmtExt A img ext)
    (hCk : Chain3ChainKeyStmtExt A img ext) (hMk : Chain3MessageKeysStmtExt A img ext)
    (hExit : Chain3ExitStmtExt A img ext) :
    Chain3OkAtWExt A img ext := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hal _
  exact segStepG_then (hEntry hC x R s0 hpc hrun hpre hal) fun s hs =>
    chain3Loop_run_ext img ext hC hSrk hCk hMk hExit x.c.fields.length 0 s (Nat.zero_add _) hs

theorem chainMerge3W_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Chain3CalleesW img ext)
    (hEntry : Chain3EntryStmt img ext) (hSrk : Chain3SrkStmt img ext)
    (hCk : Chain3ChainKeyStmt img ext) (hMk : Chain3MessageKeysStmt img ext)
    (hExit : Chain3ExitStmt img ext) :
    Chain3OkAtW img ext := by
  rw [← Chain3OkAtWExt_A0]
  rw [← Chain3EntryStmtExt_A0] at hEntry
  rw [← Chain3SrkStmtExt_A0] at hSrk
  rw [← Chain3ChainKeyStmtExt_A0] at hCk
  rw [← Chain3MessageKeysStmtExt_A0] at hMk
  rw [← Chain3ExitStmtExt_A0] at hExit
  exact chainMerge3W_ok_ext img ext hC hEntry hSrk hCk hMk hExit

/-! ## 8. Callee Offsets and Sub-Stack Splits -/

/-- `bl decode_varint [local#3]` target, relative to `chainMerge3Name`. -/
theorem c3_decodeVarint_ok_sub {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64))
      ((decodeVarint2SpecX A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr c3DecodeVarintName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]"), (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]")]
    bv_omega
  rw [heq]; exact hC.dv

/-- `bl bytes::merge [local#4]` target, relative to `chainMerge3Name`. -/
theorem c3_bytesMerge_ok_sub {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64))
      (bytesMerge3Spec A img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr c3BytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]"), (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]")]
    bv_omega
  rw [heq]; exact hC.bm

/-- `bl grow_one<MessageKey>` target, relative to `chainMerge3Name`. -/
theorem c3_growOne_ok_sub {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64))
      ((Proofs.libsignal.Stage1X.growOneChainSpecX A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr c3GrowOneName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one")]
    bv_omega
  rw [heq]; exact hC.grow

/-- The sub-stack is exactly `bytes::merge [local#4]`'s budget. -/
theorem stackAt_c3Sub_eq_bytesMerge (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      stackAt sp bytesMerge3Stack := rfl

/-- Split of the sub-stack for a `decode_varint [local#3]` call. -/
theorem stackAt_c3Sub_to_decodeVarint (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMerge3SubStackX)
          (chainMerge3SubStackX - decodeVarint2StackX) ∗
        stackAt sp decodeVarint2StackX :=
  stackAt_sub_split_seedChain sp decodeVarint2StackX
    chainMerge3SubStackX

/-- Split of the sub-stack for a `grow_one<MessageKey>` call. -/
theorem stackAt_c3Sub_to_growOne (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMerge3SubStackX)
          (chainMerge3SubStackX - Proofs.libsignal.Stage1X.growOneChainStackX) ∗
        stackAt sp Proofs.libsignal.Stage1X.growOneChainStackX :=
  stackAt_sub_split_seedChain sp Proofs.libsignal.Stage1X.growOneChainStackX chainMerge3SubStackX

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
