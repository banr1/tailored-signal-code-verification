/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Shared Definitions

Defines the preserved register bundle `Chain3MkRegs` and the four sub-step statements decomposing
the tag-4 (`message_keys`) slice (`Chain3MessageKeysStmt`) around the 104-byte scratch `MessageKey`
at `sp0 - 0xe8`: `Chain3MkHeadStmt`, `Chain3MkCntStmt`, `Chain3MkSeedStmt`, and `Chain3MkPushStmt`
(plus `A : RustAlloc`-parameterized `*Ext` variants).
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
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

/-! ## 1. Register bookkeeping -/

/-- The registers the tag-4 path keeps: `x19..x24`, `x26..x29` and `calleeSavedVRegs`
(`x25` holds the inner limit, then the `Vec` length; it is not in `Chain3LoopAtW`). -/
def Chain3MkRegs (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧
  s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧
  s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧
  s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧
  s1.readReg64 .x28 = s0.readReg64 .x28 ∧
  s1.readReg64 .x29 = s0.readReg64 .x29 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

theorem Chain3MkRegs.refl (s : State) : Chain3MkRegs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Chain3MkRegs.trans {s0 s1 s2 : State}
    (h01 : Chain3MkRegs s0 s1) (h12 : Chain3MkRegs s1 s2) : Chain3MkRegs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2⟩

theorem Chain3MkRegs.of_calleeSaved {s0 s1 : State}
    (h : CalleeSavedPreserved s0 s1) : Chain3MkRegs s0 s1 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 2. Step 4d + 4e: the push (`+0x244 → +0x0a8`) -/

/-- Steps 4d + 4e (`+0x244 → +0x0a8`): when `remaining = x25 = |rest|`, pushes the filled scratch
`MessageKey` at `sp0 - 0xe8` onto `Vec<MessageKey>` at `a + 0x30` (calling `grow_one` if `len == cap`)
and returns the 104 scratch bytes at the outer loop head `+0x0a8`. -/
def Chain3MkPushStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator)
    (mk : MessageKeyGenerator) (rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    keys.length ≤ maxMessageKeys →
    s.pc = chain3PCAtW img ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x20 = a →
    s.readReg64 .x24 = 104#64 →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0xa8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 0xe8#64) 104 ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) keys ∗
        prostMsgKeyAt A0 mk (sp0 - 0xe8#64) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))

/-! ## 3. Step 4b: the counter field (`+0x244 → +0x244`) -/

/-- Step 4b (`+0x244 → +0x244`): decodes `pbVarint 1 i.toNat` (no-op when `i = 0`) into the scratch
`MessageKey` counter at `sp0 - 136`, preserving `Chain3MkRegs`. -/
def Chain3MkCntStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    (pbVarint 1 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 →
    s.pc = chain3PCAtW img ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length)
            (rest_mk ++ rest) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))

/-! ## 4. Step 4c: the seed field (`+0x244 → +0x244`) -/

/-- Step 4c (`+0x244 → +0x244`): merges `pbBytes 5 seed` (`seed.length < 128`) via `bytes::merge`
into the empty scratch seed `Vec<u8>` at `sp0 - 160`, preserving `Chain3MkRegs`. -/
def Chain3MkSeedStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (seed rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    seed.length < 128 →
    (pbBytes 5 seed ++ rest).length < 2 ^ 62 →
    s.pc = chain3PCAtW img ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x22 = sp0 - 0xe8#64 →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 160#64) seed ∗ (ptr ↦ₛ pbBytes 5 seed) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))

/-! ## 5. Step 4a: key, default scratch, length (`+0x0a8 → +0x244`) -/

/-- Step 4a (`+0x0a8 → +0x244`): decodes outer key `0x22`, initializes the default 104-byte scratch
`MessageKey` at `sp0 - 0xe8`, decodes body length `L < 128`, and sets `x25 = |rest|`. -/
def Chain3MkHeadStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (body rest tail : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    body.length < 128 →
    tail.length ≤ rest.length →
    2 + (body.length + rest.length) < 2 ^ 62 →
    s.pc = chain3PCAtW img ext 0xa8#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x21 = BitVec.ofNat 64 tail.length →
    s.readReg64 .x22 = sp0 - 0xe8#64 →
    s.readReg64 .x23 = 1#64 →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (sp0 - 0xe8#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (body ++ rest) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 0xe8#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s0 sf ∗ R))

/-! ## 6. Arbitrary-Allocator (`A : RustAlloc`) Sub-step Statements -/

def Chain3MkPushStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator)
    (mk : MessageKeyGenerator) (rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    keys.length ≤ maxMessageKeys →
    s.pc = chain3PCAtW img ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x20 = a →
    s.readReg64 .x24 = 104#64 →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0xa8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 0xe8#64) 104 ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A 104 8 (fun m b => prostMsgKeyAt A m b) (a + 0x30#64) keys ∗
        prostMsgKeyAt A mk (sp0 - 0xe8#64) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))

def Chain3MkCntStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    (pbVarint 1 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 →
    s.pc = chain3PCAtW img ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length)
            (rest_mk ++ rest) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))

def Chain3MkSeedStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (seed rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    seed.length < 128 →
    (pbBytes 5 seed ++ rest).length < 2 ^ 62 →
    s.pc = chain3PCAtW img ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x22 = sp0 - 0xe8#64 →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A (sp0 - 160#64) seed ∗ (ptr ↦ₛ pbBytes 5 seed) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))

def Chain3MkHeadStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (body rest tail : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    body.length < 128 →
    tail.length ≤ rest.length →
    2 + (body.length + rest.length) < 2 ^ 62 →
    s.pc = chain3PCAtW img ext 0xa8#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x21 = BitVec.ofNat 64 tail.length →
    s.readReg64 .x22 = sp0 - 0xe8#64 →
    s.readReg64 .x23 = 1#64 →
    (∀ (sm : State),
      sm.pc = chain3PCAtW img ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A (sp0 - 0xe8#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
          vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (body ++ rest) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 0xe8#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))

theorem Chain3MkPushStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkPushStmtExt A0 img ext = Chain3MkPushStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3MkPushStmtExt Chain3MkPushStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

theorem Chain3MkCntStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkCntStmtExt A0 img ext = Chain3MkCntStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3MkCntStmtExt Chain3MkCntStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

theorem Chain3MkSeedStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkSeedStmtExt A0 img ext = Chain3MkSeedStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3MkSeedStmtExt Chain3MkSeedStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

theorem Chain3MkHeadStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkHeadStmtExt A0 img ext = Chain3MkHeadStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3MkHeadStmtExt Chain3MkHeadStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
