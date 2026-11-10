/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs

/-!
# `message::merge<Chain> [local#5]`: ChainKey Shared Definitions

Defines the inner-loop register bundle `Chain3InnerLoopRegs`, `chain3GAt` layout lemmas for tag 3,
and the four sub-step statements decomposing `Chain3ChainKeyStmt`:
- `Chain3Seg3aStmt` (`+0x0a8 → +0x368`): outer tag-3 header, niche initialization at `a + 0x48..0x68`,
  and inner limit `x25 = |afterCk|`;
- `Chain3Seg3bStmt` (`+0x368 → +0x368`): inner field 1 (`index` varint into `[a + 0x60]`);
- `Chain3Seg3cStmt` (`+0x368 → +0x368`): inner field 2 (`key` bytes via `bytes::merge` into `a + 0x48`);
- `Chain3Seg3dStmt` (`+0x368 → +0x0a8`): inner-loop exit when remaining length equals `|afterCk|`.
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
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

/-! ## 1. Alignment & `chain3GAt` layout helpers for tag 3 -/

theorem sp0_aligned_of_sub_240_aligned {sp0 : BitVec 64} (h : (sp0 - 0xf0#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

theorem sp_sub_240_aligned {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

theorem chain3GAt_ck_none_eq_ext (A : RustAlloc) (a : BitVec 64) (c0 : ChainG) (hck : c0.ck = none) :
    chain3GAt A a c0 =
      chain3VecAt A a c0.srk ∗ chain3VecAt A (a + 0x18#64) c0.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 := by
  unfold chain3GAt chainGRest
  rw [hck]

theorem chain3GAt_ck_none_eq (a : BitVec 64) (c0 : ChainG) (hck : c0.ck = none) :
    chain3GAt A0 a c0 =
      chain3VecAt A0 a c0.srk ∗ chain3VecAt A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 :=
  chain3GAt_ck_none_eq_ext A0 a c0 hck

theorem chain3GAt_apply_ck_eq_ext (A : RustAlloc) (a : BitVec 64) (c0 : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    chain3GAt A a (c0.apply (ChainField.ck i key)) =
      chain3VecAt A a c0.srk ∗ chain3VecAt A (a + 0x18#64) c0.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 := by
  unfold chain3GAt chainGRest ChainG.apply
  dsimp only

theorem chain3GAt_apply_ck_eq (a : BitVec 64) (c0 : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    chain3GAt A0 a (c0.apply (ChainField.ck i key)) =
      chain3VecAt A0 a c0.srk ∗ chain3VecAt A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A0 (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 :=
  chain3GAt_apply_ck_eq_ext A0 a c0 i key

/-! ## 2. Inner loop register invariant (`+0x368`) -/

/-- Register bundle preserved across the inner `ChainKey` loop (`+0x368`) of `[local#3]`. -/
def Chain3InnerLoopRegs (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    (s_init s : State) : Prop :=
  s.sp = sp0 - 0xf0#64 ∧
  s.readReg64 .x29 = sp0 - 0x50#64 ∧
  s.readReg64 .x19 = bufRef ∧
  s.readReg64 .x20 = a ∧
  s.readReg64 .x21 = BitVec.ofNat 64 outerTailLen ∧
  s.readReg64 .x22 = sp0 - 0xe8#64 ∧
  s.readReg64 .x23 = 1#64 ∧
  s.readReg64 .x24 = 104#64 ∧
  s.readReg64 .x25 = BitVec.ofNat 64 innerTailLen ∧
  s.readReg64 .x26 = s_init.readReg64 .x26 ∧
  s.readReg64 .x27 = s_init.readReg64 .x27 ∧
  s.readReg64 .x28 = s_init.readReg64 .x28

theorem Chain3InnerLoopRegs.of_calleeSaved {sp0 bufRef a : BitVec 64}
    {outerTailLen innerTailLen : Nat} {s_init s1 s2 : State}
    (h1 : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1)
    (hsp2 : s2.sp = sp0 - 0xf0#64) (hcs : CalleeSavedPreserved s1 s2) :
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s2 :=
  ⟨hsp2,
   hcs.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.1,
   hcs.1.trans h1.2.2.1,
   hcs.2.1.trans h1.2.2.2.1,
   hcs.2.2.1.trans h1.2.2.2.2.1,
   hcs.2.2.2.1.trans h1.2.2.2.2.2.1,
   hcs.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 3. Sub-step statements for `Chain3ChainKeyStmt` -/

/-- Segment 3a (`+0x0a8 → +0x368`): outer field-3 header, niche check `[a + 0x48] == noneCap`,
default `ChainKey` initialization, length `decode_varint`, and inner limit `x25 = |afterCk|`. -/
def Chain3Seg3aStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hck_lt : ck_body.length < 128)
    (_houter_le : outerTailLen ≤ afterCk.length)
    (_hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
    s0.status = .Running →
    s0.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    s0.readReg64 .x29 = sp0 - 0x50#64 →
    s0.readReg64 .x19 = bufRef →
    s0.readReg64 .x20 = a →
    s0.readReg64 .x21 = BitVec.ofNat 64 outerTailLen →
    s0.readReg64 .x22 = sp0 - 0xe8#64 →
    s0.readReg64 .x23 = 1#64 →
    s0.readReg64 .x24 = 104#64 →
    s0.readReg64 .x26 = s_init.readReg64 .x26 →
    s0.readReg64 .x27 = s_init.readReg64 .x27 →
    s0.readReg64 .x28 = s_init.readReg64 .x28 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          chain3VecAt A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s_init sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s_init sf ∗ R))

/-- Segment 3b (`+0x368 → +0x368`): inner field 1 (`index` varint stored to `[a + 0x60]`),
preserving `Chain3InnerLoopRegs`. -/
def Chain3Seg3bStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
    s0.status = .Running →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s_init sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s_init sf ∗ R))

/-- Segment 3c (`+0x368 → +0x368`): inner field 2 (`key` bytes merged into `a + 0x48` from empty
`chain3VecAt`), preserving `Chain3InnerLoopRegs`. -/
def Chain3Seg3cStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesW img ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hk_lt : k.length < 128)
    (_hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
    s0.status = .Running →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s_init sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        chain3VecAt A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtW img).onPanic x s_init sf ∗ R))

/-- Segment 3d (`+0x368 → +0x0a8`): inner-loop exit when remaining slice equals `afterCk`. -/
def Chain3Seg3dStmt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
    s0.status = .Running →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q Qp) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q Qp

abbrev Chain3CkLenStmt := Chain3Seg3aStmt
abbrev Chain3CkIdxStmt := Chain3Seg3bStmt
abbrev Chain3CkKeyStmt := Chain3Seg3cStmt
abbrev Chain3CkExitStmt := Chain3Seg3dStmt

/-! ## 4. Arbitrary-Allocator (`A : RustAlloc`) Sub-step Statements -/

def Chain3Seg3aStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hck_lt : ck_body.length < 128)
    (_houter_le : outerTailLen ≤ afterCk.length)
    (_hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
    s0.status = .Running →
    s0.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    s0.readReg64 .x29 = sp0 - 0x50#64 →
    s0.readReg64 .x19 = bufRef →
    s0.readReg64 .x20 = a →
    s0.readReg64 .x21 = BitVec.ofNat 64 outerTailLen →
    s0.readReg64 .x22 = sp0 - 0xe8#64 →
    s0.readReg64 .x23 = 1#64 →
    s0.readReg64 .x24 = 104#64 →
    s0.readReg64 .x26 = s_init.readReg64 .x26 →
    s0.readReg64 .x27 = s_init.readReg64 .x27 →
    s0.readReg64 .x28 = s_init.readReg64 .x28 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          chain3VecAt A (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s_init sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s_init sf ∗ R))

def Chain3Seg3bStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
    s0.status = .Running →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s_init sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s_init sf ∗ R))

def Chain3Seg3cStmtExt (A : RustAlloc) (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesWExt A img ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hk_lt : k.length < 128)
    (_hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
    s0.status = .Running →
    sp0 &&& 15#64 = 0#64 →
    img.FrozenLoaded s0 →
    s0.symtab = img.symtab →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x368#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s_init sf ∗ R))) →
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        chain3VecAt A (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s_init sf ∗ R))

theorem Chain3Seg3aStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3Seg3aStmtExt A0 img ext = Chain3Seg3aStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3Seg3aStmtExt Chain3Seg3aStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

theorem Chain3Seg3bStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3Seg3bStmtExt A0 img ext = Chain3Seg3bStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3Seg3bStmtExt Chain3Seg3bStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

theorem Chain3Seg3cStmtExt_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3Seg3cStmtExt A0 img ext = Chain3Seg3cStmt img ext := by
  have hp : A0.pool = emp := rfl
  unfold Chain3Seg3cStmtExt Chain3Seg3cStmt Chain3CalleesW
  simp only [hp, emp_sepConj, chainMerge3SpecAtWExt_A0]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
