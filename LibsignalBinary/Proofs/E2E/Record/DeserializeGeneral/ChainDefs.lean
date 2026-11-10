/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Base
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs

/-!
# Loop-Head Invariant and Step Definitions for General `message::merge<Chain>`

Defines the loop-head cut invariant `ChainLoopG` at `+0x120` and return postcondition `ChainRetG`
for `prost::encoding::message::merge::<Chain>` (`0x3974`) on an in-scope `ChainG`:
* Registers at `+0x120`: `x19 = bufRef`, `x20 = a`, `x24 = tail.length`, `w21 = 98`, `w22 = 97`,
  `x25 = sp + 8`, `w26 = 1`, `x29 = sp + 0xa0`, `sp = s0.sp - 0x100`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed

noncomputable abbrev chainPCAt (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (off : BitVec 64) (abs : String → Option (State → State) := fun _ => none) : BitVec 64 :=
  (tripleRatchetProgAt img.base C ctl abs).fnAddr chainMergeName + off

noncomputable abbrev chainPC (C : Crypto) (ctl : BitVec 64)
    (off : BitVec 64) : BitVec 64 :=
  chainPCAt sessionImg0 C ctl off

abbrev ChainStepGAt (img : Obj.Image) (C : Crypto) (ctl : BitVec 64) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop)
    (abs : String → Option (State → State) := fun _ => none) : Prop :=
  SegStepG (tripleRatchetProgAt img.base C ctl abs) (chainMergeGenSpecAt img) x R s0 s Q

abbrev ChainStepG (C : Crypto) (ctl : BitVec 64) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop)
    (abs : String → Option (State → State) := fun _ => none) : Prop :=
  ChainStepGAt sessionImg0 C ctl x R s0 s Q abs

/-- Loop-head invariant at `+0x120` after decoding `k` fields of `x.c.fields` at `img`: `prostChainGAt`
holds `chainGAfter x.c k` and the slice cursor points to the remaining field bytes followed by `tail`. -/
def ChainLoopGAt (img : Obj.Image) (C : Crypto) (ctl : BitVec 64) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (abs : String → Option (State → State) := fun _ => none) : Prop :=
  s.pc = chainPCAt img C ctl 0x120#64 abs ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 32 ∧
    (s.mem ⊨ prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

def ChainLoopG (C : Crypto) (ctl : BitVec 64) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chainPC C ctl 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = sessionImg0.symtab ∧ sessionImg0.FrozenLoaded s ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 32 ∧
    (s.mem ⊨ prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

def ChainRetGAt (img : Obj.Image) (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMergeGenSpecAt img).post x s0 sf ∗ R)

def ChainRetG (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  ChainRetGAt sessionImg0 x R s0 sf

theorem chainField_tag_cases (fl : ChainField) :
    (fl.tag = 1 ∨ fl.tag = 2) ∨ fl.tag = 3 ∨ fl.tag = 4 := by
  cases fl <;> simp [ChainField.tag]

theorem len_cons_sub_one_seedChain (b0 : BitVec 8) (bs1 : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs1).length - 1#64 = BitVec.ofNat 64 bs1.length := by
  simp only [List.length_cons]
  bv_omega

theorem ule_ofNat_of_gt_false_seedChain {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 k) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ult_ofNat_of_gt_true_seedChain {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 k).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem pbBytes_lt128_eq_seedChain (tag : Nat) (_htag : tag < 16)
    (b : List (BitVec 8)) (_hb : b.length < 128) :
    pbBytes tag b = BitVec.ofNat 8 (tag * 8 + 2) :: BitVec.ofNat 8 b.length :: b :=
  rfl

theorem pbBytes_pointsTo_combine_seedChain (tag : Nat) (htag : tag < 16)
    (ptr : BitVec 64) (b : List (BitVec 8)) (hb : b.length < 128) :
    (ptr ↦₈ BitVec.ofNat 8 (tag * 8 + 2)) ∗ ((ptr + 1#64) ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) =
      (ptr ↦ₛ pbBytes tag b) := by
  rw [pbBytes_lt128_eq_seedChain tag htag b hb, pointsToBytes_cons]
  rfl

theorem pbBytes_ptr_advance_seedChain (tag : Nat) (htag : tag < 16)
    (ptr : BitVec 64) (b : List (BitVec 8)) (hb : b.length < 128) :
    ptr + 1#64 + BitVec.ofNat 64 (b.length + 1) =
      ptr + BitVec.ofNat 64 (pbBytes tag b).length := by
  rw [pbBytes_lt128_eq_seedChain tag htag b hb]
  simp only [List.length_cons]
  bv_omega

end CryptoVerification.E2E.Record.DeserializeGeneral
