/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollaries
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import all Init.Data.String.Defs

/-!
# Bad-KEM Error Ownership for `Pqxdh::accept` and `initialize_bob_session`

Relocatable `[LibsignalPlacement]` / `[LibsignalFullPlacement]` owned-error contracts for
`Pqxdh::accept` (Block `79`) and `initialize_bob_session` (Block `75`) when the Kyber ciphertext
slice fails the version-4 tag/length check (`pkVecTag? 8 1568 ctBytes = none`), retaining either
the 28-byte heap `String` buffer on `InvalidMessage` (`speWord 24`) or a plain `PlainSpeTag`
witness (`7`, `10`, `31`, `34`) with no leaked heap allocations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsMemcpySym
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding Bytes PqxdhHookContracts
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhVecAppendElementsFastSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Initiator.bv_sub_sub_lit Initiator.bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc

/-! ## 1. Owned Error Payload Definitions, Field Layouts, and Relocatable Bad-KEM Specs -/

def plainSpeTags : List Nat :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 20, 21, 23, 28, 29, 30, 31, 32, 33, 34]

def PlainSpeTag (i : Nat) : Prop := i ∈ plainSpeTags

instance (i : Nat) : Decidable (PlainSpeTag i) := inferInstanceAs (Decidable (i ∈ plainSpeTags))

def strSpeTags : List Nat := [0, 1, 12, 18, 22, 24, 25, 27]

def StrSpeTag (i : Nat) : Prop := i ∈ strSpeTags

instance (i : Nat) : Decidable (StrSpeTag i) := inferInstanceAs (Decidable (i ∈ strSpeTags))

def pkVecTag? (tag : BitVec 8) (n : Nat) (l : List (BitVec 8)) :
    Option (List.Vector (BitVec 8) n) :=
  match l with
  | t :: rest => if h : t = tag ∧ rest.length = n then some ⟨rest, h.2⟩ else none
  | [] => none

def pkVec? (n : Nat) (l : List (BitVec 8)) : Option (List.Vector (BitVec 8) n) :=
  if h : l.length = n then some ⟨l, h⟩ else none

def pqxdhBadKemErrPayloadAt (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) : SepProp :=
  ∃∗ isStr : Bool,
    if isStr then
      ⌜errTag = speWord 24⌝ ∗
      ∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = w4 ∧ bs.length ≤ w2.toNat ∧ w2.toNat < 2 ^ 63 ∧ w3 ≠ 0#64⌝ ∗
        (if w2 = 0#64 then emp
         else A.live w3 w2.toNat 1 ∗ (w3 ↦ₛ bs) ∗
           memRegion (w3 + BitVec.ofNat 64 bs.length) (w2.toNat - bs.length))
    else
      ∃∗ i : Nat, ⌜PlainSpeTag i ∧ errTag = speWord i⌝

def pqxdhAcceptBadKemErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗
  memRegion (outPtr + 4#64) 4 ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ -3#64 ∧ errTag ≠ -2#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 48

def initBobBadKemErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ -1#64) ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ -3#64 ∧ errTag ≠ -2#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 288

def pqxdhAcceptBadKemFieldsAt (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8)) : SepProp :=
  ((basePtr + 32#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
  ((basePtr + 96#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
  ((basePtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
  ((basePtr + 160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
  ((basePtr + 208#64) ↦₆₄ pqskPtr) ∗
  ((basePtr + 216#64) ↦₆₄ 3168#64) ∗
  ((basePtr + 224#64) ↦₆₄ ctSlicePtr) ∗
  ((basePtr + 232#64) ↦₈ (if (match inp.opkBSk? with
    | some _ => true | none => false) = true then 1#8 else 0#8)) ∗
  (match inp.opkBSk? with
   | some opkSk => (basePtr + 265#64) ↦ₛ bytesToBv8 opkSk
   | none => .emp) ∗
  (pqskPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
  ((pqskPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
  (ctSlicePtr ↦₆₄ ctBufPtr) ∗
  ((ctSlicePtr + 8#64) ↦₆₄ BitVec.ofNat 64 ctBytes.length) ∗
  (ctBufPtr ↦ₛ ctBytes)

def bobParamsBadKemFieldsAt (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr : BitVec 64)
    (inp : AcceptKeysInput) (ctBytes : List (BitVec 8))
    (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8) : SepProp :=
  (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
  pqxdhAcceptBadKemFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ctBytes ∗
  ((argPtr + 297#64) ↦₈ sameAccountByte) ∗
  (ratchetKeyPairPtr ↦ₛ bytesToBv8 spkBPk) ∗
  ((ratchetKeyPairPtr + 32#64) ↦ₛ bytesToBv8 inp.spkBSk)

structure AcceptBadKemGhost where
  inp : AcceptKeysInput
  ctBytes : List (BitVec 8)
  argPtr : BitVec 64
  pqskPtr : BitVec 64
  ctSlicePtr : BitVec 64
  ctBufPtr : BitVec 64
  outPtr : BitVec 64

structure InitBobBadKemGhost where
  inp : AcceptKeysInput
  ctBytes : List (BitVec 8)
  ikBPk : Bytes
  spkBPk : Bytes
  sameAccountByte : BitVec 8
  argPtr : BitVec 64
  pqskPtr : BitVec 64
  ctSlicePtr : BitVec 64
  ctBufPtr : BitVec 64
  ratchetKeyPairPtr : BitVec 64
  outPtr : BitVec 64

/-- Inner specification of `Pqxdh::accept` (Block `79`) when
`pkVecTag? 8 1568 g.ctBytes = none`. -/
def pqxdhAcceptBadKemErrOwnedInnerPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec AcceptBadKemGhost where
  pre := fun (g : AcceptBadKemGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ctBytes.length < 2 ^ 63 ∧
      pkVecTag? 8#8 1568 g.ctBytes = none⌝ ∗
    pqxdhAcceptBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp g.ctBytes ∗
    memRegion g.outPtr 104 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp pqxdhEntryStack ∗
    A.pool
  post := fun (g : AcceptBadKemGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    pqxdhAcceptBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp g.ctBytes ∗
    (pqxdhAcceptBadKemErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp pqxdhEntryStack ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

def pqxdhAcceptBadKemErrOwnedPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec AcceptBadKemGhost :=
  withLsCodeRoLoaded lsmpl (pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A)

def pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec AcceptBadKemGhost :=
  withLsFrozen lsmpl (pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A)

/-- Inner specification of `initialize_bob_session` (Block `75`) when
`pkVecTag? 8 1568 g.ctBytes = none`. -/
def initializeBobSessionBadKemErrOwnedInnerPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec InitBobBadKemGhost where
  pre := fun (g : InitBobBadKemGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      g.ctBytes.length < 2 ^ 63 ∧
      pkVecTag? 8#8 1568 g.ctBytes = none⌝ ∗
    bobParamsBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ctBytes g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool
  post := fun (g : InitBobBadKemGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ctBytes g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobBadKemErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + pqxdhEntryStack) ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

def initializeBobSessionBadKemErrOwnedPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec InitBobBadKemGhost :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A)

def initializeBobSessionBadKemErrOwnedFrozenPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec InitBobBadKemGhost :=
  withLsFrozen lsmpl (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A)

/-! ## 2. Merge & Case Helpers -/

private theorem outPtr_tail64_to_spe_tail_placed (outPtr : BitVec 64) (b40 : BitVec 8) :
    ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗ memRegion (outPtr + 56#64) 48 := by
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]
    exact Entails.sepExists_right b40 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hb40) ?_
  have hm64 :
      memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63 =
        (∃∗ w5 : BitVec 64, (outPtr + 40#64) ↦₆₄ w5) ∗
        (∃∗ w6 : BitVec 64, (outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 48 := by
    rw [← ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 1) (k := 63)
          (b' := outPtr + 41#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 8) (k := 56)
          (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 48)
          (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (outPtr + 40#64),
        ProofLib.memRegion_eight (outPtr + 48#64)]
  rw [hm64]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))

private theorem outPtr_badKem_err104_owned_merge_placed (A : RustAlloc)
    (outPtr errTag w2 w3 w4 : BitVec 64) (b40 : BitVec 8)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ -3#64 ∧ errTag ≠ -2#64) :
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptBadKemErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))))))) =
      (outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗
        ((((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) ∗
          (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
            ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
            pqxdhBadKemErrPayloadAt A errTag w2 w3 w4))) := by ac_rfl
  rw [hrearr]
  unfold pqxdhAcceptBadKemErrOwnedAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (outPtr_tail64_to_spe_tail_placed outPtr b40)) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem pqxdhBadKemErrPayloadAt_plain_intro_placed (A : RustAlloc) (i : Nat)
    (hi : PlainSpeTag i) (w2 w3 w4 : BitVec 64) :
    emp ⊢ pqxdhBadKemErrPayloadAt A (speWord i) w2 w3 w4 := by
  unfold pqxdhBadKemErrPayloadAt
  refine Entails.sepExists_right false ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Entails.sepExists_right i ?_
  rw [← sepConj_emp ⌜PlainSpeTag i ∧ speWord i = speWord i⌝,
      pure_sepConj_of_true ⟨hi, rfl⟩ emp]
  exact Entails.refl _

private theorem outPtr_badKem_err104_plain_merge_placed (A : RustAlloc) (i : Nat)
    (hi : PlainSpeTag i)
    (hw1 : speWord i ≠ pollReadyOkWord ∧ speWord i ≠ -3#64 ∧ speWord i ≠ -2#64)
    (outPtr w2 w3 w4 : BitVec 64) (b40 : BitVec 8) :
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ speWord i) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptBadKemErrOwnedAt A outPtr := by
  rw [← emp_sepConj ((outPtr ↦₃₂ 1#32) ∗ _)]
  exact Entails.trans
    (sepConj_mono_left (pqxdhBadKemErrPayloadAt_plain_intro_placed A i hi w2 w3 w4))
    (outPtr_badKem_err104_owned_merge_placed A outPtr (speWord i) w2 w3 w4 b40 hw1)

private theorem err28_badKem_payload_intro_placed (A : RustAlloc) (ptr u2 u3 : BitVec 64)
    (hptr : ptr ≠ 0#64) :
    memRegion ptr 12 ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) ∗ A.live ptr 28 1 ⊢
      pqxdhBadKemErrPayloadAt A (speWord 24) 28#64 ptr 28#64 := by
  have hm12 : memRegion ptr 12 =
      (∃∗ q0 : BitVec 64, ptr ↦₆₄ q0) ∗ (∃∗ q1 : BitVec 32, (ptr + 8#64) ↦₃₂ q1) := by
    rw [ProofLib.memRegion_split' (b := ptr) (n := 8) (k := 4)
          (b' := ptr + 8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight ptr, memRegion_four (ptr + 8#64)]
  rw [hm12, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun q0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun q1 => ?_
  unfold pqxdhBadKemErrPayloadAt
  refine Entails.sepExists_right true ?_
  simp only [↓reduceIte]
  rw [pure_sepConj_of_true trivial]
  let bs : List (BitVec 8) := unpack64 q0 ++ (unpack32 q1 ++ (unpack64 u2 ++ unpack64 u3))
  refine Entails.sepExists_right bs ?_
  have hbs_len : bs.length = 28 := by simp [bs, unpack64_length, unpack32_length]
  have hpure :
      BitVec.ofNat 64 bs.length = 28#64 ∧
      bs.length ≤ (28#64 : BitVec 64).toNat ∧
      (28#64 : BitVec 64).toNat < 2 ^ 63 ∧
      ptr ≠ 0#64 := by
    rw [hbs_len]; exact ⟨rfl, by decide, by decide, hptr⟩
  rw [pure_sepConj_of_true hpure]
  have h28_ne : (28#64 : BitVec 64) ≠ 0#64 := by decide
  simp only [h28_ne, ↓reduceIte, hbs_len]
  have h28_nat : (28#64 : BitVec 64).toNat = 28 := rfl
  rw [h28_nat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  have hpts :
      (ptr ↦ₛ bs) =
        (ptr ↦₆₄ q0) ∗ ((ptr + 8#64) ↦₃₂ q1) ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) := by
    dsimp only [bs]
    rw [pointsToBytes_append, unpack64_length, pointsToBytes_append, unpack32_length,
        pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hpts]
  exact Entails.of_eq (by ac_rfl)

private theorem bv64_ofNat_ne_zero_of_pos_placed {n : Nat} (hpos : 0 < n) (hbd : n < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
  change n = 0 at hnat
  omega

private theorem bv64_ofNat_ne_1569_placed {n : Nat} (hne : n ≠ 1569) (hbd : n < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 1569#64 := by
  intro h
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
  change n = 1569 at hnat
  omega

theorem pkVecTag?_8_1568_eq_none_cases {ctBytes : List (BitVec 8)}
    (h : pkVecTag? 8#8 1568 ctBytes = none) :
    ctBytes = [] ∨
    (∃ b0 rest, ctBytes = b0 :: rest ∧ b0 ≠ 8#8) ∨
    (∃ rest, ctBytes = 8#8 :: rest ∧ (8#8 :: rest).length ≠ 1569) := by
  cases ctBytes with
  | nil => exact Or.inl rfl
  | cons b0 rest =>
    by_cases hb0 : b0 = 8#8
    · subst hb0
      refine Or.inr (Or.inr ⟨rest, rfl, ?_⟩)
      intro hlen
      have hrest : rest.length = 1568 := by simpa using hlen
      simp [pkVecTag?, hrest] at h
    · exact Or.inr (Or.inl ⟨b0, rest, rfl, hb0⟩)

private theorem cond_ne_tag8_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.zeroExtend 64 tag) 8#64) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState64]; bv_bits

private theorem cond_ne_tag8_concat_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState64 (0#56 ++ tag) 8#64) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState64]; bv_bits

private theorem cond_ne_tag8_32_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState32 (BitVec.zeroExtend 32 tag) 8#32) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState32]; bv_bits

private theorem cond_ne_tag8_32_concat_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState32 (0#24 ++ tag) 8#32) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState32]; bv_bits

private theorem cond_ne_ctLen1569_placed {ctLen : BitVec 64} (hlen : ctLen ≠ 1569#64) :
    ConditionHolds CondCode.NE (subsPState64 ctLen 1569#64) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState64]; bv_arith

/-! ## 3. Rejecting `Pqxdh::accept` Proof on Bad-KEM (Block `79`) -/

local macro "badkem_ct_exit_placed" s0:ident A:ident ctBufPtr:ident
    hbadKem:ident hct_bd:ident
    h_canon:ident h_agree:ident h_vec_append:ident hshim:ident
    halloc:ident hdealloc:ident hmemcpy:ident hpan_rawvec:ident : tactic =>
  `(tactic| (
    rcases pkVecTag?_8_1568_eq_none_cases $hbadKem with
      hct_eq | ⟨b0, rest, hct_eq, hb0⟩ | ⟨rest, hct_eq, hlen_ne⟩
    · subst hct_eq
      wp_simp_pre_fast [List.length_nil]
      wp_steps; wp_call $hdealloc (_, 192, 1); wp_steps
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed $A 7 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      clear $h_canon $h_agree $h_vec_append $hshim $halloc $hdealloc $hmemcpy $hpan_rawvec
      simp only [List.length_nil, sepConj_assoc, *]
      wp_done
    · subst hct_eq
      have hne0 : BitVec.ofNat 64 (b0 :: rest).length ≠ 0#64 :=
        bv64_ofNat_ne_zero_of_pos_placed (by simp) $hct_bd
      have hbeq0 : (BitVec.ofNat 64 (b0 :: rest).length == 0#64) = false := beq_false_of_ne hne0
      have hc_tag64 := cond_ne_tag8_placed hb0
      have hc_tag64' := cond_ne_tag8_concat_placed hb0
      have hc_tag32 := cond_ne_tag8_32_placed hb0
      have hc_tag32' := cond_ne_tag8_32_concat_placed hb0
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr b0 rest)) (by sep_focus) ?_
      wp_steps; wp_call $hdealloc (_, 192, 1); wp_steps
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr b0 rest).symm)
        (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed $A 31 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      clear $h_canon $h_agree $h_vec_append $hshim $halloc $hdealloc $hmemcpy $hpan_rawvec
      simp only [sepConj_assoc, *]
      wp_done
    · subst hct_eq
      have hne0 : BitVec.ofNat 64 (8#8 :: rest).length ≠ 0#64 :=
        bv64_ofNat_ne_zero_of_pos_placed (by simp) $hct_bd
      have hbeq0 : (BitVec.ofNat 64 (8#8 :: rest).length == 0#64) = false := beq_false_of_ne hne0
      have hne1569 : BitVec.ofNat 64 (8#8 :: rest).length ≠ 1569#64 :=
        bv64_ofNat_ne_1569_placed hlen_ne $hct_bd
      have hc_len := cond_ne_ctLen1569_placed hne1569
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr 8#8 rest)) (by sep_focus) ?_
      wp_steps; wp_call $hdealloc (_, 192, 1); wp_steps
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr 8#8 rest).symm)
        (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed $A 34 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      clear $h_canon $h_agree $h_vec_append $hshim $halloc $hdealloc $hmemcpy $hpan_rawvec
      simp only [sepConj_assoc, *]
      wp_done))

set_option maxHeartbeats 3000000 in
/-- Owned-error rejecting contract for `Pqxdh::accept` (Block `79`) when
`pkVecTag? 8 1568 g.ctBytes = none`. -/
theorem pqxdhAccept_badKem_err_owned_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A) := by
  unfold pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) (by decide) ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := hook_ok_79_of_mem h_alloc (by decide)
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  have hpan_rawvec :
      (lsProg_79 H).externAt? (lsρ acceptHandleRawVecErrorSym) = some Rust.panicked :=
    (externAt_79_of_mem (by decide)).trans h_pan_rawvec
  clear h_shim h_alloc h_dealloc h_memcpy h_pan_rawvec
  unfold withLsFrozen withRoSlice pqxdhAcceptBadKemErrOwnedInnerPlacedSpec rustPanicOnOomPlaced
  wpp_init x s0
  rcases x with ⟨inp, ctBytes, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hct_bd : ctBytes.length < 2 ^ 63 := ‹ctBytes.length < 2 ^ 63›
  have hbadKem : pkVecTag? 8#8 1568 ctBytes = none := ‹pkVecTag? 8#8 1568 ctBytes = none›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    _hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_; sep_elim_exists'
  refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_; sep_elim_exists'
  refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_; sep_elim_exists'
  unfold pqxdhAcceptBadKemFieldsAt
  refine SepWPp.of_sepWP_lsfull hF0 (mid := lsmpl.base 202) ?_; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF0_1; try simp only [arm64_norm] at hF0_1
  refine SepWPp.of_sepWP_lsfull hF0_1 (mid := (blkPl_79).base + 52#64) ?_
  wp_call (subroutine_ok_withMemEq_of_withCodeLoaded
    (spec := ecPubKeyIsCanonicalCallSpec P) h_canon hF0_1.code) ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *; rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := (blkPl_79).base + 216#64) ?_
    wp_steps; wp_call hshim (); wp_steps; have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (28, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc0 htr0 => ?_) (fun halloc0 halign0 htr0 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
      sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
      sep_elim_exists'; refine SepWPp.fold
        (Entails.of_eq (rodata_incoming_split1 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393"))) (by sep_focus) ?_
      apply SepWPp.of_sepWP_ret; wp_simp_pre_fast [Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps; refine SepWP.fold
        (Entails.of_eq (rodata_incoming_1_to_2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393"))) (by sep_focus) ?_
      wp_steps; refine SepWP.fold
        (Entails.of_eq (rodata_incoming_split2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")).symm) (by sep_focus) ?_
      refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_; sep_elim_exists'; wp_steps
      refine SepWP.fold (err28_badKem_payload_intro_placed A _ _ _ halloc0) (by sep_focus) ?_
      refine SepWP.fold (outPtr_badKem_err104_owned_merge_placed A (s0.readReg64 (.gpr 8#5))
        (speWord 24) 28#64 _ 28#64 _ (by decide)) (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec
      simp only [sepConj_assoc, *]; wp_done
  · have hsp_align_eq : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
    have hsp_orr1 : (s0.sp - 4912#64) ||| 1#64 = s0.sp - 4911#64 := sp_sub4912_orr_one hsp_align_eq
    have hpqSk_drop_len : ((bytesToBv8 inp.pqspkBSk).drop 1).length = 3167 := by simp [bytesToBv8, hpqSk]
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    simp only [hcanon_ec, ↓reduceIte] at *; rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps; wp_call hshim (); wp_steps; have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc192 htr192 => ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ acceptHandleRawVecErrorSym) ?_; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_lhs) (by convert hpan_rawvec using 2; wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_; wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag_placed hWF h_agree hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs)
        hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hvregs1⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
        sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
        refine SepWP.fold (outPtr_badKem_err104_plain_merge_placed A 10 (by decide) (by decide)
          (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec
        simp only [sepConj_assoc, *]; wp_done
      · have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
        have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by simp [bytesToBv8, hdh1_len]
        have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by simp [F_X25519, hdh1_len]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hvregs1⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_; wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩; wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _) (by sep_focus) ?_
        wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519
          (P.x25519 inp.spkBSk inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag_placed hWF h_agree hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 304#64)
          (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
          sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
          wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
          refine SepWP.fold (outPtr_badKem_err104_plain_merge_placed A 10 (by decide) (by decide)
            (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec
          simp only [sepConj_assoc, *]; wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by simp [bytesToBv8, hdh2_len]
          have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 :=
            by simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29 hvregs2
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_; wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩; wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _) (by sep_focus) ?_
          wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
            (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
            (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag_placed hWF h_agree hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 404#64)
            (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29 hvregs3
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
            sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
            wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
            refine SepWP.fold (outPtr_badKem_err104_plain_merge_placed A 10 (by decide) (by decide)
              (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
            clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec
            simp only [sepConj_assoc, *]; wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by simp [bytesToBv8, hdh3_len]
            have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
              P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
              by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29 hvregs3
            cases hopk_eq : inp.opkBSk? with
            | none =>
              simp only [Bool.false_eq_true, ↓reduceIte, emp_sepConj]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                (by sep_focus) ?_
              sep_elim_exists'
              apply SepWPp.of_sepWP_ret
              wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩; wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
                (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk)
                (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh3_ptr 32#64 0#64) (by sep_focus) ?_
              refine SepWP.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
              badkem_ct_exit_placed s0 A ctBufPtr hbadKem hct_bd
                h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec
            | some opkSk =>
              have hopkSk : opkSk.length = 32 := _hopk_sz opkSk hopk_eq
              simp only [↓reduceIte]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_lsfull hF8 (mid := lsmpl.base 207) ?_; wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩; wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps; refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64) (by sep_focus) ?_
              refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
                (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk)
                (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
              refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF8_1; try simp only [arm64_norm] at hF8_1
              refine SepWPp_call_hag_placed hWF h_agree hF8_1 (s0.readReg64 (.gpr 0#5) + 265#64) opkSk
                (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
                (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 720#64)
                (by wp_norm_lhs) (by wp_norm_lhs)
                ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk⟩
                (by sep_focus) (allowPanic_hag_placed (by wp_norm_lhs))
                (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
                (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hF8_2 => ?_)
              · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28 hcs4_29 hvregs4
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_; sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
                apply SepWPp.of_sepWP_ret; wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
                refine SepWP.fold (outPtr_badKem_err104_plain_merge_placed A 10 (by decide) (by decide)
                  (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
                clear h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec
                simp only [sepConj_assoc, *]; wp_done
              · have hdh4_len : (P.x25519 opkSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
                have hdh4_bv_len : (bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk)).length = 32 := by simp [bytesToBv8, hdh4_len]
                have hpfx4_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk ++
                  P.x25519 opkSk inp.hdr.ekAPk).length = 160 := by
                  simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, hdh4_len]
                dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29, hvregs4⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28 hcs4_29 hvregs4
                refine SepWPp.fold (Entails.of_eq (calc_to_vecAppend_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.of_sepWP_lsfull hF8_2 (mid := lsmpl.base 55) ?_; wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF8_3; try simp only [arm64_norm] at hF8_3
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_
                sep_elim_exists'
                apply SepWPp.of_sepWP_ret
                wp_call (subroutine_ok_withMemEq_of_withCodeLoaded
                  (spec := pqxdhVecAppendElementsFastSpec) h_vec_append hF8_3.code)
                  (s0.sp - 4936#64, _, dh4_ptr, bytesToBv8 (P.x25519 opkSk inp.hdr.ekAPk))
                refine SepWP.fold (vecAppend_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                wp_steps
                refine SepWP.fold (hdh4_bv_len ▸ pointsToBytes_entails_memRegion dh4_ptr _)
                  (by sep_focus) ?_; wp_call hdealloc (dh4_ptr, 32, 1)
                refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
                  (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                    P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk)
                  (P.x25519 opkSk inp.hdr.ekAPk) 128
                  (by simp only [bytesToBv8, List.length_map, hpfx3_len]))) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh4_ptr 32#64 0#64) (by sep_focus) ?_
                refine SepWP.fold (vec_ok_160_merge _ hpfx4_len) (by sep_focus) ?_
                badkem_ct_exit_placed s0 A ctBufPtr hbadKem hct_bd
                  h_canon h_agree h_vec_append hshim halloc hdealloc hmemcpy hpan_rawvec

theorem pqxdhAccept_badKem_err_owned_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : Primitives} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec P A)))
    (h_vec_append : subroutine_ok (lsProg_79 H) (lsmpl.base 55)
      (libsignalSessionLib.withCodeLoaded lsmpl pqxdhVecAppendElementsFastSpec))
    (h_shim : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H Keys.lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustDeallocSpec A))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_pan_rawvec : H acceptHandleRawVecErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A) :=
  ls_subroutine_ok_withLsFrozen_of_block
    (pqxdhAccept_badKem_err_owned_placed_ok hWF h_canon h_agree h_vec_append
      h_shim h_alloc h_dealloc h_memcpy h_pan_rawvec)

theorem pqxdhAccept_badKem_err_owned_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A) :=
  pqxdhAccept_badKem_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (CryptoVerification.E2E.Pqxdh.Shared.vecAppendElements_fast_placed_ok_cl h_memcpy)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.handleError

private abbrev withBobErrMemInv {α : Type} (Φ : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜Φ s0.mem⌝ }

private theorem call_bobErrMemInv_frame {α : Type} {prog : Program} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hcall : subroutine_ok prog entry (withBobErrMemInv Φ spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Φ sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withBobErrMemInv]) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withBobErrMemInv Φ spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withBobErrMemInv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hΦ, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right
  · dsimp only [withBobErrMemInv] at hoom_post
    rw [hoom sm] at hoom_post
    exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withBobErrMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hkf s.mem sm.mem hΦ hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withBobErrMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · dsimp only [withBobErrMemInv] at hpost
    exact (hexit sm code _ hex hpost).elim

theorem initBobBadKemErrOwnedAt_merge (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ -3#64 ∧ errTag ≠ -2#64) :
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ -1#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    initBobBadKemErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₆₄ -1#64) ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
            memRegion (outPtr + 56#64) 288))))))) =
      (outPtr ↦₆₄ -1#64) ∗
      (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (outPtr + 56#64) 288) := by ac_rfl
  rw [hrearr]
  unfold initBobBadKemErrOwnedAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem entails_sepConj_anyHeap (P : SepProp) : P ⊢ P ∗ anyHeap := by
  have hemp : P = P ∗ emp := (sepConj_emp P).symm
  conv => lhs; rw [hemp]
  exact sepConj_mono_right (entails_anyHeap emp)

theorem words2_at20_entails_memRegion16 (p w4 w5 : BitVec 64) :
    ((p + 0x20#64) ↦₆₄ w4) ∗ ((p + 0x28#64) ↦₆₄ w5) ⊢ memRegion (p + 0x20#64) 16 := by
  rw [ProofLib.memRegion_split' (b := p + 0x20#64) (n := 8) (k := 8)
        (b' := p + 0x28#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)

theorem words5_at08_entails_memRegion40 (p w1 w2 w3 w4 w5 : BitVec 64) :
    ((p + 0x08#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗
    ((p + 0x20#64) ↦₆₄ w4) ∗ ((p + 0x28#64) ↦₆₄ w5) ⊢ memRegion (p + 0x08#64) 40 := by
  rw [ProofLib.memRegion_split' (b := p + 0x08#64) (n := 8) (k := 32)
        (b' := p + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x10#64) (n := 8) (k := 24)
        (b' := p + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x18#64) (n := 8) (k := 16)
        (b' := p + 0x20#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (words2_at20_entails_memRegion16 p w4 w5)))

theorem words3_heap_entails_exists_vecU8 (A : RustAlloc) (p cap ptr len : BitVec 64) :
    (((p + 0x08#64) ↦₆₄ cap) ∗ ((p + 0x10#64) ↦₆₄ ptr) ∗ ((p + 0x18#64) ↦₆₄ len)) ∗
    (∃∗ bs : List (BitVec 8),
      ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ⊢
    ∃∗ bs : List (BitVec 8), RustHeap.vecU8 A (p + 0x08#64) bs := by
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  have hpull :
      (((p + 0x08#64) ↦₆₄ cap) ∗ ((p + 0x10#64) ↦₆₄ ptr) ∗ ((p + 0x18#64) ↦₆₄ len)) ∗
      (⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
      ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((p + 0x08#64) ↦₆₄ cap) ∗ ((p + 0x10#64) ↦₆₄ ptr) ∗ ((p + 0x18#64) ↦₆₄ len) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
    ac_rfl
  rw [hpull]
  refine Entails.pure_left fun ⟨hlen, hle, hlt, hnz⟩ => ?_
  subst hlen
  refine Entails.sepExists_right bs ?_
  unfold RustHeap.vecU8 vecU8At vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have h10 : (p + 0x08#64) + 8#64 = p + 0x10#64 := by bv_omega
  have h18 : (p + 0x08#64) + 16#64 = p + 0x18#64 := by bv_omega
  rw [h10, h18]
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hle, hlt, hnz⟩⟩
  rw [hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem plainSpeWords_entails_spePlain (out : BitVec 64)
    (i : Nat) (w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt out (speWord i) w1 w2 w3 w4 w5 ⊢
      (out ↦₆₄ speWord i) ∗ memRegion (out + 8#64) 40 := by
  unfold speWordsAt
  exact sepConj_mono_right (words5_at08_entails_memRegion40 out w1 w2 w3 w4 w5)

theorem strSpeWords_entails_speWithString (A : RustAlloc) (out : BitVec 64)
    (i : Nat) (cap ptr len w4 w5 : BitVec 64)
    (Extra : SepProp) :
    speWordsAt out (speWord i) cap ptr len w4 w5 ∗
    ((∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗ Extra) ⊢
    ((out ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), RustHeap.vecU8 A (out + 8#64) bs) ∗
      memRegion (out + 0x20#64) 16) ∗ anyHeap := by
  have hreord :
      speWordsAt out (speWord i) cap ptr len w4 w5 ∗
      ((∃∗ bs : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
            else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗ Extra) =
      ((out ↦₆₄ speWord i) ∗
        ((((out + 0x08#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗ ((out + 0x18#64) ↦₆₄ len)) ∗
          (∃∗ bs : List (BitVec 8),
            ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (if cap = 0 then emp
             else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
               memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))) ∗
        (((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5))) ∗ Extra := by
    unfold speWordsAt
    ac_rfl
  rw [hreord]
  refine sepConj_mono ?_ (entails_anyHeap Extra)
  exact sepConj_mono_right
    (sepConj_mono (words3_heap_entails_exists_vecU8 A out cap ptr len)
      (words2_at20_entails_memRegion16 out w4 w5))

set_option maxHeartbeats 1200000 in
/-- Memory-invariant owned-error rejecting contract for `initialize_bob_session` (Block `75`)
on Bad-KEM. -/
theorem initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} {Φ : Memory → Prop}
    (hkf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      ({ pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A with
          pre := fun x s0 => (pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A).pre x s0 ∗ ⌜Φ s0.mem⌝ })) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      ({ initializeBobSessionBadKemErrOwnedInnerPlacedSpec A with
          pre := fun x s0 =>
            (initializeBobSessionBadKemErrOwnedInnerPlacedSpec A).pre x s0 ∗ ⌜Φ s0.mem⌝ }) := by
  unfold initializeBobSessionBadKemErrOwnedInnerPlacedSpec bobParamsBadKemFieldsAt rustPanicOnOomPlaced
  wpp_init x s0
  obtain ⟨inp, ctBytes, ikBPk, spkBPk, sameAccountByte, argPtr, pqskPtr, ctSlicePtr, ctBufPtr,
    ratchetKeyPairPtr, outPtr⟩ := x
  dsimp only at *
  have hΦ0 : Φ s0.mem := by assumption
  subst argPtr ratchetKeyPairPtr outPtr
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.seq_frozen (Φ := Φ) hkf hΦ0 (mid := lsmpl.base 79)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hΦ1
  refine call_bobErrMemInv_frame (spec := pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A) hkf hΦ1 h_accept
    (ret_pc := (blkPl_75).base + 56#64)
    (x := ⟨inp, ctBytes, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    rfl
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 := s0)
          (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 _hΦ2 => ?_)
  dsimp only [pqxdhAcceptBadKemErrOwnedInnerPlacedSpec, pqxdhAcceptBadKemErrOwnedAt] at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28
       hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      arm64_norm, sepConj_assoc]
  refine SepWPp.exists_elim fun errTag => ?_
  refine SepWPp.exists_elim fun w2 => ?_
  refine SepWPp.exists_elim fun w3 => ?_
  refine SepWPp.exists_elim fun w4 => ?_
  refine SepWPp.exists_elim fun w5 => ?_
  refine SepWPp.exists_elim fun w6 => ?_
  refine SepWPp.pure_left fun ⟨htr1, herrTag⟩ => ?_
  apply SepWPp.of_sepWP_ret
  rw [memRegion_280_none_split s0.sp,
      memRegion_344_none_split (s0.readReg64 (.gpr 8#5))]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold
    (initBobBadKemErrOwnedAt_merge A (s0.readReg64 (.gpr 8#5)) errTag w2 w3 w4 w5 w6 herrTag)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  wp_done

theorem initializeBobSession_badKem_errOwned_placed_ok_of_accept [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedPlacedSpec A)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedPlacedSpec A) :=
  initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept
    (fun _ _ h hk => LibsignalCodeRoLoaded.of_keepsFrozen h hk) h_accept

theorem initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_accept : subroutine_ok (lsProg_75 H) (lsmpl.base 79)
      (pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec A)) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A) :=
  initializeBobSession_badKem_errOwned_memInv_placed_ok_of_accept
    (fun _ _ h hk => libsignalFrozen_of_keepsFrozen h hk) h_accept

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting contract for `initialize_bob_session`
(Block `75`) on Bad-KEM. -/
theorem initializeBobSession_badKem_errOwned_full_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionBadKemErrOwnedFrozenPlacedSpec A) :=
  initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
    (pqxdhAccept_badKem_err_owned_full_placed_ok_of_block hWF hP hH h_memcpy)

end LibsignalBinary.Proofs.SignalSession.Cli.D3
