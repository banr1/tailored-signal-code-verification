/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.CodePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `message::merge<Chain> [local#4]`: ChainKey Shared Definitions

`[LibsignalPlacement]` Block-`516` sub-step statements (`Chain3Seg3aPlacedStmt` through
`Chain3Seg3dPlacedStmt`) corresponding to `VerNe.Chain3.KeyDefs`.
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
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

/-! ## Sub-step statements for `Chain3ChainKeyPlacedStmt` -/

def Chain3Seg3aPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hck_lt : ck_body.length < 128)
    (_houter_le : outerTailLen ≤ afterCk.length)
    (_hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = lsmpl.base 516 + 0xa8#64 →
    s0.status = .Running →
    s0.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s0.mem →
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
      sm.pc = lsmpl.base 516 + 0x368#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          chain3VecAt A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))

def Chain3Seg3bPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = lsmpl.base 516 + 0x368#64 →
    s0.status = .Running →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s0.mem →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = lsmpl.base 516 + 0x368#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))

def Chain3Seg3cPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (_hk_lt : k.length < 128)
    (_hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop},
    s0.pc = lsmpl.base 516 + 0x368#64 →
    s0.status = .Running →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s0.mem →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = lsmpl.base 516 + 0x368#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗
        chain3VecAt A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s_init sf ∗ R))

def Chain3Seg3dPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  ∀ (a bufRef slot ptr sp0 : BitVec 64)
    (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop},
    s0.pc = lsmpl.base 516 + 0x368#64 →
    s0.status = .Running →
    LibsignalCodeLoaded lsmpl s0.mem →
    s0.trace = s_init.trace →
    calleeSavedVRegs s0 = calleeSavedVRegs s_init →
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0 →
    (∀ (sm : State),
      sm.pc = lsmpl.base 516 + 0xa8#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q Qp) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q Qp

abbrev Chain3CkLenPlacedStmt [LibsignalPlacement] := Chain3Seg3aPlacedStmt
abbrev Chain3CkIdxPlacedStmt [LibsignalPlacement] := Chain3Seg3bPlacedStmt
abbrev Chain3CkKeyPlacedStmt [LibsignalPlacement] := Chain3Seg3cPlacedStmt
abbrev Chain3CkExitPlacedStmt [LibsignalPlacement] := Chain3Seg3dPlacedStmt

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
