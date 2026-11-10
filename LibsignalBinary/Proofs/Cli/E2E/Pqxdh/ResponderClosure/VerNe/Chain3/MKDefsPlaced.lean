/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.CodePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `message::merge<Chain> [local#4]`: MessageKeys Shared Definitions

`[LibsignalPlacement]` Block-`516` sub-step statements (`Chain3MkPushPlacedStmt`,
`Chain3MkCntPlacedStmt`, `Chain3MkSeedPlacedStmt`, `Chain3MkHeadPlacedStmt`) corresponding to
`VerNe.Chain3.MKDefs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

/-! ## 1. Step 4d + 4e: the push (`+0x244 → +0x0a8`) -/

def Chain3MkPushPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator)
    (mk : MessageKeyGenerator) (rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    keys.length ≤ maxMessageKeys →
    s.pc = chain3PCPlacedAtW ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s.mem →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x20 = a →
    s.readReg64 .x24 = 104#64 →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 0xa8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 0xe8#64) 104 ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) keys ∗
        prostMsgKeyAt A0 mk (sp0 - 0xe8#64) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))

/-! ## 2. Step 4b: the counter field (`+0x244 → +0x244`) -/

def Chain3MkCntPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    (pbVarint 1 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 →
    s.pc = chain3PCPlacedAtW ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s.mem →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length)
            (rest_mk ++ rest) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))

/-! ## 3. Step 4c: the seed field (`+0x244 → +0x244`) -/

def Chain3MkSeedPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (seed rest : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    seed.length < 128 →
    (pbBytes 5 seed ++ rest).length < 2 ^ 62 →
    s.pc = chain3PCPlacedAtW ext 0x244#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s.mem →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x22 = sp0 - 0xe8#64 →
    s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
    (∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 160#64) seed ∗ (ptr ↦ₛ pbBytes 5 seed) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))

/-! ## 4. Step 4a: key, default scratch, length (`+0x0a8 → +0x244`) -/

def Chain3MkHeadPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (bufRef slot ptr sp0 : BitVec 64) (body rest tail : List (BitVec 8))
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State) (F : SepProp) (ret : BitVec 64)
    (Q : State → SepProp → Prop),
    body.length < 128 →
    tail.length ≤ rest.length →
    2 + (body.length + rest.length) < 2 ^ 62 →
    s.pc = chain3PCPlacedAtW ext 0xa8#64 →
    s.status = .Running →
    s.sp = sp0 - 0xf0#64 →
    sp0 &&& 15#64 = 0#64 →
    LibsignalCodeLoaded lsmpl s.mem →
    s.trace = s0.trace →
    s.readReg64 .x19 = bufRef →
    s.readReg64 .x21 = BitVec.ofNat 64 tail.length →
    s.readReg64 .x22 = sp0 - 0xe8#64 →
    s.readReg64 .x23 = 1#64 →
    (∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 0x244#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (sp0 - 0xe8#64) [] ∗ vecU8 A0 (sp0 - 208#64) [] ∗ vecU8 A0 (sp0 - 184#64) [] ∗
          vecU8At A0 (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (body ++ rest) ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))) →
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 0xe8#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
