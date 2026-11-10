/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs

/-!
# Placed `message::merge<Chain> [local#4]` Definitions and Loop Assembly

`[LibsignalPlacement]` Block-`516` contract (`chainMerge3PlacedSpecW`, `Chain3PlacedOkAtW`), loop
invariant, slice statements, and loop induction corresponding to `VerNe.Chain3.Defs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
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

/-! ## 1. Placed contract (`chainMerge3PlacedSpecW`, `Chain3PlacedOkAtW`) -/

/-- Image-independent core of `chainMerge3SpecAtW`. -/
def chainMerge3RawSpecW : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      chain3GAt A0 x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      stackAt s.sp chainMerge3StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      stackAt s0.sp chainMerge3StackX
  onPanic := Serialization.allocPanic

/-- Placed contract for `message::merge<Chain> [local#3]`. -/
def chainMerge3PlacedSpecW [LibsignalPlacement] : Spec ChainMergeGenGhost :=
  withLsCl lsmpl chainMerge3RawSpecW

/-- `message::merge<Chain> [local#4]` (Block `516`) meets `chainMerge3PlacedSpecW` on
`lsProg_516 (Rust.withPanics ext)`. -/
def Chain3PlacedOkAtW [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516) chainMerge3PlacedSpecW

abbrev chainMerge5PlacedSpecW [LibsignalPlacement] : Spec ChainMergeGenGhost :=
  chainMerge3PlacedSpecW

abbrev Chain5PlacedOkAtW [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3PlacedOkAtW ext

/-! ## 2. Placed callee contracts (`Chain3CalleesPlacedW`) -/

structure Chain3CalleesPlacedW [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop where
  dv : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 515)
    (withLsCl lsmpl (decodeVarint2SpecX A0))
  bm : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 514)
    (bytesMerge3PlacedSpec A0)
  grow : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 43)
    (withLsCl lsmpl (Proofs.libsignal.Stage1X.growOneChainSpecX A0))

/-! ## 3. Loop invariant and segment steps -/

noncomputable abbrev chain3PCPlacedAtW [LibsignalPlacement]
    (_ext : String → Option (State → State)) (off : BitVec 64) : BitVec 64 :=
  lsmpl.base 516 + off

abbrev Chain3StepPlacedAtW [LibsignalPlacement]
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_516 (Rust.withPanics ext)) chainMerge3PlacedSpecW x R s0 s Q

/-- Placed loop invariant at `+0x0a8` after `k` of the chain's fields. -/
def Chain3LoopPlacedAtW [LibsignalPlacement]
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chain3PCPlacedAtW ext 0xa8#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    LibsignalCodeLoaded lsmpl s.mem ∧
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

/-- Return state of `[local#3]` with `chainMerge3PlacedSpecW.post`. -/
def Chain3RetPlacedAtW [LibsignalPlacement]
    (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ chainMerge3PlacedSpecW.post x s0 sf ∗ R)

/-! ## 4. Placed slice statements -/

def Chain3EntryPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = lsmpl.base 516 →
    s0.status = .Running →
    (s0.mem ⊨ chainMerge3PlacedSpecW.pre x s0 ∗ R) →
    s0.spAligned = true →
    Chain3StepPlacedAtW ext x R s0 s0 (Chain3LoopPlacedAtW ext x R s0 0)

def Chain3SrkPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    Chain3LoopPlacedAtW ext x R s0 k s →
    Chain3StepPlacedAtW ext x R s0 s (Chain3LoopPlacedAtW ext x R s0 (k + 1))

def Chain3ChainKeyPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    Chain3LoopPlacedAtW ext x R s0 k s →
    Chain3StepPlacedAtW ext x R s0 s (Chain3LoopPlacedAtW ext x R s0 (k + 1))

def Chain3MessageKeysPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  Chain3CalleesPlacedW ext →
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    Chain3LoopPlacedAtW ext x R s0 k s →
    Chain3StepPlacedAtW ext x R s0 s (Chain3LoopPlacedAtW ext x R s0 (k + 1))

def Chain3ExitPlacedStmt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    Chain3LoopPlacedAtW ext x R s0 x.c.fields.length s →
    Chain3StepPlacedAtW ext x R s0 s (Chain3RetPlacedAtW x R s0)

/-! ## 5. Assembly -/

theorem chain3Loop_placed_run [LibsignalPlacement] (ext : String → Option (State → State))
    (hC : Chain3CalleesPlacedW ext)
    (hSrk : Chain3SrkPlacedStmt ext) (hCk : Chain3ChainKeyPlacedStmt ext)
    (hMk : Chain3MessageKeysPlacedStmt ext) (hExit : Chain3ExitPlacedStmt ext)
    {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      Chain3LoopPlacedAtW ext x R s0 k s →
      reaches_outcome (lsProg_516 (Rust.withPanics ext)) chainMerge3PlacedSpecW x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hExit x R s0 s hs) ?_
    intro sf ⟨hret, hcc, hmem⟩ _
    exact ⟨sf, Steps.refl _, Or.inl ⟨hret, hcc, hmem⟩⟩
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', Chain3LoopPlacedAtW ext x R s0 (k + 1) s' →
        reaches_outcome (lsProg_516 (Rust.withPanics ext)) chainMerge3PlacedSpecW x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hSrk hC x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hCk hC x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hMk hC x R s0 k s hlt h4 hs) next

theorem chainMerge3W_placed_ok [LibsignalPlacement] (ext : String → Option (State → State))
    (hC : Chain3CalleesPlacedW ext)
    (hEntry : Chain3EntryPlacedStmt ext) (hSrk : Chain3SrkPlacedStmt ext)
    (hCk : Chain3ChainKeyPlacedStmt ext) (hMk : Chain3MessageKeysPlacedStmt ext)
    (hExit : Chain3ExitPlacedStmt ext) :
    Chain3PlacedOkAtW ext := by
  intro x R s0 hpc hrun hpre hal
  exact segStepG_then (hEntry hC x R s0 hpc hrun hpre hal) fun s hs =>
    chain3Loop_placed_run ext hC hSrk hCk hMk hExit x.c.fields.length 0 s (Nat.zero_add _) hs

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
