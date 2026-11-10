/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs

/-!
# `spqr::init_inner` (`Block 324`): Relocatable `[LibsignalPlacement]` Definitions and Specifications

Defines the relocatable `[LibsignalPlacement]` specifications `initInnerPlacedSpec`,
`initInnerPlacedSpecX`, `initInnerPlacedRoSpecX`, and `InitInnerPlacedOkX` on `Block 324`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Relocatable `.rodata` Jump Table for `<States>::into_pb` (`Block 334`) -/

/-- Read-only separation-logic assertion for the 22-byte jump table of `<States>::into_pb` (`Block 334`). -/
def statesIntoPbJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ "spqr:.rodata.<spqr::v1::chunked::states::States>::into_pb") ↦ᵣ statesIntoPbJumpTableBytes

theorem lsro_statesIntoPbJumpTablePlacedAt [LibsignalPlacement] {s : State}
    (hro : LibsignalRoLoaded lsmpl s.mem) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

/-! ## 2. Relocatable Callee Specifications for `<States>::into_pb` (`Block 334`) -/

/-- Relocatable specification of `<spqr::v1::chunked::states::States>::into_pb` (`Block 334`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly. -/
def statesIntoPbPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Per-variant relocatable specification of `<States>::into_pb` (`Block 334`). -/
def statesIntoPbVariantPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (st : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨out, stA⟩ s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = stA⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStack
  post := fun ⟨out, stA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A out st.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStack
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- Extended-stack relocatable specification of `<States>::into_pb` (`Block 334`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly. -/
def statesIntoPbPlacedSpecX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp statesIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      optProtoInnerStateAt A x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp statesIntoPbStackX
  onPanic := fun _ s0 sf => statesIntoPbOnPanic s0 sf

/-- `<States>::into_pb` (`Block 334`) meets `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX A F)` on
    `libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext)` at `lsmpl.base 334`. -/
def StatesIntoPbPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
    (lsmpl.base 334)
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX A F))

/-! ## 3. Relocatable Specifications for `spqr::init_inner` (`Block 324`) -/

/-- Relocatable Hoare specification of `spqr::init_inner` (`Block 324`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly. -/
def initInnerPlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec InitInnerGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp initInnerStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp initInnerStack
  onPanic := fun _ s0 sf => initInnerOnPanic s0 sf

/-- Extended-stack relocatable specification of `spqr::init_inner` (`Block 324`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly (`initInnerStackX = 3392`B). -/
def initInnerPlacedSpecX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec InitInnerGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s.sp initInnerStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp initInnerStackX
  onPanic := fun _ s0 sf => initInnerOnPanic s0 sf

/-- Extended-stack relocatable specification of `spqr::init_inner` (`Block 324`)
    where `.rodata` is discharged from `LibsignalRoLoaded lsmpl s.mem`. -/
def initInnerPlacedRoSpecX (A : RustAlloc) (F : ShaCompress) :
    Spec InitInnerGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      A.pool ∗ stackAt s.sp initInnerStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      A.pool ∗ stackAt s0.sp initInnerStackX
  onPanic := fun _ s0 sf => initInnerOnPanic s0 sf

/-- `spqr::init_inner` (`Block 324`) meets `withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)` on
    `libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext)` at `lsmpl.base 324`. -/
def InitInnerPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
    (lsmpl.base 324)
    (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F))

private theorem satisfies_anyHeap_frame_init {m : Memory} {P Fr R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ Fr ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ Fr ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (Fr ∗ R), ← sepConj_assoc anyHeap Fr R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ Fr)))
  exact Satisfies.mono h1 h

/-- `initInnerPlacedSpec A F` entails `initInnerPlacedSpecX A F` by framing the unused bottom stack region. -/
theorem initInnerPlacedSpecX_of_initInnerPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    (h : subroutine_ok P addr (initInnerPlacedSpec A F)) :
    subroutine_ok P addr (initInnerPlacedSpecX A F) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : initInnerStack ≤ initInnerStackX := by decide
  have hsplit : stackAt s0.sp initInnerStackX =
      memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
        (initInnerStackX - initInnerStack) ∗
        stackAt s0.sp initInnerStack := by
    have h1 := stackAt_split_bottom s0.sp initInnerStack
      (initInnerStackX - initInnerStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
      (initInnerStackX - initInnerStack) ∗ R
  have hpre' : s0.mem ⊨ (initInnerPlacedSpec A F).pre x s0 ∗ R' := by
    dsimp only [initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame_init hpost⟩)
  · dsimp only [initInnerPlacedSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- `withLsCodeLoaded lsmpl (initInnerPlacedSpec A F)` entails
    `withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)` by framing the unused bottom stack region. -/
theorem withLsCodeLoaded_initInnerPlacedSpecX_of_initInnerPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (initInnerPlacedSpec A F))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : initInnerStack ≤ initInnerStackX := by decide
  have hsplit : stackAt s0.sp initInnerStackX =
      memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
        (initInnerStackX - initInnerStack) ∗
        stackAt s0.sp initInnerStack := by
    have h1 := stackAt_split_bottom s0.sp initInnerStack
      (initInnerStackX - initInnerStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
      (initInnerStackX - initInnerStack) ∗ R
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (initInnerPlacedSpec A F)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded, initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame_init hpost⟩)
  · dsimp only [withLsCodeLoaded, initInnerPlacedSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

end CryptoVerification.SpqrV1.Top.InitInner
