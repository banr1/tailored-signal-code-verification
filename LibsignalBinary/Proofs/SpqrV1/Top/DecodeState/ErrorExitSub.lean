/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Outer Loop & `ChainPB` Error Exit Paths for `spqr::decode_state` (`0x5349c`)

Proves error-exit blocks for `v1::State::merge` (`0x53bc0..0x53bd4`), outer `PqRatchetState`
`decode_key` and `skip_field` failures (`0x53af8..0x53b24`), and nested `ChainPB` field and
wire-type errors.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Shared Error Precondition Frame & `[sp + 0x2c8]` (`s0.sp - 680#64`) Helpers -/

/-- Shared separation-logic frame for error exit blocks when `protoPqRatchetStateAt` is intact at
    `s0.sp - 1040#64` and `[sp + 0x2c0]` (`s0.sp - 688#64`) is split out. -/
abbrev decodeStateErrFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) : SepProp :=
  v1StateJumpTablesAt b ∗
  x.st.at A ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 680#64) 40 ∗
  memRegion (s0.sp - 640#64) 304 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

theorem bv_sub_688_add_8 (sp : BitVec 64) :
    sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega

theorem scratch_680_split_8 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ⊢
      memRegion (sp - 672#64) 32 ∗
      (∃∗ w1 : BitVec 64, (sp - 680#64) ↦₆₄ w1) := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 8] at s1
  rw [s1, ProofLib.memRegion_eight (sp - 680#64)]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_680_fold_8 (sp w1 : BitVec 64) :
    ((sp - 680#64) ↦₆₄ w1) ∗ memRegion (sp - 672#64) 32 ⊢ memRegion (sp - 680#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 8] at s1
  rw [s1]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 680#64) w1)

theorem scratch_680_split_1_1 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ⊢
      memRegion (sp - 678#64) 38 ∗
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        ((sp - 680#64) ↦₈ b0) ∗ ((sp - 679#64) ↦₈ b1)) := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 679#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 679 1] at s2
  rw [s1, s2, ProofLib.memRegion_one (sp - 680#64), ProofLib.memRegion_one (sp - 679#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_680_fold_1_1 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 680#64) ↦₈ b0) ∗ ((sp - 679#64) ↦₈ b1) ∗ memRegion (sp - 678#64) 38 ⊢
      memRegion (sp - 680#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 679#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 679 1] at s2
  rw [s1, s2]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

/-! ## 2. `v1::State::merge` Error Push (`0x53bc0`) -/

/-- Error push at `0x53bc0..0x53bd4` (`+1828..+1848`, 6 instructions) + `0x53cf0..0x53cfc`:
stores `x0` (`errBox` from `v1::State::merge`) at `[sp + 0x2c0]` (`s0.sp - 688#64`),
sets `("PqRatchetState", "v1")` + `w4 = 5`, and jumps to `0x53dec` (`decodeState_err_push_53dec`). -/
theorem decodeState_err_push_53bc0 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1828#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1828 24
  decodeState_fetches b (Rust.withPanics ext) 2132 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2384#64)
  wp_steps 10
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm])

/-! ## 3. Outer Loop `decode_key` & `skip_field` Error Exits (`0x53af8..0x53b24`) -/

/-- Error exit at `0x53b20..0x53b24` (`+1668..+1672`, 2 instructions):
moves `x0` (`errBox`) into `x20` and branches to `0x53df4` (`decodeState_err_tail_53df4`). -/
theorem decodeState_err_53b20 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1668#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1668 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  wp_steps 2
  refine SepWP.fold (scratch_688_fold_48 s0.sp w0) (by sep_focus) ?_
  exact decodeState_err_tail_53df4 hc x curSt n s0 _ _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm]; ac_rfl)

/-- Error conversion at `0x53b14..0x53b24` (`+1656..+1672`, 5 instructions):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`), calls `DecodeError::from(sp + 0x2c0)`,
moves `x0` into `x20`, and branches to `0x53df4`. -/
theorem decodeState_err_from_53b14 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1656#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1656 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) (s.readReg64 .x8)
    (ret_pc := entry + 1668#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := hw)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  exact decodeState_err_53b20 hc x curSt v_k 0 s0 s1 _ R post hpost herr
    (by rw [decodeStateEntry_eq, hentry, hpc1]) hrun1 hsp1 hs0A htr1
    (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm, *]; ac_rfl)

/-- Error exit at `0x53af8..0x53b00` (`+1628..+1636`, 3 instructions):
`InvalidKeyValue` (`key >= 2^32`) in outer `decode_key`. -/
theorem decodeState_err_53af8 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1628#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1628 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1656#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x20)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b14 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- Error exit at `0x53b04..0x53b0c` (`+1640..+1648`, 3 instructions):
`InvalidWireType` (`(key & 7) >= 6`) in outer `decode_key`. -/
theorem decodeState_err_53b04 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1640 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1656#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b14 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- Error exit at `0x53b10` (`+1652`, 1 instruction):
`InvalidTag` (`tag == 0`) in outer `decode_key`. -/
theorem decodeState_err_53b10 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1652#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1652 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1656#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b14 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-! ## 4. `ChainPB` Error Exits (`0x53ad8`, `0x53b8c..0x53bbc`, `0x53c9c..0x53cd8`, `0x53ec4..0x53fd0`) -/

/-- Shared `ChainPB` error push at `0x53cbc..0x53cc4` (`+2080..+2088`, 3 instructions):
calls `DecodeError::push`, reloads `x1` from `[sp + 0x2c0]` (`s0.sp - 688#64`),
and jumps to `0x53cdc` (`decodeState_err_push_53cdc`). -/
theorem decodeState_err_push_53cbc {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2080#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ errBox) ∗ decodeErrorAtStackLen A errBox n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hpush := hc.decodeErrorPush_at
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hpush ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2080 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x456b0#64 - 0x4e0a4#64))
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush hpush (s0.sp - 688#64) errBox n
    (ret_pc := entry + 2084#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hn := by omega)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := entry + 2112#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53cdc hc x curSt errBox (n + 1) s0 _ _ R post hpost herr (by omega)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53c9c..0x53cb8` (`+2048..+2076`, 8 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("Chain", "epoch")`,
and delegates to `decodeState_err_push_53cbc`. -/
theorem decodeState_err_push_53c9c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2048#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x1) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2048 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2080#64)
  wp_steps 8
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error push at `0x53edc..0x53efc` (`+2624..+2656`, 9 instructions):
stores `x8` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("Chain", "recv_epoch")`,
and jumps to `0x53cbc`. -/
theorem decodeState_err_push_53edc {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x8) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2624 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2080#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error on `Chain::recv_epoch` at `0x53ec4..0x53ed8` (`+2600..+2620`, 6 instructions). -/
theorem decodeState_err_53ec4 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2600 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := entry + 2620#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2624#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53edc hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm, *]; ac_rfl)

/-- Shared tail at `0x53fa0..0x53fac` (`+2820..+2832`, 4 instructions) for `Chain::version` and `Chain::auth_key`:
sets `x0 = sp + 0x2c0`, `w2 = 5`, `w4 = 9`, and jumps to `0x53cbc`. -/
theorem decodeState_err_push_53fa0 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2820#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ errBox) ∗ decodeErrorAtStackLen A errBox n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2820 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2080#64)
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc hc x curSt errBox n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error push at `0x53f8c..0x53f9c` (`+2800..+2816`, 5 instructions) for `Chain::auth_key`:
stores `x0` (`errBox`) at `[sp + 0x2c0]` and falls through to `0x53fa0`. -/
theorem decodeState_err_push_53f8c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2800#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2800 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2820#64)
  wp_steps 5
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53fa0 hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- Error push at `0x53f18..0x53f2c` (`+2684..+2704`, 6 instructions) for `Chain::version`:
stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53fa0`. -/
theorem decodeState_err_push_53f18 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2684#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x8) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2684 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2820#64)
  wp_steps 6
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53fa0 hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- Wire-type mismatch error on `Chain::version` at `0x53f00..0x53f14` (`+2660..+2680`, 6 instructions). -/
theorem decodeState_err_53f00 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2660#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2660 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := entry + 2680#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2684#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53f18 hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53f68..0x53f88` (`+2764..+2796`, 9 instructions) for `Chain::starting_epoch`:
stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53cbc`. -/
theorem decodeState_err_push_53f68 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2764#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x8) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2764 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2080#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error on `Chain::starting_epoch` at `0x53f50..0x53f64` (`+2740..+2760`, 6 instructions). -/
theorem decodeState_err_53f50 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2740 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := entry + 2760#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2764#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53f68 hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53fb0..0x53fd0` (`+2836..+2868`, 9 instructions) for `Chain::params`:
stores `x0` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53cbc`. -/
theorem decodeState_err_push_53fb0 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2836 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2080#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error conversion at `0x53cd0..0x53cd8` (`+2100..+2108`, 3 instructions) for `Chain`:
sets `x0 = sp + 0x2c0`, calls `DecodeError::from`, moves `x0` into `x1`,
and falls through to `0x53cdc` (`decodeState_err_push_53cdc`). -/
theorem decodeState_err_from_53cd0 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hfrom := hc.decodeErrorFrom_at
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc hfrom ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2100 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) w0
    (ret_pc := entry + 2108#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := hw)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2112#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53cdc hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error conversion at `0x53ccc` (`+2096`, 1 instruction):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`) and falls through to `0x53cd0`. -/
theorem decodeState_err_from_53ccc {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2096#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2096 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2100#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53cd0 hc x curSt (s.readReg64 .x8) s0 _ _ R post hpost herr hw
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- `BufferUnderflow` (`len > rem`) on `Chain` at `0x53cc8` (`+2092`, 1 instruction). -/
theorem decodeState_err_53cc8 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2092#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2092 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2096#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- `BufferUnderflow` (`rem < limit`) on `Chain` at `0x53ad8..0x53adc` (`+1596..+1600`, 2 instructions). -/
theorem decodeState_err_53ad8 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1596#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1596 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2096#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- `InvalidKeyValue` (`key >= 2^32`) in `Chain` `decode_key` at `0x53b8c..0x53b94` (`+1776..+1784`, 3 instructions). -/
theorem decodeState_err_53b8c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1776#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1776 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2096#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- `InvalidWireType` (`(key & 7) >= 6`) in `Chain` `decode_key` at `0x53b98..0x53ba0` (`+1788..+1796`, 3 instructions). -/
theorem decodeState_err_53b98 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1788#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1788 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2096#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- `InvalidTag` (`tag == 0`) in `Chain` `decode_key` at `0x53ba4..0x53ba8` (`+1800..+1804`, 2 instructions). -/
theorem decodeState_err_53ba4 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1800 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2096#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- Wire-type mismatch error (`wt != LengthDelimited`) on `PqRatchetState::chain` at `0x53bac..0x53bbc` (`+1808..+1824`, 5 instructions). -/
theorem decodeState_err_53bac {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1808#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 1808 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2100#64)
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53cd0 hc x curSt 0x8000000000000006#64 s0 _ _ R post hpost herr
    (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

end CryptoVerification.SpqrV1.Top.DecodeState
