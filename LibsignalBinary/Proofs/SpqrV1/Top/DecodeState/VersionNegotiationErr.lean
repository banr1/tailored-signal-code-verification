/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `VersionNegotiationPB` Error Exit Paths for `spqr::decode_state` (`0x5349c`)

Proves the 15 error-exit blocks (`DecodeError::push`, `DecodeError::from`, wire-type mismatch,
`decode_key` errors, and `BufferUnderflow`) for the inlined `VersionNegotiationPB::merge` loop.
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

/-- Shared `VersionNegotiationPB` error push at `0x53dc4..0x53dc8` (`+2344..+2348`, 2 instructions):
calls `DecodeError::push`, reloads `x1` from `[sp + 0x2c0]` (`s0.sp - 688#64`),
and falls through to `0x53dcc` (`decodeState_err_push_53dcc`). -/
theorem decodeState_err_push_53dc4 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2344#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2344 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x456b0#64 - 0x4e0a4#64))
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush hpush (s0.sp - 688#64) errBox n
    (ret_pc := entry + 2348#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hn := by omega)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := entry + 2352#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53dcc hc x curSt errBox (n + 1) s0 _ _ R post hpost herr (by omega)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53da4..0x53dc0` (`+2312..+2340`, 8 instructions) for `VersionNegotiation::params`:
stores `x0` (`errBox`) at `[sp + 0x2c0]` and falls through to `0x53dc4`. -/
theorem decodeState_err_push_53da4 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2312#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2312 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2344#64)
  wp_steps 8
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dc4 hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error push at `0x53d80..0x53da0` (`+2276..+2308`, 9 instructions) for `VersionNegotiation::max_version`:
stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53dc4`. -/
theorem decodeState_err_push_53d80 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2276#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2276 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2344#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dc4 hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error on `VersionNegotiation::max_version` at `0x53d68..0x53d7c` (`+2252..+2272`, 6 instructions). -/
theorem decodeState_err_53d68 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2252#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2252 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := entry + 2272#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2276#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53d80 hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53d44..0x53d64` (`+2216..+2248`, 9 instructions) for `VersionNegotiation::version`:
stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53dc4`. -/
theorem decodeState_err_push_53d44 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2216#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2216 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2344#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dc4 hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error on `VersionNegotiation::version` at `0x53d2c..0x53d40` (`+2192..+2212`, 6 instructions). -/
theorem decodeState_err_53d2c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2192#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2192 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := entry + 2212#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2216#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53d44 hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53d08..0x53d28` (`+2156..+2188`, 9 instructions) for `VersionNegotiation::public`:
stores `x0` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53dc4`. -/
theorem decodeState_err_push_53d08 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2156#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2156 36
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2344#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dc4 hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error conversion at `0x53b7c..0x53b88` (`+1760..+1772`, 4 instructions) for `VersionNegotiation`:
sets `x0 = sp + 0x2c0`, calls `DecodeError::from`, moves `x0` into `x1`,
and branches to `0x53dcc` (`decodeState_err_push_53dcc`). -/
theorem decodeState_err_from_53b7c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1760#64)
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
  decodeState_fetches b (Rust.withPanics ext) 1760 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (0x459a8#64 - 0x4e0a4#64))
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom hfrom (s0.sp - 688#64) w0
    (ret_pc := entry + 1768#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := hw)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 2352#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53dcc hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error conversion at `0x53b78` (`+1756`, 1 instruction):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`) and falls through to `0x53b7c`. -/
theorem decodeState_err_from_53b78 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1756#64)
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
  decodeState_fetches b (Rust.withPanics ext) 1756 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1760#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b7c hc x curSt (s.readReg64 .x8) s0 _ _ R post hpost herr hw
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) rfl

/-- `InvalidKeyValue` (`key >= 2^32`) in `VersionNegotiation` `decode_key` at `0x53b5c..0x53b64` (`+1728..+1736`, 3 instructions). -/
theorem decodeState_err_53b5c {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1728#64)
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
  decodeState_fetches b (Rust.withPanics ext) 1728 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1756#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b78 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- `InvalidWireType` (`(key & 7) >= 6`) in `VersionNegotiation` `decode_key` at `0x53b68..0x53b70` (`+1740..+1748`, 3 instructions). -/
theorem decodeState_err_53b68 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1740#64)
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
  decodeState_fetches b (Rust.withPanics ext) 1740 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1756#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b78 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- `InvalidTag` (`tag == 0`) in `VersionNegotiation` `decode_key` at `0x53b74` (`+1752`, 1 instruction). -/
theorem decodeState_err_53b74 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1752#64)
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
  decodeState_fetches b (Rust.withPanics ext) 1752 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1756#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b78 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error (`wt != LengthDelimited`) on `PqRatchetState::version_negotiation` at `0x53bd8..0x53be8` (`+1852..+1868`, 5 instructions). -/
theorem decodeState_err_53bd8 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 1852#64)
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
  decodeState_fetches b (Rust.withPanics ext) 1852 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1760#64)
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b7c hc x curSt 0x8000000000000006#64 s0 _ _ R post hpost herr
    (by decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFrame]; simp only [arm64_norm]; ac_rfl)

/-- `BufferUnderflow` (`len > rem`) on `VersionNegotiation` at `0x53d00..0x53d04` (`+2148..+2152`, 2 instructions). -/
theorem decodeState_err_53d00 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2148#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFrame H_inner b A x curSt s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateErrFrame] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 2148 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1756#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b78 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) rfl

/-- `BufferUnderflow` (`rem < limit`) on `VersionNegotiation` at `0x54030..0x54034` (`+2964..+2968`, 2 instructions). -/
theorem decodeState_err_54030 {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts4K H_inner b A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 2964#64)
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
  decodeState_fetches b (Rust.withPanics ext) 2964 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1756#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b78 hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) rfl

end CryptoVerification.SpqrV1.Top.DecodeState
