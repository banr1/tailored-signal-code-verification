/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Verification of `spqr::decode_state` (Block `325`) — Outer Loop & `ChainPB` Error Exit Paths
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Shared Error Precondition Frame -/

/-- Shared separation-logic frame for error exit blocks when `protoPqRatchetStateAt` is intact at
    `s0.sp - 1040#64` and `[sp + 0x2c0]` (`s0.sp - 688#64`) is split out. -/
abbrev decodeStateErrFramePlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) : SepProp :=
  v1StateJumpTablesPlacedAt ∗
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

/-! ## 2. `v1::State::merge` Error Push (`0x53bc0`) -/

/-- Error push at `0x53bc0..0x53bd4` (`+1828..+1848`, 6 instructions) + `0x53cf0..0x53cfc`:
stores `x0` (`errBox` from `v1::State::merge`) at `[sp + 0x2c0]` (`s0.sp - 688#64`),
sets `("PqRatchetState", "v1")` + `w4 = 5`, and jumps to `0x53dec` (`decodeState_err_push_53dec_placed`). -/
theorem decodeState_err_push_53bc0_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32)
    (hpc : s.pc = decodeStatePlacedEntry + 1828#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2384#64)
  wp_steps 10
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53dec_placed hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm])

/-! ## 3. Outer Loop `decode_key` & `skip_field` Error Exits (`0x53af8..0x53b24`) -/

/-- Error exit at `0x53b20..0x53b24` (`+1668..+1672`, 2 instructions):
moves `x0` (`errBox`) into `x20` and branches to `0x53df4` (`decodeState_err_tail_53df4_placed`). -/
theorem decodeState_err_53b20_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1668#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP_ret
  wp_steps 2
  refine SepWP.fold (scratch_688_fold_48 s0.sp w0) (by sep_focus) ?_
  exact decodeState_err_tail_53df4_placed hc x curSt n s0 _ _ R post hpost herr
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm]; ac_rfl)

/-- Error conversion at `0x53b14..0x53b24` (`+1656..+1672`, 5 instructions):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`), calls `DecodeError::from(sp + 0x2c0)`,
moves `x0` into `x20`, and branches to `0x53df4`. -/
theorem decodeState_err_from_53b14_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = decodeStatePlacedEntry + 1656#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom_placed hfrom (s0.sp - 688#64) (s.readReg64 .x8)
    (ret_pc := (blkPl_325).base + 1668#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := hw)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  exact decodeState_err_53b20_placed hc x curSt v_k 0 s0 s1 _ R post hpost herr
    (by dsimp only [decodeStatePlacedEntry]; exact hpc1) hrun1 hsp1 hs0A htr1
    (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm, *]; ac_rfl)

/-- Error exit at `0x53af8..0x53b00` (`+1628..+1636`, 3 instructions):
`InvalidKeyValue` (`key >= 2^32`) in outer `decode_key`. -/
theorem decodeState_err_53af8_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1628#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1656#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x20)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b14_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm]; ac_rfl)

/-- Error exit at `0x53b04..0x53b0c` (`+1640..+1648`, 3 instructions):
`InvalidWireType` (`(key & 7) >= 6`) in outer `decode_key`. -/
theorem decodeState_err_53b04_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1656#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b14_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm]; ac_rfl)

/-- Error exit at `0x53b10` (`+1652`, 1 instruction):
`InvalidTag` (`tag == 0`) in outer `decode_key`. -/
theorem decodeState_err_53b10_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1652#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 1656#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53b14_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-! ## 4. `ChainPB` Error Exits (`0x53ad8`, `0x53b8c..0x53bbc`, `0x53c9c..0x53cd8`, `0x53ec4..0x53fd0`) -/

/-- Shared `ChainPB` error push at `0x53cbc..0x53cc4` (`+2080..+2088`, 3 instructions):
calls `DecodeError::push`, reloads `x1` from `[sp + 0x2c0]` (`s0.sp - 688#64`),
and jumps to `0x53cdc` (`decodeState_err_push_53cdc_placed`). -/
theorem decodeState_err_push_53cbc_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2080#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 688#64) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ errBox) ∗ decodeErrorAtStackLen A errBox n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hpush := hc.decodeErrorPush
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hpush ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorPush_placed hpush (s0.sp - 688#64) errBox n
    (ret_pc := (blkPl_325).base + 2084#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hn := by omega)
    (hP := by sep_focus) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2112#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53cdc_placed hc x curSt errBox (n + 1) s0 _ _ R post hpost herr (by omega)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53c9c..0x53cb8` (`+2048..+2076`, 8 instructions):
stores `x1` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("Chain", "epoch")`,
and delegates to `decodeState_err_push_53cbc_placed`. -/
theorem decodeState_err_push_53c9c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2048#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x1) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2080#64)
  wp_steps 8
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc_placed hc x curSt (s.readReg64 .x1) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error push at `0x53edc..0x53efc` (`+2624..+2656`, 9 instructions):
stores `x8` (`errBox`) at `[sp + 0x2c0]` (`s0.sp - 688#64`), sets `("Chain", "recv_epoch")`,
and jumps to `0x53cbc`. -/
theorem decodeState_err_push_53edc_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2080#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc_placed hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error on `Chain::recv_epoch` at `0x53ec4..0x53ed8` (`+2600..+2620`, 6 instructions). -/
theorem decodeState_err_53ec4_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2600#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom_placed hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := (blkPl_325).base + 2620#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2624#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53edc_placed hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm, *]; ac_rfl)

/-- Shared tail at `0x53fa0..0x53fac` (`+2820..+2832`, 4 instructions) for `Chain::version` and `Chain::auth_key`:
sets `x0 = sp + 0x2c0`, `w2 = 5`, `w4 = 9`, and jumps to `0x53cbc`. -/
theorem decodeState_err_push_53fa0_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (errBox : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2820#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ errBox) ∗ decodeErrorAtStackLen A errBox n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2080#64)
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc_placed hc x curSt errBox n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error push at `0x53f8c..0x53f9c` (`+2800..+2816`, 5 instructions) for `Chain::auth_key`:
stores `x0` (`errBox`) at `[sp + 0x2c0]` and falls through to `0x53fa0`. -/
theorem decodeState_err_push_53f8c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2800#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2820#64)
  wp_steps 5
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53fa0_placed hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- Error push at `0x53f18..0x53f2c` (`+2684..+2704`, 6 instructions) for `Chain::version`:
stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53fa0`. -/
theorem decodeState_err_push_53f18_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2684#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2820#64)
  wp_steps 6
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53fa0_placed hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- Wire-type mismatch error on `Chain::version` at `0x53f00..0x53f14` (`+2660..+2680`, 6 instructions). -/
theorem decodeState_err_53f00_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2660#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom_placed hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := (blkPl_325).base + 2680#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2684#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53f18_placed hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53f68..0x53f88` (`+2764..+2796`, 9 instructions) for `Chain::starting_epoch`:
stores `x8` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53cbc`. -/
theorem decodeState_err_push_53f68_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2764#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x8) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2080#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc_placed hc x curSt (s.readReg64 .x8) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Wire-type mismatch error on `Chain::starting_epoch` at `0x53f50..0x53f64` (`+2740..+2760`, 6 instructions). -/
theorem decodeState_err_53f50_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom_placed hfrom (s0.sp - 688#64) 0x8000000000000006#64
    (ret_pc := (blkPl_325).base + 2760#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := by decide)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2764#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53f68_placed hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm, *]; ac_rfl)

/-- Error push at `0x53fb0..0x53fd0` (`+2836..+2868`, 9 instructions) for `Chain::params`:
stores `x0` (`errBox`) at `[sp + 0x2c0]` and branches to `0x53cbc`. -/
theorem decodeState_err_push_53fb0_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64) (n : Nat)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hn : n < 2 ^ 32 - 1)
    (hpc : s.pc = decodeStatePlacedEntry + 2836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
      decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2080#64)
  wp_steps 9
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_push_53cbc_placed hc x curSt (s.readReg64 .x0) n s0 _ _ R post hpost herr hn
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, hx19]) rfl

/-- Error conversion at `0x53cd0..0x53cd8` (`+2100..+2108`, 3 instructions) for `Chain`:
sets `x0 = sp + 0x2c0`, calls `DecodeError::from`, moves `x0` into `x1`,
and falls through to `0x53cdc` (`decodeState_err_push_53cdc_placed`). -/
theorem decodeState_err_from_53cd0_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode) (hw : KindNoHeap w0)
    (hpc : s.pc = decodeStatePlacedEntry + 2100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hfrom := hc.decodeErrorFrom
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hfrom ⊢
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPp.call_decodeErrorFrom_placed hfrom (s0.sp - 688#64) w0
    (ret_pc := (blkPl_325).base + 2108#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hsp]) (hw := hw)
    (hP := by simp only [bv_sub_688_add_8]; sep_focus) ?_
  intro s1 v_k hpc1 hrun1 hsp1 htr1 hcs1 _
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [bv_sub_688_add_8 s0.sp]
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2112#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact decodeState_err_push_53cdc_placed hc x curSt v_k 0 s0 _ _ R post hpost herr (by decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
    (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- Error conversion at `0x53ccc` (`+2096`, 1 instruction):
stores `x8` at `[sp + 0x2c0]` (`s0.sp - 688#64`) and falls through to `0x53cd0`. -/
theorem decodeState_err_from_53ccc_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hw : KindNoHeap (s.readReg64 .x8))
    (hpc : s.pc = decodeStatePlacedEntry + 2096#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2100#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53cd0_placed hc x curSt (s.readReg64 .x8) s0 _ _ R post hpost herr hw
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- `BufferUnderflow` (`len > rem`) on `Chain` at `0x53cc8` (`+2092`, 1 instruction). -/
theorem decodeState_err_53cc8_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 2092#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2096#64)
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- `BufferUnderflow` (`rem < limit`) on `Chain` at `0x53ad8..0x53adc` (`+1596..+1600`, 2 instructions). -/
theorem decodeState_err_53ad8_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1596#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2096#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- `InvalidKeyValue` (`key >= 2^32`) in `Chain` `decode_key` at `0x53b8c..0x53b94` (`+1776..+1784`, 3 instructions). -/
theorem decodeState_err_53b8c_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1776#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2096#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x1)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm]; ac_rfl)

/-- `InvalidWireType` (`(key & 7) >= 6`) in `Chain` `decode_key` at `0x53b98..0x53ba0` (`+1788..+1796`, 3 instructions). -/
theorem decodeState_err_53b98_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1788#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0) (hx19 : s.readReg64 .x19 = x.outPtr)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2096#64)
  refine SepWP.fold (scratch_680_split_8 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 3
  refine SepWP.fold (scratch_680_fold_8 s0.sp (s.readReg64 .x0)) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm]; ac_rfl)

/-- `InvalidTag` (`tag == 0`) in `Chain` `decode_key` at `0x53ba4..0x53ba8` (`+1800..+1804`, 2 instructions). -/
theorem decodeState_err_53ba4_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2096#64)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53ccc_placed hc x curSt w0 s0 _ _ R post hpost herr
    (by simp only [arm64_norm, hx21]; decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    rfl

/-- Wire-type mismatch error (`wt != LengthDelimited`) on `PqRatchetState::chain` at `0x53bac..0x53bbc` (`+1808..+1824`, 5 instructions). -/
theorem decodeState_err_53bac_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (w0 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (herr : spqrDecodeState x.st.bytes = .error .stateDecode)
    (hpc : s.pc = decodeStatePlacedEntry + 1808#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗ decodeStateErrFramePlaced H_inner A x curSt s0) :
    SepWPp (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_325).base + 2100#64)
  refine SepWP.fold (scratch_680_split_1_1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; wp_steps 5
  refine SepWP.fold (scratch_680_fold_1_1 s0.sp _ _) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact decodeState_err_from_53cd0_placed hc x curSt 0x8000000000000006#64 s0 _ _ R post hpost herr
    (by decide)
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
    (by dsimp only [decodeStateErrFramePlaced]; simp only [arm64_norm]; ac_rfl)

end CryptoVerification.SpqrV1.Top.DecodeState
