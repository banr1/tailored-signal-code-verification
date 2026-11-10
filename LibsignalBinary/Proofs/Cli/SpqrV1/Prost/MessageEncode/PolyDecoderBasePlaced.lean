/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBase
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable `encode<PolynomialDecoder> [local#3]` Step Helpers (Block `455`)

Defines placed contract propositions and proves basic-block and `do_reserve` step lemmas on CLI
Block `455` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Auth
  CryptoVerification.SpqrV1.Prost.MessageEncode CryptoVerification.Cli.SpqrV1.Alloc.Placed
  CryptoVerification.Cli.SpqrV1.Varint.Placed
  CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced
  CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local arm64_norm] private theorem blkPl_451_base_eq [LibsignalPlacement] :
    (blkPl_451).base = lsmpl.base 451 := rfl
@[local arm64_norm] private theorem blkPl_460_base_eq [LibsignalPlacement] :
    (blkPl_460).base = lsmpl.base 460 := rfl
@[local arm64_norm] private theorem blkPl_493_base_eq [LibsignalPlacement] :
    (blkPl_493).base = lsmpl.base 493 := rfl

/-! ## Placed Contract Propositions for Block `455` -/

def EncodePolyDecoder1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 (Rust.withPanics ext)) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A))

def EncodePolyDecoder1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 (Rust.withPanics ext)) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A))

def EncodePolyDecoder1PinnedPlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 H) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecX A))

def EncodePolyDecoder1PlacedOkExtX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 H) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpecX A))

def EncodePolyDecoder1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def EncodePolyDecoder1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def EncodePolyDecoder1PinnedPlacedOkX [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PinnedPlacedOkExtX A (Rust.withPanics (tripleRatchetExterns C ctl abs))

def EncodePolyDecoder1PlacedPlacedOkX [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PlacedOkExtX A (Rust.withPanics (tripleRatchetExterns C ctl abs))

abbrev EncodePolyDecoder1PlacedOkX := @EncodePolyDecoder1PlacedPlacedOkX

/-! ## Step Lemmas for Block `455` (`lsProg_455 H`) -/

/-- Step `+0..+36`: allocates 48B frame (`msgEnc48SavedFrame`), saves `fp, lr, x21, x20, x19`,
sets `x20 = decA`, `x1 = v`, `x19 = v`, and `x0 = ((tag <<< 3) ||| 2#32).zeroExtend 64`. -/
theorem step_polyDecoder_prologue_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (H : String → Option (State → State)) (tag : BitVec 32) (decA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_455).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (s1 : State) (sv3 : BitVec 64),
      s1.pc = (blkPl_455).base + 36#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = ((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64 →
      s1.readReg64 .x1 = v → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp (lsProg_455 H) ret s1
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  have hw0' : BitVec.truncate 32 (s.readReg64 .x0) = tag := hw0
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 36#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ sv3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0] at hw0' ⊢; simp only [arm64_norm]
          exact polyDecoder_tag_orr_eq tag)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+40..+44` (`mov x0, x20`). -/
theorem step_polyDecoder_mov_x0_x20_40_placed [LibsignalPlacement]
    (H : String → Option (State → State)) (decA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_455).base + 44#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = decA → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp (lsProg_455 H) ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 44#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

/-- Step `+48..+52` (`mov x1, x19`). -/
theorem step_polyDecoder_mov_x1_x19_48_placed [LibsignalPlacement]
    (H : String → Option (State → State)) (decA v x0v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 48#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = x0v) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_455).base + 52#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = x0v → s1.readReg64 .x1 = v → s1.readReg64 .x19 = v →
      s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp (lsProg_455 H) ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 52#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

/-- Step `+56..+64`: loads `w0 = [x20, #0x18]` (`pb.ptsNeeded`) and branches to `+108` if `pb.ptsNeeded == 0#32`,
else falls through to `+64`. -/
theorem step_polyDecoder_check_ptsNeeded_placed [LibsignalPlacement]
    (H : String → Option (State → State)) (decA v sp : BitVec 64)
    (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 56#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + (if pb.ptsNeeded == 0#32 then 108#64 else 64#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; dsimp only [polyDecoderElemsAt]
  cases hpn : (pb.ptsNeeded == 0#32)
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 64#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 108#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+80..+104`: stores tag byte `0x08#8` (`field 1, wire type varint`) into `curBs` and sets `x1 = v`. -/
theorem step_polyDecoder_push_ptsNeeded_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 80#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 104#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 104#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+108..+116`: loads `w0 = [x20, #0x1c]` (`pb.polys`) and branches to `+160` if `pb.polys == 0#32`,
else falls through to `+116`. -/
theorem step_polyDecoder_check_polys_placed [LibsignalPlacement]
    (H : String → Option (State → State)) (decA v sp : BitVec 64)
    (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 108#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + (if pb.polys == 0#32 then 160#64 else 116#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; dsimp only [polyDecoderElemsAt]
  cases hpl : (pb.polys == 0#32)
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 160#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+132..+156`: stores tag byte `0x10#8` (`field 2, wire type varint`) into `curBs` and sets `x1 = v`. -/
theorem step_polyDecoder_push_polys_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 132#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 156#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm (vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 156#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+160..+172`: loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 3#32`, `x3 = v`. -/
theorem step_polyDecoder_prep_pts_placed [LibsignalPlacement]
    (H : String → Option (State → State)) (decA v sp : BitVec 64)
    (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 160#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_455).base + 172#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg32 .x0 = 3#32 → s1.readReg64 .x1 = g.pts.ptr →
      s1.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → s1.readReg64 .x3 = v →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp (lsProg_455 H) ret s1 (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP; dsimp only [polyDecoderElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 172#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+176..+188` / `+248..+264`: loads `w8 = [decA + 0x20]` (`boolByte pb.isComplete`).
- If `pb.isComplete = false`, branches to `+248` and executes the epilogue.
- If `pb.isComplete = true`, falls through to `+188`. -/
theorem step_polyDecoder_check_isComplete_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (H : String → Option (State → State)) (decA v sp sv3 : BitVec 64)
    (g : ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hfalse : pb.isComplete = false → ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F))
    (htrue : pb.isComplete = true → ∀ s1 : State,
      s1.pc = (blkPl_455).base + 188#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp (lsProg_455 H) (s0.readReg64 .lr) s1
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  cases hc : pb.isComplete
  · have hbyte : SpqrV1.Poly.boolByte pb.isComplete = 0#8 := by rw [hc]; rfl
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
    apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr)
    dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]; rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
    refine SepWPp.weaken_pre
      (show _ ⊢ (polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
    · rw [← hbyte]
      have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
        (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
        (s0.readReg64 .x20) (s0.readReg64 .x19)
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
      dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    · apply (hfalse hc)
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · epochEncLen_cc_close
      · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩
  · have hbyte : SpqrV1.Poly.boolByte pb.isComplete = 1#8 := by rw [hc]; rfl
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 188#64)
    dsimp only [polyDecoderElemsAt]; rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by rw [← hbyte]; dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (htrue hc _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1))

/-- Step `+204..+228`: stores tag byte `0x20#8` (`field 4, wire type varint`) into `curBs`, sets
`x9 = curPtr`, `x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length`, and compares `x8 = curCap` with `x10` at `+228`. -/
theorem step_polyDecoder_push_isComplete_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 204#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx8 : s.readReg64 .x8 = curCap) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_455).base + 228#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x8 = curCap → s1.readReg64 .x9 = curPtr →
      s1.readReg64 .x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      s1.pstate = subsPState64 curCap (BitVec.ofNat 64 (curBs ++ [0x20#8]).length) →
      MsgEnc48CalleeSavedPlaced s0 s1 →
      SepWPp (lsProg_455 H) ret s1 (vecU8At A v curCap curPtr (curBs ++ [0x20#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 228#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hlen1 : BitVec.ofNat 64 curBs.length + 1#64 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length := by
    rw [List.length_append, List.length_singleton]; exact (BitVec.ofNat_add curBs.length 1).symm
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x20#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+232..+264`: stores value byte `0x01#8` into `curBs`, updates `[v + 16] = curBs.length + 1`,
and executes the epilogue (`ldp x20, x19; ldr x21; ldp x29, x30, [sp], #0x30; ret`). -/
theorem step_polyDecoder_push_isComplete_val_epilogue_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) (A : RustAlloc) (H : String → Option (State → State))
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 232#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length) (hx19 : s.readReg64 .x19 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_455 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr); dsimp only [msgEnc48SavedFrame]; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
  refine SepWPp.weaken_pre
    (show _ ⊢ (vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
  · rw [← vecU8At_close_one A v curCap curPtr curBs 0x01#8 hlt]
    have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
      (s0.readReg64 .x20) (s0.readReg64 .x19)
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
    dsimp only [msgEnc48SavedFrame]
  · apply hnext
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · epochEncLen_cc_close
    · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩

/-! ## `do_reserve` Branch Helpers for Block `455` (`calls 460`) -/

theorem step_reserve_64_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 64#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 80#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_460).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve2_call_placed hres A hdoReserve v curCap curPtr sp
      ((blkPl_455).base + 280#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = pb.ptsNeeded.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 80#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 80#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

theorem step_reserve_116_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 132#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_460).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve2_call_placed hres A hdoReserve v curCap curPtr sp
      ((blkPl_455).base + 308#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = pb.polys.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 132#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 132#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

theorem step_reserve_188_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 204#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x8 = nextCap →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_460).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve2_call_placed hres A hdoReserve v curCap curPtr sp
      ((blkPl_455).base + 332#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

theorem step_reserve_228_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 .x8 = curCap) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hz : s.pstate = subsPState64 curCap (BitVec.ofNat 64 curBs.length)) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 232#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x9 = nextPtr → sm.readReg64 .x10 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hcap_bv : curCap = BitVec.ofNat 64 curBs.length := eq_of_beq hcap
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_460).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve2_call_placed hres A hdoReserve v curCap curPtr sp
      ((blkPl_455).base + 360#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 232#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 232#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem cap_beq_len_false_of_lt_pd {curBs : List (BitVec 8)} {curCap : BitVec 64}
    (hlt : curBs.length < curCap.toNat) :
    (curCap == BitVec.ofNat 64 curBs.length) = false := by
  have hcap_lt : curBs.length < 2 ^ 64 := Nat.lt_trans hlt (BitVec.isLt curCap)
  cases h : (curCap == BitVec.ofNat 64 curBs.length)
  · rfl
  · exfalso
    have heq : curCap.toNat = (BitVec.ofNat 64 curBs.length).toNat := congrArg BitVec.toNat (eq_of_beq h)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt] at heq; omega

theorem step_reserve_188_1_exact_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlt0 : curBs.length < curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 204#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x8 = curCap →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm (vecU8At A v curCap curPtr curBs ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := cap_beq_len_false_of_lt_pd hlt0
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 204#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
  refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0))

theorem step_reserve_228_1_exact_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlt0 : curBs.length < curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (_hx8 : s.readReg64 .x8 = curCap) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hz : s.pstate = subsPState64 curCap (BitVec.ofNat 64 curBs.length))
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 232#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x9 = curPtr → sm.readReg64 .x10 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm (vecU8At A v curCap curPtr curBs ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  subst hP
  have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := cap_beq_len_false_of_lt_pd hlt0
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_455).base + 232#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0))

theorem step_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (tag : BitVec 32) (decA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (bs0 : List (BitVec 8))
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat ∨
      bs0.length + (polyDecoderHeaderBytes tag pb).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_455).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt A g decA pb ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_455).base + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A decA g ptsElems ∗
          vecU8At A v cap1 ptr1 (bs0 ++ polyDecoderHeaderBytes tag pb) ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_455 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge_key, hge2⟩ := polyDecoderHeaderBytes_len_bounds tag pb
  refine step_polyDecoder_prologue_placed hres H tag decA v sp hhs0 hpc hrun hsp halign htr
    hw0 hx1 hx2 hcs
    (F := protoPolynomialDecoderPinnedAt A g decA pb ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hfit_key : bs0.length +
      (LibsignalProtoCodec.encodeVarint (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat ∨
      bs0.length + 10 < 2 ^ 62 := by
    rw [encodeVarint_polyDecoder_tag_eq_proto]
    rcases hfit_hdr with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) v cap0 ptr0 sp
    ((blkPl_455).base + 40#64) bs0 hfit_key
    (F := protoPolynomialDecoderPinnedAt A g decA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01
  rw [encodeVarint_polyDecoder_tag_eq_proto] at hpres01 ⊢
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x0_x20_40_placed H decA v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_493).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  refine step_msg48rep_polyDecLen_call_placed hres128 A hencLen decA sp ((blkPl_455).base + 48#64) g pb hlen_lt
    (F := vecU8At A v cap01 ptr01 (bs0 ++ Proto.encodeKey tag .lengthDelimited) ∗ A.pool ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 ptsElems hpts_eq hpts_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x1_x19_48_placed H decA v
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_451).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
  have hfit_len : (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ≤ cap01.toNat ∨
      (bs0 ++ Proto.encodeKey tag .lengthDelimited).length + 10 < 2 ^ 62 := by
    rw [List.length_append]
    rcases hfit_hdr with h | h
    · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
    · right; omega
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) v cap01 ptr01 sp ((blkPl_455).base + 56#64)
    (bs0 ++ Proto.encodeKey tag .lengthDelimited) hfit_len
    (F := polyDecoderElemsAt decA g pb ptsElems ∗
      polyDecoderRestAt A decA g ptsElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 hge1 hpres1
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = decA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [bs0_append_polyDecoderHeaderBytes bs0 tag pb]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s6 sv3 cap1 ptr1 ptsElems hpts_eq hpts_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6 (Nat.le_trans hge01 hge1) ?_)
  intro hle
  obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
  exact hpres1 (by rw [List.length_append]; omega)

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
