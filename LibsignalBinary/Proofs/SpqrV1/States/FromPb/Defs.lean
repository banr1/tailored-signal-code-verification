/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Definitions, Specifications, and Dispatch

**Checked by Lean.**

Defines the `Result<States, spqr::Error>` (`928` B) representation predicate, the total
`<PolyDecoder>::from_pb` pure model and callee contract, top-level and per-variant Hoare
specifications for `<States>::from_pb` (`0x5a0a4`, 2,911 instructions), and prologue, epilogue,
and `None`-variant stepping lemmas.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. `Result<States, spqr::Error>` Representation (`928`B = `0x3a0`) -/

/-- `spqr::Error` `u8` discriminant in `Result<States, spqr::Error>` at `out + 8`:
    * `0#8`: `Error::StateDecode`
    * `1#8`: `Error::EpochOutOfRange` (carries `u64` at `out + 16`, unused in `from_pb`)
    * `2#8`: `Error::MsgDecode`
    * `3#8`: `Error::MacVerifyFailed`
    * `4#8`: `Error::ErroneousDataReceived` -/
def spqrErrorByte : LibsignalSpqrV1.Error → BitVec 8
  | .stateDecode => 0#8
  | .epochOutOfRange _ => 1#8
  | .msgDecode => 2#8
  | .macVerifyFailed => 3#8
  | .erroneousDataReceived => 4#8
  | _ => 0#8

/-- Binary layout of `Result<spqr::v1::chunked::states::States, spqr::Error>` (`928`B = `0x3a0`):
    * `.ok st`: `chunkedStatesAt A out st` (`928`B)
    * `.error (.err err)`: `(out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (out + 9#64) 919`
    * `.error (.panic _)`: `⌜False⌝` (`States.from_pb` never returns `.error (.panic _)`). -/
def resultChunkedStatesAt (A : RustAlloc) {F : ShaCompress} (out : BitVec 64) :
    StatesResult (States spqrPolyApi (spqrAuthApi F)) → SepProp
  | .ok st => chunkedStatesAt A out st
  | .error (.err err) =>
    (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (out + 9#64) 919
  | .error (.panic _) => ⌜False⌝

theorem memRegion_out_928_split_err (out : BitVec 64) :
    memRegion out chunkedStatesSize =
      (∃∗ v0 : BitVec 64, (out ↦₆₄ v0)) ∗
      (∃∗ b8 : BitVec 8, ((out + 8#64) ↦₈ b8)) ∗
      memRegion (out + 9#64) 919 := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split out 8 920 (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 919)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (out + 8#64)]

/-! ## 2. Total Pure Model and Contract for `<PolyDecoder>::from_pb` (`0x62b1c`) -/

/-- Symbol name of `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`, 325 insns). -/
abbrev decoderFromPbName : String :=
  "<spqr::encoding::polynomial::PolyDecoder>::from_pb"

/-- Stack budget of `<PolyDecoder>::from_pb` (`1056 + allocHookStack`, matching `encoderFromPbStack`). -/
abbrev decoderFromPbStack : Nat := encoderFromPbStack

/-- Total version of `PolyDecoder.pushChunksExact4` on 4-byte-aligned byte lists. -/
def pushChunksExact4Total : List (BitVec 8) → SortedSetPt → SortedSetPt
  | b0 :: b1 :: b2 :: b3 :: rest, v =>
    let pt : Pt := { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
    let (v', _, _) := v.push pt
    pushChunksExact4Total rest v'
  | _, v => v

theorem pushChunksExact4_eq_ok :
    ∀ (pts : List (BitVec 8)) (v : SortedSetPt),
      pts.length % 4 = 0 →
      PolyDecoder.pushChunksExact4 pts v = .ok (pushChunksExact4Total pts v)
  | [], v, _ => rfl
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h
  | b0 :: b1 :: b2 :: b3 :: rest, v, h => by
    have hrest : rest.length % 4 = 0 := by
      simp only [List.length_cons] at h
      omega
    unfold PolyDecoder.pushChunksExact4 pushChunksExact4Total
    change (do
      let pt ← Pt.deserialize [b0, b1, b2, b3]
      let (v', _, _) := v.push pt
      PolyDecoder.pushChunksExact4 rest v') = _
    have hpt : Pt.deserialize [b0, b1, b2, b3] =
        .ok { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) } := rfl
    rw [hpt]
    exact pushChunksExact4_eq_ok rest (v.push { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }).1 hrest

/-- Total version of `PolyDecoder.decodeDecoderPbPts`. -/
def decodeDecoderPbPtsTotal : List (List (BitVec 8)) → Except PolynomialError (List SortedSetPt)
  | [] => .ok []
  | pts :: rest =>
    if pts.length % 4 != 0 then
      .error .serializationInvalid
    else
      let v := pushChunksExact4Total pts (SortedSetPt.withCapacity (pts.length / 4))
      match decodeDecoderPbPtsTotal rest with
      | .error e => .error e
      | .ok tail => .ok (v :: tail)

theorem decodeDecoderPbPts_eq_ok (bss : List (List (BitVec 8))) :
    PolyDecoder.decodeDecoderPbPts bss = .ok (decodeDecoderPbPtsTotal bss) := by
  induction bss with
  | nil => rfl
  | cons pts rest ih =>
    unfold PolyDecoder.decodeDecoderPbPts decodeDecoderPbPtsTotal
    by_cases hmod : (pts.length % 4 != 0) = true
    · simp [hmod, pure, Except.pure]
    · have hdiv4 : pts.length % 4 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hmod
        exact hmod
      simp only [hmod, Bool.false_eq_true, ↓reduceIte,
        pushChunksExact4_eq_ok pts (SortedSetPt.withCapacity (pts.length / 4)) hdiv4,
        ih, bind, Except.bind, pure, Except.pure]
      cases decodeDecoderPbPtsTotal rest <;> rfl

/-- Total result of `PolyDecoder.fromPb pb`. -/
def decoderFromPbResult (pb : ProtoPolynomialDecoder) : Except PolynomialError PolyDecoder :=
  if pb.pts.length != 16 then
    .error .serializationInvalid
  else
    match decodeDecoderPbPtsTotal pb.pts with
    | .error e => .error e
    | .ok outPts =>
      .ok
        { ptsNeeded := pb.ptsNeeded.toNat
          isComplete := pb.isComplete
          pts := outPts }

theorem decoderFromPb_eq_ok (pb : ProtoPolynomialDecoder) :
    PolyDecoder.fromPb pb = .ok (decoderFromPbResult pb) := by
  unfold PolyDecoder.fromPb decoderFromPbResult
  by_cases hlen : (pb.pts.length != 16) = true
  · simp [hlen, pure, Except.pure]
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte,
      decodeDecoderPbPts_eq_ok pb.pts, bind, Except.bind, pure, Except.pure]
    cases decodeDecoderPbPtsTotal pb.pts <;> rfl

@[simp]
theorem encoderFromPbStateDecode_none :
    encoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl

@[simp]
theorem encoderFromPbStateDecode_some (pb : PolynomialEncoder) :
    encoderFromPbStateDecode spqrPolyApi (some pb) =
      match fromPbResult (pbToProtoPolyEncoder pb) with
      | .ok enc => .ok enc
      | .error _ => .error (.err .stateDecode) := by
  unfold encoderFromPbStateDecode spqrPolyApi
  dsimp only
  rw [fromPb_eq_ok (pbToProtoPolyEncoder pb)]
  cases fromPbResult (pbToProtoPolyEncoder pb) <;> rfl

@[simp]
theorem decoderFromPbStateDecode_none :
    decoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl

@[simp]
theorem decoderFromPbStateDecode_some (pb : PolynomialDecoder) :
    decoderFromPbStateDecode spqrPolyApi (some pb) =
      match decoderFromPbResult (pbToProtoPolyDecoder pb) with
      | .ok dec => .ok dec
      | .error _ => .error (.err .stateDecode) := by
  unfold decoderFromPbStateDecode spqrPolyApi
  dsimp only
  rw [decoderFromPb_eq_ok (pbToProtoPolyDecoder pb)]
  cases decoderFromPbResult (pbToProtoPolyDecoder pb) <;> rfl

/-- Ghost arguments of `<PolyDecoder>::from_pb` (`0x62b1c`). -/
structure DecoderFromPbGhost where
  /-- Sret pointer (`x0`, 400-byte `Result<PolyDecoder, PolynomialError>` output). -/
  out : BitVec 64
  /-- Pointer to the 40-byte `ProtoPolynomialDecoder` moved by value (`x1`). -/
  pbA : BitVec 64
  /-- Logical `ProtoPolynomialDecoder` value at `pbA`. -/
  pb : ProtoPolynomialDecoder

/-- Specification of `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`, 325 insns). -/
def decoderFromPbSpec (A : RustAlloc) : Spec DecoderFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp decoderFromPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyDecoderFromPbAt A x.out (decoderFromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool ∗ stackAt s0.sp decoderFromPbStack
  onPanic := fun _ s0 sf => encoderFromPbOnPanic s0 sf

/-- `<PolyDecoder>::from_pb` meets `decoderFromPbSpec A` on `tripleRatchetProgAtExt b ext`. -/
def DecoderFromPbOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decoderFromPbName)
    (decoderFromPbSpec A)

/-! ## 3. Top-Level Specification of `<spqr::v1::chunked::states::States>::from_pb` (`0x5a0a4`) -/

/-- Point-slice length bound required by `<PolyEncoder>::from_pb` (`encoderFromPbSpec`). -/
def optEncoderPtsBound : Option PolynomialEncoder → Prop
  | none => True
  | some enc => ∀ bs ∈ enc.pts, bs.length ≤ 2 * 0x0555555555555555

/-- Point-slice length bound on any `PolynomialEncoder` inside a `V1State`. -/
def v1StatePtsBound (pb : V1State) : Prop :=
  match pb.innerState with
  | some (.keysSampled s) => optEncoderPtsBound s.sendingHdr
  | some (.headerSent s) => optEncoderPtsBound s.sendingEk
  | some (.ct1Received s) => optEncoderPtsBound s.sendingEk
  | some (.ct1Sampled s) => optEncoderPtsBound s.sendingCt1
  | some (.ekReceivedCt1Sampled s) => optEncoderPtsBound s.sendingCt1
  | some (.ct2Sampled s) => optEncoderPtsBound s.sendingCt2
  | _ => True

/-- Own stack frame of `<States>::from_pb` (`96 + 2304 = 2400` bytes = `0x960`). -/
abbrev statesFromPbFrame : Nat := 2400

/-- Stack budget of `<States>::from_pb` (`2400 + encoderFromPbStack = 3456 + allocHookStack`). -/
abbrev statesFromPbStack : Nat := statesFromPbFrame + encoderFromPbStack

/-- Extended-stack budget of `<States>::from_pb` (`2400 + extHookStack`). -/
abbrev statesFromPbStackX : Nat := statesFromPbFrame + extHookStack

/-- Ghost arguments of `<spqr::v1::chunked::states::States>::from_pb` (`0x5a0a4`). -/
structure StatesFromPbGhost where
  /-- Indirect return pointer (`x8`, 928-byte `Result<States, spqr::Error>` output). -/
  out : BitVec 64
  /-- Pointer to consumed 224-byte `V1State` (`x0`). -/
  pbA : BitVec 64
  /-- Logical `V1State` value at `pbA`. -/
  pb : V1State

/-- Panic postcondition of `<States>::from_pb`: heap allocation failure (`allocFailedIn`). -/
def statesFromPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Specification of `<spqr::v1::chunked::states::States>::from_pb` (`0x5a0a4..0x5ce20`, 2,911 insns):
    * Registers: `x8 = out` (928-byte `Result<States, Error>` indirect result), `x0 = pbA` (224-byte `V1State`).
    * Consumes `optProtoInnerStateAt A pbA pb.innerState` (leaving `memRegion pbA 224`) and writes
      `resultChunkedStatesAt A out (States.from_pb spqrPolyApi (spqrAuthApi F) pb)` at `out`,
      or panics with `allocFailedEvent` on heap allocation failure. -/
def statesFromPbSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) : Spec StatesFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      b &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound x.pb⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A x.pbA x.pb.innerState ∗
      statesFromPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp statesFromPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesFromPbStack
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- Per-variant specification of `0x5a0a4` (`States::from_pb`) for a fixed `pb : V1State`. -/
def statesFromPbVariantSpec (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (pb : V1State) : Spec (BitVec 64 × BitVec 64) where
  pre := fun ⟨out, pbA⟩ s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = pbA ∧
      b &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound pb⌝ ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A pbA pb.innerState ∗
      statesFromPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp statesFromPbStack
  post := fun ⟨out, pbA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
      memRegion pbA optProtoInnerStateSize ∗
      statesFromPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesFromPbStack
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- Extended-stack variant of `statesFromPbSpec`. -/
def statesFromPbSpecX (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) : Spec StatesFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      b &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound x.pb⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A x.pbA x.pb.innerState ∗
      statesFromPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp statesFromPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultChunkedStatesAt A (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp statesFromPbStackX
  onPanic := fun _ s0 sf => statesFromPbOnPanic s0 sf

/-- `<States>::from_pb` meets `statesFromPbSpec A F b` on `tripleRatchetProgAtExt b ext`. -/
def StatesFromPbOkExt (b : BitVec 64) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
    (statesFromPbSpec A F b)

/-- `<States>::from_pb` meets `(statesFromPbSpecX A F img.base).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def StatesFromPbOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr statesFromPbName)
    ((statesFromPbSpecX A F img.base).inImage img)

/-! ## 4. Stack Frame and Saved-Register Helpers (`2400`B frame) -/

/-- Saved callee-saved registers at `[s0.sp - 96 .. s0.sp)` (`12` words = `96` bytes):
    `fp, lr, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19`. -/
def statesFromPbSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_statesFromPb_split_96 (sp : BitVec 64) :
    stackAt sp statesFromPbStack =
      stackAt (sp - 96#64) (encoderFromPbStack + 2304) ∗ cells (sp - 96#64) 12 :=
  ProofLib.stackAt_split_cells sp (encoderFromPbStack + 2304) 12 (by decide)

theorem stackAt_statesFromPb_split_fsp (sp : BitVec 64) :
    stackAt (sp - 96#64) (encoderFromPbStack + 2304) =
      stackAt (sp - 2400#64) encoderFromPbStack ∗ memRegion (sp - 2400#64) 2304 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (encoderFromPbStack + 2304))
    encoderFromPbStack 2304 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (encoderFromPbStack + 2304) =
      (sp - 2400#64) - BitVec.ofNat 64 encoderFromPbStack := by
    change (sp - 96#64) - 7456#64 = (sp - 2400#64) - 5152#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (encoderFromPbStack + 2304) +
      BitVec.ofNat 64 encoderFromPbStack = sp - 2400#64 := by
    change (sp - 96#64) - 7456#64 + 5152#64 = sp - 2400#64
    bv_omega
  rw [h2, h1]

theorem memRegion_2304_split_cell0 (fsp : BitVec 64) :
    memRegion fsp 2304 =
      (∃∗ v0 : BitVec 64, (fsp ↦₆₄ v0)) ∗ memRegion (fsp + 8#64) 2296 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide),
      ProofLib.memRegion_eight fsp]

theorem cell0_2296_entails_memRegion_2304 (fsp v0 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗ memRegion (fsp + 8#64) 2296 ⊢ memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion fsp v0)

theorem statesFromPbSavedCells_entails_cells12 (s0 : State) :
    statesFromPbSavedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold statesFromPbSavedCells
  cells_unfold
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))))

theorem stack_restore_statesFromPb (s0 : State) :
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ⊢
      stackAt s0.sp statesFromPbStack := by
  rw [stackAt_statesFromPb_split_96 s0.sp, stackAt_statesFromPb_split_fsp s0.sp, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (statesFromPbSavedCells_entails_cells12 s0))

@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_2304 (sp : BitVec 64) : (sp - 96#64) - 2304#64 = sp - 2400#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_2400_add_2304 (sp : BitVec 64) : (sp - 2400#64) + 2304#64 = sp - 96#64 := by bv_omega

/-- Combined trace and callee-saved SIMD register preservation from `s0` to `s`. -/
abbrev TraceCalleeSaved (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem _root_.And.trans {α β : Type _} {a1 a2 a3 : α} {b1 b2 b3 : β}
    (h1 : a1 = a2 ∧ b1 = b2) (h2 : a2 = a3 ∧ b2 = b3) :
    a1 = a3 ∧ b1 = b3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-! ## 5. Prologue (`+0 -> +36`), Epilogue (`+64 -> +92`), and `None` Path (`0x5a0a4`) -/

/-- Prologue (`+0 -> +36`, `0x5a0a4 -> 0x5a0c8`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96` and `sp = s0.sp - 2400`,
    and stores `0#64` at `[sp, #0]`. -/
theorem states_from_pb_prologue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 36#64) s0
      (stackAt s0.sp statesFromPbStack ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
          memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
          statesFromPbSavedCells s0 ∗ Rest) ∧
        s1.sp = s0.sp - 2400#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x8 = out ∧
        s1.readReg64 .x0 = pbA ∧
        TraceCalleeSaved s1 s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 0 36
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rw [stackAt_statesFromPb_split_96 s0.sp, stackAt_statesFromPb_split_fsp s0.sp,
      memRegion_2304_split_cell0 (s0.sp - 2400#64)]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro w4
  apply ProofLib.SepWP.exists_left; intro w5
  apply ProofLib.SepWP.exists_left; intro w6
  apply ProofLib.SepWP.exists_left; intro w7
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w9
  apply ProofLib.SepWP.exists_left; intro w10
  apply ProofLib.SepWP.exists_left; intro w11
  apply ProofLib.SepWP.exists_left; intro v_fsp0
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · unfold statesFromPbSavedCells
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Epilogue (`+64 -> s0.lr`, `0x5a0e4 -> 0x5a100`):
    adds `2304` to `sp`, restores `x19..x30` from `s0.sp - 96`, and executes `ret`. -/
theorem states_from_pb_epilogue_64 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_from_pb_fetches_range b (Rust.withPanics ext) 64 32
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  unfold statesFromPbSavedCells
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hrest := stack_restore_statesFromPb s0
    unfold statesFromPbSavedCells at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest by ac_rfl))
      (sepConj_mono_left hrest)
  · wp_done

/-- `None` error path (`+36 -> s0.lr`, `0x5a0c8..0x5a100`):
    when `pb.innerState = none`, `[pbA] = none2Cap` (`-2`), so `cmn x9, #2` is equal and
    `+52..+60` writes `Err(Error::StateDecode)` (`noneCap` at `[out]`, `0#8` at `[out + 8]`)
    and returns via `+64..+92`. -/
theorem states_from_pb_none_step {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htrace1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA none ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htrace1 with ⟨htrace1, hvregs1⟩
  have hnone_pb : optProtoInnerStateAt A pbA none =
      ((pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216) := rfl
  rw [hnone_pb, memRegion_out_928_split_err out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b_out8
  apply ProofLib.SepWP.exists_left; intro v_out0
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (resultChunkedStatesAt A (F := F) out
        (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
       memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTableAt b ∗
       A.pool))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 36 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [States.from_pb, resultChunkedStatesAt, spqrErrorByte, optProtoInnerStateSize]
      have hpb : (pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216 ⊢ memRegion pbA 224 := by
        rw [ProofLib.memRegion_split pbA 8 216 (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA none2Cap)
      have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
          ((pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ 18446744073709551615#64) ∗
           ((out + 8#64) ↦₈ 0#8) ∗
           memRegion (out + 9#64) 919 ∗
           statesFromPbJumpTableAt b ∗
           A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hfsp (sepConj_mono_left hpb)) ?_
      unfold noneCap
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2⟩
    have hep := states_from_pb_epilogue_64 s0 s2
      (resultChunkedStatesAt A (F := F) out
        (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
       memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTableAt b ∗
       A.pool)
      hsp0_align hpc2 hrun2 hsp2 htr2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for `statesFromPbVariantSpec`. -/
theorem sepWPp_of_states_exit {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantSpec A F b pb).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantSpec A F b pb).onPanic (out, pbA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesFromPbVariantSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

/-- `subroutine_ok` for the `None` variant (`pb = { innerState := none }`). -/
theorem states_from_pb_none_ok_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := none }) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesFromPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, _⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA none ∗
       statesFromPbJumpTableAt b ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue (b := b) (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA none ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  have hnone := states_from_pb_none_step (A := A) (F := F) s0 s1 out pbA
    hsp0_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  exact sepWPp_of_states_exit s0 s1 out pbA { innerState := none } _ R hnone

end CryptoVerification.SpqrV1.States.FromPb
