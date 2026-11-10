/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) — Part D

Entry exposure, dispatch with `x9`, early error paths (`+1056 -> +1080/+3480 -> +4528 -> +4632`),
and `<Ct1Sent>::from_pb` phase (`+3480 -> +3548 -> +3576..+3648` and `Err` at `+3552 -> +5444`)
for Variant 7 (`InnerState.ct1Sampled`, jump-table target `+1056`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. Dispatch (`+36 -> +1056`) with `x9` and `Ct1Sampled` Input Decomposition -/

/-- Jump-table dispatch (`+36 -> +1056`, `0x5a0c8..0x5a140`) for the niche-encoded `Ct1Sampled`
variant, additionally recording `sm.readReg64 .x9 = w0` (loaded by `ldr x9, [x0]` at `+40`). -/
theorem v7_dispatch_ct1Sampled
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗
        statesFromPbJumpTableAt b ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTableAt b ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0) := by
  have hadrp := fnAddr_adrp_5a120 (b := b) (H := Rust.withPanics ext) hb
  rw [statesFromPbJumpTableAt_eq b]
  states_from_pb_fetches_range b (Rust.withPanics ext) 36 120
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, statesFromPbJumpTableBytesAt,
    BitVec.ofNat_eq_ofNat] at hadrp hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases hw0 with rfl | hlt
  · dsimp only [noneCap]
    wp_steps; wp_done
  · have hne2 := cap_add_two_beq_zero_false hlt
    have hcc := cap_xor_highBit_cc_11_false hlt
    wp_steps; wp_done

/-- Isomorphism between `V1State.Unchunked.Ct1Sent` and `V1State.Unchunked.Ct1SentEkReceived`
at the proto layout level (five 24-byte `Vec<u8>` fields + `u64 epoch`). -/
def v7_ct1SentToCt1SentEkReceived (st : V1State.Unchunked.Ct1Sent) :
    V1State.Unchunked.Ct1SentEkReceived :=
  { es := st.hdr, ek := st.es, ct1 := st.ct1, auth := st.auth, epoch := st.epoch }

theorem v7_protoUnchunkedCt1SentAt_eq (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentAt A a st =
      protoUnchunkedCt1SentEkReceivedAt A a (v7_ct1SentToCt1SentEkReceived st) := rfl

/-- Tail of `optProtoUnchunkedCt1SentAt A pbA optUc` after exposing `(pbA ↦₆₄ w0)`. -/
def v7_optProtoUnchunkedCt1SentTail (A : RustAlloc) (pbA w0 : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) : SepProp :=
  match optUc with
  | none => memRegion (pbA + 8#64) 120
  | some uc =>
    ∃∗ ptr : BitVec 64,
      protoUnchunkedCt1SentEkReceivedRestAt A pbA w0 ptr
        (v7_ct1SentToCt1SentEkReceived uc)

def v7_optUcCapProp (w0 : BitVec 64) (optUc : Option V1State.Unchunked.Ct1Sent) : Prop :=
  match optUc with
  | none => w0 = noneCap
  | some _ => w0.toNat < 2 ^ 63

theorem v7_optUcCapProp_imp_or {w0 : BitVec 64} {optUc : Option V1State.Unchunked.Ct1Sent}
    (h : v7_optUcCapProp w0 optUc) : w0 = noneCap ∨ w0.toNat < 2 ^ 63 := by
  cases optUc with
  | none => exact Or.inl h
  | some _ => exact Or.inr h

theorem v7_optProtoUnchunkedCt1Sent_expose_w0 (A : RustAlloc) (pbA : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) :
    optProtoUnchunkedCt1SentAt A pbA optUc ⊢
      ∃∗ w0 : BitVec 64,
        ⌜v7_optUcCapProp w0 optUc⌝ ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUc) := by
  cases optUc with
  | none =>
    rw [optProtoUnchunkedCt1SentAt_none]
    dsimp only [v7_optProtoUnchunkedCt1SentTail, v7_optUcCapProp]
    refine Entails.sepExists_right noneCap ?_
    exact Entails.pure_right rfl (Entails.refl _)
  | some uc =>
    rw [optProtoUnchunkedCt1SentAt_some, v7_protoUnchunkedCt1SentAt_eq]
    refine Entails.trans
      (protoUnchunkedCt1SentEkReceivedAt_expose_cap A pbA (v7_ct1SentToCt1SentEkReceived uc)) ?_
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    apply Entails.pure_left; intro hlt
    dsimp only [v7_optProtoUnchunkedCt1SentTail, v7_optUcCapProp]
    refine Entails.sepExists_right cap ?_
    refine Entails.pure_right hlt ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_right ptr ?_
    exact Entails.of_eq (by ac_rfl)

theorem v7_optProtoUnchunkedCt1Sent_unexpose_some (A : RustAlloc) (pbA w0 : BitVec 64)
    (uc : V1State.Unchunked.Ct1Sent) :
    (pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 (some uc) ⊢
      protoUnchunkedCt1SentAt A pbA uc := by
  dsimp only [v7_optProtoUnchunkedCt1SentTail]
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  rw [v7_protoUnchunkedCt1SentAt_eq]
  exact protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A pbA w0 ptr
    (v7_ct1SentToCt1SentEkReceived uc)

theorem v7_optProtoUnchunkedCt1Sent_unexpose_none (pbA : BitVec 64) :
    (pbA ↦₆₄ noneCap) ∗ memRegion (pbA + 8#64) 120 ⊢
      memRegion pbA 128 := by
  rw [ProofLib.memRegion_split pbA 8 120 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA noneCap)

/-! ## 2. Pure Model Reduction Lemmas for `InnerState.ct1Sampled` -/

theorem v7_ptsNeeded_check_eq (ptsNeeded : BitVec 32) :
    (ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = !(ptsNeeded == 576#32) := by
  have h576 : ENCAPSULATION_KEY_SIZE / 2 = (576#32).toNat := rfl
  rw [h576]
  cases h : ptsNeeded == 576#32 <;> simp only [Bool.not_true, Bool.not_false]
  · rw [beq_eq_false_iff_ne] at h
    rw [bne_iff_ne, ne_eq, BitVec.toNat_inj]
    exact h
  · rw [beq_iff_eq] at h
    subst h
    decide

theorem v7_from_pb_ct1Sampled_bad_pts (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (d : PolynomialDecoder)
    (hd : s.receivingEk = some d)
    (hpts : (d.ptsNeeded == 576#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .msgDecode) := by
  have hne : (d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = true := by
    rw [v7_ptsNeeded_check_eq, hpts]; rfl
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hd, hne, ↓reduceIte, Bind.bind, Except.bind, Functor.map, Except.map]

def v7_receivingEkPtsOk (optDecPb : Option PolynomialDecoder) : Prop :=
  match optDecPb with
  | none => True
  | some d => (d.ptsNeeded == 576#32) = true

theorem v7_receivingEk_pts_false {d : PolynomialDecoder}
    (hok : (d.ptsNeeded == 576#32) = true) :
    (d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = false := by
  rw [v7_ptsNeeded_check_eq, hok]; rfl

theorem v7_from_pb_ct1Sampled_uc_none (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_uc_err (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent) (err : Error)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = some u)
    (herr : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .error (.err err)) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err err) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, herr, Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, herr, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_enc_none (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, huc_ok, henc, encoderFromPbStateDecode_none,
      Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, huc_ok, henc, encoderFromPbStateDecode_none,
      Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_enc_err (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (e : PolynomialError)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_err : fromPbResult (pbToProtoPolyEncoder encPb) = .error e) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_err,
      Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_err,
      Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_dec_none (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (enc : PolyEncoder)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_ok : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc)
    (hdec : s.receivingEk = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hdec, huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_ok,
    decoderFromPbStateDecode_none, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_dec_err (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (enc : PolyEncoder)
    (decPb : PolynomialDecoder) (e : PolynomialError)
    (hpts : (decPb.ptsNeeded == 576#32) = true)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_ok : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc)
    (hdec : s.receivingEk = some decPb)
    (hdec_err : decoderFromPbResult (pbToProtoPolyDecoder decPb) = .error e) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
    huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_ok,
    decoderFromPbStateDecode_some, hdec_err,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_ok (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (enc : PolyEncoder)
    (decPb : PolynomialDecoder) (dec : PolyDecoder)
    (hpts : (decPb.ptsNeeded == 576#32) = true)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_ok : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc)
    (hdec : s.receivingEk = some decPb)
    (hdec_ok : decoderFromPbResult (pbToProtoPolyDecoder decPb) = .ok dec) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .ok (.ct1Sampled { uc := uc, sending_ct1 := enc, receiving_ek := dec }) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
    huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_ok,
    decoderFromPbStateDecode_some, hdec_ok,
    Bind.bind, Except.bind, Functor.map, Except.map]

/-! ## 3. Entry `ptsNeeded` Check (`+1056 -> +3480` and `+1056 -> +4632`) -/

def v7_optProtoPolyDecoderTailWithoutPts (A : RustAlloc) (d cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) : SepProp :=
  ∃∗ ptr : BitVec 64,
    ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
       memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
         ((cap.toNat - pb.pts.length) * 24)) ∗
    ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
    ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
    memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize

theorem v7_optProtoPolyDecoderTail_expose_pts (A : RustAlloc) (pbA cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    v7_optProtoPolyDecoderTail A (pbA + 184#64) cap (some pb) ⊢
      ((pbA + 208#64) ↦₃₂ pb.ptsNeeded) ∗
      v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap pb := by
  unfold v7_optProtoPolyDecoderTail v7_optProtoPolyDecoderTailWithoutPts
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have h208 : (pbA + 184#64) + protoPolynomialDecoderPtsNeededOff = pbA + 208#64 := by
    dsimp only [protoPolynomialDecoderPtsNeededOff]; bv_omega
  rw [h208]
  exact Entails.of_eq (by ac_rfl)

theorem v7_optProtoPolyDecoderTail_unexpose_pts (A : RustAlloc) (pbA cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    ((pbA + 208#64) ↦₃₂ pb.ptsNeeded) ∗
      v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap pb ⊢
      v7_optProtoPolyDecoderTail A (pbA + 184#64) cap (some pb) := by
  unfold v7_optProtoPolyDecoderTail v7_optProtoPolyDecoderTailWithoutPts
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have h208 : (pbA + 184#64) + protoPolynomialDecoderPtsNeededOff = pbA + 208#64 := by
    dsimp only [protoPolynomialDecoderPtsNeededOff]; bv_omega
  rw [h208]
  exact Entails.of_eq (by ac_rfl)

@[local simp, local arm64_norm]
theorem v7_ptsNeeded_sub_576_beq_zero {pts : BitVec 32} (h : (pts == 576#32) = false) :
    (pts - 576#32 == 0#32) = false := by
  cases h2 : pts - 576#32 == 0#32
  · rfl
  · exfalso
    have heq : pts = 576#32 := by
      have h0 := beq_iff_eq.mp h2
      bv_omega
    subst heq
    exact Bool.noConfusion h

/-- Entry `ptsNeeded` check (`+1056 -> +3480`) when `v7_receivingEkPtsOk s.receivingEk` holds:
loads `x22 = cap_dec` from `[pbA + 184]` and branches to `+3480` either because `cap_dec = noneCap`
(`s.receivingEk = none`) or because `d.ptsNeeded == 576#32` (`s.receivingEk = some d`). -/
theorem v7_entry_1056_to_3480
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA c1 w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hpts : v7_receivingEkPtsOk optDecPb)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x0)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3480#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = s0.readReg64 .x0 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  cases optDecPb with
  | none =>
    simp only [Option.map_none, v7_optDecoderCapProp] at hcap_dec
    subst hcap_dec
    states_from_pb_fetches_range b (Rust.withPanics ext) 1056 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, Option.map_none, noneCap,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
    wp_done
  | some d =>
    simp only [Option.map_some, v7_optDecoderCapProp] at hcap_dec
    unfold v7_receivingEkPtsOk at hpts
    have hd_pts : (pbToProtoPolyDecoder d).ptsNeeded = 576#32 := by
      change d.ptsNeeded = 576#32
      exact beq_iff_eq.mp hpts
    have hne := v4_ptsCap_add_one_ne_zero hcap_dec
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left
        (v7_optProtoPolyDecoderTail_expose_pts A pbA cap_dec (pbToProtoPolyDecoder d)))) ?_
    rw [hd_pts]
    states_from_pb_fetches_range b (Rust.withPanics ext) 1056 24
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, Option.map_some,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hun := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
      rw [hd_pts] at hun
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA + 184#64) ↦₆₄ cap_dec) ∗
          (((pbA + 208#64) ↦₃₂ 576#32) ∗
           v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
          Frame by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hun)
    · wp_done

/-- Helper for `+1092 -> +1096` (`bl 0x4ce90`): calls `drop_glue::<ProtoUnchunkedCt1SentEkReceived>`
    with `x0 = pbA`. -/
theorem v7_call_drop_proto_unchunked_ct1_sent_1092
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1092#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1096#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoUnchunkedCt1SentEkReceivedAt A pbA (v7_ct1SentToCt1SentEkReceived u) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 128 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received hA
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
  states_from_pb_fetches_range b (Rust.withPanics ext) 1092 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoUnchunkedCt1SentEkReceivedSize,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        (memRegion pbA 128 ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

/-- Bad `ptsNeeded` path (`+1056 -> +1080 -> +4528 -> +4632`):
when `s.receivingEk = some d` and `(d.ptsNeeded == 576#32) = false`, drops `s.uc` (if `some`),
sets `w28 = 2` (`.msgDecode`), drops `s.sendingCt1` and `s.receivingEk` via `+4528`,
and reaches `+4632` with `memRegion pbA 224`. -/
theorem v7_entry_bad_pts_1056_to_4632
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA w0 cap_dec : BitVec 64)
    (optUcPb : Option V1State.Unchunked.Ct1Sent)
    (optEncPb : Option PolynomialEncoder)
    (d : PolynomialDecoder) (Frame : SepProp)
    (hcap_uc : v7_optUcCapProp w0 optUcPb)
    (hcap_dec : v7_optDecoderCapProp cap_dec (some (pbToProtoPolyDecoder d)))
    (hpts : (d.ptsNeeded == 576#32) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUcPb) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 2#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4528#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
      A.pool ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 2#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have hne_dec := v4_ptsCap_add_one_ne_zero hcap_dec
    have hpts' : ((pbToProtoPolyDecoder d).ptsNeeded == 576#32) = false := hpts
    have hpts_sub := v7_ptsNeeded_sub_576_beq_zero hpts'
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUcPb) ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           ((pbA + 184#64) ↦₆₄ cap_dec) ∗
           A.pool ∗ Frame) by ac_rfl))
        (sepConj_mono_left
          (v7_optProtoPolyDecoderTail_expose_pts A pbA cap_dec (pbToProtoPolyDecoder d)))) ?_
    cases optUcPb with
    | none =>
      unfold v7_optUcCapProp at hcap_uc
      subst hcap_uc
      dsimp only [v7_optProtoUnchunkedCt1SentTail]
      states_from_pb_fetches_range b (Rust.withPanics ext) 1056 48
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap,
        BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hun_dec := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
        have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
        dsimp only [noneCap] at hun_uc
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
             v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
            ((pbA ↦₆₄ 18446744073709551615#64) ∗ memRegion (pbA + 8#64) 120) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             ((pbA + 184#64) ↦₆₄ cap_dec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
          (Entails.of_eq (by ac_rfl))
      · wp_done
    | some u =>
      unfold v7_optUcCapProp at hcap_uc
      have hne_uc := cap_add_one_beq_zero_false hcap_uc
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1092#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoUnchunkedCt1SentEkReceivedAt A pbA (v7_ct1SentToCt1SentEkReceived u) ∗
          A.pool ∗
          (optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 1056 36
        dsimp only [tripleRatchetProgAtExt, statesFromPbName,
          BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hun_dec := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
          have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_some A pbA w0 u
          rw [v7_protoUnchunkedCt1SentAt_eq] at hun_uc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
               v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
              ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 (some u)) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
               ((pbA + 184#64) ↦₆₄ cap_dec) ∗
               Frame) by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
            (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, htr2⟩
        refine EncoderFromPb.seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1096#64)
          (P_mid :=
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion pbA 128 ∗
            A.pool ∗
            (optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
             Frame))
          (Q := fun sm =>
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x22 = cap_dec ∧
            sm.readReg64 .x27 = pbA ∧
            TraceCalleeSaved sm s0)
          (v7_call_drop_proto_unchunked_ct1_sent_1092 hA s0 s2 out pbA cap_dec u _
            hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 htr2)
          ?_
        intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
        states_from_pb_fetches_range b (Rust.withPanics ext) 1096 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName,
          BitVec.ofNat_eq_ofNat] at hpc3 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
        wp_done
  · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx22_4, hx27_4, hx28_4, htr4⟩
    refine SepWP.mono
      (v7_cleanup_4528 hA s0 s4 out pbA cap_dec 2#64
        (optEncPb.map pbToProtoPolyEncoder) (some (pbToProtoPolyDecoder d))
        (memRegion pbA 128 ∗ Frame)
        hcap_dec hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx27_4 hx28_4 htr4)
      ?_
    intro sm Pm _ _ ⟨hPm, hq⟩
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by ac_rfl)

/-! ## 4. `<Ct1Sent>::from_pb` Phase (`+3480 -> +3648` and Error Exits) -/

/-- `s.uc = none` error path at `+3480 -> +4524 -> +4528 -> +4632`:
when `w0 = noneCap` (`x9 = noneCap`), `+3480..+3484` branches to `+4524`, sets `w28 = 0`,
and runs `v7_cleanup_4528` to reach `+4632` with `memRegion pbA 224`. -/
theorem v7_uc_none_3480_to_4632
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optEncPb : Option PolynomialEncoder)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ noneCap) ∗ v7_optProtoUnchunkedCt1SentTail A pbA noneCap none) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4528#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
      A.pool ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 0#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [v7_optProtoUnchunkedCt1SentTail]
    states_from_pb_fetches_range b (Rust.withPanics ext) 3480 8
    states_from_pb_fetches_range b (Rust.withPanics ext) 4524 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap,
      BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
      dsimp only [noneCap] at hun_uc
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 18446744073709551615#64) ∗ memRegion (pbA + 8#64) 120) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
           A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hun_uc) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    refine SepWP.mono
      (v7_cleanup_4528 hA s0 s2 out pbA cap_dec 0#64
        (optEncPb.map pbToProtoPolyEncoder) (optDecPb.map pbToProtoPolyDecoder)
        (memRegion pbA 128 ∗ Frame)
        hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2)
      ?_
    intro sm Pm _ _ ⟨hPm, hq⟩
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
