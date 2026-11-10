/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7j
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) Part K

Proves the encoder/decoder stage compositions (`+3720`, `+7348`, `+7404`) and discharges
`V7Ok7404Prop` from `v7_dec_ok_7404_to_ret`.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_memset
  stubOff_handle_error
  fnOff_ct1_sent_from_pb
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb

/-! ## 1. Stack Frame Splitting Helpers -/

theorem v7_stackAt_encoderFromPbStack_to_ct1SentFromPbStack (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 := by
  have h := ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack 816 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 816 ∗ stackAt fsp ct1SentFromPbStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_ct1SentFromPbStack_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack 816 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 816 ∗ stackAt fsp ct1SentFromPbStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_memRegion_2304_split_uc (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 240 ∗
      memRegion (fsp + 240#64) 128 ∗
      memRegion (fsp + 368#64) 1520 ∗
      memRegion (fsp + 1888#64) 128 ∗
      memRegion (fsp + 2016#64) 288 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    Entails.refl _

theorem v7_memRegion_2304_unsplit_uc (fsp : BitVec 64) :
    memRegion fsp 240 ∗
    memRegion (fsp + 240#64) 128 ∗
    memRegion (fsp + 368#64) 1520 ∗
    memRegion (fsp + 1888#64) 128 ∗
    memRegion (fsp + 2016#64) 288 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v7_memRegion_uc_rest_to_1888 (fsp : BitVec 64) :
    memRegion fsp 240 ∗
    memRegion (fsp + 240#64) 128 ∗
    memRegion (fsp + 368#64) 1520 ⊢
      memRegion fsp 1888 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

def v7_stackGapsEncDec (fsp : BitVec 64) : SepProp :=
  memRegion fsp 16 ∗
  memRegion (fsp + 32#64) 168 ∗
  memRegion (fsp + 208#64) 688 ∗
  memRegion (fsp + 952#64) 312 ∗
  memRegion (fsp + 2288#64) 16

theorem v7_memRegion_1888_288_split_encDec (fsp : BitVec 64) :
    memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ⊢
      (∃∗ slot16 : BitVec 64, (fsp + 16#64) ↦₆₄ slot16) ∗
      (∃∗ slot24 : BitVec 64, (fsp + 24#64) ↦₆₄ slot24) ∗
      (∃∗ slot200 : BitVec 64, (fsp + 200#64) ↦₆₄ slot200) ∗
      memRegion (fsp + 896#64) 56 ∗
      memRegion (fsp + 1264#64) 128 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 2016#64) 272 ∗
      v7_stackGapsEncDec fsp := by
  have h1888 : memRegion fsp 1888 ⊢
      memRegion fsp 16 ∗
      (∃∗ slot16 : BitVec 64, (fsp + 16#64) ↦₆₄ slot16) ∗
      (∃∗ slot24 : BitVec 64, (fsp + 24#64) ↦₆₄ slot24) ∗
      memRegion (fsp + 32#64) 168 ∗
      (∃∗ slot200 : BitVec 64, (fsp + 200#64) ↦₆₄ slot200) ∗
      memRegion (fsp + 208#64) 688 ∗
      memRegion (fsp + 896#64) 56 ∗
      memRegion (fsp + 952#64) 312 ∗
      memRegion (fsp + 1264#64) 128 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 := by
    exact split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      Entails.refl _
  have h288 : memRegion (fsp + 2016#64) 288 ⊢
      memRegion (fsp + 2016#64) 272 ∗ memRegion (fsp + 2288#64) 16 := by
    exact split_top <|
      split_step (Entails.refl _) <|
      Entails.refl _
  refine Entails.trans (sepConj_mono h1888 h288) ?_
  unfold v7_stackGapsEncDec
  exact Entails.of_eq (by ac_rfl)

theorem v7_memRegion_1888_128_272_to_400 (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 272 ⊢
      memRegion (fsp + 1888#64) 400 := by
  exact collapse_top <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v7_stackGapsEncDec_unsplit (fsp slot16 slot24 slot200 : BitVec 64) :
    ((fsp + 16#64) ↦₆₄ slot16) ∗
    ((fsp + 24#64) ↦₆₄ slot24) ∗
    ((fsp + 200#64) ↦₆₄ slot200) ∗
    memRegion (fsp + 896#64) 56 ∗
    memRegion (fsp + 1264#64) 128 ∗
    memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 1792#64) 56 ∗
    memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1888#64) 400 ∗
    v7_stackGapsEncDec fsp ⊢
      memRegion fsp 2304 := by
  have hcol :
      memRegion fsp 16 ∗
      ((fsp + 16#64) ↦₆₄ slot16) ∗
      ((fsp + 24#64) ↦₆₄ slot24) ∗
      memRegion (fsp + 32#64) 168 ∗
      ((fsp + 200#64) ↦₆₄ slot200) ∗
      memRegion (fsp + 208#64) 688 ∗
      memRegion (fsp + 896#64) 56 ∗
      memRegion (fsp + 952#64) 312 ∗
      memRegion (fsp + 1264#64) 128 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 ⊢
        memRegion fsp 2304 := by
    exact collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  unfold v7_stackGapsEncDec
  refine Entails.trans (Entails.of_eq ?_) hcol
  ac_rfl

theorem v7_pbA_128_56_40_to_224 (pbA : BitVec 64) :
    memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40 ⊢
      memRegion pbA optProtoInnerStateSize := by
  change _ ⊢ memRegion pbA 224
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v7_sepWPp_call_wpp {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => hnext sf hpcf hrunf hspf hcsf)

/-- Compose a `SepWP` reaching `+4632` with `v7_err_4632` and `sepWPp_of_states_exit`. -/
theorem v7_seq_err_4632_wpp
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64) (s : V1State.Chunked.Ct1Sampled)
    (err : LibsignalSpqrV1.Error) (P R : SepProp)
    (hfrom_pb : States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err err))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1 P
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧
        TraceCalleeSaved sm s0)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s1 P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).onPanic (out, pbA) s0 sf ∗ R)) := by
  apply sepWPp_of_states_exit s0 s1 out pbA { innerState := some (.ct1Sampled s) } P R
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTableAt b ∗
       A.pool))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧
      TraceCalleeSaved sm s0)
    (SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)
    ?_
  intro sm hpcm hrunm ⟨hspm, hx19m, hx28m, htrm⟩
  refine SepWP.mono
    (v7_err_4632 (A := A) (F := F) s0 sm out err
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align hpcm hrunm hspm hx19m hx28m htrm) ?_
  intro sf Pf _ _ ⟨hPf, hq⟩
  rw [hfrom_pb]
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hq⟩

/-- Hypothesis for the final `Ok(dec)` success path (`+7404 -> +7520 -> +4500 -> +7088 -> s0.x30`)
of Variant 7 (`InnerState.ct1Sampled`). -/
def V7Ok7404Prop {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (s0 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) : Prop :=
  ∀ (s1 : State) (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (dec : PolyDecoder),
    (s0.sp &&& 15#64 == 0#64) = true →
    c1.toNat < 2 ^ 63 →
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .ok (.ct1Sampled { uc := uc, sending_ct1 := enc, receiving_ek := dec }) →
    s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7404#64 →
    s1.status = .Running →
    s1.sp = s0.sp - 2400#64 →
    s1.readReg64 .x19 = out →
    s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
    s1.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 →
    s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
    s1.readReg64 .x24 = c2 →
    s1.readReg64 .x26 = l1 →
    s1.readReg64 .x27 = pbA →
    TraceCalleeSaved s1 s0 →
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.ok dec) ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)

/-- Stage at `+7404` after `<PolyDecoder>::from_pb` returns. -/
theorem v7_after_dec_call_7404
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (e : PolynomialEncoder) (enc : PolyEncoder)
    (d : PolynomialDecoder) (R : SepProp)
    (h7404_ok : V7Ok7404Prop (A := A) (F := F) (b := b) (ext := ext) s0 out pbA s)
    (hpts : (d.ptsNeeded == 576#32) = true)
    (hs_uc : s.uc = some u)
    (huc : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (hs_enc : s.sendingCt1 = some e)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    (hs_dec : s.receivingEk = some d)
    (hc1 : c1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
          (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).onPanic (out, pbA) s0 sf ∗ R)) := by
  cases hdec : decoderFromPbResult (pbToProtoPolyDecoder d) with
  | error err =>
    have hfrom_pb := v7_from_pb_ct1Sampled_dec_err F s u uc e enc d err
      hpts hs_uc huc hs_enc henc hs_dec hdec
    apply v7_seq_err_4632_wpp s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (v7_dec_err_7404_to_4632 hA s0 s1 out c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
          uc enc err
          ((((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTableAt b)
          hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1) ?_)
    intro sm Pm _ _ ⟨hPm, hspm, hx19m, hx28m, htrm⟩
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    refine ⟨Entails.trans hPm ?_, hspm, hx19m, hx28_b, htrm⟩
    have hunsplit := v7_stackGapsEncDec_unsplit (s0.sp - 2400#64) (v7_polyEncoderTag enc) c1 p1
    refine Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       v7_stackGapsEncDec (s0.sp - 2400#64)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTableAt b ∗
       A.pool) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hunsplit) (Entails.of_eq (by ac_rfl))
  | ok dec =>
    have hfrom_pb := v7_from_pb_ct1Sampled_ok F s u uc e enc d dec
      hpts hs_uc huc hs_enc henc hs_dec hdec
    apply sepWPp_of_states_exit s0 s1 out pbA { innerState := some (.ct1Sampled s) } _ R
    exact h7404_ok s1 c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc enc dec
      hsp0_align hc1 hfrom_pb hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1

/-- Stage at `+7348` after `Ok(enc)` has been moved to `fsp + 1392..1792`. -/
theorem v7_after_enc_ok_7348
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec_sub : DecoderFromPbOkExt b A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (e : PolynomialEncoder) (enc : PolyEncoder) (R : SepProp)
    (h7404_ok : V7Ok7404Prop (A := A) (F := F) (b := b) (ext := ext) s0 out pbA s)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (hcap_dec : v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder))
    (hs_uc : s.uc = some u)
    (huc : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (hs_enc : s.sendingCt1 = some e)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    (hc1 : c1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hpstate1 : s1.pstate = addsPState64 cap_dec 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        memRegion (pbA + 128#64) 56 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).onPanic (out, pbA) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases hs_dec : s.receivingEk with
  | none =>
    have hfrom_pb := v7_from_pb_ct1Sampled_dec_none F s u uc e enc hs_uc huc hs_enc henc hs_dec
    rw [hs_dec] at hcap_dec
    dsimp only [Option.map, v7_optDecoderCapProp] at hcap_dec
    subst hcap_dec
    simp only [Option.map]
    apply v7_seq_err_4632_wpp s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (v7_enc_ok_none_dec_7348_to_4632 hA s0 s1 out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
          uc enc
          (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           memRegion (pbA + 128#64) 56 ∗
           statesFromPbJumpTableAt b)
          hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 hpstate1 htr1) ?_)
    intro sm Pm _ _ ⟨hPm, hspm, hx19m, hx28m, htrm⟩
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    refine ⟨Entails.trans hPm ?_, hspm, hx19m, hx28_b, htrm⟩
    have hunsplit := v7_stackGapsEncDec_unsplit (s0.sp - 2400#64) (v7_polyEncoderTag enc) c1 p1
    have hpb224 := v7_pbA_128_56_40_to_224 pbA
    refine Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       v7_stackGapsEncDec (s0.sp - 2400#64)) ∗
      (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTableAt b ∗
       A.pool) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hunsplit (sepConj_mono_left hpb224)) (Entails.of_eq (by ac_rfl))
  | some d =>
    rw [hs_dec] at hcap_dec hpts
    dsimp only [v7_receivingEkPtsOk] at hpts
    dsimp only [Option.map, v7_optDecoderCapProp] at hcap_dec
    simp only [Option.map]
    have hcap_dec_lt : cap_dec.toNat < 2 ^ 63 := by omega
    refine v4_sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
      (P_mid :=
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
         protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
         A.pool ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
        (polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
         v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
         (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
         memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
         v7_stackGapsEncDec (s0.sp - 2400#64) ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTableAt b))
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x1 = (s0.sp - 2400#64) + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
        sm.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7404#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7400#64)
        (P_mid :=
          (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
           protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
           A.pool ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
          (polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
           v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
           v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTableAt b))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x1 = (s0.sp - 2400#64) + 1848#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
          sm.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 ∧
          sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x26 = l1 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (SepWP.mono
            (v7_copy_dec_7348_to_7400 s0 s1 (s0.sp - 2400#64) out pbA cap_dec c2 l1
              ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64)
              (pbToProtoPolyDecoder d)
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
               polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
               v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
               v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
               (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
               (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
               (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
               memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
               memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
               v7_stackGapsEncDec (s0.sp - 2400#64) ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               memRegion pbA 128 ∗
               memRegion (pbA + 128#64) 56 ∗
               statesFromPbJumpTableAt b ∗
               A.pool)
              hfsp_align hcap_dec_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hpstate1 htr1) ?_)
        intro sm Pm _ _ ⟨hPm, hq⟩
        refine ⟨Entails.trans hPm ?_, hq⟩
        have hpb224 := v7_pbA_128_56_40_to_224 pbA
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
          ((memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
            protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1848#64) (pbToProtoPolyDecoder d) ∗
            A.pool ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
           (polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
            v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
            v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
            (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
            (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
            memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
            memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
            v7_stackGapsEncDec (s0.sp - 2400#64) ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            statesFromPbJumpTableAt b)) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpb224) (Entails.of_eq (by ac_rfl))
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
        exact v7_bl_decoder_7400_to_35448 s0 s2 (s0.sp - 2400#64) out pbA c2 l1
          ((s0.sp - 2400#64) + 1392#64) ((s0.sp - 2400#64) + 848#64) _
          hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 htr2
    · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx30_3, htr3⟩
      have halign3 : s3.spAligned = true := by
        unfold State.spAligned; rw [hsp3]; exact hfsp_align
      refine v7_sepWPp_call_wpp (v4_sub_ok_decoder_from_pb hdec_sub)
        (x := ⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 1848#64, pbToProtoPolyDecoder d⟩)
        hpc3 hrun3 halign3 hx30_3
        (fun R' hm => by
          dsimp only [decoderFromPbSpec, polyDecoderSize, decoderFromPbStack]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_3, hx1_3⟩, ?_⟩
          rw [hsp3]
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
        (fun sf => by
          dsimp only [decoderFromPbSpec, statesFromPbVariantSpec]
          exact v4_onPanic_frame_entails htr3)
        (fun _ _ => rfl)
        ?_
      intro s4 hpc4 hrun4 hsp4 hcs4
      have hsp4' : s4.sp = s0.sp - 2400#64 := hsp4.trans hsp3
      have hx19_4 : s4.readReg64 .x19 = out := (hcs4.1).trans hx19_3
      have hx21_4 : s4.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := (hcs4.2.2.1).trans hx21_3
      have hx22_4 : s4.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64 := (hcs4.2.2.2.1).trans hx22_3
      have hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := (hcs4.2.2.2.2.1).trans hx23_3
      have hx24_4 : s4.readReg64 .x24 = c2 := (hcs4.2.2.2.2.2.1).trans hx24_3
      have hx26_4 : s4.readReg64 .x26 = l1 := (hcs4.2.2.2.2.2.2.2.1).trans hx26_3
      have hx27_4 : s4.readReg64 .x27 = pbA := (hcs4.2.2.2.2.2.2.2.2.1).trans hx27_3
      dsimp only [decoderFromPbSpec, protoPolynomialDecoderSize, decoderFromPbStack]
      rw [hsp3]
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ⌜s4.trace = s3.trace⌝ ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
           (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
         polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
         v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
         (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
         memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
         memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
         v7_stackGapsEncDec (s0.sp - 2400#64) ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTableAt b ∗
         A.pool) by ac_rfl)) ?_
      apply SepWPp.pure_elim; intro htr4
      exact v7_after_dec_call_7404 hA s0 s4 out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
        s u uc e enc d R h7404_ok hpts hs_uc huc hs_enc henc hs_dec hc1 hsp0_align
        hpc4 hrun4 hsp4' hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx26_4 hx27_4 ⟨htr4.trans htr3.1, hcs4.2.2.2.2.2.2.2.2.2.2.2.trans htr3.2⟩

/-- Stage at `+3720` after `<PolyEncoder>::from_pb` returns. -/
theorem v7_after_enc_call_3720
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec_sub : DecoderFromPbOkExt b A ext)
    (s0 s1 : State) (out pbA cap_dec slot16 slot200 c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (e : PolynomialEncoder) (R : SepProp)
    (h7404_ok : V7Ok7404Prop (A := A) (F := F) (b := b) (ext := ext) s0 out pbA s)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (hcap_dec : v7_optDecoderCapProp cap_dec (s.receivingEk.map pbToProtoPolyDecoder))
    (hs_uc : s.uc = some u)
    (huc : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (hs_enc : s.sendingCt1 = some e)
    (hc1 : c1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = (s0.sp - 2400#64) + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
          (fromPbResult (pbToProtoPolyEncoder e)) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        memRegion (pbA + 128#64) 56 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantSpec A F b { innerState := some (.ct1Sampled s) }).onPanic (out, pbA) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases henc : fromPbResult (pbToProtoPolyEncoder e) with
  | error err =>
    have hfrom_pb := v7_from_pb_ct1Sampled_enc_err F s u uc e err hpts hs_uc huc hs_enc henc
    apply v7_seq_err_4632_wpp s0 s1 out pbA s .stateDecode _ R hfrom_pb hsp0_align
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (v7_enc_err_3720_to_4632 hA s0 s1 out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
          uc err (s.receivingEk.map pbToProtoPolyDecoder)
          (memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
           (((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
           memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
           memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
           v7_stackGapsEncDec (s0.sp - 2400#64) ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           memRegion pbA 128 ∗
           memRegion (pbA + 128#64) 56 ∗
           statesFromPbJumpTableAt b)
          hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx27_1 hx28_1 htr1) ?_)
    intro sm Pm _ _ ⟨hPm, hspm, hx19m, hx28m, htrm⟩
    have hx28_b : (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx28m]; rfl
    refine ⟨Entails.trans hPm ?_, hspm, hx19m, hx28_b, htrm⟩
    have hunsplit := v7_stackGapsEncDec_unsplit (s0.sp - 2400#64) slot16 c1 slot200
    have hpb224 := v7_pbA_128_56_40_to_224 pbA
    refine Entails.trans (Entails.of_eq (show _ =
      ((((s0.sp - 2400#64) + 16#64) ↦₆₄ slot16) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ slot200) ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       v7_stackGapsEncDec (s0.sp - 2400#64)) ∗
      (memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       statesFromPbJumpTableAt b ∗
       A.pool) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hunsplit (sepConj_mono_left hpb224)) (Entails.of_eq (by ac_rfl))
  | ok enc =>
    refine v4_sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7348#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
        v7_stackGapsEncDec (s0.sp - 2400#64) ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 128 ∗
        memRegion (pbA + 128#64) 56 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (Q_regs := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (SepWP.mono
          (v7_enc_ok_move_3720_to_7348 hA s0 s1 (s0.sp - 2400#64) out pbA cap_dec c2 l1 p1
            ((s0.sp - 2400#64) + 1392#64) slot16 slot200 enc
            (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
             v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
             (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
             memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
             memRegion ((s0.sp - 2400#64) + 1848#64) 40 ∗
             v7_stackGapsEncDec (s0.sp - 2400#64) ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             memRegion pbA 128 ∗
             memRegion (pbA + 128#64) 56 ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (s.receivingEk.map pbToProtoPolyDecoder)) ∗
             statesFromPbJumpTableAt b ∗
             A.pool)
            hfsp_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_)
      intro sm Pm _ _ ⟨hPm, hq⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, _, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, hpstate2, htr2⟩
      exact v7_after_enc_ok_7348 hA hdec_sub s0 s2 out pbA cap_dec
        c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 s u uc e enc R
        h7404_ok hpts hcap_dec hs_uc huc hs_enc henc hc1 hsp0_align
        hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hpstate2 htr2

/-- Every error returned by `Unchunked.SendCt.Ct1Sent.from_pb` is `.err .stateDecode`. -/
theorem v7_ct1Sent_from_pb_error_eq (F : ShaCompress) (u : V1State.Unchunked.Ct1Sent)
    {e : StatesError} (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .error e) :
    e = .err .stateDecode := by
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h
  split at h
  · rcases hauth : u.auth with _ | a <;> rw [hauth] at h <;> [injection h with h; nomatch h]
    exact h.symm
  · injection h with h; exact h.symm


/-- `V7Ok7404Prop` holds unconditionally via `v7_dec_ok_7404_to_ret`. -/
theorem v7_ok7404Prop_holds
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) :
    V7Ok7404Prop (A := A) (F := F) (b := b) (ext := ext) s0 out pbA s := by
  intro s1 c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc enc dec
    hsp0_align _ hfrom_pb hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1
  have h208_1056 :
      memRegion ((s0.sp - 2400#64) + 208#64) 688 ∗
      memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
      memRegion ((s0.sp - 2400#64) + 952#64) 312 ⊢
      memRegion ((s0.sp - 2400#64) + 208#64) 1056 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  have h1792_96 :
      memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
      memRegion ((s0.sp - 2400#64) + 1848#64) 40 ⊢
      memRegion ((s0.sp - 2400#64) + 1792#64) 96 := by
    exact collapse_top <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  unfold v7_stackGapsEncDec
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 208#64) 688 ∗
       memRegion ((s0.sp - 2400#64) + 896#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 952#64) 312) ∗
      (memRegion ((s0.sp - 2400#64) + 1792#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 1848#64) 40) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 16 ∗
       (((s0.sp - 2400#64) + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       memRegion ((s0.sp - 2400#64) + 32#64) 168 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
       polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
       resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.ok dec) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
       (memRegion pbA optProtoInnerStateSize ∗
        statesFromPbJumpTableAt b ∗
        A.pool)) by ac_rfl))
      (Entails.trans (sepConj_mono h208_1056 (sepConj_mono_left h1792_96))
        (Entails.of_eq (by ac_rfl))))
    (SepWP.mono
      (v7_dec_ok_7404_to_ret hA s0 s1 out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
        uc enc dec
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1) ?_)
  intro sf Pf _ _ ⟨hPf, hq⟩
  rw [hfrom_pb]
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hq⟩

end CryptoVerification.SpqrV1.States.FromPb
