/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 5 (`NoHeaderReceived`, `+1344`) — Part A

OOM cold path (`+11596`), shared `+6500` error exit, inline `ProtoPolynomialDecoder`
deallocation (`+6420..+6500`), and protobuf unpacking helpers for `NoHeaderReceived`.
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::from_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  stubOff_handle_error

/-! ## Subroutine & WPp Helpers (`v5a_*`) -/

theorem v5a_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v5a_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v5a_sepWPp_call_ret {α : Type} {prog : Program}
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
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v5a_sub_ok_dealloc_125316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide))
    hA.dealloc

theorem v5a_sub_ok_decoder_from_pb
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
      (decoderFromPbSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 35448) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_decoder_from_pb (by decide))
    hdec

theorem v5a_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v5a_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v5a_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Shared OOM cold path at `+11596` (`mov w0, #1; mov x1, x27; bl handle_error`). -/
theorem v5a_states_from_pb_oom_11596
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
    (by rw [hfn, stubOff_handle_error])
  states_from_pb_fetches_range b (Rust.withPanics ext) 11596 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  unfold statesFromPbOnPanic
  simpa only [sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

theorem v5a_optProtoInnerStateAt_noHeaderReceived (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.NoHeaderReceived) :
    optProtoInnerStateAt A pbA (some (.noHeaderReceived s)) =
      (pbA ↦₆₄ 0x8000000000000005#64) ∗
      optProtoPolynomialDecoderAt A (pbA + 8#64) (s.receivingHdr.map pbToProtoPolyDecoder) ∗
      optProtoUnchunkedNoHeaderReceivedAt A (pbA + 48#64) s.uc ∗
      memRegion (pbA + 104#64) 120 := by
  have h48 : pbA + 8#64 + 40#64 = pbA + 48#64 := by bv_omega
  simp only [optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedNoHeaderReceivedAt, h48, sepConj_assoc]

@[simp]
theorem v5a_spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

theorem v5a_states_from_pb_noHeaderReceived_ptsNeeded_ne (F : ShaCompress)
    (d : PolynomialDecoder) (uc : Option V1State.Unchunked.NoHeaderReceived)
    (hne : (d.ptsNeeded == 48#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived { uc := uc, receivingHdr := some d }) } =
      .error (.err .msgDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = true := by
    simpa [bne] using hne
  erw [hne']
  rfl

theorem v5a_states_from_pb_noHeaderReceived_uc_none_dec_none (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived { uc := none, receivingHdr := none }) } =
      .error (.err .stateDecode) := rfl

theorem v5a_states_from_pb_noHeaderReceived_uc_none_dec_some (F : ShaCompress)
    (d : PolynomialDecoder) (heq : (d.ptsNeeded == 48#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived { uc := none, receivingHdr := some d }) } =
      .error (.err .stateDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = false := by
    simpa [bne] using heq
  erw [hne']
  rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_none_dec_none (F : ShaCompress)
    (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := none, epoch := ep }, receivingHdr := none }) } =
      .error (.err .stateDecode) := rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_none_dec_some (F : ShaCompress)
    (ep : BitVec 64) (d : PolynomialDecoder) (heq : (d.ptsNeeded == 48#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := none, epoch := ep }, receivingHdr := some d }) } =
      .error (.err .stateDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb,
    Unchunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = false := by
    simpa [bne] using heq
  erw [hne']
  rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_some_dec_none (F : ShaCompress)
    (authPb : ProtoAuthenticator) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := some authPb, epoch := ep }, receivingHdr := none }) } =
      .error (.err .stateDecode) := rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_some_dec_some (F : ShaCompress)
    (authPb : ProtoAuthenticator) (ep : BitVec 64) (d : PolynomialDecoder)
    (heq : (d.ptsNeeded == 48#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some d }) } =
      match decoderFromPbResult (pbToProtoPolyDecoder d) with
      | .ok dec =>
        .ok (.noHeaderReceived
          { uc := { auth := Authenticator.fromPb authPb, epoch := ep }
            receiving_hdr := dec })
      | .error _ => .error (.err .stateDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb,
    Unchunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = false := by
    simpa [bne] using heq
  erw [hne']
  simp only [Bool.false_eq_true, ↓reduceIte,
    v5a_spqrAuthApi_from_pb, decoderFromPbStateDecode_some,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases decoderFromPbResult (pbToProtoPolyDecoder d) <;> rfl

/-! ## Shared Error Exit at `+6500` & `ProtoPolynomialDecoder` Deallocation Loop (`+6420..+6500`) -/

theorem v5a_memRegion_2304_split_216 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 216 ∗
      (∃∗ w216 : BitVec 64, ((fsp + 216#64) ↦₆₄ w216)) ∗
      memRegion (fsp + 224#64) 2080 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v5a_memRegion_2304_join_216 (fsp w216 : BitVec 64) :
    memRegion fsp 216 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ memRegion (fsp + 224#64) 2080 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+6500` (`0x5ba08 -> s0.x30`):
loads `x9` from `[sp, #216]`, sets `x8 = noneCap`, stores `x27` to `[out + 8]` and `x8, x9` to `[out + 16..32]`,
and branches to `+60`. -/
theorem v5a_states_from_pb_err_6500
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6500#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : (s1.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v5a_memRegion_2304_split_216 (s0.sp - 2400#64)))) ?_
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro w216
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 6500 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x27) noneCap w216
      rw [hx27_1] at htail
      have hstack := v5a_memRegion_2304_join_216 (s0.sp - 2400#64) w216
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x27) ∗
           ((out + 16#64) ↦₆₄ noneCap) ∗
           ((out + 24#64) ↦₆₄ w216) ∗
           memRegion (out + 32#64) 896) ∗
          (memRegion (s0.sp - 2400#64) 216 ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ w216) ∗
           memRegion ((s0.sp - 2400#64) + 224#64) 2080) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono htail (sepConj_mono_left hstack))
        (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60 s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

@[reducible]
def v5a_Saved6428Preserved (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x22 = ptsPtr ∧
  s.readReg64 .x23 = ptsCap ∧
  s.readReg64 .x27 = x27_val ∧
  TraceCalleeSaved s s0

theorem v5a_proto_decoder_dealloc_body_6452
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6440#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          sm.readReg64 .x28 = cnt ∧
          sm.readReg64 .x21 = cur + 8#64) := by
  have hdealloc := v5a_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 6452 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hpres hx28 hx21
  rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 6440#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
        sm.readReg64 .x28 = cnt ∧
        sm.readReg64 .x21 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v5a_proto_decoder_dealloc_loop_6452
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6476#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val) := by
  have hbody := v5a_proto_decoder_dealloc_body_6452 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x27_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 6440 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx28 hx21
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := entry + 6440#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x21 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx28 hx21) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx28_1, hx21_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx28_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx22_1, hx23_1, hx27_1, htrace_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx28_1
      refine Drop.seq_clean (mid := entry + 6452#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x21 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx22_1, hx23_1, hx27_1, htrace_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx28_2, hx21_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx28_2 hx21_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+6428 -> +6500` (`0x5b9c0 -> 0x5ba08`):
when `x23 = ptsCap`, `x22 = ptsPtr`, `x28 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and the `pts` buffer itself, then reaches `+6500`. -/
theorem v5a_states_from_pb_dealloc_proto_decoder_6428
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6428#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val) := by
  have hdealloc := v5a_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  have hloop := v5a_proto_decoder_dealloc_loop_6452 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x27_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 6428 12
  states_from_pb_fetches_range b (Rust.withPanics ext) 6476 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 6476#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx28 ⊢
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine Drop.seq_clean (mid := entry + 6452#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x21 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
        wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx28_loop, hx21_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx28_loop hx21_loop)
        have hsplit : ptsCap.toNat * 24 =
            (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion ptsPtr ((bs :: tl).length * 24) ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
            A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
          rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
            ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by ac_rfl)
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl))
          (sepConj_mono_left hjoin)
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx22_3, hx23_3, hx27_3, htrace_3⟩
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx23_3 ⊢
      wp_steps; wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      wp_done

theorem v5a_ptsCap_add_one_ne_zero {ptsCap : BitVec 64} (h : ptsCap.toNat * 24 < 2 ^ 63) :
    ¬((ptsCap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h1 : (ptsCap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

theorem v5a_states_from_pb_dealloc_none_proto_decoder_6420
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x27_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr noneCap x27_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6500#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr noneCap x27_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 6420 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
  change s.readReg64 .x23 = 0xffffffffffffffff#64 at hx23
  wp_steps
  wp_done

theorem v5a_states_from_pb_dealloc_some_proto_decoder_6420
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val) := by
  have h6428 := v5a_states_from_pb_dealloc_proto_decoder_6428 hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 6420 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h6428 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 6428#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
      sm.readReg64 .x28 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
    have hne := v5a_ptsCap_add_one_ne_zero hpts_cap_lt
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx28_1⟩
    exact h6428 s1 fsp out ptsPtr ptsCap x27_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx28_1

/-! ## Unpacking & Packing Lemmas for `Option<ProtoPolynomialDecoder>` and `Option<ProtoUnchunkedNoHeaderReceived>` -/

def v5a_optProtoPolyDecoderWordsAt (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗ ((a + 32#64) ↦₆₄ w32)

theorem v5a_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v5a_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜EncoderFromPb.loByte w = b⌝ ∗ (a ↦₆₄ w) := by
  have hsplit : memRegion (a + 1#64) 7 ⊢
      (∃∗ d1 : BitVec 32, ((a + 1#64) ↦₃₂ d1)) ∗
      (∃∗ h5 : BitVec 16, ((a + 5#64) ↦₁₆ h5)) ∗
      (∃∗ b7 : BitVec 8, ((a + 7#64) ↦₈ b7)) := by
    exact split_top <|
      split_step (mem32_entails _) <|
      split_step (mem16_entails _) <|
      mem8_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro h5
  apply Entails.sepExists_elim; intro d1
  let w : BitVec 64 := b7 ++ h5 ++ d1 ++ b
  refine Entails.sepExists_right w ?_
  have hw0 : w.extractLsb' 0 8 = b := by dsimp [w]; bv_kernel
  have hw1 : w.extractLsb' 8 32 = d1 := by dsimp [w]; bv_kernel
  have hw5 : w.extractLsb' 40 16 = h5 := by dsimp [w]; bv_kernel
  have hw7 : w.extractLsb' 56 8 = b7 := by dsimp [w]; bv_kernel
  have hlo : EncoderFromPb.loByte w = b := hw0
  refine Entails.pure_right hlo ?_
  rw [v5a_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]
  exact Entails.refl _

theorem v5a_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

def v5a_optProtoPolyDecoderHeap (A : RustAlloc) :
    Option ProtoPolynomialDecoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 32 → BitVec 32 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, d24, d28, w32 =>
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      EncoderFromPb.loByte w32 = boolByte pb.isComplete⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w8 (w0.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
       memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))

theorem v5a_optProtoPolyDecoderWordsAt_entails_40
    (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v5a_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ⊢ memRegion a 40 := by
  unfold v5a_optProtoPolyDecoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion a w0) <|
    collapse_step (Drop.pointsTo64_entails_memRegion (a + 8#64) w8) <|
    collapse_step (Drop.pointsTo64_entails_memRegion (a + 16#64) w16) <|
    collapse_step (pointsTo32_entails_memRegion_4 (a + 24#64) d24) <|
    collapse_step (pointsTo32_entails_memRegion_4 (a + 28#64) d28) <|
    Drop.pointsTo64_entails_memRegion (a + 32#64) w32

theorem v5a_optProtoPolyDecoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A a optDec ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ d24 : BitVec 32, ∃∗ d28 : BitVec 32, ∃∗ w32 : BitVec 64,
        v5a_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
        v5a_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 := by
  cases optDec with
  | none =>
    dsimp only [optProtoPolynomialDecoderAt, optProtoPolynomialDecoderNoneTailSize,
      v5a_optProtoPolyDecoderHeap]
    have hsplit : memRegion (a + 8#64) 32 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ d24 : BitVec 32, (a + 24#64) ↦₃₂ d24) ∗
        (∃∗ d28 : BitVec 32, (a + 28#64) ↦₃₂ d28) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem32_entails _) <| split_step (mem32_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro d28
    apply Entails.sepExists_elim; intro d24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right d24
        (Entails.sepExists_right d28 (Entails.sepExists_right w32 ?_)))))
    unfold v5a_optProtoPolyDecoderWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    unfold optProtoPolynomialDecoderAt protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
      vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
      protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
      protoPolynomialDecoderPadSize Poly.vecHeaderBytes
    have h33 : a + 0x21#64 = (a + 32#64) + 1#64 := by bv_omega
    rw [h33]
    have h8_64 := v5a_byte_pad7_entails_64 (a + 32#64) (boolByte pb.isComplete)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro c1
    apply Entails.sepExists_elim; intro p1
    refine Entails.trans
      (Entails.of_eq (show _ =
        ⌜pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
        ((((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
         ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
          (if c1 = 0#64 then emp
           else A.live p1 (c1.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 p1 pb.pts ∗
             memRegion (p1 + BitVec.ofNat 64 (pb.pts.length * 24)) ((c1.toNat - pb.pts.length) * 24)))) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hle, hcap, hp_ne⟩
    refine Entails.trans (sepConj_mono_left h8_64) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w32
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hw32
    refine Entails.sepExists_right c1 (Entails.sepExists_right p1
      (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
        (Entails.sepExists_right pb.ptsNeeded
          (Entails.sepExists_right pb.polys
            (Entails.sepExists_right w32 ?_)))))
    dsimp only [v5a_optProtoPolyDecoderWordsAt, v5a_optProtoPolyDecoderHeap]
    refine Entails.trans
      (Entails.pure_right
        (φ := BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
          pb.ptsNeeded = pb.ptsNeeded ∧ pb.polys = pb.polys ∧
          pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧
          p1 ≠ 0#64 ∧ EncoderFromPb.loByte w32 = boolByte pb.isComplete)
        ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩ (Entails.refl _)) ?_
    exact Entails.of_eq (by ac_rfl)

theorem v5a_protoPolyDecoderAt_pack (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v5a_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
      v5a_optProtoPolyDecoderHeap A (some pb) w0 w8 w16 d24 d28 w32 ⊢
    protoPolynomialDecoderAt A a pb := by
  dsimp only [v5a_optProtoPolyDecoderWordsAt, v5a_optProtoPolyDecoderHeap]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      EncoderFromPb.loByte w32 = boolByte pb.isComplete⌝ ∗
    (((a + 32#64) ↦₆₄ w32) ∗
     ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗
      (if w0 = 0#64 then emp
       else A.live w8 (w0.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
         memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24)))) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize Poly.vecHeaderBytes
  have hcell32 := v5a_pointsTo64_entails_byte_pad7 (a + 32#64) w32 (boolByte pb.isComplete) hw32
  have h33 : (a + 32#64) + 1#64 = a + 0x21#64 := by bv_omega
  rw [h33] at hcell32
  refine Entails.trans (sepConj_mono_left hcell32) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
     (if w0 = 0#64 then emp
      else A.live w8 (w0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))) ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (a + 0x21#64) 7 by ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8 ?_)
  exact Entails.trans
    (Entails.pure_right (φ := pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0#64)
      ⟨hle, hcap, hp_ne⟩ (Entails.refl _))
    (Entails.of_eq (by ac_rfl))

/-- The 7 64-bit words of `Option<ProtoUnchunkedNoHeaderReceived>` at `a` (`56` bytes). -/
def v5a_optProtoUcWordsAt (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48)

theorem v5a_optProtoUcWordsAt_entails_56 (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v5a_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 ⊢ memRegion a 56 := by
  unfold v5a_optProtoUcWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

def v5a_vecU8Heap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Payload A cap ptr bs

theorem v5a_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v5a_vecU8Heap A bs cap ptr len := by
  unfold vecU8 v5a_vecU8Heap
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_header_payload A a cap ptr bs]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v5a_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v5a_vecU8Heap A bs cap ptr len ⊢
      ⌜len = BitVec.ofNat 64 bs.length ∧
        bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      vecCapPtrDealloc A cap ptr := by
  unfold v5a_vecU8Heap vecU8Payload vecCapPtrDealloc
  apply Entails.pure_left; intro hlen
  apply Entails.pure_left; rintro ⟨hle, hcap, hp⟩
  refine Entails.pure_right ⟨hlen, hle, hcap, hp⟩ ?_
  by_cases hc : cap = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepConj_mono_right
    have h1 := ProofLib.pointsToBytes_entails_memRegion ptr bs
    have hadd : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
    have h2 : memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        memRegion ptr cap.toNat := by
      rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
    rw [← h2]
    exact sepConj_mono_left h1

/-- Address-independent heap and pure constraints for `Option<ProtoUnchunkedNoHeaderReceived>`. -/
def v5a_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.NoHeaderReceived →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _ => ⌜w0 = none2Cap⌝
  | some { auth := none, epoch := ep }, w0, _, _, _, _, _, w48 =>
    ⌜w0 = noneCap ∧ w48 = ep⌝
  | some { auth := some authPb, epoch := ep }, w0, w8, w16, w24, w32, w40, w48 =>
    ⌜w48 = ep⌝ ∗
    v5a_vecU8Heap A authPb.rootKey w0 w8 w16 ∗
    v5a_vecU8Heap A authPb.macKey w24 w32 w40

theorem v5a_optProtoUcAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.NoHeaderReceived) :
    optProtoUnchunkedNoHeaderReceivedAt A a optUc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        v5a_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
        v5a_optProtoUcHeap A optUc w0 w8 w16 w24 w32 w40 w48 := by
  cases optUc with
  | none =>
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt, v5a_optProtoUcHeap]
    have hsplit : memRegion (a + 8#64) 48 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) ∗
        (∃∗ w48 : BitVec 64, (a + 48#64) ↦₆₄ w48) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right none2Cap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 ?_))))))
    unfold v5a_optProtoUcWordsAt
    exact Entails.trans (Entails.pure_right (rfl : none2Cap = none2Cap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some uc =>
    rcases uc with ⟨ep, optAuth⟩
    cases optAuth with
    | none =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, protoUnchunkedNoHeaderReceivedAt,
        optProtoAuthenticatorAt, v5a_optProtoUcHeap]
      have hsplit : memRegion (a + 8#64) 40 ⊢
          (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
          (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
          (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
          (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
          (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) := by
        exact split_top <|
          split_step (mem64_entails _) <| split_step (mem64_entails _) <|
          split_step (mem64_entails _) <| split_step (mem64_entails _) <|
          mem64_entails _
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right hsplit)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply Entails.sepExists_elim; intro w40
      apply Entails.sepExists_elim; intro w32
      apply Entails.sepExists_elim; intro w24
      apply Entails.sepExists_elim; intro w16
      apply Entails.sepExists_elim; intro w8
      refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
        (Entails.sepExists_right w16 (Entails.sepExists_right w24
          (Entails.sepExists_right w32 (Entails.sepExists_right w40
            (Entails.sepExists_right ep ?_))))))
      unfold v5a_optProtoUcWordsAt
      exact Entails.trans
        (Entails.pure_right (⟨rfl, rfl⟩ : noneCap = noneCap ∧ ep = ep) (Entails.refl _))
        (Entails.of_eq (by ac_rfl))
    | some authPb =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, protoUnchunkedNoHeaderReceivedAt,
        optProtoAuthenticatorAt, protoAuthenticatorAt, v5a_optProtoUcHeap]
      refine Entails.trans
        (sepConj_mono_left
          (sepConj_mono (v5a_vecU8_unpack A a authPb.rootKey)
            (v5a_vecU8_unpack A (a + 24#64) authPb.macKey))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        BitVec.add_assoc, BitVec.reduceAdd]
      apply Entails.sepExists_elim; intro w24
      apply Entails.sepExists_elim; intro w32
      apply Entails.sepExists_elim; intro w40
      apply Entails.sepExists_elim; intro w0
      apply Entails.sepExists_elim; intro w8
      apply Entails.sepExists_elim; intro w16
      refine Entails.sepExists_right w0 (Entails.sepExists_right w8
        (Entails.sepExists_right w16 (Entails.sepExists_right w24
          (Entails.sepExists_right w32 (Entails.sepExists_right w40
            (Entails.sepExists_right ep ?_))))))
      unfold v5a_optProtoUcWordsAt
      exact Entails.trans
        (Entails.pure_right (rfl : ep = ep) (Entails.refl _))
        (Entails.of_eq (by ac_rfl))

/-- All 224 bytes of `pbA` when `pbA + 8..48` and `pbA + 48..104` are unpacked into words. -/
def v5a_pbAHeadersAt (pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) : SepProp :=
  (pbA ↦₆₄ 0x8000000000000005#64) ∗
  v5a_optProtoPolyDecoderWordsAt (pbA + 8#64) w8 w16 w24 d32 d36 w40 ∗
  v5a_optProtoUcWordsAt (pbA + 48#64) w48 w56 w64 w72 w80 w88 w96 ∗
  memRegion (pbA + 104#64) 120

theorem v5a_pbAHeadersAt_eq (pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 =
      (pbA ↦₆₄ 0x8000000000000005#64) ∗
      ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗ ((pbA + 24#64) ↦₆₄ w24) ∗
      ((pbA + 32#64) ↦₃₂ d32) ∗ ((pbA + 36#64) ↦₃₂ d36) ∗ ((pbA + 40#64) ↦₆₄ w40) ∗
      ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
      ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗ ((pbA + 88#64) ↦₆₄ w88) ∗
      ((pbA + 96#64) ↦₆₄ w96) ∗
      memRegion (pbA + 104#64) 120 := by
  unfold v5a_pbAHeadersAt v5a_optProtoPolyDecoderWordsAt v5a_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v5a_pbAHeadersAt_entails_224 (pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ⊢
      memRegion pbA optProtoInnerStateSize := by
  unfold v5a_pbAHeadersAt
  dsimp only [optProtoInnerStateSize]
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (v5a_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    collapse_step (v5a_optProtoUcWordsAt_entails_56 _ _ _ _ _ _ _ _) <|
    Entails.refl _

theorem v5a_optProtoInnerStateAt_unpack (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.NoHeaderReceived) :
    optProtoInnerStateAt A pbA (some (.noHeaderReceived s)) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ d32 : BitVec 32, ∃∗ d36 : BitVec 32, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64,
        v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A (s.receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
        v5a_optProtoUcHeap A s.uc w48 w56 w64 w72 w80 w88 w96 := by
  rw [v5a_optProtoInnerStateAt_noHeaderReceived A pbA s]
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono_left (v5a_optProtoPolyDecoderAt_unpack A (pbA + 8#64) (s.receivingHdr.map pbToProtoPolyDecoder)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro d32
  apply Entails.sepExists_elim; intro d36
  apply Entails.sepExists_elim; intro w40
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v5a_optProtoUcAt_unpack A (pbA + 48#64) s.uc))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w88
  apply Entails.sepExists_elim; intro w96
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right d32
      (Entails.sepExists_right d36 (Entails.sepExists_right w40
        (Entails.sepExists_right w48 (Entails.sepExists_right w56
          (Entails.sepExists_right w64 (Entails.sepExists_right w72
            (Entails.sepExists_right w80 (Entails.sepExists_right w88
              (Entails.sepExists_right w96 ?_))))))))))))
  unfold v5a_pbAHeadersAt
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
