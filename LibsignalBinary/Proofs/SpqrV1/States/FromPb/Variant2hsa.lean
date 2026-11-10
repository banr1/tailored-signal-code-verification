/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part A

Model reduction lemmas, protobuf unpacking/packing helpers for `HeaderSent` (`176`B), and
shared error epilogues and inline `ProtoPolynomialDecoder` deallocation (`+4420..+9228`).
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
open V1State.Chunked
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

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## Pure Model Reduction Lemmas for `HeaderSent` -/

theorem v2hs_ptsNeeded_bne_eq (ptsNeeded : BitVec 32) :
    (ptsNeeded.toNat != CIPHERTEXT1_SIZE / 2) = !(ptsNeeded == 480#32) := by
  change (ptsNeeded.toNat != 480) = !(ptsNeeded == 480#32)
  cases h : (ptsNeeded == 480#32)
  · have hne : ptsNeeded.toNat ≠ 480 := by
      intro heq
      have h1 : ptsNeeded = 480#32 := BitVec.eq_of_toNat_eq heq
      rw [h1] at h
      contradiction
    simp [hne]
  · have heq : ptsNeeded = 480#32 := beq_iff_eq.mp h
    subst heq
    rfl

theorem v2hs_from_pb_headerSent_bad_pts_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (d : PolynomialDecoder)
    (hdec : s.receivingCt1 = some d)
    (hpts : (d.ptsNeeded == 480#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .msgDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at hdec
    subst hdec
    simp only [States.from_pb, Chunked.SendEk.HeaderSent.from_pb,
      v2hs_ptsNeeded_bne_eq, hpts, Bool.not_false, ↓reduceIte,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_headerSent_from_pb_after_pts (F : ShaCompress)
    (uc : Option V1State.Unchunked.EkSent)
    (sendingEk : Option PolynomialEncoder)
    (receivingCt1 : Option PolynomialDecoder)
    (hdec : match receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true) :
    Chunked.SendEk.HeaderSent.from_pb spqrPolyApi (spqrAuthApi F)
      { uc := uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } =
    (do
      let u ← match uc with
        | none => Except.error (StatesError.err .stateDecode)
        | some u => Except.ok u
      let uc ← Unchunked.SendEk.EkSent.from_pb (spqrAuthApi F) u
      let sendingEk ← encoderFromPbStateDecode spqrPolyApi sendingEk
      let receivingCt1 ← decoderFromPbStateDecode spqrPolyApi receivingCt1
      Except.ok { uc := uc, sending_ek := sendingEk, receiving_ct1 := receivingCt1 }) := by
  cases receivingCt1 with
  | none =>
    simp only [Chunked.SendEk.HeaderSent.from_pb, Bind.bind, Except.bind]
    cases uc <;> rfl
  | some d =>
    simp only at hdec
    simp only [Chunked.SendEk.HeaderSent.from_pb, v2hs_ptsNeeded_bne_eq, hdec,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    cases uc <;> rfl

theorem v2hs_from_pb_headerSent_uc_none_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec
    subst huc
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F none sendingEk receivingCt1 hdec,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_from_pb_headerSent_bad_dk_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (u : V1State.Unchunked.EkSent)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u)
    (hdk : (BitVec.ofNat 64 u.dk.length == 2400#64) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec
    subst huc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = false := by
      change (u.dk.length == 2400) = false
      rw [beq_eq_false_iff_ne]
      intro hlen
      rw [hlen] at hdk
      exact Bool.noConfusion hdk
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F (some u) sendingEk receivingCt1 hdec,
      Unchunked.SendEk.EkSent.from_pb, hdk_eq, Bool.false_eq_true, ↓reduceIte,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_from_pb_headerSent_auth_none_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (u : V1State.Unchunked.EkSent)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u)
    (hdk : u.dk.length = 2400)
    (hauth : u.auth = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec
    subst huc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = true := by
      change (u.dk.length == 2400) = true
      simp [hdk]
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F (some u) sendingEk receivingCt1 hdec,
      Unchunked.SendEk.EkSent.from_pb, hdk_eq, hauth, ↓reduceIte,
      Functor.map, Except.map, Bind.bind, Except.bind]

theorem v2hs_from_pb_headerSent_sendingEk_none_eq (F : ShaCompress)
    (s : V1State.Chunked.HeaderSent) (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (hdec : match s.receivingCt1 with
            | none => True
            | some d => (d.ptsNeeded == 480#32) = true)
    (huc : s.uc = some u)
    (hdk : u.dk.length = 2400)
    (hauth : u.auth = some auth)
    (henc : s.sendingEk = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerSent s) } = .error (.err .stateDecode) := by
  cases s with
  | mk uc sendingEk receivingCt1 =>
    simp only at huc hdec henc
    subst huc henc
    have hdk_eq : (u.dk.length == DECAPSULATION_KEY_SIZE) = true := by
      change (u.dk.length == 2400) = true
      simp [hdk]
    simp only [States.from_pb, v2hs_headerSent_from_pb_after_pts F (some u) none receivingCt1 hdec,
      Unchunked.SendEk.EkSent.from_pb, hdk_eq, hauth, encoderFromPbStateDecode, ↓reduceIte,
      Pure.pure, Except.pure, Functor.map, Except.map, Bind.bind, Except.bind]

/-! ## Shared Error Epilogue (`+9224/+9228 -> +60 -> s0.x30`) and Decoder Deallocation (`+4420..+4512`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem v2hs_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[local simp, local arm64_norm, local wp_norm]
theorem v2hs_bfm_loByte_eq (x23 x26 : BitVec 64) :
    (((x26 &&& 72057594037927935#64) <<< 8) ||| (x23 &&& 255#64)).extractLsb' 0 8 =
      x23.extractLsb' 0 8 := by
  bv_kernel

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+9228` (`0x5c4b0 -> +60 -> s0.x30`):
when `x23` has low byte `spqrErrorByte err` and `x19 = out`, executes `bfxil x23, x26, #8, #56`,
writes `x25, x21` to `[out + 16..32]`, sets `x8 = noneCap`, writes `x23` to `[out + 8]`,
and branches to `+60`. -/
theorem v2hs_err_cleanup_9228
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
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
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9228 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out
        (((s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8) ||| (s1.readReg64 .x23 &&& 255#64))
        (s1.readReg64 .x25) (s1.readReg64 .x21)
      rw [v2hs_bfm_loByte_eq, hx23_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ (((s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8) |||
             (s1.readReg64 .x23 &&& 255#64))) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x25) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x21) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60 s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

theorem v2hs_memRegion_2304_split_232 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 232 ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 2064 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v2hs_memRegion_2304_join_232 (fsp w232 : BitVec 64) :
    memRegion fsp 232 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 2064 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+9224` (`0x5c4ac -> +9228 -> +60 -> s0.x30`):
loads `x21` from `[sp, #232]` and falls through to `v2hs_err_cleanup_9228`. -/
theorem v2hs_err_cleanup_9224
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9224#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
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
    (sepConj_mono_right (sepConj_mono_left (v2hs_memRegion_2304_split_232 (s0.sp - 2400#64)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w232
  have hjoin := v2hs_memRegion_2304_join_232 (s0.sp - 2400#64) w232
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9224 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · simp only [arm64_norm] at hjoin ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 232 ∗
         ((s0.sp - 2168#64) ↦₆₄ w232) ∗
         memRegion (s0.sp - 2160#64) 2064) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hjoin) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, htr2⟩
    exact v2hs_err_cleanup_9228 s0 s2 out err Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 htr2

@[reducible]
def v2hs_Saved4436Preserved (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = ptsPtr ∧
  s.readReg64 .x22 = ptsCap ∧
  s.readReg64 .x23 = x23_val ∧
  TraceCalleeSaved s s0

theorem v2hs_proto_decoder_dealloc_body_4460
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4460#64 →
      s.status = .Running →
      v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4448#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x24 = cur + 8#64) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 4460 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hpres hx21 hx24
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 4448#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = cnt ∧
        sm.readReg64 .x24 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v2hs_proto_decoder_dealloc_loop_4460
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4460#64 →
      s.status = .Running →
      v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hbody := v2hs_proto_decoder_dealloc_body_4460 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 4448 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx21 hx24
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := entry + 4448#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x24 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx21 hx24) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx21_1, hx24_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htrace_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine Drop.seq_clean (mid := entry + 4460#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x24 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htrace_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx21_2, hx24_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx21_2 hx24_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- `ProtoPolynomialDecoder` inline deallocation (`+4436 -> +4484`):
when `x22 = ptsCap`, `x20 = ptsPtr`, `x21 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and reaches `+4484`. -/
theorem v2hs_states_from_pb_dealloc_proto_decoder_4436
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4436#64)
    (hrun : s.status = .Running)
    (hpres : v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hloop := v2hs_proto_decoder_dealloc_loop_4460 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 4436 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  cases pts with
  | nil =>
    rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
    simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, arrayAt, emp_sepConj] at hx21 ⊢
    wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
  | cons bs tl =>
    have hlen_pos : 0 < (bs :: tl).length := by simp
    have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
      have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
      omega
    have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
    have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
    simp only [hcap_ne, ↓reduceIte]
    refine Drop.seq_clean (mid := entry + 4460#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
           ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
         Frame))
      (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x24 = ptsPtr + 8#64)
      ?_ ?_
    · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx21_loop, hx24_loop⟩
      refine SepWP.strengthen_entails_const ?_
        (hloop (bs :: tl) ptsPtr s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
          hx21_loop hx24_loop)
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

/-- `ProtoPolynomialDecoder` inline deallocation (`+4484 -> +9228`):
loads `x21` from `[fsp + 232]`, deallocates the outer `pts` buffer if `ptsCap ≠ 0`, and jumps to `+9228`. -/
theorem v2hs_states_from_pb_dealloc_proto_decoder_4484
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64)
    (hrun : s.status = .Running)
    (hpres : v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s
      ((if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 4484 32
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
  by_cases hc : ptsCap = 0#64
  · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22 ⊢
    wp_steps; wp_done
  · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    wp_steps
    wp_apply
    wp_steps
    refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_
    wp_done

/-- Shared `Option<ProtoPolynomialDecoder>::None` inline deallocation at `+4420 -> +9224`:
when `x22 = noneCap`, `cmn x22, #1; b.eq +9224` jumps directly to `+9224`. -/
theorem v2hs_states_from_pb_dealloc_none_proto_decoder_4420
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out x23_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9224#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 4420 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change s.readReg64 .x22 = 0xffffffffffffffff#64 at hx22
  wp_steps
  wp_done

/-- Shared `Option<ProtoPolynomialDecoder>::Some` inline deallocation at `+4420 -> +9228`:
when `x22 = ptsCap` with `ptsCap.toNat * 24 < 2^63` and stack cells `[fsp + 1040] = ptsPtr`,
`[fsp + 1048] = BitVec.ofNat 64 pts.length`, `[fsp + 232] = w232`, deallocates `pts` and reaches `+9228`. -/
theorem v2hs_states_from_pb_dealloc_some_proto_decoder_4420
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) := by
  have h4436 := v2hs_states_from_pb_dealloc_proto_decoder_4436 hA s0
  have h4484 := v2hs_states_from_pb_dealloc_proto_decoder_4484 hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 4420 16
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h4436 h4484 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 4436#64)
    (P_mid := (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
    (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx21_1⟩
    refine Drop.seq_clean (mid := entry + 4484#64)
      (P_mid := (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
      (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val)
      ?_ ?_
    · have h1 := h4436 s1 fsp out ptsPtr ptsCap x23_val pts
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
        hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx21_1
      exact SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl)) h1
    · intro s2 hpc2 hrun2 hpres2
      have h2 := h4484 s2 fsp out ptsPtr ptsCap x23_val w232
        (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
        hfsp_align hpts_cap_lt hpc2 hrun2 hpres2
      refine SepWP.mono h2 fun sm Pm _ _ ⟨hPm, hsp_m, hx19_m, _, _, hx23_m, htr_m⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp_m, hx19_m, hx23_m, htr_m⟩

/-! ## Protobuf Unpacking Helpers & Shared Error Epilogues (`+4420`, `+4396`, `+4392`) -/

/-- Five 64-bit words (`40` bytes) of `Option<ProtoPolynomialDecoder>` at `a`. -/
def v2hs_optProtoDecoderWordsAt (a d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ d_w0) ∗ ((a + 8#64) ↦₆₄ d_w8) ∗ ((a + 16#64) ↦₆₄ d_w16) ∗
  ((a + 24#64) ↦₆₄ d_w24) ∗ ((a + 32#64) ↦₆₄ d_w32)

theorem v2hs_optProtoDecoderWordsAt_entails_40
    (a d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderWordsAt a d_w0 d_w8 d_w16 d_w24 d_w32 ⊢ memRegion a 40 := by
  unfold v2hs_optProtoDecoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

/-- Address-independent heap and pure constraints for `Option<ProtoPolynomialDecoder>`
associated with 5 64-bit words `d_w0..d_w32`. -/
def v2hs_optProtoDecoderHeap (A : RustAlloc)
    (optDec : Option ProtoPolynomialDecoder)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) : SepProp :=
  v4b_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
    (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32

theorem v2hs_optProtoDecoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A a optDec ⊢
      ∃∗ d_w0 : BitVec 64, ∃∗ d_w8 : BitVec 64, ∃∗ d_w16 : BitVec 64,
      ∃∗ d_w24 : BitVec 64, ∃∗ d_w32 : BitVec 64,
        v2hs_optProtoDecoderWordsAt a d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 := by
  refine Entails.trans (v4b_optProtoPolyDecoderAt_unpack A a optDec) ?_
  apply Entails.sepExists_elim; intro d_w0
  apply Entails.sepExists_elim; intro d_w8
  apply Entails.sepExists_elim; intro d_w16
  apply Entails.sepExists_elim; intro d24
  apply Entails.sepExists_elim; intro d28
  apply Entails.sepExists_elim; intro d_w32
  refine Entails.sepExists_right d_w0
    (Entails.sepExists_right d_w8
      (Entails.sepExists_right d_w16
        (Entails.sepExists_right (d28 ++ d24)
          (Entails.sepExists_right d_w32 ?_))))
  unfold v4b_optProtoPolyDecoderWordsAt v2hs_optProtoDecoderWordsAt v2hs_optProtoDecoderHeap
  have hlo : (d28 ++ d24).extractLsb' 0 32 = d24 := by bv_kernel
  have hhi : (d28 ++ d24).extractLsb' 32 32 = d28 := by bv_kernel
  rw [hlo, hhi]
  have h24 := ProofLib.pointsTo32_pair (a + 24#64) d24 d28
  have hadd : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
  rw [hadd] at h24
  rw [← h24]
  exact Entails.of_eq (by ac_rfl)

/-- Ten 64-bit words (`80` bytes) of `Option<ProtoUnchunkedEkSent>` at `a`. -/
def v2hs_ucWordsAt (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) : SepProp :=
  (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
  ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
  ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
  ((a + 72#64) ↦₆₄ u80)

theorem v2hs_ucWordsAt_entails_80
    (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    v2hs_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢ memRegion a 80 := by
  unfold v2hs_ucWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v2hs_split_72_words (a : BitVec 64) :
    memRegion (a + 8#64) 72 ⊢
      (∃∗ u16 : BitVec 64, (a + 8#64) ↦₆₄ u16) ∗
      (∃∗ u24 : BitVec 64, (a + 16#64) ↦₆₄ u24) ∗
      (∃∗ u32 : BitVec 64, (a + 24#64) ↦₆₄ u32) ∗
      (∃∗ u40 : BitVec 64, (a + 32#64) ↦₆₄ u40) ∗
      (∃∗ u48 : BitVec 64, (a + 40#64) ↦₆₄ u48) ∗
      (∃∗ u56 : BitVec 64, (a + 48#64) ↦₆₄ u56) ∗
      (∃∗ u64 : BitVec 64, (a + 56#64) ↦₆₄ u64) ∗
      (∃∗ u72 : BitVec 64, (a + 64#64) ↦₆₄ u72) ∗
      (∃∗ u80 : BitVec 64, (a + 72#64) ↦₆₄ u80) := by
  exact split_top <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    mem64_entails _

/-- Address-independent heap and pure constraints for `Option<ProtoUnchunkedEkSent>`
associated with 10 64-bit words `u8..u80`. -/
def v2hs_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.EkSent →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, u8, _, _, _, _, _, _, _, _, _ => ⌜u8 = noneCap⌝
  | some st, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80 =>
    v4b_vecU8Heap A st.dk u8 u16 u24 ∗
    v1_optProtoAuthHeap A st.auth u32 u40 u48 u56 u64 u72 ∗
    ⌜u80 = st.epoch⌝

theorem v2hs_optProtoUcAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSent) :
    optProtoUnchunkedEkSentAt A a optUc ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64,
        v2hs_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 := by
  cases optUc with
  | none =>
    simp only [optProtoUnchunkedEkSentAt, v2hs_optProtoUcHeap]
    refine Entails.trans (sepConj_mono_right (v2hs_split_72_words a)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u24
    apply Entails.sepExists_elim; intro u16
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80 ?_)))))))))
    unfold v2hs_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some st =>
    simp only [optProtoUnchunkedEkSentAt, protoUnchunkedEkSentAt, v2hs_optProtoUcHeap]
    have hdk := v4b_vecU8_unpack A a st.dk
    have hauth := v3cr_optProtoAuth_unpack A (a + 24#64) st.auth
    refine Entails.trans (sepConj_mono hdk (sepConj_mono_left hauth)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u8
    apply Entails.sepExists_elim; intro u16
    apply Entails.sepExists_elim; intro u24
    simp only [arm64_norm]
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right st.epoch ?_)))))))))
    unfold v2hs_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : st.epoch = st.epoch) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))

/-- Eleven 128-bit (`↦₁₂₈`) chunks covering `base + 0..176` (`176` bytes). -/
def v2hs_pb128At (base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) : SepProp :=
  (base ↦₁₂₈ (u16 ++ u8)) ∗ ((base + 16#64) ↦₁₂₈ (u32 ++ u24)) ∗
  ((base + 32#64) ↦₁₂₈ (u48 ++ u40)) ∗ ((base + 48#64) ↦₁₂₈ (u64 ++ u56)) ∗
  ((base + 64#64) ↦₁₂₈ (u80 ++ u72)) ∗ ((base + 80#64) ↦₁₂₈ (w8 ++ w0)) ∗
  ((base + 96#64) ↦₁₂₈ (w24 ++ w16)) ∗ ((base + 112#64) ↦₁₂₈ (w40 ++ w32)) ∗
  ((base + 128#64) ↦₁₂₈ (d_w0 ++ w48)) ∗ ((base + 144#64) ↦₁₂₈ (d_w16 ++ d_w8)) ∗
  ((base + 160#64) ↦₁₂₈ (d_w32 ++ d_w24))

theorem v2hs_words_eq_pb128
    (base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
     w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_ucWordsAt base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v1_optProtoPolyEncoderWordsAt (base + 80#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (base + 136#64) d_w0 d_w8 d_w16 d_w24 d_w32 =
      v2hs_pb128At base u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [v2hs_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v2hs_optProtoDecoderWordsAt, v2hs_pb128At]
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm]

theorem v2hs_pb128_entails_full_224
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
     w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000002#64) ∗
      v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (pbA + 184#64) 40 ⊢
      memRegion pbA optProtoInnerStateSize := by
  rw [← v2hs_words_eq_pb128]
  have h80 := v2hs_ucWordsAt_entails_80 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 88#64) w0 w8 w16 w24 w32 w40 w48
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (pbA + 144#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h224 : (pbA ↦₆₄ 0x8000000000000002#64) ∗ memRegion (pbA + 8#64) 80 ∗
      memRegion (pbA + 88#64) 56 ∗ memRegion (pbA + 144#64) 40 ∗ memRegion (pbA + 184#64) 40 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| Entails.refl _
  simp only [arm64_norm] at h56 h40 ⊢
  exact Entails.trans (sepConj_mono_right (sepConj_mono h80 (sepConj_mono h56 (sepConj_mono_left h40)))) h224

theorem v2hs_memRegion_176_to_128 (base : BitVec 64) :
    memRegion base 176 ⊢
      (∃∗ q0 : BitVec 128, base ↦₁₂₈ q0) ∗ (∃∗ q1 : BitVec 128, (base + 16#64) ↦₁₂₈ q1) ∗
      (∃∗ q2 : BitVec 128, (base + 32#64) ↦₁₂₈ q2) ∗ (∃∗ q3 : BitVec 128, (base + 48#64) ↦₁₂₈ q3) ∗
      (∃∗ q4 : BitVec 128, (base + 64#64) ↦₁₂₈ q4) ∗ (∃∗ q5 : BitVec 128, (base + 80#64) ↦₁₂₈ q5) ∗
      (∃∗ q6 : BitVec 128, (base + 96#64) ↦₁₂₈ q6) ∗ (∃∗ q7 : BitVec 128, (base + 112#64) ↦₁₂₈ q7) ∗
      (∃∗ q8 : BitVec 128, (base + 128#64) ↦₁₂₈ q8) ∗ (∃∗ q9 : BitVec 128, (base + 144#64) ↦₁₂₈ q9) ∗
      (∃∗ q10 : BitVec 128, (base + 160#64) ↦₁₂₈ q10) := by
  exact split_top <|
    split_step0 (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    mem128_entails _

theorem v2hs_memRegion_1032_split_232 (fsp : BitVec 64) :
    memRegion fsp 1032 ⊢
      memRegion fsp 232 ∗ (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 792 := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <| Entails.refl _

theorem v2hs_memRegion_1032_unsplit_232 (fsp w232 : BitVec 64) :
    memRegion fsp 232 ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 792 ⊢ memRegion fsp 1032 := by
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem v2hs_collapse_frame_2304 (fsp d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    memRegion fsp 1032 ∗ v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 1232 ⊢ memRegion fsp 2304 := by
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h2304 : memRegion fsp 1032 ∗ memRegion (fsp + 1032#64) 40 ∗ memRegion (fsp + 1072#64) 1232 ⊢
      memRegion fsp 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h40)) h2304

/-- Shared error epilogue from `+4420 -> s0.x30`:
deallocates `receivingCt1` (`optDec`) at `fsp + 1032..1072`, writes `Err(err)` to `out`,
restores callee-saved registers and stack, and returns. -/
theorem v2hs_epilogue_4420_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1032 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hx23_lo : ((spqrErrorByte err).zeroExtend 64).extractLsb' 0 8 = spqrErrorByte err := by bv_kernel
  cases optDec with
  | none =>
    dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hd_w0; subst hd_w0
    have hcol := v2hs_collapse_frame_2304 (s0.sp - 2400#64) noneCap d_w8 d_w16 d_w24 d_w32
    have hpre_ent :
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1032 ∗
         v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
      refine Entails.trans (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (memRegion (s0.sp - 2400#64) 1032 ∗
         v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (s0.sp - 2400#64 + 1072#64) 1232) ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hcol)
    refine SepWP.weaken_pre hpre_ent ?_
    have h4420 := v2hs_states_from_pb_dealloc_none_proto_decoder_4420 s0 s
      (s0.sp - 2400#64) out ((spqrErrorByte err).zeroExtend 64)
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))
      hpc hrun hsp hx19 hx22 hx23 htr
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9224#64)
      (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))
      (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      h4420 ?_
    intro sm hpcm hrunm ⟨hspm, hx19m, hx23m, htrm⟩
    have hx23m_lo : (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err := by rw [hx23m, hx23_lo]
    have h9224 := v2hs_err_cleanup_9224 (A := A) (F := F) s0 sm out err
      (A.pool ∗ Rest) hsp0_align hpcm hrunm hspm hx19m hx23m_lo htrm
    refine SepWP.mono h9224 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩
  | some pb =>
    dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; rintro ⟨hd_w16, _, _, hpts_le, hpts_cap_lt, _, _⟩; subst hd_w16
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (v2hs_memRegion_1032_split_232 (s0.sp - 2400#64)))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w232
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    let fsp := s0.sp - 2400#64
    let Frame4420 : SepProp :=
      ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗ ((fsp + 1064#64) ↦₆₄ d_w32) ∗
      memRegion fsp 232 ∗ memRegion (fsp + 240#64) 792 ∗ memRegion (fsp - 5152#64) 1056 ∗
      memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
    have hpre_eq :
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗ memRegion fsp 232 ∗
         (((fsp + 232#64) ↦₆₄ w232) ∗ (memRegion (fsp + 240#64) 792 ∗
           (v2hs_optProtoDecoderWordsAt (fsp + 1032#64)
              d_w0 d_w8 (BitVec.ofNat 64 pb.pts.length) d_w24 d_w32 ∗
            ((if d_w0 = 0#64 then emp
              else A.live d_w8 (d_w0.toNat * 24) 8 ∗
                arrayAt (fun bs addr => vecU8 A addr bs) 24 d_w8 pb.pts ∗
                memRegion (d_w8 + BitVec.ofNat 64 (pb.pts.length * 24))
                  ((d_w0.toNat - pb.pts.length) * 24)) ∗
             (memRegion (fsp + 1072#64) 1232 ∗ (statesFromPbSavedCells s0 ∗
               (memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))))))))) =
        (((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if d_w0 = 0#64 then emp
           else A.live d_w8 (d_w0.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 d_w8 pb.pts ∗
             memRegion (d_w8 + BitVec.ofNat 64 (pb.pts.length * 24))
               ((d_w0.toNat - pb.pts.length) * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420) := by
      dsimp only [v2hs_optProtoDecoderWordsAt, Frame4420, fsp]
      simp only [arm64_norm]; ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hpre_eq) ?_
    have h4420 := v2hs_states_from_pb_dealloc_some_proto_decoder_4420 hA s0 s
      fsp out d_w8 d_w0 ((spqrErrorByte err).zeroExtend 64) w232 pb.pts Frame4420
      hfsp_align hpts_le hpts_cap_lt hpc hrun hsp hx19 hx22 hx23 htr
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
      (P_mid := ((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      h4420 ?_
    intro sm hpcm hrunm ⟨hspm, hx19m, hx23m, htrm⟩
    have hpost_ent :
        (((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420) ⊢
        stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
      have hre :
          (((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420) =
          ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
           ((memRegion fsp 232 ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 792) ∗
            v2hs_optProtoDecoderWordsAt (fsp + 1032#64)
              d_w0 d_w8 (BitVec.ofNat 64 pb.pts.length) d_w24 d_w32 ∗
            memRegion (fsp + 1072#64) 1232) ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) := by
        dsimp only [v2hs_optProtoDecoderWordsAt, Frame4420]
        simp only [arm64_norm]; ac_rfl
      rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
      refine Entails.trans (Entails.of_eq hre) ?_
      have h1032 := v2hs_memRegion_1032_unsplit_232 fsp w232
      have h2304 := v2hs_collapse_frame_2304 fsp d_w0 d_w8 (BitVec.ofNat 64 pb.pts.length) d_w24 d_w32
      exact sepConj_mono_right (sepConj_mono_left (Entails.trans (sepConj_mono_left h1032) h2304))
    refine SepWP.weaken_pre hpost_ent ?_
    have hx23m_lo : (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err := by rw [hx23m, hx23_lo]
    have h9228 := v2hs_err_cleanup_9228 (A := A) (F := F) s0 sm out err
      (A.pool ∗ Rest) hsp0_align hpcm hrunm hspm hx19m hx23m_lo htrm
    refine SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

end CryptoVerification.SpqrV1.States.FromPb
