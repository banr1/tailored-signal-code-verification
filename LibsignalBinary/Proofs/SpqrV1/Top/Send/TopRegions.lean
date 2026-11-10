/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatch
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge1
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Phase 4 Finish, Output Size Bounds, and `.headerReceived` Panic Path for `spqr::send`

Proves the alignment-free Phase 4 result builder (`step_send_finish_320a4'`), the
`pqRatchetStatePBEncodedLen` output size bound, `PolyEncoder.nextChunk` infallibility on
well-formed encoders, and the `.headerReceived` panic path when `K.encaps1` returns `none`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

/-! ## Alignment-Free Phase 4 Finish (`0x320a4 -> 0x31a54`) -/

/-- `0x320a4 -> 0x32114` (`entry + 6216#64 -> entry + 6328#64`, 28 instructions = 112 bytes),
    without requiring `hret_align` on `ret`. -/
theorem step_send_build_result_320a4' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (Frame : SepProp)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6216#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 4192#64) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6328#64) s
      (memRegion ret 72 ∗ vecU8 A (s.sp + 1424#64) stBytes ∗ vecU8 A (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A s.sp key ∗ ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x19 = v_20 ∧ sf.readReg64 .x21 = x21 ∧
        sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x25 = x25 ∧ sf.readReg64 .x27 = x27 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗
          memRegion (s.sp + 1424#64) 24 ∗ memRegion (s.sp + 4080#64) 24 ∗
          memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range b (Rust.withPanics ext) 6216 112
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  have hst_exp := vecU8_expose_words A (s.sp + 1424#64) stBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst_exp
  have hmsg_exp := vecU8_expose_words A (s.sp + 4080#64) msgBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmsg_exp
  refine SepWP.focus_weaken hst_exp (by sep_focus) ?_; wp_pull_exists; rename_i stCap stPtr
  refine SepWP.focus_weaken hmsg_exp (by sep_focus) ?_; wp_pull_exists; rename_i msgCap msgPtr
  wp_conv_pre =>
    rw [memRegion_72_split_48_24 ret, memRegion_48_words6 ret,
        memRegion_48_words6 (s.sp + 4192#64), memRegion_16_words2 (s.sp + 7136#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_pull_exists
  have hret_st := words_to_vecU8 A ret stCap stPtr stBytes
  have hret_msg := words_to_vecU8 A (ret + 24#64) msgCap msgPtr msgBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_msg
  have h1424 := words3_to_memRegion_24' (s.sp + 1424#64) stCap stPtr (BitVec.ofNat 64 stBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1424
  have h4080 := words3_to_memRegion_24' (s.sp + 4080#64) msgCap msgPtr (BitVec.ofNat 64 msgBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4080
  have h4192 := words6_to_memRegion_48 (s.sp + 4192#64)
    stCap stPtr (BitVec.ofNat 64 stBytes.length) msgCap msgPtr (BitVec.ofNat 64 msgBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4192
  have h7136 := words2_to_memRegion_16 (s.sp + 7136#64) stCap stPtr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h7136
  cases key with
  | some k =>
    dsimp only [optMsgKeySlotsAt]; wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_words3' (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_pull_exists; wp_steps
    have hret_key := optKeyAt_some_of_words A (ret + 48#64) mkCap mkPtr k
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 32#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    refine SepWP.focus_weaken hret_st (by sep_focus) ?_
    refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
    refine SepWP.focus_weaken hret_key (by sep_focus) ?_
    refine SepWP.focus_weaken (sendResultAt_some_of_parts A ret stBytes msgBytes (some k) hmsg_len) (by sep_focus) ?_
    refine SepWP.focus_weaken h8 (by sep_focus) ?_
    refine SepWP.focus_weaken h24 (by sep_focus) ?_
    refine SepWP.focus_weaken h1424 (by sep_focus) ?_
    refine SepWP.focus_weaken h4080 (by sep_focus) ?_
    refine SepWP.focus_weaken h4192 (by sep_focus) ?_
    refine SepWP.focus_weaken h7136 (by sep_focus) ?_
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | none =>
    dsimp only [optMsgKeySlotsAt]; wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_split_8_16 (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_pull_exists
    refine SepWP.focus_weaken (vecU8Heap_entails_dealloc A mkCap mkPtr []) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
    have hret_key := optKeyAt_none_of_word A (ret + 48#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    by_cases hc0 : (mkCap == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : mkCap = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq; wp_steps
      refine SepWP.focus_weaken hret_st (by sep_focus) ?_
      refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
      refine SepWP.focus_weaken hret_key (by sep_focus) ?_
      refine SepWP.focus_weaken (sendResultAt_some_of_parts A ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
      refine SepWP.focus_weaken h8 (by sep_focus) ?_
      refine SepWP.focus_weaken (words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 0#64) (by sep_focus) ?_
      refine SepWP.focus_weaken h1424 (by sep_focus) ?_
      refine SepWP.focus_weaken h4080 (by sep_focus) ?_
      refine SepWP.focus_weaken h4192 (by sep_focus) ?_
      refine SepWP.focus_weaken h7136 (by sep_focus) ?_
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    · rw [send_stackAt_callee_eq_allocHook s.sp]; wp_steps
      wp_call hdealloc_raw (mkPtr, mkCap.toNat, 1)
      refine SepWP.focus_weaken hret_st (by sep_focus) ?_
      refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
      refine SepWP.focus_weaken hret_key (by sep_focus) ?_
      refine SepWP.focus_weaken (sendResultAt_some_of_parts A ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
      refine SepWP.focus_weaken h8 (by sep_focus) ?_
      refine SepWP.focus_weaken h24 (by sep_focus) ?_
      refine SepWP.focus_weaken h1424 (by sep_focus) ?_
      refine SepWP.focus_weaken h4080 (by sep_focus) ?_
      refine SepWP.focus_weaken h4192 (by sep_focus) ?_
      refine SepWP.focus_weaken h7136 (by sep_focus) ?_
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by ac_rfl)⟩

/-- `0x320a4 -> 0x31a54` (`entry + 6216#64 -> entry + 4600#64`), without requiring `hret_align`. -/
theorem step_send_finish_320a4' {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext) (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (Frame : SepProp) (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6216#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hflag : x21 = LibsignalTripleRatchetRepr.noneCap ∨ BitVec.truncate 32 v_20 = 0#32) (hx25_ch : (x25 + 1#64 == 0#64) = !st.chain.isSome)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64) s
      (memRegion ret 72 ∗ vecU8 A (s.sp + 1424#64) stBytes ∗ vecU8 A (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A s.sp key ∗ ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
        pqRatchetStatePBPinnedAt A g (s.sp + 4704#64) st ∗
        spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗ memRegion (s.sp + 1424#64) 24 ∗
          memRegion (s.sp + 4080#64) 24 ∗ memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 4704#64) 352 ∗
          memRegion (s.sp + 7136#64) 16 ∗ spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  refine SepWP.focus_weaken (pqRatchetStatePBPinnedAt_entails_proto A g (s.sp + 4704#64) st) (by sep_focus) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.seq (step_send_build_result_320a4' hdealloc s ret v_20 x21 x23 x25 x27 stBytes msgBytes key
      (Drop.protoPqRatchetStateAt A (s.sp + 4704#64) st ∗ spqrSendDropJumpTableAt b ∗ Frame)
      hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 hx28 hsp_align) ?_)
  intro s1 Q1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx25_1, _, hvregs1, hQ1⟩
  have hflag1 : s1.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s1.readReg32 .x19 = 0#32 := by
    rcases hflag with h21 | h20
    · left; rw [hx21_1, h21]
    · right; simp only [State.readReg32, hx19_1, h20]
  refine SepWP.seq (step_send_epoch_dealloc_32114 s1 x23 x25 Q1 hpc1 hrun1 hx23_1 hx25_1 hflag1) ?_
  intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hx25_2, hvregs2, hQ2⟩
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2, hsp1]
  have hx25_2' : (s2.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome := by rw [hx25_2, hx25_ch]
  have hQ2' := Entails.trans hQ2 hQ1; rw [← hsp1, ← hsp2] at hQ2'
  refine SepWP.weaken_pre (Entails.trans hQ2' (Entails.of_eq (by ac_rfl)))
    (SepWP.mono (step_send_drop_pq_state_32134 hb hdealloc s2 st x23
      (spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
        memRegion (s2.sp + 8#64) 8 ∗ memRegion (s2.sp + 24#64) 24 ∗
        memRegion (s2.sp + 1424#64) 24 ∗ memRegion (s2.sp + 4080#64) 24 ∗
        memRegion (s2.sp + 4192#64) 48 ∗ memRegion (s2.sp + 7136#64) 16 ∗ Frame)
      hpc2 hrun2 hsp2_align hx23_2 hx25_2') ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
  refine ⟨hrunf, htrf.trans (htr2.trans htr1), hspf.trans (hsp2.trans hsp1), hx23_f, hvregsf.trans (hvregs2.trans hvregs1), ?_⟩
  rw [hsp2, hsp1] at hQf; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))

/-! ## `pqRatchetStatePBEncodedLen` Output Size Bound -/

open CryptoVerification.SpqrV1.Top.StateSize in
theorem pqRatchetStatePBEncodedLen_lt_of_send (F : ShaCompress) (K : MlKem)
    {stateBytes tape tape' : Bytes} {statePb : PqRatchetStatePB V1State} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB}
    (hs : stateBytes.length < 2 ^ 32)
    (hdec : decodeState (spqrDeps F K) stateBytes = .ok statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hsend0 : st0.send K tape = .ok (sOut, tape'))
    (hch_le : optRaw rawChain chainPb ≤ optRaw rawChain statePb.chain + 624) :
    Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := statePb.versionNegotiation
        chain := chainPb
        inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63 := by
  rw [← Prost.EncodeToVec.pqRatchetStatePBEncodedLen_eq_proto]
  have hraw := decodeState_spqrDeps_raw_le hdec
  rcases States.from_pb_raw_le hfrom with ⟨hst0_raw, hst0_pts⟩
  have hst1_raw := (States.send_raw_le hst0_pts hsend0).1
  have hraw' : optRaw rawVN statePb.versionNegotiation + optRaw rawChain statePb.chain +
      rawV1State pb ≤ 201 * stateBytes.length := by
    simpa only [pbToPqRatchetState, rawPqState, rawPqInner, hinner, Option.map, optRaw_some] using hraw
  have hle : rawPqState {
      versionNegotiation := statePb.versionNegotiation
      chain := chainPb
      inner := some (.v1 sOut.state.into_pb) } ≤ 356 * 2 ^ 32 + 2000000 := by
    show optRaw rawVN statePb.versionNegotiation + optRaw rawChain chainPb +
      rawV1State sOut.state.into_pb ≤ 356 * 2 ^ 32 + 2000000
    omega
  exact (encodeState_length_lt_of_rawPqState_le hle).2.2.1

/-! ## `PolyEncoder.nextChunk` Infallibility on Well-Formed Encoders -/

def PolyEncoderValid (enc : PolyEncoder) : Prop :=
  match enc.s with
  | .points pts => pts.length = NUM_POLYS ∧ ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555
  | .polys polys => polys.length = NUM_POLYS

private def firstSlowIdxAux (idx : Nat) (pts : List Point) : Nat → Nat → Nat
  | 0, _ => 16
  | rem + 1, i =>
    if idx < (pts[i]?.getD ⟨[]⟩).value.length then
      firstSlowIdxAux idx pts rem (i + 1)
    else i

private theorem firstSlowIdxAux_le_16 (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → firstSlowIdxAux idx pts rem i ≤ 16
  | 0, _, _ => by simp [firstSlowIdxAux]
  | rem + 1, i, h => by
    unfold firstSlowIdxAux; split_ifs
    · exact firstSlowIdxAux_le_16 idx pts rem (i + 1) (by omega)
    · omega

private theorem firstSlowIdxAux_fast (idx : Nat) (pts : List Point) :
    ∀ (rem i j : Nat), i + rem = 16 → i ≤ j → j < firstSlowIdxAux idx pts rem i →
      idx < (pts[j]?.getD ⟨[]⟩).value.length
  | 0, _, _, _, _, hj => by simp [firstSlowIdxAux] at hj; omega
  | rem + 1, i, j, h, hij, hj => by
    unfold firstSlowIdxAux at hj; split_ifs at hj with hlt
    · rcases Nat.eq_or_lt_of_le hij with rfl | hgt
      · exact hlt
      · exact firstSlowIdxAux_fast idx pts rem (i + 1) j (by omega) hgt hj
    · omega

private theorem firstSlowIdxAux_slow (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → firstSlowIdxAux idx pts rem i < 16 →
      (pts[firstSlowIdxAux idx pts rem i]?.getD ⟨[]⟩).value.length ≤ idx
  | 0, _, _, hlt16 => by simp [firstSlowIdxAux] at hlt16
  | rem + 1, i, h, hlt16 => by
    unfold firstSlowIdxAux at hlt16 ⊢; split_ifs at hlt16 ⊢
    · exact firstSlowIdxAux_slow idx pts rem (i + 1) (by omega) hlt16
    · omega

private theorem chunkPointsPolysBytes_length (idx : BitVec 16) (pts : List Point)
    (polys : List LibsignalSpqrV1.Poly) (i k rem total : Nat)
    (htot : total = k + rem) :
    (chunkPointsBytes idx pts i k ++ chunkPolysBytes idx polys (i + k) rem).length = 2 * total := by
  rw [List.length_append, chunkPointsBytes_length, chunkPolysBytes_length, htot, Nat.mul_add]

private theorem chunkAtLoop_points_prefix_ge_eq (idx : BitVec 32) (pts : List Point)
    (polys : List LibsignalSpqrV1.Poly)
    (hlen_pts : pts.length = 16)
    (hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok polys) :
    ∀ (total k i rem : Nat)
      (_hle : (i + k) + (rem + 1) ≤ 16)
      (htot : total = k + (rem + 1)),
      (∀ j (hj : j < pts.length), i ≤ j → j < i + k →
        (idx.setWidth 16).toNat < (pts[j]'hj).value.length) →
      (pts[i + k]'(by omega)).value.length ≤ (idx.setWidth 16).toNat →
      PolyEncoder.chunkAtLoop (idx.setWidth 16) i total { idx := idx, s := .points pts } =
        .ok ({ idx := idx, s := .polys polys },
          ⟨chunkPointsBytes (idx.setWidth 16) pts i k ++
            chunkPolysBytes (idx.setWidth 16) polys (i + k) (rem + 1),
            chunkPointsPolysBytes_length (idx.setWidth 16) pts polys i k (rem + 1) total htot⟩)
  | 0, k, i, rem, _, htot, _, _ => by omega
  | t + 1, 0, i, rem, hle, htot, _hfast, hslow => by
    have ht : t = rem := by omega
    subst ht
    simp only [Nat.add_zero, chunkPointsBytes, List.nil_append] at hle hslow ⊢
    exact chunkAtLoop_points_ge_eq idx pts polys t i hle hlen_pts hslow hloop
  | t + 1, k + 1, i, rem, hle, htot, hfast, hslow => by
    have hi16 : i < 16 := by omega
    have hi_len : i < pts.length := by omega
    have hlt_i : (idx.setWidth 16).toNat < (pts[i]'hi_len).value.length :=
      hfast i hi_len (Nat.le_refl i) (by omega)
    have hpt_opt : pts[i]? = some (pts[i]'hi_len) := List.getElem?_eq_getElem hi_len
    have hval_opt : (pts[i]'hi_len).value[(idx.setWidth 16).toNat]? =
        some ((pts[i]'hi_len).value[(idx.setWidth 16).toNat]'hlt_i) :=
      List.getElem?_eq_getElem hlt_i
    have hmod : ((idx.setWidth 16).toNat * 16 + i) % 16 = i := totalIdx_mod_16 (idx.setWidth 16) hi16
    have hdiv : ((idx.setWidth 16).toNat * 16 + i) / 16 = (idx.setWidth 16).toNat :=
      totalIdx_div_16 (idx.setWidth 16) hi16
    have hpt := pointAt_points_lt_eq (idx := idx) hi_len hlt_i
    have hadd_assoc : (i + 1) + k = i + (k + 1) := by omega
    have ih := chunkAtLoop_points_prefix_ge_eq idx pts polys hlen_pts hloop t k (i + 1) rem
      (by omega) (by omega)
      (fun j hj hij hjk => hfast j hj (by omega) (by omega))
      (by simpa [hadd_assoc] using hslow)
    unfold PolyEncoder.chunkAtLoop chunkPointsBytes
    simp only [hmod, hdiv, hpt, ih, hpt_opt, hval_opt, Option.getD_some,
      hadd_assoc, List.cons_append, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

private def pointToPolyPure (pt : Point) : Poly :=
  if pt.value.length = 0 then
    Poly.zero
  else
    let pts := PolyEncoder.enumeratePts 0 pt.value
    Poly.lagrangeSum pts (completePointsBasisPure pts)

private theorem fromCompletePoints_enumeratePts_eq (pt : Point)
    (hbound : pt.value.length ≤ 0x0555555555555555) :
    Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 pt.value) =
      .ok (.ok (pointToPolyPure pt)) := by
  have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
    enumeratePts_length 0 pt.value
  by_cases hn0 : pt.value.length = 0
  · have hnil : pt.value = [] := List.eq_nil_of_length_eq_zero hn0
    unfold pointToPolyPure
    simp only [hn0, ↓reduceIte]
    rw [hnil]
    rfl
  · have hcomp : Poly.checkCompletePoints 0 (PolyEncoder.enumeratePts 0 pt.value) = true :=
      checkCompletePoints_enumeratePts 0 pt.value
    have hbound' : (PolyEncoder.enumeratePts 0 pt.value).length ≤ 0x0555555555555555 := by
      omega
    rw [fromCompletePoints_eq_ok (PolyEncoder.enumeratePts 0 pt.value) hcomp hbound']
    unfold pointToPolyPure
    simp [hn0]

private theorem pointsToPolysLoop_eq_map (pts : List Point)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555) :
    ∀ (rem i : Nat) (acc : List Poly),
      i + rem = pts.length →
      PolyEncoder.pointsToPolysLoop pts i rem acc =
        .ok (acc ++ (pts.drop i).map pointToPolyPure)
  | 0, i, acc, hlen => by
    have hi : i = pts.length := by omega
    subst hi
    simp [PolyEncoder.pointsToPolysLoop]
  | rem + 1, i, acc, hlen => by
    have hi : i < pts.length := by omega
    have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
    have hbound_i : (pts[i]'hi).value.length ≤ 0x0555555555555555 :=
      hbounds (pts[i]'hi) (List.getElem_mem hi)
    have hfc := fromCompletePoints_enumeratePts_eq (pts[i]'hi) hbound_i
    have ih := pointsToPolysLoop_eq_map pts hbounds rem (i + 1)
      (acc ++ [pointToPolyPure (pts[i]'hi)]) (by omega)
    have hdrop : pts.drop i = (pts[i]'hi) :: pts.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    unfold PolyEncoder.pointsToPolysLoop
    simp only [hpt, hfc, ih, hdrop, List.map_cons, List.append_assoc, List.singleton_append,
      Bind.bind, Except.bind]

private theorem nextChunk_points_slow_eq {idx : BitVec 32} {pts : List Point}
    (hlen_pts : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (i0 : Nat) (hi0 : i0 < 16)
    (hfast : ∀ j (hj : j < pts.length), j < i0 →
      (idx.setWidth 16).toNat < (pts[j]'hj).value.length)
    (hslow : (pts[i0]'(by omega)).value.length ≤ (idx.setWidth 16).toNat) :
    PolyEncoder.nextChunk { idx := idx, s := .points pts } =
      .ok ({ idx := idx + 1#32, s := .polys (pts.map pointToPolyPure) },
        { index := idx.setWidth 16,
          data := ⟨chunkPointsBytes (idx.setWidth 16) pts 0 i0 ++
            chunkPolysBytes (idx.setWidth 16) (pts.map pointToPolyPure) i0 (15 - i0 + 1),
            by simpa using chunkPointsPolysBytes_length (idx.setWidth 16) pts
                 (pts.map pointToPolyPure) 0 i0 (15 - i0 + 1) 16 (by omega)⟩ }) := by
  have hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok (pts.map pointToPolyPure) := by
    have h := pointsToPolysLoop_eq_map pts hbounds 16 0 [] (by omega)
    simp only [List.nil_append, List.drop_zero] at h
    exact h
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt
  have hchunk := chunkAtLoop_points_prefix_ge_eq idx pts (pts.map pointToPolyPure) hlen_pts hloop
    16 i0 0 (15 - i0) (by omega) (by omega)
    (fun j hj _ hjlt => hfast j hj (by omega)) (by simpa using hslow)
  simp only [Nat.zero_add] at hchunk
  rw [hchunk]
  rfl

open CryptoVerification.SpqrV1.Poly.NextChunk in
theorem nextChunk_ok_of_valid {enc : PolyEncoder} (hv : PolyEncoderValid enc) :
    ∃ enc' chunk, enc.nextChunk = .ok (enc', chunk) := by
  rcases enc with ⟨idx, s⟩
  cases s with
  | polys polys =>
    have hlen : polys.length = 16 := hv
    exact ⟨_, _, nextChunk_polys_eq hlen⟩
  | points pts =>
    rcases hv with ⟨hlen_pts, hbounds⟩
    have hlen16 : pts.length = 16 := hlen_pts
    let i0 := firstSlowIdxAux (idx.setWidth 16).toNat pts 16 0
    have hi0_le : i0 ≤ 16 := firstSlowIdxAux_le_16 (idx.setWidth 16).toNat pts 16 0 (by omega)
    by_cases hi0 : i0 < 16
    · have hi0_len : i0 < pts.length := by omega
      have hslow : (pts[i0]'hi0_len).value.length ≤ (idx.setWidth 16).toNat := by
        have h := firstSlowIdxAux_slow (idx.setWidth 16).toNat pts 16 0 (by omega) hi0
        change (pts[i0]?.getD ⟨[]⟩).value.length ≤ (idx.setWidth 16).toNat at h
        simpa [List.getElem?_eq_getElem hi0_len] using h
      have hfast : ∀ j (hj : j < pts.length), j < i0 →
          (idx.setWidth 16).toNat < (pts[j]'hj).value.length := by
        intro j hj hjlt
        have h := firstSlowIdxAux_fast (idx.setWidth 16).toNat pts 16 0 j (by omega) (by omega) hjlt
        simpa [List.getElem?_eq_getElem hj] using h
      exact ⟨_, _, nextChunk_points_slow_eq hlen16 hbounds i0 hi0 hfast hslow⟩
    · have hi0_16 : i0 = 16 := by omega
      have hall : ∀ k (hk : k < pts.length),
          (idx.setWidth 16).toNat < (pts[k]'hk).value.length := by
        intro k hk
        have hk_i0 : k < i0 := by omega
        have h := firstSlowIdxAux_fast (idx.setWidth 16).toNat pts 16 0 k (by omega) (by omega) hk_i0
        simpa [List.getElem?_eq_getElem hk] using h
      exact ⟨_, _, nextChunk_points_all_lt_eq hlen16 hall⟩

theorem polyEncoderAt_entails_valid (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    Poly.polyEncoderAt A a enc ⊢ ⌜PolyEncoderValid enc⌝ ∗ Poly.polyEncoderAt A a enc := by
  rcases enc with ⟨idx, s⟩
  unfold Poly.polyEncoderAt Poly.encoderStateAt PolyEncoderValid
  dsimp only
  cases s with
  | points pts =>
    dsimp only
    have hpull :
        ((⌜pts.length = NUM_POLYS ∧ ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555⌝ ∗
          (a ↦₆₄ Poly.polyEncoderPointsTag) ∗ Poly.pointListOf A (a + Poly.polyEncoderVecsOff) pts) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) =
        ⌜pts.length = NUM_POLYS ∧ ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555⌝ ∗
        (((a ↦₆₄ Poly.polyEncoderPointsTag) ∗ Poly.pointListOf A (a + Poly.polyEncoderVecsOff) pts) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  | polys polys =>
    dsimp only
    have hpull :
        ((⌜polys.length = NUM_POLYS⌝ ∗
          (a ↦₆₄ Poly.polyEncoderPolysTag) ∗ Poly.polyListOf A (a + Poly.polyEncoderVecsOff) polys) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) =
        ⌜polys.length = NUM_POLYS⌝ ∗
        (((a ↦₆₄ Poly.polyEncoderPolysTag) ∗ Poly.polyListOf A (a + Poly.polyEncoderVecsOff) polys) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

theorem encodeBytesResult_valid {msg : Bytes} {enc : PolyEncoder}
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 1048576)
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63" msg = .ok enc ∨
            expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" msg = .ok enc) :
    PolyEncoderValid enc := by
  obtain ⟨enc0, he0, he1, he2⟩ := encodeBytesResult_of_len_even_le heven hle
  have h_eq : enc0 = enc := by
    rcases henc with h | h
    · exact Except.ok.inj (he1.symm.trans h)
    · exact Except.ok.inj (he2.symm.trans h)
  subst h_eq
  have h1 : (msg.length % 2 != 0) = false := by simp [heven]
  have h2 : ¬ (65536 * NUM_POLYS < msg.length) := by
    change ¬ (65536 * 16 < msg.length); omega
  have he0' :
      encodeBytesResult msg =
        .ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate NUM_POLYS { value := [] })) } := by
    unfold encodeBytesResult; simp [h1, h2]
  cases he0.symm.trans he0'
  unfold PolyEncoderValid
  dsimp only
  have hinit_len : (List.replicate NUM_POLYS ({ value := [] } : Point)).length = 16 := by decide
  refine ⟨(distributeMsgChunks_eq_ok msg 0 (List.replicate NUM_POLYS { value := [] }) heven hinit_len).2, ?_⟩
  intro pt hpt
  have hlen_pt := distributeMsgChunksTotal_value_length_le msg 0 (List.replicate NUM_POLYS { value := [] })
    heven hinit_len (by intro p hp; rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; decide) pt hpt
  omega

theorem send_keysSampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_hdr) :
    ∃ sOut tape', (States.keysSampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_hdr = .ok (enc', chunk) := by
    change st.sending_hdr.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendEk.KeysSampled.send_hdr_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_headerSent_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hv_ek : PolyEncoderValid st.sending_ek) :
    ∃ sOut tape', (States.headerSent st).send K tape = .ok (sOut, tape') := by
  obtain ⟨ek', chunk_ek, hnc_ek⟩ := nextChunk_ok_of_valid hv_ek
  have hnc_ek' : spqrPolyApi.next_chunk st.sending_ek = .ok (ek', chunk_ek) := by
    change st.sending_ek.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (ek', chunk_ek)
    rw [hnc_ek]; rfl
  unfold States.send Chunked.SendEk.HeaderSent.send_ek_chunk
  simp only [hnc_ek', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ct1Received_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (hv_ek : PolyEncoderValid st.sending_ek) :
    ∃ sOut tape', (States.ct1Received st).send K tape = .ok (sOut, tape') := by
  obtain ⟨ek', chunk_ek, hnc_ek⟩ := nextChunk_ok_of_valid hv_ek
  have hnc_ek' : spqrPolyApi.next_chunk st.sending_ek = .ok (ek', chunk_ek) := by
    change st.sending_ek.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (ek', chunk_ek)
    rw [hnc_ek]; rfl
  unfold States.send Chunked.SendEk.Ct1Received.send_ek_chunk
  simp only [hnc_ek', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ct1Sampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_ct1) :
    ∃ sOut tape', (States.ct1Sampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_ct1 = .ok (enc', chunk) := by
    change st.sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendCt.Ct1Sampled.send_ct1_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ekReceivedCt1Sampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_ct1) :
    ∃ sOut tape', (States.ekReceivedCt1Sampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_ct1 = .ok (enc', chunk) := by
    change st.sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ct2Sampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_ct2) :
    ∃ sOut tape', (States.ct2Sampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_ct2 = .ok (enc', chunk) := by
    change st.sending_ct2.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendCt.Ct2Sampled.send_ct2_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem keysUnsampled_macKey_le_rawV1State {F : ShaCompress}
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    s.uc.auth.macKey.length ≤ rawV1State (States.keysUnsampled (P := spqrPolyApi) s).into_pb := by
  unfold States.into_pb Chunked.SendEk.KeysUnsampled.into_pb
    Unchunked.SendEk.KeysUnsampled.into_pb spqrAuthApi Authenticator.intoPb
    rawV1State rawInnerState rawChKeysUnsampled rawUcKeysUnsampled rawAuth optRaw
  dsimp only
  omega

theorem send_keysUnsampled_ok_of_le_64 {F : ShaCompress} (K : MlKem) {tape : Bytes}
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (hk : st.uc.auth.macKey.length < 2 ^ 32)
    (h64 : 64 ≤ tape.length) :
    ∃ (sOut : V1Send spqrPolyApi (spqrAuthApi F)) (tape' : Bytes),
      (States.keysUnsampled (P := spqrPolyApi) st).send K tape = .ok (sOut, tape') := by
  let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
  let hdr := (K.fromSeed seed).1.toList
  have hhdr_len : hdr.length = 64 := fromSeed_hdr_len K seed
  have hmac_ok : st.uc.auth.macHdr F st.uc.epoch hdr = .ok (st.uc.auth.macHdrUnchecked F st.uc.epoch hdr) := by
    apply Authenticator.macHdr_of_lt F st.uc.auth st.uc.epoch hdr hk
    have hlbl : Authenticator.hdrLabel.length = 33 := by rfl
    have hep : (CryptoGames.HMAC.toBEBytes 8 st.uc.epoch).length = 8 := by rfl
    rw [List.length_append, List.length_append, hlbl, hep, hhdr_len]
    omega
  let mac := st.uc.auth.macHdrUnchecked F st.uc.epoch hdr
  have hmsg_len : (hdr ++ mac).length = 96 := by
    rw [List.length_append]
    have h2 : mac.length = 32 := macHdrUnchecked_length F st.uc.auth st.uc.epoch hdr
    omega
  obtain ⟨sending_hdr, _, henc, _⟩ := encodeBytesResult_of_len_even_le (msg := hdr ++ mac)
    (by rw [hmsg_len]) (by rw [hmsg_len]; decide)
  have hv_hdr : PolyEncoderValid sending_hdr :=
    encodeBytesResult_valid (by rw [hmsg_len]) (by rw [hmsg_len]; decide) (Or.inl henc)
  obtain ⟨sending_hdr', chunk, hnc⟩ := nextChunk_ok_of_valid hv_hdr
  have hsend := send_hdr_chunk_of_ok K st h64 hmac_ok henc hnc
  unfold States.send
  simp only [hsend, StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_headerReceived_ok_or_encaps1_of_le_32 {F : ShaCompress} (K : MlKem) {tape : Bytes}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (h32 : 32 ≤ tape.length) :
    (∃ sOut tape', (States.headerReceived st).send K tape = .ok (sOut, tape')) ∨
    (K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none ∧
     (States.headerReceived st).send K tape = .error (.panic .encaps1Failed)) := by
  cases hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ with
  | none =>
    right
    have herr := send_ct1_chunk_of_encaps1_none K st h32 hencaps
    refine ⟨rfl, ?_⟩
    dsimp only [States.send]
    rw [herr]
    rfl
  | some triple =>
    left
    rcases triple with ⟨ct1, es, ss⟩
    obtain ⟨sending_ct1, _, henc⟩ := encodeBytesResult_ct1 ct1
    have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length ct1
    have hv_ct1 : PolyEncoderValid sending_ct1 :=
      encodeBytesResult_valid (by rw [hct1_len]) (by rw [hct1_len]; decide) (Or.inr henc)
    obtain ⟨sending_ct1', chunk, hnc⟩ := nextChunk_ok_of_valid hv_ct1
    have hsend_ct1 := send_ct1_chunk_of_ok K st h32 hencaps henc hnc
    unfold States.send
    simp only [hsend_ct1, StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    exact ⟨_, _, rfl⟩

def statesPolyEncoderValid {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysSampled st => PolyEncoderValid st.sending_hdr
  | .headerSent st => PolyEncoderValid st.sending_ek
  | .ct1Received st => PolyEncoderValid st.sending_ek
  | .ct1Sampled st => PolyEncoderValid st.sending_ct1
  | .ekReceivedCt1Sampled st => PolyEncoderValid st.sending_ct1
  | .ct2Sampled st => PolyEncoderValid st.sending_ct2
  | _ => True

private theorem pull_pure_2 (P : Prop) (A B C : SepProp) :
    A ∗ (⌜P⌝ ∗ B) ∗ C ⊢ ⌜P⌝ ∗ (A ∗ B ∗ C) := by
  apply Entails.of_eq; ac_rfl

private theorem pull_pure_ct1Sampled (P : Prop) (A B : SepProp) :
    (⌜P⌝ ∗ A) ∗ B ⊢ ⌜P⌝ ∗ (A ∗ B) := by
  apply Entails.of_eq; ac_rfl

theorem chunkedStatesAt_entails_polyEncoderValid (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st0 : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a st0 ⊢ ⌜statesPolyEncoderValid st0⌝ ∗ chunkedStatesAt A a st0 := by
  cases st0 with
  | keysSampled s =>
    dsimp only [chunkedStatesAt, chunkedKeysSampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_hdr)))) ?_
    apply Entails.of_eq; ac_rfl
  | headerSent s =>
    dsimp only [chunkedStatesAt, chunkedHeaderSentAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ek)))) ?_
    apply Entails.of_eq; ac_rfl
  | ct1Received s =>
    dsimp only [chunkedStatesAt, chunkedCt1ReceivedAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ek)))) ?_
    apply Entails.of_eq; ac_rfl
  | ct1Sampled s =>
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_left (polyEncoderAt_entails_valid A a s.sending_ct1)) ?_
    apply Entails.of_eq; ac_rfl
  | ekReceivedCt1Sampled s =>
    dsimp only [chunkedStatesAt, chunkedEkReceivedCt1SampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ct1)))) ?_
    apply Entails.of_eq; ac_rfl
  | ct2Sampled s =>
    dsimp only [chunkedStatesAt, chunkedCt2SampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ct2)))) ?_
    apply Entails.of_eq; ac_rfl
  | _ =>
    exact Entails.pure_right trivial (Entails.refl _)

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp Qp' : State → SepProp → Prop}
    (hq : ∀ sf P_f, Q sf P_f → Q' sf P_f)
    (hqp : ∀ sf P_f, Qp sf P_f → Qp' sf P_f)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp' := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hq_f⟩ | ⟨hpan, P_f, hmf, hqp_f⟩ | hoom
  · exact Or.inl ⟨hpc, hrun, P_f, hmf, hq sf P_f hq_f⟩
  · exact Or.inr (Or.inl ⟨hpan, P_f, hmf, hqp sf P_f hqp_f⟩)
  · exact Or.inr (Or.inr hoom)

theorem sepWPp_lift_allowPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {P_panic : Prop} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P_f => Q sf P_f)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine sepWPp_mono_post (fun _ _ hq => hq) (fun sf P_f hqp hm => ?_) h
  have hm' := hqp hm
  refine Satisfies.mono (sepConj_mono_left ?_) hm'
  apply Entails.pure_left; intro ⟨ha, htr⟩
  exact Entails.pure_right ⟨Or.inr ha, htr⟩ (Entails.refl _)

theorem finish_model_panic {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {P_panic : Prop}
    {post : State → SepProp → Prop}
    (hp : P_panic)
    (hextern : prog.externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.panic hrun hextern fun hm => ?_
  have htr_pref : s0.trace <+: (Rust.panicked s).trace := by
    simp only [Rust.panicked, htr]; exact List.prefix_refl _
  have hany : P ∗ R ⊢ (⌜(P_panic ∨ allocFailedIn s0 (Rust.panicked s)) ∧ s0.trace <+: (Rust.panicked s).trace⌝ ∗ anyHeap) ∗ R := by
    refine sepConj_mono_left (Entails.pure_right ⟨Or.inl hp, htr_pref⟩ (entails_anyHeap _))
  exact Satisfies.mono hany hm

theorem sepWPp_bind {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q sm Pm → SepWPp prog ret sm Pm Q' Qp) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨hpc, hrun, Pm, hmm, hq⟩ | hpan
  · obtain ⟨sf, hsteps2, hout2⟩ := h2 sm Pm hpc hrun hq R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

section HeaderReceivedPanic

attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_33d70 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 13588#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "spqr::send::<libsignal_session::HookRng>") + 13588)) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_33d78 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 13596#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "spqr::send::<libsignal_session::HookRng>") + 13596)) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

attribute [local simp, local arm64_norm ↓, local wp_norm ↓] spqrSend_fnOff

theorem step_headerReceived_1312_encaps1_none
    {img : Obj.Image} {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl)) (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (hencaps : K.encaps1 hdr rand = none) (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {P_panic : Prop} {post : State → SepProp → Prop}
    (hp : P_panic) (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64) (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7536#64) 32 ∗
      tapeAt ctl cur tape ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) sessionShimSpec :=
    hA.shim_ok_at spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) (by simp only [arm64_norm, spqrSendName])
  have hallocz : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed")) (rustAllocZeroedSpec A) :=
    alloc_zeroed_ok_at_ext img.base A ext hZero spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed")) (by simp only [arm64_norm, spqrSendName, allocZeroedName])
  have hrng_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "libsignal_session_rng_fill")) (rngFillSpec ctl) :=
    hook_ok_at (hname := rngFillName) rfl (by simp only [arm64_norm, spqrSendName, rngFillName]; rfl)
      (by simp only [arm64_norm, rngFillName]) (fun _ => by simp only [arm64_norm, rngFillName]) (by decide +kernel) hrng
  have henc1_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "libcrux_ml_kem::mlkem768::incremental::encapsulate1")) (mlkemEncaps1Spec K) :=
    hook_ok_at (hname := mlkemEncaps1Name) rfl (by simp only [arm64_norm, spqrSendName, mlkemEncaps1Name]; rfl)
      (by simp only [arm64_norm, mlkemEncaps1Name]) (fun _ => by simp only [arm64_norm, mlkemEncaps1Name]) (by decide +kernel) henc1
  have haerr : (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) = some Rust.panicked :=
    panic_at_handle_error_ext img.base ext spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error"))
      (by change libsignalSessionCode.fnOff spqrSendName + num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error") = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error"; rw [spqrSend_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])
  have hunwrap : (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::result::unwrap_failed")) = some Rust.panicked :=
    panic_at_sym_ext img.base ext spqrSendName "core::result::unwrap_failed"
      (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::result::unwrap_failed")) (by simp only [arm64_norm, spqrSendName]) (hp := by decide +kernel)
  have hadrp1 := fnAddr_adrp_33d70 (H := Rust.withPanics ext) hbase
  have hadrp2 := fnAddr_adrp_33d78 (H := Rust.withPanics ext) hbase
  have hhdr_toNat : (BitVec.ofNat 64 hdr.length).toNat = hdr.length := Nat.mod_eq_of_lt (by omega)
  spqr_send_fetches_range img.base (Rust.withPanics ext) 1312 192
  spqr_send_fetches_range img.base (Rust.withPanics ext) 11832 64
  spqr_send_fetches_range img.base (Rust.withPanics ext) 13588 48
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_bind (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::result::unwrap_failed")) (Q := fun sf _ => sf.trace = s0.trace)
    (sepWPp_lift_allowPanic ?_) ?_
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed")) img hinv
    rw [memRegion_48_eq_words6 (sp + 4192#64), memRegion_32_eq_words4 (sp + 7136#64),
        memRegion_32_eq_words4 (sp + 7536#64)]
    dsimp only [authInlineWordsAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 14 (apply SepWP.exists_elim; intro _)
    wp_steps
    refine SepWP.fold (words4At_entails_memRegion (sp + 7136#64) _ _ _ _) (by dsimp only [words4At]; sep_focus) ?_
    wp_apply
    wp_conv_pre => rw [List.take_append_of_le_length h32, Nat.min_eq_left h32, ← hrand_val]
    wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv1
    refine call_rustAllocZeroed_inImage hallocz 2080 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := entry + 1400#64) (sp_call := sp) hinv1
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *]) (by sep_focus)
      (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
      (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
    · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom1; wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
    · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, _⟩
      simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
      apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed")) img hinv_ok1
      wp_steps; wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv2
      refine call_rustAllocZeroed_inImage hallocz 32 ⟨by decide, ⟨0, rfl⟩, by decide⟩
        (s0 := s0) (ret_pc := entry + 1424#64) (sp_call := sp) hinv2
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hsp_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *]) (by sep_focus)
        (fun sf2 hinv_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
        (fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
      · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom2; wp_steps
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro _
        exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
      · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, _⟩
        simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2
        apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::result::unwrap_failed")) img hinv_ok2
        obtain ⟨rw0, rw1, rw2, rw3, hrand_words⟩ :=
          exists_words4_of_len32 rand.toList (List.Vector.toList_length rand)
        wp_conv_pre => rw [hrand_words (sp + 7136#64)]; dsimp only [words4At]
        wp_steps
        have hfold_rand_7536 : words4At (sp + 7536#64) rw0 rw1 rw2 rw3 ⊢ ((sp + 7536#64) ↦ₛ rand.toList) := by
          rw [hrand_words (sp + 7536#64)]; exact Entails.refl _
        refine SepWP.fold hfold_rand_7536 (by dsimp only [words4At]; sep_focus) ?_
        refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
        wp_apply
        wp_conv_pre => simp only [hencaps, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro _
        refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp) (by simp only [hsp2]; sep_focus) ?_
        have h7536 : ((sp + 7536#64) ↦ₛ rand.toList) ⊢ memRegion (sp + 7536#64) 32 := by
          have h := pointsToBytes_entails_memRegion (sp + 7536#64) rand.toList
          rwa [List.Vector.toList_length] at h
        refine SepWP.fold h7536 (by sep_focus) ?_
        rw [ProofLib.memRegion_split' (b := sp + 7536#64) (n := 1) (k := 31) (b' := sp + 7537#64)
              rfl (by rw [BitVec.add_assoc]; rfl) (by decide), ProofLib.memRegion_one (sp + 7536#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro _; wp_steps
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro _
        exact SepWPp.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
  · intro sm Pm hpc_sm hrun_sm htr_sm
    exact finish_model_panic hp (by rw [hpc_sm]; exact hunwrap) hrun_sm htr_sm

/-- Wrapper around `step_headerReceived_1312_encaps1_none` starting from `chunkedStatesAt A (sp + 0x950#64) (.headerReceived st)` and `statesSendPreArmScratch sp`. -/
theorem step_send_arm_headerReceived_encaps1_none {F : ShaCompress} {K : MlKem}
    {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64} {ext : String → Option (State → State)}
    (hbase : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl))
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    {s0 s : State} (sp cur : BitVec 64) (tape : Bytes) (h32 : 32 ≤ tape.length)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none)
    {ret : BitVec 64} {P Frame R : SepProp} {P_panic : Prop} {post : State → SepProp → Prop}
    (hp : P_panic) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tapeAt ctl cur tape ∗
      chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗ statesSendPreArmScratch sp) ∗ Frame) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  subst hP; unfold statesSendPreArmScratch
  apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64) img hinv
  refine SepWP.fold (chunkedStatesAt_headerReceived_expose sp st) (by sep_focus) ?_
  rw [ProofLib.memRegion_eight (sp + 4056#64),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 48) (k := 456) (b' := sp + 4240#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 961) (k := 1439) (b' := sp + 5665#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 32) (k := 368) (b' := sp + 7168#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 32) (k := 368) (b' := sp + 7568#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d4056; apply SepWP.exists_elim; intro g
  apply SepWP.exists_elim; intro hdr_cap; apply SepWP.exists_elim; intro hdr_ptr
  refine SepWP.fold (Entails.refl ⌜st.uc.hdr.length < 2 ^ 63⌝) (by sep_focus) ?_
  refine SepWP.pure_elim fun hhdr_lt => ?_
  apply SepWP.done hpc hrun; intro hinv0
  exact step_headerReceived_1312_encaps1_none hbase hA hZero hrng henc1 g st.uc.auth st.uc.epoch
    hdr_cap hdr_ptr st.uc.hdr hhdr_lt sp cur tape h32 rand rfl hencaps d4056
    (Frame := memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4240#64) 456 ∗ memRegion (sp + 5665#64) 1439 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7168#64) 368 ∗
      memRegion (sp + 7568#64) 368 ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
      polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗
      memRegion (sp + 2872#64) 440 ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hp hinv0 hsp_align hpc hrun hsp hx24 hx26 hx28 htr (by ac_rfl)

end HeaderReceivedPanic

/-! ## Phase 4 + Epilogue (`0x320a4 -> s0.readReg64 .x30`) -/

theorem message_serialize_len_lt_2_32 (msg : Message spqrPolyApi) (idx : BitVec 32) :
    (msg.serialize idx).length < 2 ^ 32 :=
  message_serialize_length_lt_2_32 msg idx

theorem memRegion_0_60_join (sp w0 w16 : BitVec 64) :
    (sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 8 ∗ ((sp + 16#64) ↦₆₄ w16) ∗
      memRegion (sp + 24#64) 24 ∗ memRegion (sp + 0x30#64) 48 ⊢
    memRegion sp 0x60 := by
  rw [ProofLib.memRegion_split' (b := sp) (n := 8) (k := 88) (b' := sp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := sp + 8#64) (n := 8) (k := 80) (b' := sp + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 72) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 24#64) (n := 24) (k := 48) (b' := sp + 0x30#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))

def stackRestA (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0xb0#64) 224 ∗ memRegion (sp + 0x548#64) 8 ∗
  memRegion (sp + 0x576#64) 10 ∗ memRegion (sp + 0x928#64) 40

theorem memRegion_b0_950_eq (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x950 - 0xb0) =
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗ stackRestA sp := by
  unfold stackRestA
  rw [ProofLib.memRegion_split' (b := sp + 0xb0#64) (n := 224) (k := 1984) (b' := sp + 0x190#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x190#64) (n := 928) (k := 1056) (b' := sp + 0x530#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x530#64) (n := 24) (k := 1032) (b' := sp + 0x548#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x548#64) (n := 8) (k := 1024) (b' := sp + 0x550#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x550#64) (n := 38) (k := 986) (b' := sp + 0x576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x576#64) (n := 10) (k := 976) (b' := sp + 0x580#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x580#64) (n := 16) (k := 960) (b' := sp + 0x590#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 920) (k := 40) (b' := sp + 0x928#64) rfl (by bv_omega) (by decide)]
  ac_rfl

def stackRestC (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0xdd8#64) 8 ∗ memRegion (sp + 4184#64) 8 ∗
  memRegion (sp + 4696#64) 8 ∗ memRegion (sp + 7128#64) 8 ∗
  memRegion (sp + 7936#64) 32

theorem memRegion_cf0_1f20_eq (sp : BitVec 64) :
    memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗
      memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4056#64) 8 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 0x1260#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗ stackRestC sp := by
  unfold stackRestC
  rw [ProofLib.memRegion_split' (b := sp + 0xcf0#64) (n := 80) (k := 4576) (b' := sp + 0xd40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xd40#64) (n := 80) (k := 4496) (b' := sp + 0xd90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xd90#64) (n := 72) (k := 4424) (b' := sp + 0xdd8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xdd8#64) (n := 8) (k := 4416) (b' := sp + 3552#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 3552#64) (n := 504) (k := 3912) (b' := sp + 4056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4056#64) (n := 8) (k := 3904) (b' := sp + 4064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4064#64) (n := 16) (k := 3888) (b' := sp + 4080#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 104) (k := 3784) (b' := sp + 4184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4184#64) (n := 8) (k := 3776) (b' := sp + 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 504) (k := 3272) (b' := sp + 4696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4696#64) (n := 8) (k := 3264) (b' := sp + 0x1260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 2400) (k := 864) (b' := sp + 7104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 24) (k := 840) (b' := sp + 7128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7128#64) (n := 8) (k := 832) (b' := sp + 7136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 400) (k := 432) (b' := sp + 7536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 400) (k := 32) (b' := sp + 7936#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_b0_1f20_eq (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) =
      memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0x950#64) 928 ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) := by
  rw [ProofLib.memRegion_split' (b := sp + 0xb0#64) (n := 0x950 - 0xb0) (k := 0x1f20 - 0x950) (b' := sp + 0x950#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x950#64) (n := 928) (k := 0x1f20 - 0xcf0) (b' := sp + 0xcf0#64) rfl (by bv_omega) (by decide)]

theorem sepWPp_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem msgKey_slots_nil (A : RustAlloc) (sp : BitVec 64) :
    ((sp + 24#64) ↦₆₄ BitVec.ofNat 64 ([] : Bytes).length) ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗
        DecodeState.vecU8Heap A mkCap mkPtr []) ⊢
    optMsgKeySlotsAt A sp none := by
  dsimp only [optMsgKeySlotsAt, List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkCap
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkPtr
  exact Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.of_eq (by ac_rfl)))

theorem msgKey_slots_len32 (A : RustAlloc) (sp : BitVec 64) (msgKey : Bytes)
    (h32 : msgKey.length = 32) :
    ((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗
        DecodeState.vecU8Heap A mkCap mkPtr msgKey) ⊢
    optMsgKeySlotsAt A sp (some ⟨msgKey, h32⟩) := by
  dsimp only [optMsgKeySlotsAt, List.Vector.toList]; rw [h32]
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkCap
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkPtr
  exact Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.of_eq (by ac_rfl)))

theorem spqrHkdfWith_len_64 (F : ShaCompress) (salt ikm info : Bytes) :
    (spqrHkdfWith F salt ikm info 64).length = 64 := by
  change (CryptoGames.HKDF.hkdfExpand F (hkdfExtractBytes F salt ikm) info 64).length = 64
  rw [HkdfToSliceProof.hkdfExpand_64_eq]
  simp [Expand.t1_length, Expand.t2_length]

theorem nextKey_msgKey_len_32 (F : ShaCompress) (ced : ChainEpochDirection)
    {ced' : ChainEpochDirection} {idx : BitVec 32} {msgKey : Bytes}
    (h : ced.nextKey (spqrHkdfWith F) = .ok (ced', (idx, msgKey))) :
    msgKey.length = 32 := by
  unfold ChainEpochDirection.nextKey at h
  dsimp only [Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at h
  rcases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) ced.next ced.ctr with _ | ⟨next', ctr', idx', mk'⟩ <;>
    rw [hnk] at h <;> dsimp only at h
  · contradiction
  · injection h with hpair; injection hpair with _ hout; injection hout with _ hmk
    unfold ChainEpochDirection.nextKeyInternal at hnk
    split at hnk <;> first | contradiction | skip
    split at hnk <;> first | contradiction | skip
    injection hnk with h1; injection h1 with _ h2; injection h2 with _ h3; injection h3 with _ hmk'
    rw [← hmk, ← hmk', List.length_take, List.length_drop, spqrHkdfWith_len_64]
    decide

theorem sendKey_msgKey_len_32 (F : ShaCompress) (c : Chain) (ep : Epoch)
    {c' : Chain} {idx : BitVec 32} {msgKey : Bytes}
    (h : c.sendKey (spqrHkdfWith F) ep = .ok (c', (idx, msgKey))) :
    msgKey.length = 32 := by
  unfold Chain.sendKey at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind, ChainResult.ofError] at h
    rcases hcidx : c.epochIdx ep with _ | idx0 <;> rw [hcidx] at h <;> dsimp only at h
    · contradiction
    · split at h
      · contradiction
      · rename_i link hlink
        rcases hnk : link.send.nextKey (spqrHkdfWith F) with _ | ⟨send', idx', mk'⟩ <;>
          rw [hnk] at h <;> dsimp only [ChainResult.ofPanic] at h
        · contradiction
        · injection h with hpair
          injection hpair with _ hout
          injection hout with _ hmk
          rw [← hmk]
          exact nextKey_msgKey_len_32 F link.send hnk

theorem sendKeyIntoPbChain_msgKey_len_32 (F : ShaCompress) (c : Chain) (epoch : Epoch)
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (h : sendKeyIntoPbChain (spqrHkdfWith F) c epoch = .ok (idx, msgKey, chainPb)) :
    msgKey.length = 32 := by
  unfold sendKeyIntoPbChain at h
  split at h
  · contradiction
  · rcases hsk : c.sendKey (spqrHkdfWith F) (epoch - 1#64) with e | ⟨c2, idx', mk'⟩ <;>
      rw [hsk] at h <;> dsimp only [SpqrApiResult.ofChainResult] at h
    · rcases e with _ | _ <;> contradiction
    · injection h with h1; injection h1 with _ h2; injection h2 with hmk _
      rw [← hmk]
      exact sendKey_msgKey_len_32 F c (epoch - 1#64) hsk

theorem sendChainPhase_msgKey_cases (F : ShaCompress) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (epoch : Epoch)
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (h : sendChainPhase (spqrHkdfWith F) chain vn key epoch = .ok (idx, msgKey, chainPb)) :
    msgKey = [] ∨ msgKey.length = 32 := by
  unfold sendChainPhase at h
  rcases hres : sendResolveChain (spqrHkdfWith F) chain vn with _ | (_ | c0) <;>
    rw [hres] at h <;> dsimp only [Bind.bind, Except.bind, sendStepChain] at h
  · contradiction
  · split at h
    · injection h with h1; injection h1 with _ h2; injection h2 with hmk _; exact Or.inl hmk.symm
    · contradiction
  · rcases key with _ | es <;> dsimp only at h
    · exact Or.inr (sendKeyIntoPbChain_msgKey_len_32 F c0 epoch h)
    · rcases hae : c0.addEpoch (spqrHkdfWith F) es with _ | c1 <;>
        rw [hae] at h <;> dsimp only [SpqrApiResult.ofChainPanic] at h
      · contradiction
      · exact Or.inr (sendKeyIntoPbChain_msgKey_len_32 F c1 epoch h)

theorem msgKey_to_optMsgKeySlotsAt (A : RustAlloc) (sp : BitVec 64) (msgKey : Bytes)
    (h : msgKey = [] ∨ msgKey.length = 32) :
    ∃ salt : CryptoGames.HKDF.Salt,
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt ∧
      (((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗
          DecodeState.vecU8Heap A mkCap mkPtr msgKey) ⊢
        optMsgKeySlotsAt A sp salt) := by
  rcases h with rfl | h32
  · refine ⟨none, rfl, msgKey_slots_nil A sp⟩
  · have hne : msgKey.isEmpty = false := by
      cases msgKey with
      | nil => simp at h32
      | cons _ _ => rfl
    refine ⟨some ⟨msgKey, h32⟩, ?_, msgKey_slots_len32 A sp msgKey h32⟩
    simp [hne, messageKeyToSalt?, h32]

theorem memRegion_1424_224_eq_24_200 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 224 =
      memRegion (sp + 1424#64) 24 ∗ memRegion (sp + 1448#64) 200 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 200) (b' := sp + 1448#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_590_224_eq_88_136 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 224 =
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 1512#64) 136 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 88) (k := 136) (b' := sp + 1512#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_1060_80_eq_48_32 (sp : BitVec 64) :
    memRegion (sp + 0x1060#64) 80 =
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 32 :=
  ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 48) (k := 32) (b' := sp + 4240#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_1260_928_eq_352_576 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 928 =
      memRegion (sp + 4704#64) 352 ∗ memRegion (sp + 5056#64) 576 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 352) (k := 576) (b' := sp + 5056#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_1260_928_eq_88_840 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 928 =
      memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 88) (k := 840) (b' := sp + 4792#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_7136_400_eq_16_384 (sp : BitVec 64) :
    memRegion (sp + 7136#64) 400 =
      memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 7152#64) 384 :=
  ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_0_30_eq (sp : BitVec 64) :
    memRegion sp 0x30 =
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗
      memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 8 ∗
      memRegion (sp + 32#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp) (n := 8) (k := 40) (b' := sp + 0x8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := sp + 0x8#64) (n := 8) (k := 32) (b' := sp + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 24) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 24#64) (n := 8) (k := 16) (b' := sp + 32#64) rfl (by bv_omega) (by decide)]

theorem memRegion_32_16_eq_8_8 (sp : BitVec 64) :
    memRegion (sp + 32#64) 16 =
      memRegion (sp + 32#64) 8 ∗ memRegion (sp + 0x28#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 32#64) (n := 8) (k := 8) (b' := sp + 0x28#64)
    rfl (by bv_omega) (by decide)

def stackRestB0_950 (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
  memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1648#64) 696 ∗ stackRestA sp

theorem memRegion_590_920_eq (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 920 =
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 1512#64) 136 ∗ memRegion (sp + 1648#64) 696 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 88) (k := 832) (b' := sp + 1512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 1512#64) (n := 136) (k := 696) (b' := sp + 1648#64) rfl (by bv_omega) (by decide)]

theorem memRegion_b0_950_eq_rest (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x950 - 0xb0) =
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x590#64) 88 ∗
      memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp := by
  rw [memRegion_b0_950_eq sp, memRegion_590_920_eq sp]
  unfold stackRestB0_950
  ac_rfl

def stackRestCF0_1F20 (sp : BitVec 64) : SepProp :=
  memRegion (sp + 3632#64) 424 ∗ memRegion (sp + 4056#64) 8 ∗
  memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4104#64) 80 ∗
  memRegion (sp + 4272#64) 424 ∗ memRegion (sp + 5632#64) 1472 ∗
  memRegion (sp + 7120#64) 8 ∗ memRegion (sp + 7152#64) 384 ∗
  memRegion (sp + 7584#64) 352 ∗ stackRestC sp

theorem statesSendPostArmScratch_split (sp : BitVec 64) :
    statesSendPostArmScratch sp ∗ stackRestC sp =
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
      memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
      memRegion (sp + 7136#64) 16 ∗ stackRestCF0_1F20 sp := by
  unfold statesSendPostArmScratch stackRestCF0_1F20
  rw [ProofLib.memRegion_split' (b := sp + 3552#64) (n := 80) (k := 424) (b' := sp + 3632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 24) (k := 80) (b' := sp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 80) (k := 424) (b' := sp + 4272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 88) (k := 2312) (b' := sp + 4792#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4792#64) (n := 840) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_cf0_1f20_eq_rest (sp : BitVec 64) :
    memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
      memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
      memRegion (sp + 0x1d70#64) 48 ∗ stackRestCF0_1F20 sp := by
  rw [memRegion_cf0_1f20_eq sp]
  unfold stackRestCF0_1F20
  rw [ProofLib.memRegion_split' (b := sp + 3552#64) (n := 80) (k := 424) (b' := sp + 3632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 24) (k := 80) (b' := sp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 80) (k := 424) (b' := sp + 4272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 88) (k := 2312) (b' := sp + 4792#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4792#64) (n := 840) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 16) (k := 8) (b' := sp + 7120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 48) (k := 352) (b' := sp + 7584#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_b0_1f20_eq_finish (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) =
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1424#64) 24 ∗
      memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4240#64) 32 ∗ memRegion (sp + 4704#64) 352 ∗
      memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
      memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
      stackRestCF0_1F20 sp := by
  have h590 : memRegion (sp + 0x590#64) 920 =
      memRegion (sp + 1424#64) 24 ∗ memRegion (sp + 1448#64) 200 ∗ memRegion (sp + 1648#64) 696 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 224) (k := 696) (b' := sp + 1648#64) rfl (by bv_omega) (by decide),
        memRegion_1424_224_eq_24_200 sp]
    ac_rfl
  have h1260 : memRegion (sp + 0x1260#64) 2400 =
      memRegion (sp + 4704#64) 352 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 5632#64) 1472 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 928) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
        memRegion_1260_928_eq_352_576 sp]
    ac_rfl
  rw [memRegion_b0_1f20_eq sp, memRegion_b0_950_eq sp, h590, memRegion_cf0_1f20_eq sp, h1260]
  unfold stackRestB0_950 stackRestCF0_1F20
  rw [ProofLib.memRegion_split' (b := sp + 3552#64) (n := 80) (k := 424) (b' := sp + 3632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 24) (k := 80) (b' := sp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 80) (k := 424) (b' := sp + 4272#64) rfl (by bv_omega) (by decide),
      memRegion_1060_80_eq_48_32 sp,
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 16) (k := 8) (b' := sp + 7120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 48) (k := 352) (b' := sp + 7584#64) rfl (by bv_omega) (by decide)]
  ac_rfl


end CryptoVerification.SpqrV1.Top.Send
