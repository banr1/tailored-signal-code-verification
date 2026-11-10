/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatch
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Alignment-Free Phase 4 Finish & `.headerReceived` `encaps1 = none` Panic Arm

Proves alignment-free `step_send_finish_320a4'` (`+6216 -> +4600`) and the `.headerReceived`
panic path (`K.encaps1 hdr rand = none`) for `spqr::send::<signal_session_ratchet::Coins>`.
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

/-! ## 1. Phase 4 Finish (`+6216 -> +4600`) without `hret_align` -/

/-- `entry + 6216#64 -> entry + 6328#64`, 28 instructions = 112 bytes,
    without requiring `hret_align` on `ret`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_build_result_320a4' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (Frame : SepProp)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6216#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 4192#64) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6328#64) s
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
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 6216 112
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- `entry + 6216#64 -> entry + 4600#64`, without requiring `hret_align`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_finish_320a4' {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext) (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (Frame : SepProp) (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 6216#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hflag : x21 = LibsignalTripleRatchetRepr.noneCap ∨ BitVec.truncate 32 v_20 = 0#32) (hx25_ch : (x25 + 1#64 == 0#64) = !st.chain.isSome)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 4600#64) s
      (memRegion ret 72 ∗ vecU8 A (s.sp + 1424#64) stBytes ∗ vecU8 A (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A s.sp key ∗ ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
        pqRatchetStatePBPinnedAt A g (s.sp + 4704#64) st ∗
        CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q => sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗ memRegion (s.sp + 1424#64) 24 ∗
          memRegion (s.sp + 4080#64) 24 ∗ memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 4704#64) 352 ∗
          memRegion (s.sp + 7136#64) 16 ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  refine SepWP.focus_weaken (pqRatchetStatePBPinnedAt_entails_proto A g (s.sp + 4704#64) st) (by sep_focus) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.seq (CryptoVerification.Cli.SpqrV1.Top.Send.step_send_build_result_320a4' hdealloc s ret v_20 x21 x23 x25 x27 stBytes msgBytes key
      (Drop.protoPqRatchetStateAt A (s.sp + 4704#64) st ∗ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗ Frame)
      hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 hx28 hsp_align) ?_)
  intro s1 Q1 hpc1 _ ⟨hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx25_1, _, hvregs1, hQ1⟩
  have hflag1 : s1.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s1.readReg32 .x19 = 0#32 := by
    rcases hflag with h21 | h20
    · left; rw [hx21_1, h21]
    · right; simp only [State.readReg32, hx19_1, h20]
  refine SepWP.seq (CryptoVerification.Cli.SpqrV1.Top.Send.step_send_epoch_dealloc_32114 s1 x23 x25 Q1 hpc1 hrun1 hx23_1 hx25_1 hflag1) ?_
  intro s2 Q2 hpc2 _ ⟨hrun2, htr2, hsp2, hx23_2, hx25_2, hvregs2, hQ2⟩
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2, hsp1]
  have hx25_2' : (s2.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome := by rw [hx25_2, hx25_ch]
  have hQ2' := Entails.trans hQ2 hQ1; rw [← hsp1, ← hsp2] at hQ2'
  refine SepWP.weaken_pre (Entails.trans hQ2' (Entails.of_eq (by ac_rfl)))
    (SepWP.mono (CryptoVerification.Cli.SpqrV1.Top.Send.step_send_drop_pq_state_32134 hb hdealloc s2 st x23
      (spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
        memRegion (s2.sp + 8#64) 8 ∗ memRegion (s2.sp + 24#64) 24 ∗
        memRegion (s2.sp + 1424#64) 24 ∗ memRegion (s2.sp + 4080#64) 24 ∗
        memRegion (s2.sp + 4192#64) 48 ∗ memRegion (s2.sp + 7136#64) 16 ∗ Frame)
      hpc2 hrun2 hsp2_align hx23_2 hx25_2') ?_)
  intro sf Qf _ _ ⟨hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
  refine ⟨hrunf, htrf.trans (htr2.trans htr1), hspf.trans (hsp2.trans hsp1), hx23_f, hvregsf.trans (hvregs2.trans hvregs1), ?_⟩
  rw [hsp2, hsp1] at hQf; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))

/-! ## 2. Size Bound for `pqRatchetStatePBEncodedLen` on `send` Output -/

section HeaderReceivedPanic

attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

@[local arm64_norm, local wp_norm]
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_33d70 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 13588#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") + 13588)) := by
  rw [Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff]
  revert hb; bv_bits

@[local arm64_norm, local wp_norm]
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_33d78 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 13596#64) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% ((ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") + 13596)) := by
  rw [Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff]
  revert hb; bv_bits

attribute [local simp, local arm64_norm ↓, local wp_norm ↓] CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_headerReceived_1312_encaps1_none_noRng
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)} (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (hencaps : K.encaps1 hdr rand = none) (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {P_panic : Prop} {post : State → SepProp → Prop}
    (hp : P_panic) (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64) (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7536#64) 32 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base cur tape ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) sessionShimSpec :=
    hA.shim_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) (by fnoff_eq)
  have hallocz : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc_zeroed")) (rustAllocZeroedSpec A) :=
    alloc_zeroed_ok_at_ext img.base A ext hZero CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc_zeroed")) (by fnoff_eq)
  have hrng_call := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_coinsFill_ok (b := img.base) hA hbase
  have henc1_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "libcrux_ml_kem::mlkem768::incremental::encapsulate1")) (mlkemEncaps1Spec K) :=
    hook_ok_at (hname := mlkemEncaps1Name) rfl (by fnoff_eq) (by fnoff_eq) (by fnoff_eq) (by decide +kernel) henc1
  have haerr : (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) = some Rust.panicked :=
    panic_at_handle_error_ext img.base ext CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error"))
      (by change libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error") = libsignalSessionCode.fnOff "alloc::raw_vec::handle_error"; rw [CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])
  have hunwrap : (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::result::unwrap_failed")) = some Rust.panicked :=
    panic_at_sym_ext img.base ext CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName "core::result::unwrap_failed"
      (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::result::unwrap_failed")) (by fnoff_eq) (hp := by decide +kernel)
  have hadrp1 := CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_33d70 (H := Rust.withPanics ext) hbase
  have hadrp2 := CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_adrp_33d78 (H := Rust.withPanics ext) hbase
  have hhdr_toNat : (BitVec.ofNat 64 hdr.length).toNat = hdr.length := Nat.mod_eq_of_lt (by omega)
  spqr_send_fetches_range_cli img.base (Rust.withPanics ext) 1312 192
  spqr_send_fetches_range_cli img.base (Rust.withPanics ext) 11832 64
  spqr_send_fetches_range_cli img.base (Rust.withPanics ext) 13588 48
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry
  examples_hide_fetches; subst hP
  refine sepWPp_bind (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::result::unwrap_failed")) (Q := fun sf _ => sf.trace = s0.trace)
    (sepWPp_lift_allowPanic ?_) ?_
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc_zeroed")) img hinv
    rw [memRegion_48_eq_words6 (sp + 4192#64), memRegion_32_eq_words4 (sp + 7136#64),
        memRegion_32_eq_words4 (sp + 7536#64)]
    dsimp only [authInlineWordsAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 14 (apply SepWP.exists_elim; intro _)
    wp_steps
    refine SepWP.fold (words4At_entails_memRegion (sp + 7136#64) _ _ _ _) (by dsimp only [words4At]; sep_focus) ?_
    refine SepWP.fold (CryptoVerification.Cli.SpqrV1.Top.Send.coinsAt_entails_coinsAfter_zero img.base cur tape) (by sep_focus) ?_
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
    · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) img hinv_oom1; wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
    · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, _⟩
      simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
      apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc_zeroed")) img hinv_ok1
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
      · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) img hinv_oom2; wp_steps
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro _
        exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
      · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, _⟩
        simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2
        apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::result::unwrap_failed")) img hinv_ok2
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

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_headerReceived_1312_encaps1_none
    {img : Obj.Image} {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (_hrng : HookSat ext rngFillName (rngFillSpec ctl)) (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (hencaps : K.encaps1 hdr rand = none) (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {P_panic : Prop} {post : State → SepProp → Prop}
    (hp : P_panic) (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64) (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7536#64) 32 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base cur tape ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_headerReceived_1312_encaps1_none_noRng
    hbase hA hZero henc1 g auth epoch hdr_cap hdr_ptr hdr hhdr_lt sp cur tape h32 rand hrand_val hencaps d4056
    hp hinv hsp_align hpc hrun hsp hx24 hx26 hx28 htrace hP

/-- Wrapper around `CryptoVerification.Cli.SpqrV1.Top.Send.step_headerReceived_1312_encaps1_none_noRng` starting from `chunkedStatesAt A (sp + 0x950#64) (.headerReceived st)` and `statesSendPreArmScratch sp`, without unused `rngFill` hook hypothesis. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_arm_headerReceived_encaps1_none_noRng {F : ShaCompress} {K : MlKem}
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hbase : img.base &&& 0xfff#64 = 0#64) (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    {s0 s : State} (sp cur : BitVec 64) (tape : Bytes) (h32 : 32 ≤ tape.length)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none)
    {ret : BitVec 64} {P Frame R : SepProp} {P_panic : Prop} {post : State → SepProp → Prop}
    (hp : P_panic) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur tape ∗
      chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗ statesSendPreArmScratch sp) ∗ Frame) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  subst hP; unfold statesSendPreArmScratch
  apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 1312#64) img hinv
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
  exact CryptoVerification.Cli.SpqrV1.Top.Send.step_headerReceived_1312_encaps1_none_noRng hbase hA hZero henc1 g st.uc.auth st.uc.epoch
    hdr_cap hdr_ptr st.uc.hdr hhdr_lt sp cur tape h32 rand rfl hencaps d4056
    (Frame := memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4240#64) 456 ∗ memRegion (sp + 5665#64) 1439 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7168#64) 368 ∗
      memRegion (sp + 7568#64) 368 ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
      polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗
      memRegion (sp + 2872#64) 440 ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hp hinv0 hsp_align hpc hrun hsp hx24 hx26 hx28 htr (by ac_rfl)

/-- Wrapper around `CryptoVerification.Cli.SpqrV1.Top.Send.step_headerReceived_1312_encaps1_none` starting from `chunkedStatesAt A (sp + 0x950#64) (.headerReceived st)` and `statesSendPreArmScratch sp`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_arm_headerReceived_encaps1_none {F : ShaCompress} {K : MlKem}
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
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur tape ∗
      chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗ statesSendPreArmScratch sp) ∗ Frame) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  let _ := hrng
  exact CryptoVerification.Cli.SpqrV1.Top.Send.step_send_arm_headerReceived_encaps1_none_noRng
    hbase hA hZero henc1 sp cur tape h32 st hencaps hp hinv hpc hrun hsp hsp_align htr hx24 hx26 hx28 hP

end HeaderReceivedPanic

end CryptoVerification.SpqrV1.Top.Send
