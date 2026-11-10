/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Nat.Bitwise.Basic
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeader
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3a
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked3a
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<signal_session_ratchet::Coins>` Phase 3e (Part 3a): `V1State` Variants `idx = 10, 6`

Proves shared bytes-field stepping helpers and `V1State::encode_raw` arms `ct2Sampled` (`idx = 10`)
and `headerReceived` (`idx = 6`) for the CLI image.
-/

@[expose] public section

set_option linter.style.longLine false

set_option autoImplicit false

set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalTripleRatchet
  (spqrSendName withStack subroutine_ok_withStack_of_subroutine_ok)

open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding allowPanic_not_exited

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Shared Stepping Helpers for Bytes Fields -/

private theorem step_send_memcpy_call_4k {resStack : Nat}
    (b : BitVec 64) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  have hmemcpy_inv := subroutine_ok_withStepInv s0 hmemcpy
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy_inv hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · intro sf _ R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withStepInv, withStack, etvMemcpyRegionSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.send3a_step_memcpy_slice_4k {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (sp cap ptr srcCap srcPtr ret_pc : BitVec 64) (bs4 srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false) (hsrc_le : srcBs.length ≤ srcCap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs4.length) (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 srcBs.length) (hsrc_lt : srcBs.length < 2 ^ 64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length) srcBs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
          (cap.toNat - bs4.length - srcBs.length)) ∗ EncodedLen.vecU8Buf A srcCap srcPtr srcBs ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
            ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
            ((ptr + BitVec.ofNat 64 bs4.length) ↦ₛ srcBs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs4.length - srcBs.length)) ∗ EncodedLen.vecU8Buf A srcCap srcPtr srcBs ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP; rw [vecU8Buf_eq_of_nonempty A srcCap srcPtr srcBs hemp hsrc_le]
  have hlen_toNat : (BitVec.ofNat 64 srcBs.length).toNat = srcBs.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  refine step_send_memcpy_call_4k b ext hmemcpy (ptr + BitVec.ofNat 64 bs4.length) srcPtr sp ret_pc srcBs
    (F := ((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗ ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
      memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length) (cap.toNat - bs4.length - srcBs.length) ∗
      (⌜srcBs.length ≤ srcCap.toNat ∧ srcCap.toNat < 2 ^ 63 ∧ srcPtr ≠ 0⌝ ∗ A.live srcPtr srcCap.toNat 1 ∗
        memRegion (srcPtr + BitVec.ofNat 64 srcBs.length) (srcCap.toNat - srcBs.length)) ∗
      A.pool ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 (by simp only [hx2, hlen_toNat]) hinv0 (by ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm hpcm hrunm hspm htrm hcsm hinvm)
  rw [vecU8Buf_eq_of_nonempty A srcCap srcPtr srcBs hemp hsrc_le]; ac_rfl

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.send3a_step_memcpy_slice {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) etvMemcpyRegionSpec)
    (sp cap ptr srcCap srcPtr ret_pc : BitVec 64) (bs4 srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false) (hsrc_le : srcBs.length ≤ srcCap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs4.length) (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 srcBs.length) (hsrc_lt : srcBs.length < 2 ^ 64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length) srcBs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
          (cap.toNat - bs4.length - srcBs.length)) ∗ EncodedLen.vecU8Buf A srcCap srcPtr srcBs ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
            ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
            ((ptr + BitVec.ofNat 64 bs4.length) ↦ₛ srcBs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs4.length - srcBs.length)) ∗ EncodedLen.vecU8Buf A srcCap srcPtr srcBs ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) :=
  CryptoVerification.Cli.SpqrV1.Top.Send.send3a_step_memcpy_slice_4k b A ext
    (subroutine_ok_withStack_of_subroutine_ok hmemcpy (encodeToVecCalleeStackOf resStack))
    sp cap ptr srcCap srcPtr ret_pc bs4 srcBs hemp hsrc_le halign
    hpc hrun hsp htr hlr hx0 hx1 hx2 hsrc_lt hinv0 hP hnext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct2Sampled {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) {s0 s : State}
    (hct2Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : PolynomialEncoderPBGhost × Unchunked2PBGhost) (v : V1State.Chunked.Ct2Sampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct2Sampled v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 8896#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) v.sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) v.uc) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm (((optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) v.sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) v.uc) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct2Sampled v)) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 8896 8960; send_fetches_cli b (Rust.withPanics ext) hfn 9376 9488
  send_fetches_cli b (Rust.withPanics ext) hfn 10124 10296; examples_hide_fetches; subst hP; rcases v with ⟨uc, sendingCt2⟩
  rw [etv3_encodeInnerState_ct2Sampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x5a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optCt2SentCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧ (Prost.EncodeToVec.optCt2SentCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyEncCap g.1 sendingCt2 + 1#64 == 0#64) = !sendingCt2.isSome ∧ (Prost.EncodeToVec.optPolyEncCap g.1 sendingCt2 + 1#64 != 0#64) = sendingCt2.isSome))
    (fun R' hm => ⟨Prost.EncodeToVec.optCt2SentPBPinnedAt_cap_bounds (p := sp + 4896#64)
        (R := optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
      Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x5a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9424 : ∀ sm1 : State, sm1.pc = entry + 9424#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 → sm1.readReg64 .x21 = s.readReg64 .x21 →
      sm1.readReg64 .x22 = Prost.EncodeToVec.optCt2SentCap g.2 uc → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x25 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm1 (((optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optCt2SentPBPinnedAt_eq A g.2 (sp + 4896#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 9424#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optCt2SentPBPinnedAt_eq A g.2 (sp + 4896#64) none, ← hpack]))
        (h9424 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optCt2SentPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    | some u =>
      rw [Prost.EncodeToVec.optCt2SentPBPinnedAt_eq A g.2 (sp + 4896#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct2SentPBEncodedLen u < 2 ^ 64 ∧ optCt2SentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) < optCt2SentPBFieldEncodedLen (some u) := by dsimp only [optCt2SentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ProtoRepr.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv3_bv_optCt2Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optCt2SentPBPinnedAt_eq A g.2 (sp + 4896#64) (some u)]
      refine step_send_leaf_encLen16_call hres b ext (ct2SentPBPinnedAt A) ct2SentPBEncodedLen hct2Len (sp + 4896#64) sp (entry + 9384#64) g.2 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optCt2SentPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩ hinv_m1
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 9424#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optCt2SentPBPinnedAt]; ac_rfl))
        (h9424 _ (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10128 : ∀ sm2 : State, sm2.pc = entry + 10128#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingCt2) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 → sm2.readReg64 .x21 = s.readReg64 .x21 →
      sm2.readReg64 .x22 = Prost.EncodeToVec.optCt2SentCap g.2 uc → sm2.readReg64 .x23 = s.readReg64 .x23 →
      sm2.readReg64 .x24 = Prost.EncodeToVec.optPolyEncCap g.1 sendingCt2 → sm2.readReg64 .x25 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm2 (((optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingCt2 with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10128#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.1 (sp + 4840#64) none]))
        (h10128 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
    | some enc =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.1 (sp + 4840#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ : polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) < optPolynomialEncoderPBFieldEncodedLen (some enc) := by dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ProtoRepr.ult_of_lt_of_fit hvar_e_lt hopt_e_lt, bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.1 (sp + 4840#64) (some enc)]
      refine step_send_leaf_encLen16_call hres b ext (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen (sp + 4840#64) sp (entry + 9444#64) g.1 enc henc_fit
        (F := optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 10128#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl))
        (h10128 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingCt2) (b := optCt2SentPBFieldEncodedLen uc) (c := v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)) rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x5a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
  refine step_send_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
    (sp + 1424#64) cap ptr sp (entry + 10144#64) (bs ++ [0x5a#8]) hfit_var
    (F := (optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 uc
  suffices h10280 : ∀ sm4 : State, sm4.pc = entry + 10280#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = Prost.EncodeToVec.optPolyEncCap g.1 sendingCt2 → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4 (((optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10280#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl))
        (h10280 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv3_encodeOptCt2Sent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : ct2SentPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      have hpack_tag := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr; rw [h1432, h1440] at hpack_tag
      refine step_send_leaf_encLen16_call hres b ext (ct2SentPBPinnedAt A) ct2SentPBEncodedLen hct2Len (sp + 4896#64) sp (entry + 10200#64) g.2 u hu_lt
        (F := optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_m3.trans hinv4) (by rw [← hpack_tag]; dsimp only [optCt2SentPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4 ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
      set bs_u1 := (bs1 ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))
      have hfit_uvar : (bs1 ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      refine step_send_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) (sp + 1424#64) cap ptr sp (entry + 10208#64) (bs1 ++ [0x0a#8]) hfit_uvar
        (F := optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ ct2SentPBPinnedAt A g.2 (sp + 4896#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m4.trans hinv5) (by ac_rfl) ?_
      intro sm5 hpcm5 hrunm5 hspm5 htrm5 ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩ hinv_m5
      simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, hm4_27, hm4_28, hm4_fp] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
      dsimp only [ct2SentPBPinnedAt, unchunked2PinnedAt]
      have h4896_48 : (sp + 4896#64) + 0x30#64 = sp + 4944#64 := by bv_omega
      rw [h4896_48]
      refine sepWPp_extract_pure
        ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
        (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4896#64)
          (R := optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ ((sp + 4944#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
            vecU8At A (sp + 1424#64) cap ptr bs_u1 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp only [bs_u1]; ac_rfl)) hm))
        fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
      set bs_u2 := bs_u1 ++ Proto.encodeUint64Field 1#32 u.epoch
      suffices h10260 : ∀ sm6 : State, sm6.pc = entry + 10260#64 → sm6.status = .Running → sm6.sp = sp → sm6.trace = s0.trace →
          sm6.readReg64 .x19 = s.readReg64 .x19 → sm6.readReg64 .x20 = sp + 4704#64 → sm6.readReg64 .x21 = s.readReg64 .x21 →
          sm6.readReg64 .x22 = Prost.EncodeToVec.optCt2SentCap g.2 (some u) → sm6.readReg64 .x23 = s.readReg64 .x23 →
          sm6.readReg64 .x24 = Prost.EncodeToVec.optPolyEncCap g.1 sendingCt2 → sm6.readReg64 .x25 = w25 →
          sm6.readReg64 .x27 = s.readReg64 .x27 → sm6.readReg64 .x28 = s.readReg64 .x28 → sm6.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm6 →
          SepWPp (tripleRatchetProgAtExt b ext) ret sm6 (((optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optAuthenticatorPBPinnedAt A g.2 (sp + 4896#64) u.auth ∗ ((sp + 4944#64) ↦₆₄ u.epoch)) ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs_u2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
        cases hep : u.epoch == 0#64
        · have hfit_ep : bs_u1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
            rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs_u1, bs1]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
          have hlt_ep : bs_u1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
          have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
          rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs_u1 hlt_ep hcap hptr, h1432, h1440]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
          apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
          have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs_u1 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
          refine step_send_encode_varint_call b A ext hvarint u.epoch (sp + 1424#64) cap ptr sp (entry + 10260#64) (bs_u1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ optAuthenticatorPBPinnedAt A g.2 (sp + 4896#64) u.auth ∗ ((sp + 4944#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6) (by rw [← hpack_ep]; ac_rfl) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, hm6_25, _, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
          simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_27, hm5_28, hm5_fp] at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25 hm6_27 hm6_28 hm6_fp
          refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl))
            (h10260 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25 hm6_27 hm6_28 hm6_fp hinv_m6)
        · apply SepWPp.of_sepWP_cs (mid := entry + 10260#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
          refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl))
            (h10260 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6))
      intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx27_6 hx28_6 hfp_6 hinv_6
      have hx22_eq : Prost.EncodeToVec.optCt2SentCap g.2 (some u) = optAuthCap g.2 u.auth := rfl; rw [hx22_eq] at hx22_6
      cases hauth : u.auth with
      | none =>
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        apply SepWPp.of_sepWP_cs (mid := entry + 10280#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq]; simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, Proto.encodeOptMessage, optCt2SentPBPinnedAt, ct2SentPBPinnedAt, unchunked2PinnedAt, h4896_48, List.append_nil, List.append_assoc]))
          (h10280 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_6.trans hinv7))
      | some auth =>
        simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
        have hfit_auth : bs_u2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
          rw [hauth] at hfit; dsimp only [bs_u2, bs_u1, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
        apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
        refine step_send_encode_auth_call b A ext hauthEnc (sp + 4896#64) (sp + 1424#64) cap ptr sp (entry + 10280#64) g.2 auth bs_u2 hfit_auth
          (F := (optPolynomialEncoderPBPinnedAt A g.1 (sp + 4840#64) sendingCt2 ∗ ((sp + 4944#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_6.trans hinv7) (by simp only [hauth, optAuthenticatorPBPinnedAt]; ac_rfl) ?_
        intro sm7 hpcm7 hrunm7 hspm7 htrm7 ⟨hm7_19, hm7_20, hm7_21, _, hm7_23, hm7_24, hm7_25, _, hm7_27, hm7_28, hm7_fp, _⟩ hinv_m7
        simp only [arm64_norm, hx19_6, hx20_6, hx21_6, hx23_6, hx24_6, hx25_6, hx27_6, hx28_6, hfp_6] at hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25 hm7_27 hm7_28 hm7_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10280 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25 hm7_27 hm7_28 hm7_fp hinv_m7)
        dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq]
        simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, Proto.encodeOptMessage, optCt2SentPBPinnedAt, ct2SentPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h4896_48, List.append_assoc]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingCt2 with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv3_encodeInnerState_ct2Sampled_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 11748#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_tail_11748_polyEnc b A ext hfn hpolyEnc (sp + 4840#64) sp cap ptr g.1 enc bs2 hfit_enc halign
      (F := optCt2SentPBPinnedAt A g.2 (sp + 4896#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv3_encodeInnerState_ct2Sampled_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl))
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)

/-! ## 2. Variant `idx = 6`: `.headerReceived` (`+8788 .. +11208`) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.send3a_step_headerReceived_some {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) {s0 s : State}
    (hhrLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked3PBGhost) (u : V1State.Unchunked.HeaderReceived) (bs : List (BitVec 8))
    (hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 10948#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (headerReceivedPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 11196#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm ((headerReceivedPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
        vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 10948 11196; examples_hide_fetches; subst hP
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  rw [etv3_encodeOptHeaderReceived_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack1 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
  refine step_send_leaf_encLen16_call hres b ext (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen hhrLen (sp + 4840#64) sp (entry + 10992#64) g u hu_lt
    (F := ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv1) (by rw [← hpack1]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, hm24, hm25, _, hm27, hm28, hmfp, _⟩ hinv_m1
  simp only [arm64_norm, hx24, hx25] at hm19 hm20 hm21 hm22 hm23 hm24 hm25 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))
  have hfit_var : (bs ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine step_send_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) (sp + 1424#64) cap ptr sp (entry + 11000#64) (bs ++ [0x0a#8]) hfit_var
    (F := headerReceivedPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
  simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
  dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
  have ⟨h4840_24, h4840_72⟩ : (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧ (sp + 4840#64) + 0x48#64 = sp + 4912#64 := ⟨by bv_omega, by bv_omega⟩
  rw [h4840_24, h4840_72]
  refine sepWPp_extract_pure
    ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
    (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4864#64)
      (R := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
        vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; ac_rfl)) hm))
    fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
  set bs2 := bs1 ++ Proto.encodeUint64Field 1#32 u.epoch
  suffices h11052 : ∀ sm3 : State, sm3.pc = entry + 11052#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
      sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = s.readReg64 .x20 → sm3.readReg64 .x21 = s.readReg64 .x21 →
      sm3.readReg64 .x22 = s.readReg64 .x22 → sm3.readReg64 .x23 = s.readReg64 .x23 →
      sm3.readReg64 .x24 = sp + 4704#64 → sm3.readReg64 .x25 = w25 →
      sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm3 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hep : u.epoch == 0#64
    · have hfit_ep : bs1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
        rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]; simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
      have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt_ep hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
      refine step_send_encode_varint_call b A ext hvarint u.epoch (sp + 1424#64) cap ptr sp (entry + 11052#64) (bs1 ++ [0x08#8])
        (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
        (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3) (by rw [← hpack_ep]) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
      simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl))
        (h11052 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp hinv_m3)
    · apply SepWPp.of_sepWP_cs (mid := entry + 11052#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl))
        (h11052 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
  set bs3 := bs2 ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
  suffices h11084 : ∀ sm4 : State, sm4.pc = entry + 11084#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x20 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x22 = s.readReg64 .x22 → sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hauth : u.auth with
    | none =>
      rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) none]; simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 11084#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) none]; simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, List.append_nil]))
        (h11084 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
    | some auth =>
      rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) (some auth)]; simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
      have hfit_auth : bs2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
        rw [hauth] at hfit; dsimp only [bs2, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) (some auth)]
      refine step_send_encode_auth_call b A ext hauthEnc (sp + 4864#64) (sp + 1424#64) cap ptr sp (entry + 11084#64) g.auth auth bs2 hfit_auth
        (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4) (by dsimp only [optAuthenticatorPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
      simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h11084 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, optAuthenticatorPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4840#64) (cap := g.f3.cap) (ptr := g.f3.ptr) (bs := u.hdr)
    (F := optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by dsimp only [bs3]; ac_rfl) fun hhdr_le hhdr_cap _ => ?_
  have ⟨h4848, h4856⟩ : (sp + 4840#64) + 8#64 = sp + 4848#64 ∧ (sp + 4840#64) + 16#64 = sp + 4856#64 := ⟨by bv_omega, by bv_omega⟩
  rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856]
  have hhdr_lt : u.hdr.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hhdr_lt
  cases hemp : u.hdr.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz hbnez
    have hne_hdr : u.hdr ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 3#32 u.hdr = [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.hdr.length) ++ u.hdr := by
      rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all : bs3.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.hdr.length)).length + u.hdr.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
    have hlt_tag : bs3.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs3 hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine send3a_step_bytes_varint b A ext hvarint 0x1a#8 sp cap ptr (entry + 11144#64) bs3 u.hdr hemp hfit_all hcap hptr halign
      (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
        EncodedLen.vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5) (by ac_rfl) ?_
    intro sm5 bs4 hpcm5 hrunm5 hspm5 htrm5 ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_26, hm5_27, hm5_28, hm5_fp, _⟩ hinv_m5 hfit_mc hcmp_mc
    simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_26 hm5_27 hm5_28 hm5_fp
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
    refine CryptoVerification.Cli.SpqrV1.Top.Send.send3a_step_memcpy_slice_4k b A ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr (entry + 11184#64) bs4 u.hdr hemp hhdr_le halign
      (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hhdr_lt (hinv_m5.trans hinv6) (by ac_rfl) ?_
    intro sm6 hpcm6 hrunm6 hspm6 htrm6 ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
    simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_26, hm5_27, hm5_28, hm5_fp] at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 11196#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
    have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs4 u.hdr hfit_mc hcap hptr hne_hdr
    have hbs_eq : bs4 ++ u.hdr = bs ++ Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) := by
      rw [etv3_encodeOptHeaderReceived_some_eq, henc_eq]; dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
    rw [h1432, h1440, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7))
    dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
    rw [h4840_24, h4840_72, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856, ← hpack_mc]; ac_rfl
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : Proto.encodeBytesField 3#32 u.hdr = [] := by rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
    apply SepWPp.of_sepWP_cs (mid := entry + 11196#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
    rw [h4840_24, h4840_72, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856, etv3_encodeOptHeaderReceived_some_eq, henc_nil]
    dsimp only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerReceived {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry) {s0 s : State}
    (hhrLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked3PBGhost × PolynomialDecoderPBGhost) (v : V1State.Chunked.HeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerReceived v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 8788#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) v.receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm (((optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) v.receivingEk) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.headerReceived v)) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 8788 8896; send_fetches_cli b (Rust.withPanics ext) hfn 9792 9868
  send_fetches_cli b (Rust.withPanics ext) hfn 10916 10948; send_fetches_cli b (Rust.withPanics ext) hfn 11196 11208
  examples_hide_fetches; subst hP; rcases v with ⟨uc, receivingEk⟩
  rw [etv3_encodeInnerState_headerReceived_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x3a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optHeaderReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧ (Prost.EncodeToVec.optHeaderReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧ (Prost.EncodeToVec.optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm => ⟨Prost.EncodeToVec.optHeaderReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
      Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4920#64)
        (R := optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x3a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9796 : ∀ sm1 : State, sm1.pc = entry + 9796#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x24 = sp + 4704#64 → sm1.readReg64 .x25 = Prost.EncodeToVec.optHeaderReceivedCap g.1 uc →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm1 (((optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optHeaderReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 9796#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optHeaderReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none, ← hpack]))
        (h9796 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optHeaderReceivedPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    | some u =>
      rw [Prost.EncodeToVec.optHeaderReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : headerReceivedPBEncodedLen u < 2 ^ 64 ∧ optHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) < optHeaderReceivedPBFieldEncodedLen (some u) := by dsimp only [optHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ProtoRepr.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv3_bv_optHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optHeaderReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]
      refine step_send_leaf_encLen16_call hres b ext (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen hhrLen (sp + 4840#64) sp (entry + 8852#64) g.1 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optHeaderReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, _, hm21, _, hm23, hm24, hm25, _, hm27, hm28, hmfp, _⟩ hinv_m1
      simp only [arm64_norm] at hm19 hm21 hm23 hm24 hm25 hm27 hm28 hmfp
      apply SepWPp.of_sepWP_cs (mid := entry + 9796#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optHeaderReceivedPBPinnedAt]; ac_rfl))
        (h9796 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10920 : ∀ sm2 : State, sm2.pc = entry + 10920#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 → sm2.readReg64 .x21 = s.readReg64 .x21 →
      sm2.readReg64 .x22 = Prost.EncodeToVec.optPolyDecCap g.2 receivingEk → sm2.readReg64 .x23 = s.readReg64 .x23 →
      sm2.readReg64 .x24 = sp + 4704#64 → sm2.readReg64 .x25 = Prost.EncodeToVec.optHeaderReceivedCap g.1 uc →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm2 (((optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingEk with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4920#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 10920#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4920#64) none]))
        (h10920 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
    | some dec =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4920#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ProtoRepr.ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.2 (sp + 4920#64) (some dec)]
      refine step_send_leaf_encLen16_call hres b ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen (sp + 4920#64) sp (entry + 9824#64) g.2 dec hdec_fit
        (F := optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
      simp only [arm64_norm, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      apply SepWPp.of_sepWP_cs (mid := entry + 10920#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl))
        (h10920 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingEk) (b := optHeaderReceivedPBFieldEncodedLen uc) (c := v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)) rfl hsub_len
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x3a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
  refine step_send_encode_varint_call b A ext hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
    (sp + 1424#64) cap ptr sp (entry + 10936#64) (bs ++ [0x3a#8]) hfit_var
    (F := (optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 uc
  suffices h11196 : ∀ sm4 : State, sm4.pc = entry + 11196#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x22 = Prost.EncodeToVec.optPolyDecCap g.2 receivingEk → sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm4 (((optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply SepWPp.of_sepWP_cs (mid := entry + 11196#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl))
        (h11196 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      apply SepWPp.of_sepWP_cs (mid := entry + 10948#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine CryptoVerification.Cli.SpqrV1.Top.Send.send3a_step_headerReceived_some hres b A ext hfn hhrLen hvarint hauthEnc hmemcpy sp cap ptr w25 g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialDecoderPBPinnedAt A g.2 (sp + 4920#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4) (by dsimp only [bs1, optHeaderReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [bs2, bs1, optHeaderReceivedPBPinnedAt]; ac_rfl))
        (h11196 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    apply SepWPp.of_sepWP_cs (mid := entry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv3_encodeInnerState_headerReceived_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply SepWPp.of_sepWP_cs (mid := entry + 11208#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_tail_11208_polyDec2 b A ext hfn hpolyDec (sp + 4920#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optHeaderReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_headerReceived_eq]
    simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 3. `StepSendInnerStateAt6616` Bridges for Variants 10 and 6 -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct2Sampled_at_6616 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 : State}
    (hct2Len : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct2Sampled) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.ct2Sampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  send_fetches_cli b (Rust.withPanics ext) hfn 6616 6632; examples_hide_fetches; subst hP
  replace hx8 : s.readReg64 .x8 = 10#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 8896#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4896⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 64#64 = sp + 4896#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4896]
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_ct2Sampled hres b A ext hfn
    hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc
    sp cap ptr w25 g.b.gCt2Sampled v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗ memRegion (sp + 4832#64 + 120#64) 104 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4896, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerReceived_at_6616_4k {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 : State}
    (hhrLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderReceived) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.headerReceived v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  send_fetches_cli b (Rust.withPanics ext) hfn 6616 6632; examples_hide_fetches; subst hP
  replace hx8 : s.readReg64 .x8 = 6#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 8788#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4920⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 88#64 = sp + 4920#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4920]
  refine CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerReceived hres b A ext hfn
    hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec
    sp cap ptr w25 g.b.gHeaderReceived v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (sp + 4832#64 + 128#64) 96 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4920, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerReceived_at_6616 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 : State}
    (hhrLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderReceived) :
    StepSendInnerStateAt6616 resStack b A ext entry roBase s0 (.headerReceived v) :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_send_v1_headerReceived_at_6616_4k hres b A ext hfn
    hhrLen hpolyDecLen hvarint hauthEnc
    (subroutine_ok_withStack_of_subroutine_ok hmemcpy (encodeToVecCalleeStackOf resStack)) hpolyDec v

end CryptoVerification.SpqrV1.Top.Send
