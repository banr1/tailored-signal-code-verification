/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 7 (Relocatable)

Relocatable `[LibsignalPlacement]` common `recv_ek_chunk` prefix (`+11404 -> +11496`) and
Path 4a (`outMsg = none, ack = false`: `+11496 -> s0.x30`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open Obj.MultiPlacedLib

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local irreducible] addChunkTotal decodedMessageTotal
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

theorem ct1Sampled_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hq))

theorem ct1Sampled_sepWPp_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ hcrom =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hent (h2 sm hpc hrun hcrom hq))))

theorem sepWPp_of_ct1Sampled_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (P R : SepProp)
    (hexit : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantPlacedSpec A F K self msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R))
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantPlacedSpec A F K self msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  apply SepWPp.of_sepWP
  refine SepWP.mono hexit ?_
  intro sf Pf hpc_sf hrun_sf ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
  refine SepWPp.done hpc_sf hrun_sf ⟨hsp_sf, hcs_sf, fun hmem => ?_⟩
  dsimp only [statesRecvVariantPlacedSpec]
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right htr_sf hPf)) hmem

set_option maxHeartbeats 1200000 in
/-- Common `recv_ek_chunk` prefix (`+11404 -> +11496`):
    extracts the stack frame and `c_uc : Words16`, copies `st.uc` to `fsp + 3696` and `st.receiving_ek`
    to `fsp + 2752`, and calls `PolyDecoder::add_chunk` and `PolyDecoder::decoded_message`. -/
theorem ct1Sampled_recv_ek_common_prefix_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {P_pan : Prop}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (Rest R : SepProp)
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack),
      sf.pc = (blkPl_332).base + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = outA →
      sf.readReg64 .x20 = st.uc.epoch →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x22 = ack_val →
      sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = fsp + 3272#64 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        (optVecU8At A (fsp + 3832#64) (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
          polyDecoderAt A (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A selfA st.sending_ct1 ∗
            wordsAt (selfA + 400#64) c_uc.toList ∗
            wordsAt (fsp + 3696#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest))
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s_in
      (polyEncoderAt A selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have ⟨_, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hpre :
      polyEncoderAt A selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest ⊢
      ∃∗ c_uc : Words16, ∃∗ sc : CopyScratchStack, ∃∗ k : EpilogueStoreStack,
        wordsAt (selfA + 400#64) c_uc.toList ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (fsp + 3832#64) 24 ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗
          (polyEncoderAt A selfA st.sending_ct1 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono (Relocatable.extract_128 (Relocatable.of_unchunkedCt1SentAt A st.uc) (selfA + 400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (memRegion_4144_entails_copyScratch_and_epilogueStack fsp))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, memRegion_3168_split_prefix fsp]
    apply Entails.sepExists_elim; intro sc
    apply Entails.sepExists_elim; intro k
    apply Entails.sepExists_elim; intro c_uc
    refine Entails.sepExists_right c_uc (Entails.sepExists_right sc (Entails.sepExists_right k ?_))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  apply sepWPp_intro_ex' hrun; intro c_uc
  apply sepWPp_intro_ex' hrun; intro sc
  apply sepWPp_intro_ex' hrun; intro k
  refine ct1Sampled_sepWPp_seq_clean_lscro hcro
    (ct1Sampled_recv_ek_prefix_copy_placed hmemcpy s_in fsp selfA k.we8 c_uc st.receiving_ek _
      hfsp_align hpc hrun hsp hx1) ?_
  intro s1 hpc1 hrun1 hcro1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hx29_1, htr1⟩
  have hreord :
      wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        polyDecoderAt A (fsp + 2752#64) st.receiving_ek ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        memRegion (selfA + 528#64) 400 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (fsp + 3832#64) 24 ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗
          (polyEncoderAt A selfA st.sending_ct1 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) ⊢
      memRegion (fsp + 3832#64) 24 ∗
        polyDecoderAt A (fsp + 2752#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗
          epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3856#64) 288 ∗
          Rest) := Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hreord ?_
  apply SepWPp.of_sepWP
  refine ct1Sampled_recv_ek_add_and_decode_placed (P_pan := P_pan) hadd_call hdec_call s0 s1 fsp msgA
    st.receiving_ek chunk (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
    hsort hdm _ R hcro1 hfsp_align hpc1 hrun1 hsp1 (hx24_1.trans hx24) (htr1.trans htr) ?_
  intro sf hpc_sf hrun_sf hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx28_sf hx29_sf htr_sf hcl_sf _
  apply SepWP.done hpc_sf hrun_sf
  exact hnext sf c_uc sc k hpc_sf hrun_sf hsp_sf
    (hx19_sf.trans (hx19_1.trans hx19))
    (hx20_sf.trans (hx20_1.trans hx20))
    (hx21_sf.trans (hx21_1.trans hx21))
    (hx22_sf.trans (hx22_1.trans hx22))
    (hx23_sf.trans (hx23_1.trans hx23))
    hx24_sf
    (hx28_sf.trans (hx28_1.trans hx28))
    (hx29_sf.trans (hx29_1.trans hx29))
    htr_sf hcl_sf

set_option maxHeartbeats 2000000 in
/-- Path 4a from `+11496 -> s0.x30` (`outMsg = none, ack = false`):
    returns `Ok { key := none, state := .ct1Sampled { st with receiving_ek := addChunkTotal st.receiving_ek chunk } }`. -/
theorem ct1Sampled_path_none_no_ack_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx22 : s_in.readReg64 .x22 = 0#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A (fsp + 3832#64) none ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
          memRegion selfA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.seq
    (ct1Sampled_recv_ek_decode_branch_none_placed s_in fsp _ hfsp_align hpc hrun hsp) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx19_1, _, _, hx22_1, hx23_1, _, _, hx29_1, htr1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq
    (ct1Sampled_none_branch_no_ack_placed s1 _ hpc1 hrun1 (hx22_1.trans hx22)) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hs2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hsp2 : s2.sp = fsp := by rw [hs2]; exact hsp1
  have hx19_2 : s2.readReg64 .x19 = outA := by rw [hs2, State.readReg64_setPC, hx19_1, hx19]
  have hx23_2 : s2.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 := by
    rw [hs2, State.readReg64_setPC, hx23_1, hx23]
  have hx29_2 : s2.readReg64 .x29 = fsp + 4144#64 := by rw [hs2, State.readReg64_setPC, hx29_1, hx29]
  have htr2 : TraceCalleeSaved s2 s0 := by rw [hs2]; exact htr1.trans htr
  have hpre2 :
      memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest ⊢
      ∃∗ c_enc : Words50, ∃∗ d400 : Split400,
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64,
      ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
      ∃∗ v4096 : BitVec 64, ∃∗ v4104 : BitVec 64, ∃∗ v4112 : BitVec 64,
        ⌜c_enc.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗ ⌜d400.mid352.length = 352⌝ ∗
        wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
        wordsAt (selfA + 256#64) c_enc.c2.toList ∗
        wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
        ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ split400At (fsp + 2752#64) d400 ∗
        memRegion (fsp + 1872#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗ ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗ ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          (relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
            memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
              memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
              memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
              memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
              memRegion (fsp + 4120#64) 24) ∗
            memRegion outA v1RecvSize ∗
            statesRecvSavedCells s0 ∗ Rest)) := by
    refine Entails.trans (Entails.of_eq (show _ =
        polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
          (wordsAt (fsp + 3696#64) c_uc.toList ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288) ∗
          (wordsAt (selfA + 400#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
            statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (polyEncoderAt_extract_words50 A selfA st.sending_ct1)
      (sepConj_mono (Relocatable.extract_split400 (Relocatable.of_polyDecoderAt A dec') (fsp + 2752#64))
        (sepConj_mono_left (memRegion_none_no_ack_split fsp c_uc)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
    apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro vc90
    apply Entails.sepExists_elim; intro vc98; apply Entails.sepExists_elim; intro c_ca0
    apply Entails.sepExists_elim; intro v4096; apply Entails.sepExists_elim; intro v4104
    apply Entails.sepExists_elim; intro v4112; apply Entails.sepExists_elim; intro d400
    apply Entails.sepExists_elim; intro c_enc
    refine Entails.sepExists_right c_enc (Entails.sepExists_right d400
      (Entails.sepExists_right v976 (Entails.sepExists_right v984
        (Entails.sepExists_right v992 (Entails.sepExists_right vc90
          (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
            (Entails.sepExists_right v4096 (Entails.sepExists_right v4104
              (Entails.sepExists_right v4112 ?_))))))))))
    dsimp only [words50At, mkC3FromEnc2Uc14, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_
  apply ProofLib.SepWP.exists_left; intro c_enc; apply ProofLib.SepWP.exists_left; intro d400
  apply ProofLib.SepWP.exists_left; intro v976; apply ProofLib.SepWP.exists_left; intro v984
  apply ProofLib.SepWP.exists_left; intro v992; apply ProofLib.SepWP.exists_left; intro vc90
  apply ProofLib.SepWP.exists_left; intro vc98; apply ProofLib.SepWP.exists_left; intro c_ca0
  apply ProofLib.SepWP.exists_left; intro v4096; apply ProofLib.SepWP.exists_left; intro v4104
  apply ProofLib.SepWP.exists_left; intro v4112
  wp_focus_pure; intro htag_enc
  wp_focus_pure; intro hmid352
  refine SepWP.seq
    (ct1Sampled_copy_none_no_ack_part1_placed hmemcpy s2 fsp selfA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc)
      c_uc.w14 c_uc.w15 d400 sc k v976 v984 v992 vc90 vc98 v4096 v4104 v4112 _
      hmid352 hfsp_align hpc2 hrun2 hsp2 hx29_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx23_3, hx29_3, htr3⟩
  let d := mkSplit928From528And400 c_enc.c0 c_enc.c1 c_enc.c2
    (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15 d400
  have hP3' : P3 ⊢
      copyScratchStackAt fsp (copyFullScratch sc d) ∗
      epilogueStoreStackPart1At fsp
        { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      mid376At (fsp + 976#64) c_uc.w14 c_uc.w15 d400.w0 d400.mid352 ∗
      wordsAt (fsp + 1352#64) d400.tail.toList ∗
      ((fsp + 3216#64) ↦₆₄ (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).w13) ∗
      ((fsp + 3224#64) ↦₆₄ (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).w14) ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
        wordsAt (selfA + 256#64) c_enc.c2.toList ∗
        wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
        ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
        memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 1872#64) 400 ∗ memRegion (fsp + 4096#64) 24 ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
          memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
          memRegion (fsp + 4120#64) 24) ∗
        memRegion outA v1RecvSize ∗
        statesRecvSavedCells s0 ∗ Rest) := Entails.trans hP3 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP3' ?_
  have htag_01 : c_enc.c0.w0 = 0#64 ∨ c_enc.c0.w0 = 1#64 := by
    rw [htag_enc]; exact polyEncoderTagVal_zero_or_one st.sending_ct1
  refine SepWP.seq
    (ct1Sampled_copy_none_no_ack_part2_placed hmemcpy s3 fsp selfA outA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc)
      c_uc.w14 c_uc.w15 d400 sc k c_ca0 _
      htag_01 hmid352 hfsp_align hpc3 hrun3 hsp3
      (hx19_3.trans hx19_2) (hx23_3.trans (hx23_2.trans htag_enc.symm))) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  let k' := epilogueStackOfSplit928 d noneCap k.w200 k.w208
  have hmid' : k'.mid.length = 376 := by
    dsimp only [k', epilogueStackOfSplit928, d, mkSplit928From528And400]
    exact mid376Bytes_length c_uc.w14 c_uc.w15 d400.w0 hmid352
  have hP4' : P4 ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        statesRecvSavedCells s0 ∗ Rest) := by
    refine Entails.trans hP4 ?_
    simp only [memRegion_out_960_split_states_key]
    have hself := chunks528_and_400_entails_memRegion_928 selfA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15
    have hstk3168 := memRegion_none_no_ack_join fsp
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 976#64) 376 ∗ memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 1872#64) 400 ∗
          memRegion (fsp + 3216#64) 16 ∗ memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗ memRegion (fsp + 4096#64) 24 ∗
          (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
            memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
            memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
            memRegion (fsp + 4120#64) 24)) ∗
        (wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
          wordsAt (selfA + 256#64) c_enc.c2.toList ∗
          wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
          ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
          memRegion (selfA + 528#64) 400) ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself)))))))))
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq
    (ct1Sampled_epilogue_store_placed hmemcpy s4 fsp outA k' _ hmid' hfsp_align hpc4 hrun4 hsp4 hx19_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, htr5⟩
  have heq_split : epilogueSplit928 s4 k' = d :=
    epilogueSplit928_of_eq s4 d noneCap k.w200 k.w208 hregs4
  have hP5' : P5 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
        memRegion selfA chunkedStatesSize ∗ Rest) := by
    refine Entails.trans hP5 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp (copyFullScratch sc d) k' hmid'
    have hst_out := split928At_reconstruct_ct1Sampled_updated (A := A) outA st dec' c_enc c_uc d400 htag_enc hmid352
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s4.readReg64 .x20) k.w200 k.w208
    dsimp only [resultV1RecvAt, v1RecvAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗
          relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s4.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324_placed s0 s5 _ hsp0_align hpc5 hrun5 hsp5 (htr5.trans (htr4.trans (htr3.trans htr2)))) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_sepWPp_seq_clean_lscl
  ct1Sampled_sepWPp_seq_clean_lscro
  sepWPp_of_ct1Sampled_exit_placed
  ct1Sampled_recv_ek_common_prefix_placed
  ct1Sampled_path_none_no_ack_placed
)

end CryptoVerification.SpqrV1.States.Recv
