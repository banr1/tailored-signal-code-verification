/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedSteps
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.noHeaderReceived` Arm, Part 2 (Relocatable)

Relocatable `[LibsignalPlacement]` `<NoHeaderReceived>::recv_hdr_chunk` call bridge (`+8568 ->
+8616`) and top-level variant contract `states_recv_noHeaderReceived_placed_ok_ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48 Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

/-! ## 1. Call to `NoHeaderReceived::recv_hdr_chunk` (`+8612 -> +8616`) & Helpers -/

private theorem sepWPp_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hQ hcro'))))

theorem call_noHeaderReceivedRecvHdrChunk_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
      (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec F A)))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (Frame R : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (heq : msg.epoch = st.uc.epoch)
    (hp : msg.payload = .hdr chunk)
    (hinv : PolyDecoderStrictSorted st.receiving_hdr)
    (hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 369)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 4240#64) + 1856#64)
    (hx1 : s.readReg64 .x1 = (s0.sp - 4240#64) + 976#64)
    (hx2 : s.readReg64 .x2 = st.uc.epoch)
    (hx3 : s.readReg64 .x3 = msgA + 10#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hlr : s.readReg64 Reg.lr = lsmpl.base 332 + 8616#64)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ sf : State,
      sf.pc = lsmpl.base 332 + 8616#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 4240#64 →
      sf.readReg64 .x19 = outA →
      TraceCalleeSaved sf s0 →
      SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        ((noHeaderReceivedRecvChunkResultAt A ((s0.sp - 4240#64) + 1856#64) (st.recv_hdr_chunk st.uc.epoch chunk) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) chunkedNoHeaderReceivedSize ∗
          chunkAt (msgA + 10#64) chunk ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) noHeaderReceivedRecvHdrChunkStackX) ∗ Frame)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg).post
              (outA, selfA, msgA) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg).onPanic
              (outA, selfA, msgA) s0 sf ∗ R))) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((memRegion ((s0.sp - 4240#64) + 1856#64) chunkedHeaderReceivedSize ∗
        chunkedNoHeaderReceivedAt A ((s0.sp - 4240#64) + 976#64) st ∗
        chunkAt (msgA + 10#64) chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) noHeaderReceivedRecvHdrChunkStackX) ∗ Frame)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  refine SepWPp.call hcall
    (x := ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, st, st.uc.epoch, msgA + 10#64, chunk⟩)
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    dsimp only [noHeaderReceivedRecvHdrChunkPlacedSpec]
    rw [hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hinv⟩, hm⟩
  · dsimp only [withLsCodeRoLoaded, noHeaderReceivedRecvHdrChunkPlacedSpec, statesRecvVariantPlacedSpec, statesRecvOnPanic] at hmem ⊢
    refine allowPanic_frame (fun ⟨hpan_or, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hpan_or ⊢
    rw [htr.1] at hpan_or htr_sub
    rcases hpan_or with hpan | haf
    · exact ⟨Or.inl (states_recv_noHeaderReceived_isPanic_hdr K st msg chunk heq hp hpan), htr_sub⟩
    · exact ⟨Or.inr haf, htr_sub⟩
  · dsimp only [withLsCodeRoLoaded, noHeaderReceivedRecvHdrChunkPlacedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr_sf => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hcs_sf.1.trans hx19) ⟨htr_sf.trans htr.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩

theorem nhr_step_2132_2180_spills_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp out st_ptr msg_ptr msg_ep : BitVec 64)
    (w : Words57) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 2132#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = st_ptr) (hx19 : s.readReg64 .x19 = out) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 2180#64) s
      (memRegion (fsp + 2752#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       (msg_ptr ↦₆₄ msg_ep) ∗ sendEkSpillsAt fsp sp ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 2752#64) w ∗ words57At (st_ptr + 8#64) w ∗
          (msg_ptr ↦₆₄ msg_ep) ∗ sendEkSpillsAt fsp { sp with w62 := w.b0.w6 } ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧ sm.readReg64 .x24 = msg_ptr ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.b0.w6)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.b0.w6) == 0#32) ∧ TraceCalleeSaved sm s) := by
  have h := nhr_step_2132_2180_placed hmemcpy_sat s fsp out st_ptr msg_ptr msg_ep sp.w62 w
    (words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) sp.b1 ∗ words10At (fsp + 168#64) sp.b2 ∗
     words10At (fsp + 248#64) sp.b3 ∗ words10At (fsp + 328#64) sp.b4 ∗ words10At (fsp + 408#64) sp.b5 ∗
     ((fsp + 488#64) ↦₆₄ sp.w60) ∗ ((fsp + 496#64) ↦₆₄ sp.w61) ∗
     ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
     ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗ ((fsp + 560#64) ↦₆₄ sp.w230) ∗ ((fsp + 960#64) ↦₁₂₈ sp.q3c0) ∗ Frame)
    hfsp_align hpc hrun hsp hx1 hx19 hx24
  refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [sendEkSpillsAt]; ac_rfl)) (SepWP.mono h ?_)
  intro sm Pm _ _ ⟨hPm, hrest⟩
  exact ⟨Entails.trans hPm (Entails.of_eq (by dsimp only [sendEkSpillsAt]; ac_rfl)), hrest⟩

theorem nhr_step_8568_to_call_entry_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s1 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words57) (Frame : SepProp)
    (hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = lsmpl.base 332 + 8568#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = st.uc.epoch)
    (hx21 : s1.readReg64 .x21 = selfA) (hx24 : s1.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 369) s1
      ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        memRegion (selfA + 464#64) 464 ∗
        words57At ((s0.sp - 4240#64) + 2752#64) w ∗ nhrUnusedRestAt (s0.sp - 4240#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA (.hdr chunk) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion ((s0.sp - 4240#64) + 1856#64) chunkedHeaderReceivedSize ∗
          chunkedNoHeaderReceivedAt A ((s0.sp - 4240#64) + 976#64) st ∗
          chunkAt (msgA + 10#64) chunk ∗
          memRegion selfA chunkedStatesSize ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          memRegion ((s0.sp - 4240#64) + 1432#64) 424 ∗
          memRegion ((s0.sp - 4240#64) + 2336#64) 400 ∗
          (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = s0.sp - 4240#64 ∧
        sm.readReg64 .x0 = (s0.sp - 4240#64) + 1856#64 ∧
        sm.readReg64 .x1 = (s0.sp - 4240#64) + 976#64 ∧
        sm.readReg64 .x2 = st.uc.epoch ∧
        sm.readReg64 .x3 = msgA + 10#64 ∧
        sm.readReg64 .x19 = outA ∧
        sm.readReg64 .x30 = lsmpl.base 332 + 8616#64 ∧
        TraceCalleeSaved sm s0) := by
  set fsp := s0.sp - 4240#64
  rw [memRegion_880_split_456_424_nhr fsp, memRegion_880_split_480_400_1856_nhr fsp]
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := lsmpl.base 332 + 8612#64)
    (P_mid := memRegion (fsp + 1856#64) chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A (fsp + 976#64) st ∗
      chunkAt (msgA + 10#64) chunk ∗
      memRegion selfA chunkedStatesSize ∗
      sendEkUnusedAt fsp ∗
      memRegion (fsp + 1432#64) 424 ∗
      memRegion (fsp + 2336#64) 400 ∗
      (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗
      memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 ∗
      stackAt fsp statesRecvCalleeStackX ∗ Frame)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x0 = fsp + 1856#64 ∧
      s2.readReg64 .x1 = fsp + 976#64 ∧ s2.readReg64 .x2 = st.uc.epoch ∧
      s2.readReg64 .x3 = msgA + 10#64 ∧ s2.readReg64 .x19 = outA ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep := nhr_step_8568_hdr_8612_placed hmemcpy_sat s1 fsp outA selfA msgA st.uc.epoch chunk w
      ((selfA ↦₆₄ 7#64) ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
       memRegion (selfA + 464#64) 464 ∗
       words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp ∗
       memRegion (fsp + 1432#64) 424 ∗ memRegion (fsp + 1856#64) 480 ∗
       memRegion (fsp + 2336#64) 400 ∗ (msgA ↦₆₄ msg.epoch) ∗ Frame)
      hfsp_align hpc hrun hsp hx19 hx20 hx21 hx24
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h0_2, h1_2, h2_2, h3_2, h19_2, _, _, _, _, htr2⟩
    refine ⟨Entails.trans hPm ?_, hsp2, h0_2, h1_2, h2_2, h3_2, h19_2, htr2.trans htr⟩
    have hpre := nhr_hdr_pre_call_entails A fsp selfA st w
    rw [messagePayloadAt_hdr_eq msgA chunk]
    unfold chunkedHeaderReceivedSize
    refine Entails.trans (Entails.of_eq (show _ =
      ((words57At (fsp + 976#64) w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
       ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
       (words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp)) ∗
      (memRegion (fsp + 1856#64) 480 ∗ chunkAt (msgA + 10#64) chunk ∗
       memRegion (fsp + 1432#64) 424 ∗ memRegion (fsp + 2336#64) 400 ∗
       (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗
       memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpre) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, h0_2, h1_2, h2_2, h3_2, h19_2, htr2⟩
    have hcall := nhr_step_8612_call_placed (ext := ext) s2 fsp st.uc.epoch msgA
      (memRegion (fsp + 1856#64) chunkedHeaderReceivedSize ∗
       chunkedNoHeaderReceivedAt A (fsp + 976#64) st ∗
       chunkAt (msgA + 10#64) chunk ∗
       memRegion selfA chunkedStatesSize ∗
       sendEkUnusedAt fsp ∗
       memRegion (fsp + 1432#64) 424 ∗
       memRegion (fsp + 2336#64) 400 ∗
       (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗
       memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      hpc2 hrun2 hsp2 h0_2 h1_2 h2_2 h3_2
    refine SepWP.mono hcall ?_
    intro sm Pm _ _ ⟨hPm, hsp_m, h0_m, h1_m, h2_m, h3_m, h30_m, hcs_m, htr_m⟩
    exact ⟨hPm, hsp_m, h0_m, h1_m, h2_m, h3_m, hcs_m.1.trans h19_2, h30_m, htr_m.trans htr2⟩

theorem nhr_hdr_8568_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 369)
      (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec F A)))
    (s0 s1 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words57) (sp1 : SendEkSpills) (R : SepProp)
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (heq : msg.epoch = st.uc.epoch) (hp : msg.payload = .hdr chunk)
    (hinv : PolyDecoderStrictSorted st.receiving_hdr)
    (hsp0_align : s0.spAligned = true)
    (hpc : s1.pc = lsmpl.base 332 + 8568#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = st.uc.epoch)
    (hx21 : s1.readReg64 .x21 = selfA) (hx24 : s1.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        memRegion (selfA + 464#64) 464 ∗
        words57At ((s0.sp - 4240#64) + 2752#64) w ∗ nhrUnusedRestAt (s0.sp - 4240#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA (.hdr chunk) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        (statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine sepWPp_seq_clean_lscro hcro1
    (nhr_step_8568_to_call_entry_placed hmemcpy_sat s0 s1 outA selfA msgA st msg chunk w
      (statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
       sendEkSpillsAt fsp sp1 ∗
       memRegion (fsp + 576#64) 376 ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx19 hx20 hx21 hx24 htr) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, h0_2, h1_2, h2_2, h3_2, h19_2, h30_2, htr2⟩ hcro2
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (memRegion (fsp + 1856#64) chunkedHeaderReceivedSize ∗
     chunkedNoHeaderReceivedAt A (fsp + 976#64) st ∗
     chunkAt (msgA + 10#64) chunk ∗
     tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
     stackAt fsp noHeaderReceivedRecvHdrChunkStackX) ∗
    (statesRecvJumpTablePlacedAt ∗ Unchunked.unchunkedSendCt2PlacedRoAt ∗
     memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
     (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗
     memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 ∗
     memRegion (fsp - 19552#64) 848 ∗
     sendEkSpillsAt fsp sp1 ∗ memRegion (fsp + 576#64) 376 ∗
     memRegion (fsp + 1432#64) 424 ∗ memRegion (fsp + 2336#64) 400 ∗
     sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by
      dsimp only [statesRecvRoPlacedAt, fsp]
      rw [stackAt_statesRecvCallee_eq_noHeaderReceivedRecvHdrChunk (s0.sp - 4240#64)]
      ac_rfl)) ?_
  refine call_noHeaderReceivedRecvHdrChunk_placed hcall s0 s2 outA selfA msgA st msg chunk _ R
    hcro2 heq hp hinv hfsp_align hpc2 hrun2 hsp2 h0_2 h1_2 h2_2 h3_2 h19_2 h30_2 htr2 ?_
  intro s3 hpc3 hrun3 hsp3 h19_3 htr3
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    noHeaderReceivedRecvChunkResultAt A (fsp + 1856#64) (st.recv_hdr_chunk st.uc.epoch chunk) ∗
    (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) ∗
    memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
    stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
    memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
    memRegion (fsp + 2336#64) 400 ∗ sendEkUnusedAt fsp ∗
    statesRecvSavedCells s0 by
      dsimp only [statesRecvRoPlacedAt, chunkedNoHeaderReceivedSize, fsp]
      rw [stackAt_statesRecvCallee_eq_noHeaderReceivedRecvHdrChunk (s0.sp - 4240#64),
          memRegion_880_split_456_424_nhr (s0.sp - 4240#64),
          ← messageAt_hdr_recompose msgA msg chunk hp]
      ac_rfl)) ?_
  cases hres : st.recv_hdr_chunk st.uc.epoch chunk with
  | error e =>
    cases e with
    | panic msg_pan =>
      dsimp only [noHeaderReceivedRecvChunkResultAt]
      exact SepWPp.pure_left (fun h => False.elim h)
    | err err =>
      have hrecv : (States.noHeaderReceived st).recv K msg = .error (.err err) := by
        rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp, hres]
      have hexit := nhr_err_8616_ret_placed (A := A) (F := F) (ext := ext) s0 s3 outA selfA err sp1
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
        hsp0_align hpc3 hrun3 hsp3 h19_3 htr3
      refine sepWPp_of_statesRecv_exit_placed s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by ac_rfl)
  | ok step =>
    cases step with
    | stillReceiving outSt =>
      have hrecv : (States.noHeaderReceived st).recv K msg =
          .ok { key := none, state := .noHeaderReceived outSt } := by
        rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp, hres]
      refine SepWPp.weaken_pre (sepConj_mono_left (nhr_still_1856_split (A := A) (F := F) fsp outSt)) ?_
      simp only [sepExists_sepConj_left]
      apply sepWPp_intro_ex_nhr hrun3; intro w_out
      apply sepWPp_intro_ex_nhr hrun3; intro w58
      apply sepWPp_intro_ex_nhr hrun3; intro w59
      have hexit := nhr_still_8616_ret_placed (A := A) (F := F) hmemcpy_sat s0 s3 outA selfA w58 w59 outSt w_out sp1
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
        hsp0_align hpc3 hrun3 hsp3 h19_3 htr3
      refine sepWPp_of_statesRecv_exit_placed s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; ac_rfl)) (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by ac_rfl)
    | done outSt =>
      have hrecv : (States.noHeaderReceived st).recv K msg =
          .ok { key := none, state := .headerReceived outSt } := by
        rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp, hres]
      refine SepWPp.weaken_pre (sepConj_mono_left (nhr_done_1856_split (A := A) (F := F) fsp outSt)) ?_
      simp only [sepExists_sepConj_left]
      apply sepWPp_intro_ex_nhr hrun3; intro w_out
      rw [sepConj_assoc]
      apply SepWPp.pure_left; intro ⟨hw0_ne_err, hw0_ne_none⟩
      have hexit := nhr_done_8616_ret_placed (A := A) (F := F) hmemcpy_sat s0 s3 outA selfA outSt w_out sp1
        (messageAt spqrPolyApi msgA msg ∗ statesRecvJumpTablePlacedAt ∗
         ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
        hsp0_align hw0_ne_err hw0_ne_none hpc3 hrun3 hsp3 h19_3 htr3
      refine sepWPp_of_statesRecv_exit_placed s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre
        (Entails.of_eq (by dsimp only [statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt, BitVec.ofNat_eq_ofNat, fsp]; ac_rfl))
        (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]
      exact Entails.of_eq (by dsimp only [statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt, BitVec.ofNat_eq_ofNat]; ac_rfl)

/-- Per-variant relocatable specification proof for `States.noHeaderReceived st` (`tag = 7#64`). -/
theorem states_recv_noHeaderReceived_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.noHeaderReceived st) msg)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.noHeaderReceived st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.noHeaderReceived st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_noHeaderReceived_placed (ext := ext) s1 (s0.sp - 4240#64) selfA
    (chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 464#64) 464 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  set fsp := s0.sp - 4240#64
  have hpre_split :
      (selfA ↦₆₄ 7#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 464#64) 464 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words57, ∃∗ sp : SendEkSpills,
        ⌜w.b0.w6 = st.uc.epoch⌝ ∗
        (memRegion (fsp + 2752#64) 456 ∗ words57At (selfA + 8#64) w ∗
         (msgA ↦₆₄ msg.epoch) ∗ sendEkSpillsAt fsp sp ∗
         stackAt fsp statesRecvCalleeStackX ∗
         ((selfA ↦₆₄ 7#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
          memRegion (selfA + 464#64) 464 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
          statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
          memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0))) := by
    unfold messageAt
    have hex57 := chunkedNoHeaderReceivedAt_extract57 A (selfA + 8#64) st
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          memRegion (fsp + 2752#64) 456 ∗ nhrUnusedRestAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Entails.sepExists_elim; intro sp
      refine Entails.sepExists_right sp ?_
      refine Entails.trans (Entails.of_eq (show _ =
        sendEkUnusedAt fsp ∗ (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left (sendEkUnusedAt_split_nhr fsp)) (Entails.of_eq (by ac_rfl))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      ((selfA ↦₆₄ 7#64) ∗ statesRecvRoPlacedAt ∗ memRegion (selfA + 464#64) 464 ∗
       memRegion outA v1RecvSize ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hex57 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro sp
    apply Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp (Entails.of_eq (by ac_rfl)))
  refine SepWPp.weaken_pre hpre_split ?_
  apply sepWPp_intro_ex_nhr hrun2; intro w
  apply sepWPp_intro_ex_nhr hrun2; intro sp
  apply SepWPp.pure_left; intro hw6
  set sp1 := { sp with w62 := w.b0.w6 }
  refine sepWPp_seq_clean_lscro hcro2 (nhr_step_2132_2180_spills_placed hC.hmemcpy_sat s2 fsp outA selfA msgA msg.epoch w sp
    ((selfA ↦₆₄ 7#64) ∗
     relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
     memRegion (selfA + 464#64) 464 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
     statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
     memRegion (fsp + 576#64) 376 ∗
     memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
     nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
    hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, h3_19, h3_20, h3_21, h3_24, _, h3_8, h3_z, htr3⟩ hcro3
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr20
  rw [hw6] at h3_8 h3_z
  by_cases hgt : msg.epoch > st.uc.epoch
  · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 1#32 := ekCmpW8_of_gt hgt
    rw [hcmp] at h3_8 h3_z
    have hz_f : s3.pstate.z = false := h3_z
    have hrecv := states_recv_noHeaderReceived_gt K st msg hgt
    have hexit := nhr_gt_2180_ret_placed (A := A) (F := F) hC.hdealloc_sat s0 s3 outA selfA msg.epoch st sp1
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      hcro3.1 hsp0_align hpc3 hrun3 hsp3 hz_f h3_8 h3_19 h3_20 htr30
    refine sepWPp_of_statesRecv_exit_placed s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
    refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
    · have hrec := recompose57 (F_pred := fun dst => chunkedNoHeaderReceivedAt A dst st) (fsp + 2752#64) w
      have hself := selfA_noHeaderReceived_entails_memRegion selfA w
      unfold messageAt
      refine Entails.trans (Entails.of_eq (show _ =
        (words57At (fsp + 2752#64) w ∗
         relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
        ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
        (((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
         statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
         memRegion (fsp + 1856#64) 880 ∗ nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hrec (sepConj_mono_left hself)) (Entails.of_eq (by dsimp only [fsp]; ac_rfl))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by ac_rfl)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 255#32 := ekCmpW8_of_lt hlt
      rw [hcmp] at h3_8 h3_z
      have hz_f : s3.pstate.z = false := h3_z
      have hrecv := states_recv_noHeaderReceived_lt K st msg hlt
      refine sepWPp_seq_clean (nhr_step_2180_lt_8664_placed (ext := ext) s3 fsp _ hpc3 hrun3 hsp3 hz_f h3_8) ?_
      intro s4 hpc4 hrun4 ⟨hsp4, h4_19, _, _, _, _, htr4⟩
      have hexit := nhr_noop_8664_ret_placed (A := A) (F := F) hC.hmemcpy_sat s0 s4 outA selfA st w sp1
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
        hsp0_align rfl hpc4 hrun4 hsp4 (h4_19.trans h3_19) (htr4.trans htr30)
      refine sepWPp_of_statesRecv_exit_placed s0 s4 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
      · have hself := selfA_noHeaderReceived_entails_memRegion selfA w
        unfold messageAt
        refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
          (((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
           statesRecvRoPlacedAt ∗ A.pool ∗ memRegion outA v1RecvSize ∗
           words57At (fsp + 2752#64) w ∗
           relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
           stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
           memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
           memRegion (fsp + 1856#64) 880 ∗ nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by dsimp only [fsp]; ac_rfl))
      · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv]; exact Entails.of_eq (by ac_rfl)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 0#32 := ekCmpW8_of_eq heq
      rw [hcmp] at h3_z
      have hz_t : s3.pstate.z = true := h3_z
      refine sepWPp_seq_clean_lscro hcro3 (nhr_step_2180_eq_8568_placed (ext := ext) s3 fsp _ hpc3 hrun3 hsp3 hz_t) ?_
      intro s4 hpc4 hrun4 ⟨hsp4, h4_19, h4_20, h4_21, h4_24, _, htr4⟩ hcro4
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      by_cases hhdr : ∃ chunk, msg.payload = .hdr chunk
      · rcases hhdr with ⟨chunk, hp⟩
        have h20_eq : s4.readReg64 .x20 = st.uc.epoch := by
          rw [h4_20, h3_20, heq]
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (nhr_hdr_8568_ret_placed hC.hmemcpy_sat hC.noHeaderReceivedRecvHdrChunk_ok
            s0 s4 outA selfA msgA st msg chunk w sp1 R
            hcro4 heq hp hinv hsp0_align hpc4 hrun4 hsp4
            (h4_19.trans h3_19) h20_eq (h4_21.trans h3_21) (h4_24.trans h3_24) htr40)
        rw [hp]; dsimp only [fsp]; ac_rfl
      · have hno : ∀ c, msg.payload ≠ .hdr c := fun c hc => hhdr ⟨c, hc⟩
        have hrecv := states_recv_noHeaderReceived_eq_non_hdr K st msg heq hno
        have hstep_no := nhr_step_8568_non_hdr_8664_placed (ext := ext) s4 fsp msgA msg.payload
          (words57At (fsp + 2752#64) w ∗ words57At (selfA + 8#64) w ∗
           (msgA ↦₆₄ msg.epoch) ∗ sendEkSpillsAt fsp sp1 ∗
           (selfA ↦₆₄ 7#64) ∗
           relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
           memRegion (selfA + 464#64) 464 ∗
           statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool ∗
           stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
           nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
          hno hpc4 hrun4 hsp4 (h4_24.trans h3_24)
        refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep_no) ?_
        intro s5 hpc5 hrun5 ⟨hsp5, h5_19, _, _, _, _, htr5⟩
        have hexit := nhr_noop_8664_ret_placed (A := A) (F := F) hC.hmemcpy_sat s0 s5 outA selfA st w sp1
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
          hsp0_align rfl hpc5 hrun5 hsp5 (h5_19.trans (h4_19.trans h3_19)) (htr5.trans htr40)
        refine sepWPp_of_statesRecv_exit_placed s0 s5 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
        refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
        · have hself := selfA_noHeaderReceived_entails_memRegion selfA w
          unfold messageAt
          refine Entails.trans (Entails.of_eq (show _ =
            ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
            (((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             statesRecvRoPlacedAt ∗ A.pool ∗ memRegion outA v1RecvSize ∗
             words57At (fsp + 2752#64) w ∗
             relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
             stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
             memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
             memRegion (fsp + 1856#64) 880 ∗ nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by dsimp only [fsp]; ac_rfl))
        · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
          refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
          rw [hrecv]; exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Recv

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

export CryptoVerification.SpqrV1.States.Recv (
  states_recv_noHeaderReceived_placed_ok_ext
)

end LibsignalBinary.Proofs.SpqrV1.States.Recv
