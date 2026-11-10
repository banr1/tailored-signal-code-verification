/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1Sampled
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekReceivedCt1Sampled` Arm (`AllocContractsX`)

Instantiates `EkRecvMode` at `statesRecvStackXExt` (`40176` B) under `AllocContractsX` and
`.inImage img` to establish `states_recv_ekReceivedCt1Sampled_ok_x_{ext,ax}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.States.Leaves

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

private def ekRecvMode_inImage {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((growToCalleeExtSendEk ekReceivedCt1SampledRecvCt1AckStack
        (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)).inImage img)) : EkRecvMode A F K img.base ext where
  Inv := ImgCallInv img; P_stk := fun sp0 => memRegion (sp0 - 40176#64) 16384
  specOut := fun st msg => statesRecvVariantSpecExt A F K img.base (.ekReceivedCt1Sampled st) msg
  seq := fun hinv h1 h2 => SepWP.seq_inImage hinv
    (SepWP.mono h1 fun sm _ hp hr ⟨hPm, hQ⟩ hinv_m => SepWP.weaken_pre hPm (h2 sm hp hr hinv_m hQ))
  seq_p := fun hinv h1 h2 => sepWPp_seq_clean_inImage_sendek hinv h1 h2
  writeback := fun hrel s0 s outA sp P_rest hinv => states_recv_writeback_59e88_ext hAx hrel s0 s outA sp P_rest hinv
  exit_p := fun s0 s outA selfA msgA st msg P R h =>
    sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekReceivedCt1Sampled st) msg P R
      (SepWP.mono h fun _ _ _ _ ⟨hPf, hsp, hcs, htr⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_recv_ext)), hsp, hcs, htr⟩)
  call_ack := fun s0 s outA selfA msgA st outSt msg Frame R hb hinv_img hok hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19 hlr htr hnext => by
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 4240#64) + 976#64) chunkedCt2SampledSize ∗ chunkedEkReceivedCt1SampledAt A ((s0.sp - 4240#64) + 1856#64) st ∗
       unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt) ∗ Frame by
        rw [stackAt_statesRecvCalleeExt_eq_X s0.sp])) ?_
    refine SepWPp.call_imgInv hcall hinv_img (x := ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, st, outSt⟩) (F := Frame)
      hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
      (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
    · intro R' hm; refine satisfies_inImage_pre hinv_img ?_
      dsimp only [growToCalleeExtSendEk, ekReceivedCt1SampledRecvCt1AckSpec]
      rw [hsp]; rw [stackAt_statesRecvCalleeExt_split (s0.sp - 4240#64) ekReceivedCt1SampledRecvCt1AckStack] at hm
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨⟨hb, hx0, hx1, hx2, hok⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_recv_ext)) hm⟩
    · dsimp only [Spec.inImage, growToCalleeExtSendEk, ekReceivedCt1SampledRecvCt1AckSpec, statesRecvVariantSpecExt, statesRecvOnPanic] at hmem ⊢
      refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
      unfold allocFailedIn at haf ⊢; rw [htr.1] at haf htr_sub; exact ⟨Or.inr haf, htr_sub⟩
    · dsimp only [Spec.inImage, growToCalleeExtSendEk, ekReceivedCt1SampledRecvCt1AckSpec]; simp only [hsp, sepConj_assoc]
      refine SepWPp.pure_left fun htr_sf => SepWPp.weaken_pre ?_
        (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hcs_sf.1.trans hx19) ⟨htr_sf.trans htr.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩ hinv_sf)
      exact Entails.trans
        (Entails.of_eq (show _ =
          (chunkedCt2SampledAt A ((s0.sp - 4240#64) + 976#64) outSt ∗ memRegion ((s0.sp - 4240#64) + 1856#64) chunkedEkReceivedCt1SampledSize ∗
           unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt) ∗ Frame by
            rw [stackAt_statesRecvCalleeExt_split (s0.sp - 4240#64) ekReceivedCt1SampledRecvCt1AckStack]; sep_ac_rfl_recv_ext))
        (Entails.of_eq (by rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]))

theorem states_recv_ekReceivedCt1Sampled_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      ((growToCalleeExtSendEk ekReceivedCt1SampledRecvCt1AckStack
        (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)).inImage img))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ekReceivedCt1Sampled st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp; intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hsym0⟩, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion (s0.sp - 40176#64) 16384 ∗
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekReceivedCt1Sampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_recv_ext)) hmem,
    states_recv_ekReceivedCt1Sampled_sepWPp_gen (ekRecvMode_inImage hAx hcall)
      hdealloc st msg outA selfA msgA R s0 ⟨hF0, hsym0⟩ hb hx0 hx1 hx2 hinv hsp0_align hpc0 hrun0⟩

end CryptoVerification.SpqrV1.States.Recv
