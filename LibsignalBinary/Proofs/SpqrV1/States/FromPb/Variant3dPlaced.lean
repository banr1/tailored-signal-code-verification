/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 3 (`Ct1Received`, `+692`) — Post-`uc` Composition

Relocatable Block-`333` post-`uc` and post-encoder continuations (`+924`, `+1012`, `+4884`, `+4984`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

section

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333

theorem v3_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P P_mid : SepProp} {Q : State → Prop}
    {post Qpan : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWPp prog target_pc sm P_mid post Qpan) :
    SepWPp prog target_pc s P post Qpan :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem v3_sepWPp_call_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  have h1 : SepWPp prog ret_pc s (P_step ∗ F)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        dsimp only [withLsCodeLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨hcl, hpre (F ∗ R') hm⟩)
      (fun sf code _ _ hpost => by
        dsimp only [withLsCodeLoaded] at hpost
        rw [hexit_eq] at hpost
        exact not_satisfies_false_sepConj hpost)
      (fun sm _ hm_f => Satisfies.mono (sepConj_mono_left (hpan sm)) hm_f)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf _ _ hpost => by
        dsimp only [withLsCodeLoaded] at hpost
        rw [hoom_eq] at hpost
        exact (not_satisfies_false_sepConj hpost).elim)
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_out | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

set_option maxHeartbeats 800000 in
theorem v3_ct1Received_ok_4984_to_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (out pbA : BitVec 64)
    (ucSt : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (enc : PolyEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
     e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
     e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4984#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = w_tag) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = la2) (hx21 : s.readReg64 .x21 = pa4)
    (hx22 : s.readReg64 .x22 = pa1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24 : s.readReg64 .x24 = la1) (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_polyEncoderHeap A enc
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultChunkedStatesAt A (F := F) out (.ok (.ct1Received { uc := ucSt, sending_ek := enc })) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h104 := v3cr_split_104_72 (s0.sp - 2400#64)
  have h208 := v3cr_split_208_16 (s0.sp - 2400#64)
  have h232 := v3cr_split_232_1656 (s0.sp - 2400#64)
  have h608 := v3a_memRegion_608_287_split (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono h104
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h208 (sepConj_mono_right (sepConj_mono
            (Entails.trans h232 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h608)))))))
            (Entails.refl _)))))))))))))) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u887; apply ProofLib.SepWP.exists_left; intro u880
  apply ProofLib.SepWP.exists_left; intro u864; apply ProofLib.SepWP.exists_left; intro q848
  apply ProofLib.SepWP.exists_left; intro u832; apply ProofLib.SepWP.exists_left; intro q816
  apply ProofLib.SepWP.exists_left; intro q800; apply ProofLib.SepWP.exists_left; intro q784
  apply ProofLib.SepWP.exists_left; intro q768; apply ProofLib.SepWP.exists_left; intro q752
  apply ProofLib.SepWP.exists_left; intro q736; apply ProofLib.SepWP.exists_left; intro q720
  apply ProofLib.SepWP.exists_left; intro q704; apply ProofLib.SepWP.exists_left; intro q688
  apply ProofLib.SepWP.exists_left; intro q672; apply ProofLib.SepWP.exists_left; intro q656
  apply ProofLib.SepWP.exists_left; intro q640; apply ProofLib.SepWP.exists_left; intro q624
  apply ProofLib.SepWP.exists_left; intro q608; apply ProofLib.SepWP.exists_left; intro w592
  apply ProofLib.SepWP.exists_left; intro q576; apply ProofLib.SepWP.exists_left; intro bs240
  apply ProofLib.SepWP.exists_left; intro u232; apply ProofLib.SepWP.exists_left; intro u208
  apply ProofLib.SepWP.exists_left; intro d172; apply ProofLib.SepWP.exists_left; intro u160
  apply ProofLib.SepWP.exists_left; intro w120; apply ProofLib.SepWP.exists_left; intro w112
  apply ProofLib.SepWP.exists_left; intro w104
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜bs240.length = 328⌝ ∗
    ((((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
     (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
     (((s0.sp - 2400#64) + 160#64) ↦₆₄ u160) ∗
     (((s0.sp - 2400#64) + 172#64) ↦₃₂ d172) ∗
     (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
     (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
     (((s0.sp - 2400#64) + 208#64) ↦₆₄ u208) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ u232) ∗
     (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ q608) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ q624) ∗
     (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ q640) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ q656) ∗
     (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ q672) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ q688) ∗
     (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ q704) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ q720) ∗
     (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ q736) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ q752) ∗
     (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ q768) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ q784) ∗
     (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ q800) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ q816) ∗
     (((s0.sp - 2400#64) + 832#64) ↦₆₄ u832) ∗ (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ q848) ∗
     (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗
     (((s0.sp - 2400#64) + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗
     (((s0.sp - 2400#64) + 887#64) ↦₆₄ u887) ∗
     v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
       w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
       e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ memRegion (s0.sp - 2400#64) 64 ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
      (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
      (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
      memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
      (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
      (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
      (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
      memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
      statesFromPbSavedCells s0 ∗
      (v3cr_polyEncoderHeap A enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
         e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
         e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest))) by ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hbs240
  refine SepWP.seq (v3cr_pack_enc_4984_to_8180_placed s (s0.sp - 2400#64) out
    w_tag ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392
    u160 u208 u232 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    u832 q848 u864 u880 u887 _
    hfsp_align hpc hrun hsp hx15 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx7_2,
    hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2, hx15_2, hx16_2, hx17_2, hx18_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx30_2, htr2⟩
  have hcol := v3cr_collapse_0_64_72_24 (s0.sp - 2400#64) uc_ep
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (show _ =
    (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 24) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ la2) ∗
     (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
     (((s0.sp - 2400#64) + 208#64) ↦₆₄ e_w8) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ca2) ∗
     (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ e_q160) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ e_q176) ∗
     (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ e_q192) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ e_q208) ∗
     (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ e_q224) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ e_q240) ∗
     (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ e_q256) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ e_q272) ∗
     (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ e_q288) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ e_q304) ∗
     (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ e_q320) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ e_q336) ∗
     (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ e_q352) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ e_q368) ∗
     (((s0.sp - 2400#64) + 832#64) ↦₆₄ e_w384) ∗
     (((s0.sp - 2400#64) + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
     (((s0.sp - 2400#64) + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
     (((s0.sp - 2400#64) + 864#64) ↦ₛ hiBytes7 e_w152) ∗
     (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
     (((s0.sp - 2400#64) + 888#64) ↦ₛ hiBytes7 e_w120) ∗
     (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
        w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
        e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
        e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
     (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
     (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
     memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
     (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
     (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
     (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
     memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
     statesFromPbSavedCells s0 ∗
     (v3cr_polyEncoderHeap A enc
        w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
        e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
        e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)) by ac_rfl))) ?_
  refine SepWP.weaken_pre (sepConj_mono_left hcol) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d92
  have hstk := v3cr_post_4984_to_epilogue_stack (s0.sp - 2400#64)
    la3 la2 pa3 pa2 la4 ca1 e_w8 ca4 ca2
    d92 w104 w112 w120 bs240 q576 w592
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
    e_w384 e_w136 e_w144 e_w152 e_w112 e_w120
    w_tag e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96 e_w104 e_w128 e_w392
  have hstk_pre :
      (memRegion (s0.sp - 2400#64) 92 ∗ (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ la2) ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ e_w8) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ca2) ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ e_q160) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ e_q176) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ e_q192) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ e_q208) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ e_q224) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ e_q240) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ e_q256) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ e_q272) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ e_q288) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ e_q304) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ e_q320) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ e_q336) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ e_q352) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ e_q368) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ e_w384) ∗
       (((s0.sp - 2400#64) + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
       (((s0.sp - 2400#64) + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ hiBytes7 e_w152) ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ hiBytes7 e_w120) ∗
       (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
       statesFromPbSavedCells s0 ∗
       (v3cr_polyEncoderHeap A enc
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        d92 ((loByte e_w136).zeroExtend 32)
        w104 w112 w120 la2 la4 e_w8 ca4 ca2 bs240 q576 w592
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
        e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384
        (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
        (e_w152 >>> 8) (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8)
        (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32 ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (v3cr_polyEncoderHeap A enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
         e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
         e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) := by
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      ((((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ la2) ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ e_w8) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ca2) ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ e_q160) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ e_q176) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ e_q192) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ e_q208) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ e_q224) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ e_q240) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ e_q256) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ e_q272) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ e_q288) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ e_q304) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ e_q320) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ e_q336) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ e_q352) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ e_q368) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ e_w384) ∗
       (((s0.sp - 2400#64) + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
       (((s0.sp - 2400#64) + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ hiBytes7 e_w152) ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ hiBytes7 e_w120) ∗
       (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
       memRegion (s0.sp - 2400#64) 92 ∗ (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993) ∗
      statesFromPbSavedCells s0 ∗
      (v3cr_polyEncoderHeap A enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
         e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
         e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
      (Entails.of_eq (by ac_rfl))
  have hep := states_from_pb_epilogue_8180_placed hA.memcpy s0 s2 out
    d92 ((loByte e_w136).zeroExtend 32)
    w104 w112 w120 la2 la4 e_w8 ca4 ca2 bs240 hbs240 q576 w592
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384
    (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
    (e_w152 >>> 8) (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8)
    (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32
    (v3cr_polyEncoderHeap A enc
       w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
       e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
       ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
     memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 (htr2.trans htr)
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hstk_pre) (SepWP.mono hep ?_)
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m⟩
  dsimp only [State.readReg32] at hPm hx3_2 hx21_2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2,
      hx0_2, hx3_2, hx27_2, hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2,
      hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2] at hPm
  have hclose := v3cr_epilogueOutFull_ct1Received_close A (F := F) out ucSt enc
    w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w104 w112 w120 (d92.setWidth 8) q576
    (overlapWord7 (q576.extractLsb' 64 64) w592) bs240 hbs240
    (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32
  refine ⟨Entails.trans hPm ?_, hsp_m, hcc_m, htr_m⟩
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out
       5#64 w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80
       (((e_w88.extractLsb' 0 8).zeroExtend 32).setWidth 8)
       ((v3a_pack88 e_w88).setWidth 32)
       (((v3a_pack88 e_w88 >>> 32).setWidth 32).setWidth 16)
       (((v3a_pack88 e_w88 >>> 48).setWidth 32).setWidth 8)
       e_w96 e_w104
       (((loByte e_w112).zeroExtend 32).setWidth 8)
       (unshiftWord e_w112 (loByte e_w120))
       (overlapWord7 (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8))
       e_w128
       (((loByte e_w136).zeroExtend 32).setWidth 8)
       (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
       (overlapWord7
         ((unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 64 64)
         (e_w152 >>> 8))
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392
       ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
       w104 w112 w120 (d92.setWidth 8) q576
       (overlapWord7 (q576.extractLsb' 64 64) w592) bs240
       (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32 ∗
     v3cr_polyEncoderHeap A enc
       w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
       e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
       ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep) ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack ∗ Rest) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hclose) (Entails.of_eq (by ac_rfl))

theorem v3_ct1Received_err_1024_to_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1024#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = pa1)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have h1024 := v3cr_states_from_pb_err_1024_placed hA s0 s out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4
    (memRegion (s0.sp - 2400#64) 64 ∗
     (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
     (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
     memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
     (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ Rest)
    hsp0_align hpc hrun hsp hx19 hx22 hx28 hx26 hx21 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h1024) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx22_2, htr2⟩
  have h2304 :
      memRegion (s0.sp - 2400#64) 64 ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
      (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
      memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      memRegion ((s0.sp - 2400#64) + 232#64) 2072 ⊢
      memRegion (s0.sp - 2400#64) 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have hP2' : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) := by
    refine Entails.trans hP2 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (memRegion (s0.sp - 2400#64) 64 ∗
       (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
       (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       memRegion ((s0.sp - 2400#64) + 232#64) 2072) ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left h2304)
  have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx22_2]; rfl
  have h4968 := v3cr_states_from_pb_err_4968_placed (A := A) (F := F) (ext := ext) s0 s2 out .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte htr2
  refine SepWP.weaken_pre hP2' (SepWP.mono h4968 ?_)
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m⟩
  exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp_m, hcc_m, htr_m⟩

theorem v3_ct1Received_err_4884_to_exit_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx1 : s.readReg64 .x1 = ca1)
    (hx22 : s.readReg64 .x22 = pa1) (hx0 : s.readReg64 .x0 = pa2)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have h4884 := v3cr_states_from_pb_err_4884_placed hA s0 s out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4
    (memRegion (s0.sp - 2400#64) 176 ∗
     memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
     memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ Rest)
    hsp0_align hpc hrun hsp hx19 hx1 hx22 hx0 hx28 hx26 hx21 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h4884) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx22_2, htr2⟩
  have h2304 :
      memRegion (s0.sp - 2400#64) 176 ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      memRegion ((s0.sp - 2400#64) + 232#64) 2072 ⊢
      memRegion (s0.sp - 2400#64) 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have hP2' : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) := by
    refine Entails.trans hP2 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (memRegion (s0.sp - 2400#64) 176 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       memRegion ((s0.sp - 2400#64) + 232#64) 2072) ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left h2304)
  have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx22_2]; rfl
  have h4968 := v3cr_states_from_pb_err_4968_placed (A := A) (F := F) (ext := ext) s0 s2 out .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte htr2
  refine SepWP.weaken_pre hP2' (SepWP.mono h4968 ?_)
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m⟩
  exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp_m, hcc_m, htr_m⟩

set_option maxHeartbeats 1200000 in
theorem v3_ct1Received_post_enc_1012_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1012#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = la2)
    (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = ca2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
          (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases henc : fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error err =>
    rw [v3cr_states_from_pb_ct1Received_sendingEk_err_any_eq u ucSt pbEnc err huc henc]
    have herr := v10_resultPolyEncoder_err_entails_tag_392 A (s0.sp - 2400#64) err
    have hdealloc := v3cr_unchunkedHeap_entails_dealloc A (F := F) ucSt
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    have hpre_err :
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest ⊢
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        (memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗
         (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
         (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
         vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) := by
      refine Entails.trans (Entails.of_eq (show _ =
        resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        (memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗
         (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
         (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono herr (sepConj_mono_left hdealloc)) (Entails.of_eq (by ac_rfl))
    refine SepWP.seq (SepWP.weaken_pre hpre_err
      (v3cr_post_enc_1012_err_placed s (s0.sp - 2400#64) out pa1 pa4 ca3 ca2 _
        hfsp_align hpc hrun hsp hx19 hx21 hx22 hx26 hx28)) ?_
    intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
    have h2072 :
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ⊢
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 := by
      refine Entails.trans (Entails.of_eq (show _ =
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 by ac_rfl)) ?_
      exact collapse_top <| collapse_step (Entails.refl _) <|
        collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
        collapse_step (Entails.refl _) <| Entails.refl _
    have hP2' : P2 ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest := by
      refine Entails.trans hP2 ?_
      refine Entails.trans (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗
         (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
         (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A ca1 pa1 ∗ vecCapPtrDealloc A ca2 pa2 ∗
         vecCapPtrDealloc A ca3 pa3 ∗ vecCapPtrDealloc A ca4 pa4 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h2072) (Entails.of_eq (by ac_rfl))
    exact SepWP.weaken_pre hP2'
      (v3_ct1Received_err_1024_to_exit_placed hA s0 s2 out pbA ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx28_2 hx26_2 hx21_2 (htr2.trans htr))
  | ok enc =>
    rw [v3cr_states_from_pb_ct1Received_ok_eq u ucSt pbEnc enc huc henc]
    dsimp only [resultPolyEncoderFromPbAt]
    have hopen := v3cr_polyEncoderAt_open A ((s0.sp - 2400#64) + 1888#64) enc
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hopen)))))))))))))) ?_
    wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w_tag
    apply ProofLib.SepWP.exists_left; intro e_w8; apply ProofLib.SepWP.exists_left; intro e_w16
    apply ProofLib.SepWP.exists_left; intro e_w24; apply ProofLib.SepWP.exists_left; intro e_w32
    apply ProofLib.SepWP.exists_left; intro e_w40; apply ProofLib.SepWP.exists_left; intro e_w48
    apply ProofLib.SepWP.exists_left; intro e_w56; apply ProofLib.SepWP.exists_left; intro e_w64
    apply ProofLib.SepWP.exists_left; intro e_w72; apply ProofLib.SepWP.exists_left; intro e_w80
    apply ProofLib.SepWP.exists_left; intro e_w88; apply ProofLib.SepWP.exists_left; intro e_w96
    apply ProofLib.SepWP.exists_left; intro e_w104; apply ProofLib.SepWP.exists_left; intro e_w112
    apply ProofLib.SepWP.exists_left; intro e_w120; apply ProofLib.SepWP.exists_left; intro e_w128
    apply ProofLib.SepWP.exists_left; intro e_w136; apply ProofLib.SepWP.exists_left; intro e_w144
    apply ProofLib.SepWP.exists_left; intro e_w152; apply ProofLib.SepWP.exists_left; intro e_q160
    apply ProofLib.SepWP.exists_left; intro e_q176; apply ProofLib.SepWP.exists_left; intro e_q192
    apply ProofLib.SepWP.exists_left; intro e_q208; apply ProofLib.SepWP.exists_left; intro e_q224
    apply ProofLib.SepWP.exists_left; intro e_q240; apply ProofLib.SepWP.exists_left; intro e_q256
    apply ProofLib.SepWP.exists_left; intro e_q272; apply ProofLib.SepWP.exists_left; intro e_q288
    apply ProofLib.SepWP.exists_left; intro e_q304; apply ProofLib.SepWP.exists_left; intro e_q320
    apply ProofLib.SepWP.exists_left; intro e_q336; apply ProofLib.SepWP.exists_left; intro e_q352
    apply ProofLib.SepWP.exists_left; intro e_q368; apply ProofLib.SepWP.exists_left; intro e_w384
    apply ProofLib.SepWP.exists_left; intro e_w392
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜(w_tag - 2#64 == 0#64) = false⌝ ∗
      (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
         e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
         e_w384 e_w392 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗
       (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
       (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_polyEncoderHeap A enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
         e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
         e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    apply ProofLib.SepWP.pure_elim; intro htag_ne2
    dsimp only [v3cr_polyEncoderWordsAt]
    rw [sepConj_assoc (((s0.sp - 2400#64) + 1888#64) ↦₆₄ w_tag)]
    refine SepWP.seq (v3cr_post_enc_1012_ok_placed s (s0.sp - 2400#64) out w_tag la2 pa4 pa1 la1 ca3 ca2 _
      hfsp_align htag_ne2 hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28) ?_
    intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx15_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
    have h4984 := v3_ct1Received_ok_4984_to_exit_placed hA s0 s2 out pbA ucSt enc
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
      e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
      e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 Rest
      hsp0_align hpc2 hrun2 hsp2 hx15_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 (htr2.trans htr)
    refine SepWP.weaken_pre (Entails.trans hP2 ?_) h4984
    dsimp only [v3cr_polyEncoderWordsAt]
    exact Entails.of_eq (by ac_rfl)

theorem v3_ct1Received_some_enc_924_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hEnc : Variant2aPlaced.EncoderFromPbPlacedOkExt A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200 : BitVec 64)
    (R : SepProp)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hpts : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx1 : s.readReg64 .x1 = ca1) (hx8 : s.readReg64 .x8 = w0)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h1496_split :
      v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 =
        (((s0.sp - 2400#64) + 1504#64) ↦₆₄ w8) ∗
        ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48)) := by
    dsimp only [v1_optProtoPolyEncoderWordsAt]
    simp only [v1_bv_add_add_lit, BitVec.ofNat_eq_ofNat]; ac_rfl
  have hcopy := v3cr_copy_enc_to_call_924_placed (ext := ext) s (s0.sp - 2400#64) out pbA
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w0 w8 w16 w24 w32 w40 w48 v64 v96 v184 v192 v200 e0 e8 e16 e24 e32 e40 e48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
      ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
       (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
       (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48)) ∗
      memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
      v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      statesFromPbJumpTablePlacedAt ∗ A.pool)
    hfsp_align hpc hrun hsp hx0 hx1 hx8 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  refine SepWPp.weaken_pre (by rw [h1496_split]; exact Entails.of_eq (by ac_rfl))
    (v3_sepWPp_seq_clean_lscl hcl hcopy ?_)
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hlr1, htr1⟩
  have hpre_pack :
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
      (((s0.sp - 2400#64) + 1504#64) ↦₆₄ w8) ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48)) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool) ⊢
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) ∗
       A.pool ∗ stackAt s1.sp encoderFromPbStack) ∗
      (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1592 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
    rw [hsp1]
    have hpack_enc := v1_optProtoPolyEncoderAt_pack_some A ((s0.sp - 2400#64) + 240#64)
      (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48
    have h400 := v3_collapse_1888_400 (s0.sp - 2400#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    have h1592 := v3_collapse_fsp_296_1592 (s0.sp - 2400#64) w0 w8 w16 w24 w32 w40 w48
    have hpb224 := v3_collapse_pbA_112_224 pbA w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296) ∗
      (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48) ∗
      (memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        ((((s0.sp - 2400#64) + 1504#64) ↦₆₄ w8) ∗
         ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
          (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
          (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48))) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336) ∗
      (memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56) ∗
      (A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
    rw [← h1496_split]
    exact Entails.trans
      (sepConj_mono h400 (sepConj_mono hpack_enc (sepConj_mono h1592 (sepConj_mono_left hpb224))))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hpre_pack ?_
  have hsp1_align : s1.spAligned = true := by
    unfold State.spAligned; rw [hsp1]; exact hfsp_align
  refine v3_sepWPp_call_lscl hEnc
    (x := ⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 240#64, pbToProtoPolyEncoder pbEnc⟩)
    hcl1 hpc1 hrun1 hsp1_align hlr1
    (fun R' hm => by
      dsimp only [encoderFromPbSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_1, hx1_1, hpts⟩, hm⟩)
    (fun sf => v3_encoderFromPbOnPanic_entails s0 s1 sf _ (htr1.trans htr))
    (fun _ _ => rfl)
    ?_
  intro s2 hpc2 hrun2 hsp2 hcs2 _hcl2
  have h1656 := v3_collapse_fsp_232_1656 (s0.sp - 2400#64)
  dsimp only [encoderFromPbSpec]
  rw [sepConj_assoc]
  apply SepWPp.pure_left; intro htr2
  have hpost_pack :
      (resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) protoPolynomialEncoderSize ∗
       A.pool ∗ stackAt s1.sp encoderFromPbStack) ∗
      (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1592 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
      memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
      resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
        (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ statesFromPbJumpTablePlacedAt := by
    rw [hsp1]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 240#64) protoPolynomialEncoderSize ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1592) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64)
         (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h1656) (Entails.of_eq (by ac_rfl))
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, _, hx28_cs, _, hvregs_cs⟩
  have h1012 := v3_ct1Received_post_enc_1012_placed hA s0 s2 out pbA u ucSt pbEnc
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    statesFromPbJumpTablePlacedAt huc hsp0_align hpc2 hrun2 (hsp2.trans hsp1)
    (hx19_cs.trans hx19_1) (hx20_cs.trans hx20_1) (hx21_cs.trans hx21_1)
    (hx22_cs.trans hx22_1) (hx23_cs.trans hx23_1) (hx24_cs.trans hx24_1)
    (hx25_cs.trans hx25_1) (hx26_cs.trans hx26_1) (hx28_cs.trans hx28_1)
    ((⟨htr2, hvregs_cs⟩ : TraceCalleeSaved s2 s1).trans (htr1.trans htr))
  refine SepWPp.weaken_pre hpost_pack (SepWPp.of_sepWP_ret (SepWP.mono h1012 ?_))
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v3_sepWPp_seq_clean_lscl
  v3_sepWPp_call_lscl
  v3_ct1Received_ok_4984_to_exit_placed
  v3_ct1Received_err_1024_to_exit_placed
  v3_ct1Received_err_4884_to_exit_placed
  v3_ct1Received_post_enc_1012_placed
  v3_ct1Received_some_enc_924_placed
)
end CryptoVerification.SpqrV1.States.FromPb
