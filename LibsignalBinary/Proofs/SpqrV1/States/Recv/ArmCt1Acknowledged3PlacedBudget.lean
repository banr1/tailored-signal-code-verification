/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ct1Acknowledged` Arm, Part 3 (Budget-Threaded)

Top-level budget-threaded relocatable `.ct1Acknowledged` variant contracts
`states_recv_ct1Acknowledged_placed_{ok_ext_ofPrePostEnv,ok_ext,ofEnv_ok_ext}` under
`withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open LibsignalBinary.Proofs.SpqrV1.States.Recv
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (Ct1AckRecvEkTailPreEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux (
  ct1AckPayloadChunk?_eq_none_of_ne sepWPp_seq_vm_lscro sepWPp_seq_vm_lscro_dep
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
  statesRecvVariantPlacedSpecOfEnv statesRecvVariantPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_prologue_pool_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
  addChunkTotal decodedMessageTotal DecodedMessageEnv Ct1AckRecvEkTailPreEnv
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Re-Exports from `ArmCt1Acknowledged3PlacedBudgetAux` -/

alias ct1AckPayloadChunk? := ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk?
alias Ct1AcknowledgedChunkPreEnv := ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkPreEnv
alias Ct1AcknowledgedChunkPostEnv := ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkPostEnv
alias Ct1AcknowledgedChunkEnv := ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkEnv
alias ct1AcknowledgedChunkPreEnv_nonempty :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1AcknowledgedChunkPreEnv_nonempty
alias ct1AcknowledgedChunkPostEnv_nonempty :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1AcknowledgedChunkPostEnv_nonempty
alias StatesRecvCt1AcknowledgedPreEnv :=
  ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPreEnv
alias StatesRecvCt1AcknowledgedPostEnv :=
  ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv
alias StatesRecvCt1AcknowledgedEnv :=
  ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedEnv
alias statesRecvCt1AcknowledgedPreEnv_nonempty :=
  ArmCt1Acknowledged3PlacedBudgetAux.statesRecvCt1AcknowledgedPreEnv_nonempty
alias statesRecvCt1AcknowledgedPostEnv_of_pre :=
  ArmCt1Acknowledged3PlacedBudgetAux.statesRecvCt1AcknowledgedPostEnv_of_pre
alias statesRecvCt1AcknowledgedPostEnv_nonempty :=
  ArmCt1Acknowledged3PlacedBudgetAux.statesRecvCt1AcknowledgedPostEnv_nonempty
alias ct1Ack_step_4468_done_4924_placed :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1Ack_step_4468_done_4924_placed
alias ct1Ack_done_4468_ret_placed :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1Ack_done_4468_ret_placed
alias ct1Ack_step_608_632_words66_placed :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1Ack_step_608_632_words66_placed
alias ct1Ack_ek_4448_ret_placed_ofPrePostEnv :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1Ack_ek_4448_ret_placed_ofPrePostEnv
alias ct1Ack_ek_4448_ret_placed :=
  ArmCt1Acknowledged3PlacedBudgetAux.ct1Ack_ek_4448_ret_placed

/-! ## 2. Top-Level Budget-Threaded `.ct1Acknowledged` Contracts -/

/-- Envelope-parametric budget-threaded relocatable `.ct1Acknowledged` variant contract under
    `withLsCodeRoLoaded` (ready for `states_recv_placed_ok_ext_of_variants_ofPrePostEnv`). -/
theorem states_recv_ct1Acknowledged_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPreChunk : ∀ (outA selfA msgA fsp : BitVec 64) (chunk : Chunk)
      (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
      (st_cost : M.σ),
      msg.epoch = st.uc.epoch →
      ct1AckPayloadChunk? msg.payload = some chunk →
      st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ct1AcknowledgedRecvEkPre ⟨fsp + 1856#64, selfA + 8#64, msgA + 10#64, st, chunk, res⟩))
    (hPostGt : ∀ (outA selfA msgA : BitVec 64) (evs : List AllocEvent),
      msg.epoch > st.uc.epoch →
      FreeOnlyEvs evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ evs)
    (hPostLt : ∀ (outA selfA msgA : BitVec 64),
      msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ [])
    (hPostChunk : ∀ (outA selfA msgA fsp : BitVec 64) (chunk : Chunk)
      (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
      (evs : List AllocEvent),
      msg.epoch = st.uc.epoch →
      ct1AckPayloadChunk? msg.payload = some chunk →
      st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      envs.ct1AcknowledgedRecvEkPost ⟨fsp + 1856#64, selfA + 8#64, msgA + 10#64, st, chunk, res⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ evs)
    (hPostOther : ∀ (outA selfA msgA : BitVec 64),
      msg.epoch = st.uc.epoch →
      ct1AckPayloadChunk? msg.payload = none →
      PostEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
          (.ct1Acknowledged st) msg PreEnv PostEnv)) := by
  have hmemcpy := hC.hmemcpy_sat
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv, hfit0, _hlr_ls⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗
       chunkedStatesAt A.repAlloc selfA (.ct1Acknowledged st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue_pool_placed (M := M) (A := A) (lim := lim) (ext := ext)
    st_cost s0
    (memRegion outA v1RecvSize ∗
     chunkedStatesAt A.repAlloc selfA (.ct1Acknowledged st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
    hsp0_align hpc0 hrun0
  refine sepWPp_seq_vm_lscro_dep hcro0 hpro ?_
  intro s1 hpc1 hrun1 _hvm01 ⟨_hacp01, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := ArmCt1Acknowledged1PlacedBudget.states_recv_dispatch_ct1Acknowledged_placed
    (ext := ext) s1 (s0.sp - 4240#64) selfA
    (chunkedCt1AcknowledgedAt A.repAlloc (selfA + 8#64) st ∗
     memRegion (selfA + 536#64) 392 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     A.pool lim st_cost s1 ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_vm_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hvm12
    ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  set fsp := s0.sp - 4240#64
  have hpre_split :
      (selfA ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedCt1AcknowledgedAt A.repAlloc (selfA + 8#64) st ∗
       memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       A.pool lim st_cost s1 ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words66, ∃∗ sp : SendEkSpills,
        ⌜st.receiving_ek.pts.length = 16 ∧ (w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch)⌝ ∗
        (memRegion (fsp + 976#64) 528 ∗ words66At (selfA + 8#64) w ∗
         stackAt fsp statesRecvCalleeStackX ∗
         ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
          ct1AckPayloadTailAt msgA msg.payload ∗
          (selfA ↦₆₄ 11#64) ∗
          relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
          memRegion (selfA + 536#64) 392 ∗
          statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
          sendEkSpillsAt fsp sp ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
          memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0))) := by
    rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, ← A.pool_of_vmPreserved hvm12]
    have hex66 : chunkedCt1AcknowledgedAt A.repAlloc (selfA + 8#64) st ⊢
        ∃∗ w : Words66,
          ⌜st.receiving_ek.pts.length = 16 ∧ (w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch)⌝ ∗
          words66At (selfA + 8#64) w ∗
          relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) := by
      refine Entails.trans (chunkedCt1AcknowledgedAt_entails_pts_length_16 A.repAlloc (selfA + 8#64) st) ?_
      apply Entails.pure_left; intro hlen
      refine Entails.trans (chunkedCt1AcknowledgedAt_extract66 A.repAlloc (selfA + 8#64) st) ?_
      apply Arm64.Entails.sepExists_elim; intro w
      apply Entails.pure_left; intro hw
      exact Entails.sepExists_right w (Entails.pure_right ⟨hlen, hw⟩ (Entails.refl _))
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352 ∗
          memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Arm64.Entails.sepExists_elim; intro sp
      rw [memRegion_976_880_split_528_352 fsp]
      exact Entails.sepExists_right sp (Entails.of_eq (by sep_ac_rfl))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedCt1AcknowledgedAt A.repAlloc (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      ((selfA ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗
       ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
        ct1AckPayloadTailAt msgA msg.payload) ∗
       A.pool lim st_cost s2 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hex66 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Arm64.Entails.sepExists_elim; intro sp
    apply Arm64.Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp (Entails.of_eq (by sep_ac_rfl)))
  refine SepWPp.weaken_pre hpre_split ?_
  apply ct1Ack_sepWPp_intro_ex hrun2; intro w
  apply ct1Ack_sepWPp_intro_ex hrun2; intro sp
  apply SepWPp.pure_left; rintro ⟨hlen, _, hep⟩
  refine sepWPp_seq_vm_lscro hcro2
    (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_588_608_placed hmemcpy s2 fsp outA selfA msgA w
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
       ct1AckPayloadTailAt msgA msg.payload ∗
       (selfA ↦₆₄ 11#64) ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
       sendEkSpillsAt fsp sp ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s2b hpc2b hrun2b hvm_2_2b ⟨hsp2b, hx19_2b, hx20_2b, hx24_2b, _, htr2b⟩ hcro2b
  have htr2b0 : TraceCalleeSaved s2b s0 := htr2b.trans htr20
  refine sepWPp_seq_vm_lscro hcro2b (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (ct1Ack_step_608_632_words66_placed (ext := ext) s2b fsp outA selfA msgA msg.epoch w
      (words66At (selfA + 8#64) w ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
       ct1AckPayloadTailAt msgA msg.payload ∗
       (selfA ↦₆₄ 11#64) ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc2b hrun2b hsp2b hx19_2b hx20_2b hx24_2b)) ?_
  intro s3 hpc3 hrun3 hvm_2b_3 ⟨hsp3, hx2_3, hx9_3, hx19_3, hx20_3, hx24_3, _, hx8_3, hz_3, htr3⟩ hcro3
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr2b0
  have hvm23 : VmPreserved s2 s3 := hvm_2_2b.trans hvm_2b_3
  rw [hep] at hx9_3 hx8_3 hz_3
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_seq_vm_lscro hcro3
      (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_632_644_gt_placed (ext := ext)
        s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
        hgt hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
    intro s4 hpc4 hrun4 hvm34 ⟨hsp4, hx2_4, _, hx19_4, _, _, _, htr4⟩ hcro4
    have hrecv := states_recv_ct1Acknowledged_gt K st msg hgt
    have hexit := ArmCt1Acknowledged1PlacedBudget.ct1Ack_gt_644_ret_placed
      hC.hdealloc_sat st_cost s0 s4 outA selfA msg.epoch st
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      hcro4.1 hsp0_align hpc4 hrun4 hsp4 hx2_4 hx19_4 (htr4.trans htr30)
    refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      s0 s4 outA selfA msgA (.ct1Acknowledged st) msg st_cost _ R ?_
    refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
    · rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, ← A.pool_of_vmPreserved (hvm23.trans hvm34)]
      have hself_mem := selfA_ct1Acknowledged_entails_memRegion selfA w
      have hrecomp := recompose66_ct1Acknowledged A.repAlloc (fsp + 976#64) w st
      have hstk := sendEkFrame_entails_976_2288 fsp sp
      refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
        (words66At (fsp + 976#64) w ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w))) ∗
        (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp) ∗
        (((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
          ct1AckPayloadTailAt msgA msg.payload) ∗
         statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
         memRegion (fsp + 1504#64) 352 ∗ A.pool lim st_cost s4 ∗
         stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono hself_mem (sepConj_mono hrecomp (sepConj_mono_left hstk)))
        (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl))
    · intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, _hacp_sf, hcs_sf, htr_sf⟩
      refine ⟨⟨evs, hPostGt outA selfA msgA evs hgt hevs, Entails.trans hPf ?_⟩,
        hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by sep_ac_rfl)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_seq_vm_lscro hcro3
        (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_632_4516_lt_placed (ext := ext)
          s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
          hlt hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
      intro s4 hpc4 hrun4 hvm34 ⟨hsp4, _, hx9_4, hx19_4, hx20_4, _, _, htr4⟩ _hcro4
      have hrecv := states_recv_ct1Acknowledged_lt K st msg hlt
      rw [← hep] at hx9_4
      have hexit := ArmCt1Acknowledged2PlacedBudget.ct1Ack_noop_4516_ret_placed
        (A := A.repAlloc) (F := F) hmemcpy s0 s4 outA selfA st w sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s4)
        hsp0_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx20_4 (htr4.trans htr30)
      refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        s0 s4 outA selfA msgA (.ct1Acknowledged st) msg st_cost [] (hPostLt outA selfA msgA hlt) _ R ?_
      refine SepWP.weaken_pre
        (Entails.of_eq (by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, ← A.pool_of_vmPreserved (hvm23.trans hvm34)]
          dsimp only [fsp]; sep_ac_rfl))
        (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hvm4f, hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm4f]
      exact Entails.of_eq (by sep_ac_rfl)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      refine sepWPp_seq_vm_lscro hcro3
        (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_632_4432_eq_placed (ext := ext)
          s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
          heq hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
      intro s4 hpc4 hrun4 hvm34 ⟨hsp4, hx2_4, hx9_4, hx19_4, hx20_4, hx24_4, _, htr4⟩ hcro4
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      have hvm24 : VmPreserved s2 s4 := hvm23.trans hvm34
      rw [heq] at hx2_4
      cases hpay : msg.payload with
      | ek chunk =>
        have hchunk : ct1AckPayloadChunk? msg.payload = some chunk := by
          rw [hpay]; rfl
        have hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag msg.payload) &&& 25769803782#64) != 2#32) = false := by
          rw [hpay]; exact messagePayloadTag_and6_bne_2_of_ek chunk
        refine sepWPp_seq_vm_lscro hcro4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; sep_ac_rfl))
            (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_4432_4448_ek_placed (ext := ext)
              s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hcond hpc4 hrun4 hsp4 hx2_4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 hvm45 ⟨hsp5, hx2_5, _, hx19_5, hx20_5, hx24_5, _, htr5⟩ hcro5
        have hmsg_recomp :
            chunkAt (msgA + 10#64) chunk ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
             memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) ⊢
            messageAt spqrPolyApi msgA msg := by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, hpay]
          dsimp only [ct1AckPayloadTailAt]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWPp.weaken_pre
          (Entails.of_eq (by
            rw [hpay, ← A.pool_of_vmPreserved (hvm24.trans hvm45)]
            dsimp only [ct1AckPayloadTailAt, fsp]; sep_ac_rfl))
          (ct1Ack_ek_4448_ret_placed_ofPrePostEnv (PreEnv := PreEnv)
            hmemcpy hC.ct1AcknowledgedRecvEkChunk_ok st_cost
            s0 s5 outA selfA msgA st msg chunk w sp
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag (.ek chunk)) ∗
             memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)
            R hcro5 hlen hinv
            (fun res hrecv => hPreChunk outA selfA msgA (s0.sp - 4240#64) chunk res st_cost heq hchunk hrecv hfit0)
            (fun res evs hrecv hevs => hPostChunk outA selfA msgA (s0.sp - 4240#64) chunk res evs heq hchunk hrecv hevs)
            (fun res hrecv => states_recv_ct1Acknowledged_eq_ek_res K st msg chunk res heq hpay hrecv)
            (by rw [← hpay]; exact hmsg_recomp)
            hsp0_align hpc5 hrun5 hsp5 hx2_5 hx19_5 hx20_5 hx24_5 (htr5.trans htr40))
      | ekCt1Ack chunk =>
        have hchunk : ct1AckPayloadChunk? msg.payload = some chunk := by
          rw [hpay]; rfl
        have hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag msg.payload) &&& 25769803782#64) != 2#32) = false := by
          rw [hpay]; exact messagePayloadTag_and6_bne_2_of_ekCt1Ack chunk
        refine sepWPp_seq_vm_lscro hcro4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; sep_ac_rfl))
            (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_4432_4448_ek_placed (ext := ext)
              s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hcond hpc4 hrun4 hsp4 hx2_4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 hvm45 ⟨hsp5, hx2_5, _, hx19_5, hx20_5, hx24_5, _, htr5⟩ hcro5
        have hmsg_recomp :
            chunkAt (msgA + 10#64) chunk ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
             memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) ⊢
            messageAt spqrPolyApi msgA msg := by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, hpay]
          dsimp only [ct1AckPayloadTailAt]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWPp.weaken_pre
          (Entails.of_eq (by
            rw [hpay, ← A.pool_of_vmPreserved (hvm24.trans hvm45)]
            dsimp only [ct1AckPayloadTailAt, fsp]; sep_ac_rfl))
          (ct1Ack_ek_4448_ret_placed_ofPrePostEnv (PreEnv := PreEnv)
            hmemcpy hC.ct1AcknowledgedRecvEkChunk_ok st_cost
            s0 s5 outA selfA msgA st msg chunk w sp
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag (.ekCt1Ack chunk)) ∗
             memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)
            R hcro5 hlen hinv
            (fun res hrecv => hPreChunk outA selfA msgA (s0.sp - 4240#64) chunk res st_cost heq hchunk hrecv hfit0)
            (fun res evs hrecv hevs => hPostChunk outA selfA msgA (s0.sp - 4240#64) chunk res evs heq hchunk hrecv hevs)
            (fun res hrecv => states_recv_ct1Acknowledged_eq_ekCt1Ack_res K st msg chunk res heq hpay hrecv)
            (by rw [← hpay]; exact hmsg_recomp)
            hsp0_align hpc5 hrun5 hsp5 hx2_5 hx19_5 hx20_5 hx24_5 (htr5.trans htr40))
      | _ =>
        have hek : ∀ c, msg.payload ≠ .ek c := by intro c h; rw [hpay] at h; cases h
        have hekAck : ∀ c, msg.payload ≠ .ekCt1Ack c := by intro c h; rw [hpay] at h; cases h
        have hnone : ct1AckPayloadChunk? msg.payload = none := ct1AckPayloadChunk?_eq_none_of_ne hek hekAck
        have hrecv := states_recv_ct1Acknowledged_eq_other K st msg heq hek hekAck
        refine sepWPp_seq_vm_lscro hcro4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; sep_ac_rfl))
            (ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_4432_4516_not_ek_placed (ext := ext)
              s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hek hekAck hpc4 hrun4 hsp4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 hvm45 ⟨hsp5, hx9_5, hx19_5, hx20_5, _, _, htr5⟩ _hcro5
        rw [← hep] at hx9_5
        have hexit := ArmCt1Acknowledged2PlacedBudget.ct1Ack_noop_4516_ret_placed
          (A := A.repAlloc) (F := F) hmemcpy s0 s5 outA selfA st w sp
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s5)
          hsp0_align hpc5 hrun5 hsp5 hx9_5 hx19_5 hx20_5 (htr5.trans htr40)
        refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          s0 s5 outA selfA msgA (.ct1Acknowledged st) msg st_cost [] (hPostOther outA selfA msgA heq hnone) _ R ?_
        refine SepWP.weaken_pre
          (Entails.of_eq (by
            rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, ← A.pool_of_vmPreserved (hvm24.trans hvm45)]
            dsimp only [fsp]; sep_ac_rfl))
          (SepWP.mono hexit ?_)
        intro sf Pf _ _ ⟨hvm5f, hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm5f]
        exact Entails.of_eq (by sep_ac_rfl)

alias states_recv_ct1Acknowledged_placed_cro_ok_ext_ofPrePostEnv :=
  states_recv_ct1Acknowledged_placed_ok_ext_ofPrePostEnv

private theorem ite_pos {α : Sort _} {c : Prop} {inst : Decidable c} (hc : c) (t e : α) :
    @ite α c inst t e = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h => exact False.elim (h hc)

private theorem ite_neg {α : Sort _} {c : Prop} {inst : Decidable c} (hc : ¬ c) (t e : α) :
    @ite α c inst t e = e := by
  cases inst with
  | isTrue h => exact False.elim (hc h)
  | isFalse _ => rfl

/-- Canonical exact-envelope budget-threaded relocatable `.ct1Acknowledged` variant contract
    under `withLsCodeRoLoaded` (`StatesRecvCt1AcknowledgedPreEnv` /
    `StatesRecvCt1AcknowledgedPostEnv`). -/
theorem states_recv_ct1Acknowledged_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
          (.ct1Acknowledged st) msg
          (StatesRecvCt1AcknowledgedPreEnv K)
          (StatesRecvCt1AcknowledgedPostEnv K))) := by
  refine states_recv_ct1Acknowledged_placed_ok_ext_ofPrePostEnv A lim F K ext hC st msg
    ?_ ?_ ?_ ?_ ?_
  · intro outA selfA msgA fsp chunk res st_cost heq hchunk _hrecv hfit evs hevs
    apply hfit evs
    dsimp only [StatesRecvCt1AcknowledgedPreEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPreEnv]
    rw [ite_pos heq,
      show ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk? msg.payload = some chunk from hchunk]
    exact hevs
  · intro outA selfA msgA evs hgt hevs
    dsimp only [StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    rw [ite_pos hgt]
    exact hevs
  · intro outA selfA msgA hlt
    dsimp only [StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := fun hgt =>
      BitVec.lt_irrefl _ (BitVec.lt_trans hlt hgt)
    have hne : msg.epoch ≠ st.uc.epoch := fun heq => by
      rw [heq] at hlt
      exact BitVec.lt_irrefl _ hlt
    rw [ite_neg hnotgt, ite_neg hne]
  · intro outA selfA msgA fsp chunk res evs heq hchunk _hrecv hevs
    dsimp only [StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos heq,
      show ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk? msg.payload = some chunk from hchunk]
    exact hevs
  · intro outA selfA msgA heq hnone
    dsimp only [StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos heq,
      show ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk? msg.payload = none from hnone]

alias states_recv_ct1Acknowledged_placed_cro_ok_ext :=
  states_recv_ct1Acknowledged_placed_ok_ext

/-- Single-envelope (`StatesRecvCt1AcknowledgedEnv K`) budget-threaded relocatable
    `.ct1Acknowledged` variant contract under `withLsCodeRoLoaded`. -/
theorem states_recv_ct1Acknowledged_placed_ofEnv_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfEnv M A lim F K
          (.ct1Acknowledged st) msg
          (StatesRecvCt1AcknowledgedEnv K))) := by
  refine states_recv_ct1Acknowledged_placed_ok_ext_ofPrePostEnv A lim F K ext hC st msg
    ?_ ?_ ?_ ?_ ?_
  · intro outA selfA msgA fsp chunk res st_cost heq hchunk _hrecv hfit evs hevs
    apply hfit evs
    dsimp only [StatesRecvCt1AcknowledgedEnv, StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos heq,
      show ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk? msg.payload = some chunk from hchunk]
    exact Or.inl hevs
  · intro outA selfA msgA evs hgt hevs
    dsimp only [StatesRecvCt1AcknowledgedEnv, StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    rw [ite_pos hgt]
    exact hevs
  · intro outA selfA msgA hlt
    dsimp only [StatesRecvCt1AcknowledgedEnv, StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := fun hgt =>
      BitVec.lt_irrefl _ (BitVec.lt_trans hlt hgt)
    have hne : msg.epoch ≠ st.uc.epoch := fun heq => by
      rw [heq] at hlt
      exact BitVec.lt_irrefl _ hlt
    rw [ite_neg hnotgt, ite_neg hne]
  · intro outA selfA msgA fsp chunk res evs heq hchunk _hrecv hevs
    dsimp only [StatesRecvCt1AcknowledgedEnv, StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos heq,
      show ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk? msg.payload = some chunk from hchunk]
    exact hevs
  · intro outA selfA msgA heq hnone
    dsimp only [StatesRecvCt1AcknowledgedEnv, StatesRecvCt1AcknowledgedPostEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedEnv,
      ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos heq,
      show ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk? msg.payload = none from hnone]

alias states_recv_ct1Acknowledged_placed_ofEnv_cro_ok_ext :=
  states_recv_ct1Acknowledged_placed_ofEnv_ok_ext

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudget
