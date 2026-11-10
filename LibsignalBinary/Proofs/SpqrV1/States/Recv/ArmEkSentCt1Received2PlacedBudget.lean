/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ekSentCt1Received` Arm, Part 2 (Budget-Threaded)

Allocator-event envelope (`StatesRecvEkSentCt1ReceivedEnv`), budget-threaded `eq_ct2` branch,
and top-level `[LibsignalPlacement]` contracts `states_recv_ekSentCt1Received_placed_ok_ext*`
(`tag = 6#64`, Block `332`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.CodeLayout
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1PlacedBudget (
  call_ekSentCt1ReceivedRecvCt2Chunk_ofPrePostEnv_placed
  ekSentCt1Received_arm_eq_other_pool_placed
  ekSentCt1Received_arm_lt_pool_placed
  ekSentCt1Received_post_call_err_56574_pool_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs StatesRecvPlacedContractsOfEnv
  sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
  statesRecvCalleeEnvs
  statesRecvVariantPlacedSpecOfEnv statesRecvVariantPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_dispatch_pool_placed states_recv_prologue_pool_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget (
  RecvCt2ChunkEnv recvCt2ChunkEnv_nonempty recvCt2ChunkPlacedSpec
  recvCt2ChunkPlacedSpecOfPrePostEnv
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332

private theorem sepWPp_seq_vm_lscro [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm (P_mid sm) post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hvm hQ hcro'))))

private theorem sepWPp_seq_ex_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → α → SepProp}
    {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ ∃ a : α, (Pm ⊢ P_mid sm a) ∧ Q sm))
    (h2 : ∀ (sm : State) (a : α), sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm (P_mid sm a) post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, a, hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm a hpc hrun hvm hQ hcro'))))

/-! ## 1. Exact Arm Envelope for `States.ekSentCt1Received` (Block `332`, `tag = 6#64`) -/

/-- Allocator-event envelope of `<States>::recv` on `.ekSentCt1Received st`
    (`tag = 6#64`, Block `332`):
    - `x.msg.epoch == st.uc.epoch`, `.ct2 chunk`: `RecvCt2ChunkEnv ⟨0, 0, st, st.uc.epoch, 0, chunk⟩`;
    - `x.msg.epoch == st.uc.epoch`, non-`.ct2`: `[]`;
    - `x.msg.epoch > st.uc.epoch`: `FreeOnlyEvs`;
    - `x.msg.epoch < st.uc.epoch`: `[]`. -/
def StatesRecvEkSentCt1ReceivedEnv {F : ShaCompress}
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .ekSentCt1Received st =>
    if x.msg.epoch == st.uc.epoch then
      match x.msg.payload with
      | .ct2 chunk =>
        RecvCt2ChunkEnv ⟨0, 0, st, st.uc.epoch, 0, chunk⟩ evs
      | _ => evs = []
    else if x.msg.epoch > st.uc.epoch then
      FreeOnlyEvs evs
    else
      evs = []
  | _ => evs = []

theorem statesRecvEkSentCt1ReceivedEnv_nonempty {F : ShaCompress}
    (x : StatesRecvGhost F) :
    ∃ evs, StatesRecvEkSentCt1ReceivedEnv x evs := by
  unfold StatesRecvEkSentCt1ReceivedEnv
  split
  · split
    · split
      · exact recvCt2ChunkEnv_nonempty _
      · exact ⟨[], rfl⟩
    · split
      · exact ⟨[], FreeOnlyEvs.nil⟩
      · exact ⟨[], rfl⟩
  · exact ⟨[], rfl⟩

abbrev EkSentCt1ReceivedArmEnv {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  StatesRecvEkSentCt1ReceivedEnv ⟨0, 0, 0, .ekSentCt1Received st, msg⟩ evs

theorem ekSentCt1ReceivedArmEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    ∃ evs, EkSentCt1ReceivedArmEnv st msg evs :=
  statesRecvEkSentCt1ReceivedEnv_nonempty _

/-- Every event trace in `StatesRecvEkSentCt1ReceivedEnv` on `.ekSentCt1Received st` embeds into
    the peak-spec arm shape (`SeqEnv (RecvCt2ChunkEnv ...) FreeOnlyEvs` in the same-epoch
    `.ct2 chunk` case and `FreeOnlyEvs` otherwise). -/
theorem statesRecvEkSentCt1ReceivedEnv_imp_seq_or_freeOnly {F : ShaCompress}
    {outA selfA msgA : BitVec 64}
    {st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)}
    {msg : Message spqrPolyApi} {evs : List AllocEvent}
    (h : StatesRecvEkSentCt1ReceivedEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs) :
    if msg.epoch == st.uc.epoch then
      match msg.payload with
      | .ct2 chunk =>
        SeqEnv (RecvCt2ChunkEnv ⟨0, 0, st, msg.epoch, 0, chunk⟩) FreeOnlyEvs evs
      | _ => FreeOnlyEvs evs
    else
      FreeOnlyEvs evs := by
  dsimp only [StatesRecvEkSentCt1ReceivedEnv] at h
  by_cases heq_b : (msg.epoch == st.uc.epoch) = true
  · have heq : msg.epoch = st.uc.epoch := beq_iff_eq.mp heq_b
    simp only [heq_b, ↓reduceIte] at h ⊢
    cases hp : msg.payload with
    | ct2 chunk =>
      rw [hp] at h
      dsimp only at h ⊢
      rw [heq]
      exact Or.inl h
    | none | hdr _ | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ =>
      rw [hp] at h
      subst h
      exact FreeOnlyEvs.nil
  · simp only [heq_b, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hgt : msg.epoch > st.uc.epoch
    · simp only [hgt, ↓reduceIte] at h
      exact h
    · simp only [hgt, ↓reduceIte] at h
      subst h
      exact FreeOnlyEvs.nil

/-! ## 2. Re-exported Pre/Post-Call Blocks from `ArmEkSentCt1Received2PlacedBudgetAux` -/

abbrev ekSentCt1Received_post_call_still_56574_placed :=
  @ArmEkSentCt1Received2PlacedBudgetAux.ekSentCt1Received_post_call_still_56574_placed

abbrev ekSentCt1Received_post_call_still_56574_pool_placed :=
  @ArmEkSentCt1Received2PlacedBudgetAux.ekSentCt1Received_post_call_still_56574_pool_placed

abbrev ekSentCt1Received_post_call_done_56574_placed :=
  @ArmEkSentCt1Received2PlacedBudgetAux.ekSentCt1Received_post_call_done_56574_placed

abbrev ekSentCt1Received_post_call_done_56574_pool_placed :=
  @ArmEkSentCt1Received2PlacedBudgetAux.ekSentCt1Received_post_call_done_56574_pool_placed

abbrev ekSentCt1Received_pre_call_228_350_placed :=
  @ArmEkSentCt1Received2PlacedBudgetAux.ekSentCt1Received_pre_call_228_350_placed

/-! ## 3. `eq_ct2` Arm (`+228 -> s0.x30`) and Complete `.ekSentCt1Received` Arm -/

set_option maxHeartbeats 800000 in
/-- Envelope-parametric relocatable `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch` and
    `msg.payload = .ct2 chunk` (`+228 -> s0.x30`, Block `332`), threading `RustCliAllocBudget M`. -/
theorem ekSentCt1Received_arm_eq_ct2_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hfit_callee : FitsEnv M lim st_cost
      (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
        st, st.uc.epoch, msgA + 10#64, chunk⟩))
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (evs : List AllocEvent),
      CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
        st, st.uc.epoch, msgA + 10#64, chunk⟩ evs →
      ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (States.recv K (.ekSentCt1Received st) msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      Q_post Q_panic := by
  rcases hinv with ⟨hsort, hroot⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  refine sepWPp_seq_ex_lscro hcro
    (ekSentCt1Received_pre_call_228_350_placed hmemcpy_sat st_cost s0 s outA selfA msgA
      st msg chunk P_rest heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr) ?_
  intro sm sp1 hpcm hrunm _ ⟨hsp_m, hlr_m, hx0_m, hx1_m, hx2_m, hx3_m, hx19_m, htr_m⟩ hcro_m
  refine SepWPp.of_sepWP
    (call_ekSentCt1ReceivedRecvCt2Chunk_ofPrePostEnv_placed hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk st_cost hsort hroot hfit_callee
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := lsmpl.base 332 + 4384#64) (R := R)
      hcro_m hpcm hrunm hsp_m hfsp_align hlr_m htr_m hx0_m hx1_m hx2_m hx3_m rfl hpanic ?_)
  intro evs hevs sf2 hpc2 hrun2 hsp2 hcs2 htr2
  have hmsg_eq :
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
       chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
      messageAt spqrPolyApi msgA msg := by
    dsimp only [messageAt]
    rw [hpay, messagePayloadAt_ct2 msgA chunk]
  have hx19_2 : sf2.readReg64 .x19 = outA := hcs2.1.trans hx19_m
  cases hres : st.recv_ct2_chunk K st.uc.epoch chunk with
  | error err =>
    cases err with
    | panic p =>
      dsimp only [ekSentCt1ReceivedRecvChunkResultAt]; rw [sepConj_assoc]
      exact SepWP.pure_elim fun hfalse => False.elim hfalse
    | err e =>
      have he := recv_ct2_chunk_err_eq_macVerifyFailed st st.uc.epoch chunk e hres
      subst he
      have hmodel := states_recv_ekSentCt1Received_eq_ct2_err K st msg chunk .macVerifyFailed heq hpay hres
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (ekSentCt1Received_post_call_err_56574_pool_placed (A := A) (lim := lim) (F := F)
            (M.stepEvents evs st_cost)
            s0 sf2 outA sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗
             messageAt spqrPolyApi msgA msg ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)
            hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨_, hPf, hsp_sf, _, hcs_sf, htr_sf⟩ =>
            hdone evs hevs sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX]
      sep_ac_rfl
  | ok outRes =>
    cases outRes with
    | stillReceiving outSt =>
      have hmodel := states_recv_ekSentCt1Received_eq_ct2_still K st msg chunk outSt heq hpay hres
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (ekSentCt1Received_post_call_still_56574_pool_placed (A := A) (lim := lim) hmemcpy_sat
            (M.stepEvents evs st_cost) s0 sf2 outA outSt sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗
             messageAt spqrPolyApi msgA msg ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)
            hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone evs hevs sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX]
      sep_ac_rfl
    | done pair =>
      rcases pair with ⟨nhr, sec⟩
      have hmodel := states_recv_ekSentCt1Received_eq_ct2_done K st msg chunk nhr sec heq hpay hres
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (ekSentCt1Received_post_call_done_56574_pool_placed (A := A) (lim := lim) hmemcpy_sat
            (M.stepEvents evs st_cost) s0 sf2 outA nhr sec sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗
             messageAt spqrPolyApi msgA msg ∗
             tokenInitPlacedAt ∗ reduceTablePlacedAt)
            hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone evs hevs sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX]
      sep_ac_rfl

/-- Envelope-parametric complete relocatable `.ekSentCt1Received` arm of `<States>::recv`
    (`+228 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_ekSentCt1Received_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hFit : FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩))
    (hPre_ct2 : ∀ chunk,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
          st, st.uc.epoch, msgA + 10#64, chunk⟩))
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hPost_ct2 : ∀ chunk evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
        st, st.uc.epoch, msgA + 10#64, chunk⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs)
    (hPost_other : msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct2 c) →
      PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ekSentCt1Received st) msg
              PreEnv PostEnv).post ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ekSentCt1Received st) msg
              PreEnv PostEnv).onPanic ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  have hpre_comm :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
      statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by sep_ac_rfl
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      s0 s outA selfA msgA (.ekSentCt1Received st) msg st_cost _ R ?_
    rw [states_recv_ekSentCt1Received_gt K st msg hgt, hpre_comm]
    refine SepWP.mono
      (ArmEkSentCt1Received1PlacedBudget.ekSentCt1Received_arm_gt_placed hdealloc st_cost
        s0 s outA selfA msgA st msg
        statesRecvRoPlacedAt hgt hcro.1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, _, hcs_sf, htr_sf⟩ =>
        ⟨⟨evs, hPost_gt hgt evs hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
         hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        s0 s outA selfA msgA (.ekSentCt1Received st) msg st_cost [] (hPost_lt hlt) _ R ?_
      rw [states_recv_ekSentCt1Received_lt K st msg hlt, hpre_comm, AllocCostModel.stepEvents_nil]
      refine SepWP.mono
        (ekSentCt1Received_arm_lt_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
          statesRecvRoPlacedAt hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct2 chunk =>
        dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]
        rw [show memRegion outA v1RecvSize ∗
              chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTablePlacedAt ∗
                ((lsLogFilterAddr ↦₆₄ 0#64) ∗
                  ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
              A.pool lim st_cost s ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTablePlacedAt ∗
              ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
              memRegion outA v1RecvSize ∗
              chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cost s ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by sep_ac_rfl]
        refine ekSentCt1Received_arm_eq_ct2_placed (K := K) hcall hmemcpy_sat st_cost
          s0 s outA selfA msgA st msg chunk
          (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R
          hcro hinv (hPre_ct2 chunk heq hpay hFit) heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
          (fun evs hevs sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
          (fun sf Pf hpan hmem_f => ?_)
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantPlacedSpecOfPrePostEnv]
          rw [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨evs, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨htrf, hPost_ct2 chunk evs heq hpay hevs⟩,
            Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]
          sep_ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantPlacedSpecOfPrePostEnv]
          unfold DefsPlacedBudget.statesRecvBudgetOnPanic
            LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesRecvBudgetOnPanic
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨states_recv_ekSentCt1Received_eq_ct2_panic K st msg chunk heq hpay hpan'.1.1,
            hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1 _ | ct1Ack _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          s0 s outA selfA msgA (.ekSentCt1Received st) msg st_cost []
          (hPost_other heq hct2) _ R ?_
        rw [states_recv_ekSentCt1Received_eq_other K st msg heq hct2, hpre_comm,
            AllocCostModel.stepEvents_nil]
        refine SepWP.mono
          (ekSentCt1Received_arm_eq_other_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
            statesRecvRoPlacedAt heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

theorem states_recv_arm_ekSentCt1Received_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {Env : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hFit : FitsEnv M lim st_cost (Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩))
    (hPre_ct2 : ∀ chunk,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      FitsEnv M lim st_cost (Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
          st, st.uc.epoch, msgA + 10#64, chunk⟩))
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch →
      Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hPost_ct2 : ∀ chunk evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
        st, st.uc.epoch, msgA + 10#64, chunk⟩ evs →
      Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs)
    (hPost_other : msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct2 c) →
      Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ekSentCt1Received st) msg Env).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ekSentCt1Received st) msg Env).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) :=
  states_recv_arm_ekSentCt1Received_placed_ofPrePostEnv
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R hFit
    hPre_ct2 hPost_gt hPost_lt hPost_ct2 hPost_other
    hcro hinv hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- Canonical exact-envelope (`StatesRecvEkSentCt1ReceivedEnv`) relocatable `.ekSentCt1Received`
    arm of `<States>::recv` (`+228 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_ekSentCt1Received_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350)
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F M A lim)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hFit : FitsEnv M lim st_cost
      (StatesRecvEkSentCt1ReceivedEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ekSentCt1Received st) msg
              StatesRecvEkSentCt1ReceivedEnv).post ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ekSentCt1Received st) msg
              StatesRecvEkSentCt1ReceivedEnv).onPanic ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  refine states_recv_arm_ekSentCt1Received_placed_ofEnv hdealloc hcall hmemcpy_sat st_cost
    s0 s outA selfA msgA st msg R hFit
    (fun chunk heq hp hfits => ?_)
    (fun hgt evs hevs => ?_)
    (fun hlt => ?_)
    (fun chunk evs heq hp hevs => ?_)
    (fun heq hno => ?_)
    hcro hinv hpc hrun hsp hsp_align hx1 hx19 hx24 htr
  · have heq_b : (msg.epoch == st.uc.epoch) = true := beq_iff_eq.mpr heq
    have henv_eq :
        StatesRecvEkSentCt1ReceivedEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ =
          RecvCt2ChunkEnv ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64,
            st, st.uc.epoch, msgA + 10#64, chunk⟩ := by
      funext evs
      dsimp only [StatesRecvEkSentCt1ReceivedEnv, RecvCt2ChunkEnv]
      simp only [heq_b, ↓reduceIte, hp]
    exact Eq.mp (congrArg (FitsEnv M lim st_cost) henv_eq) hfits
  · have hne : (msg.epoch == st.uc.epoch) = false :=
      beq_eq_false_iff_ne.mpr fun h => BitVec.lt_irrefl _ (h ▸ hgt)
    dsimp only [StatesRecvEkSentCt1ReceivedEnv]
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hgt]
    exact hevs
  · have hne : (msg.epoch == st.uc.epoch) = false :=
      beq_eq_false_iff_ne.mpr fun h => BitVec.lt_irrefl _ (h ▸ hlt)
    have hnot_gt : ¬ msg.epoch > st.uc.epoch :=
      fun hgt => BitVec.lt_irrefl _ (BitVec.lt_trans hlt hgt)
    dsimp only [StatesRecvEkSentCt1ReceivedEnv]
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hnot_gt]
  · have heq_b : (msg.epoch == st.uc.epoch) = true := beq_iff_eq.mpr heq
    dsimp only [RecvCt2ChunkEnv] at hevs
    dsimp only [StatesRecvEkSentCt1ReceivedEnv, RecvCt2ChunkEnv]
    simp only [heq_b, ↓reduceIte, hp]
    exact hevs
  · cases hp : msg.payload with
    | ct2 c => exact False.elim (hno c hp)
    | none | hdr _ | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ =>
      dsimp only [StatesRecvEkSentCt1ReceivedEnv]
      simp only [beq_iff_eq.mpr heq, hp, ↓reduceIte]

/-! ## 4. Top-Level Relocatable `subroutine_ok` Contracts (`tag = 6#64`, Block `332`) -/

/-- Envelope-parametric top-level relocatable `subroutine_ok` theorem for `<States>::recv`
    (Block `332`) on the `.ekSentCt1Received` variant (`tag = 6#64`). -/
theorem states_recv_ekSentCt1Received_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ outA selfA msgA evs, FreeOnlyEvs evs →
        PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch →
      ∀ outA selfA msgA, PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hPost_other : msg.epoch = st.uc.epoch → (∀ c, msg.payload ≠ .ct2 c) →
      ∀ outA selfA msgA, PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hCt2_pre : ∀ outA selfA msgA chunk st_cost oA sA,
      msg.epoch = st.uc.epoch → msg.payload = .ct2 chunk →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ekSentCt1ReceivedRecvCt2Pre ⟨oA, sA, st, st.uc.epoch, msgA + 10#64, chunk⟩))
    (hCt2_post : ∀ outA selfA msgA chunk oA sA evs,
      msg.epoch = st.uc.epoch → msg.payload = .ct2 chunk →
      envs.ekSentCt1ReceivedRecvCt2Post ⟨oA, sA, st, st.uc.epoch, msgA + 10#64, chunk⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ekSentCt1Received st) msg
          PreEnv PostEnv)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv, hfit, hlr_ls⟩, hmem⟩
  have _hlr_x30 : LsRetAddr624 (s0.readReg64 .x30) := hlr_ls
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) hsp0_align hpc0 hrun0
  refine sepWPp_seq_vm_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 _ ⟨_, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s1
    (s0.sp - 4240#64) selfA 6#64
    (chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_vm_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 _ ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have hpre2 :
      (selfA ↦₆₄ 6#64) ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      (chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre2 ?_
  exact states_recv_arm_ekSentCt1Received_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv)
    hC.hdealloc_sat hC.ekSentCt1ReceivedRecvCt2Chunk_ok hC.hmemcpy_sat st_cost
    s0 s2 outA selfA msgA st msg R hfit
    (fun chunk heq hp hF => hCt2_pre outA selfA msgA chunk st_cost _ _ heq hp hF)
    (fun hgt evs hevs => hPost_gt hgt outA selfA msgA evs hevs)
    (fun hlt => hPost_lt hlt outA selfA msgA)
    (fun chunk evs heq hp hevs => hCt2_post outA selfA msgA chunk _ _ evs heq hp hevs)
    (fun heq hno => hPost_other heq hno outA selfA msgA)
    hcro2 hinv hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1)

theorem states_recv_ekSentCt1Received_placed_ok_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {Env : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ outA selfA msgA evs, FreeOnlyEvs evs →
        Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch →
      ∀ outA selfA msgA, Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hPost_other : msg.epoch = st.uc.epoch → (∀ c, msg.payload ≠ .ct2 c) →
      ∀ outA selfA msgA, Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ [])
    (hCt2_pre : ∀ outA selfA msgA chunk st_cost oA sA,
      msg.epoch = st.uc.epoch → msg.payload = .ct2 chunk →
      FitsEnv M lim st_cost (Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ekSentCt1ReceivedRecvCt2Pre ⟨oA, sA, st, st.uc.epoch, msgA + 10#64, chunk⟩))
    (hCt2_post : ∀ outA selfA msgA chunk oA sA evs,
      msg.epoch = st.uc.epoch → msg.payload = .ct2 chunk →
      envs.ekSentCt1ReceivedRecvCt2Post ⟨oA, sA, st, st.uc.epoch, msgA + 10#64, chunk⟩ evs →
      Env ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ evs) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ekSentCt1Received st) msg Env)) :=
  states_recv_ekSentCt1Received_placed_ok_ext_ofPrePostEnv
    hC st msg hPost_gt hPost_lt hPost_other hCt2_pre hCt2_post

/-- Canonical zero-side-condition relocatable specification proof for
    `States.ekSentCt1Received st` (`tag = 6#64`, Block `332`) under `StatesRecvPlacedContracts`
    and the exact arm envelope `StatesRecvEkSentCt1ReceivedEnv`. -/
theorem states_recv_ekSentCt1Received_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ekSentCt1Received st) msg
          StatesRecvEkSentCt1ReceivedEnv)) := by
  refine states_recv_ekSentCt1Received_placed_ok_ext_ofEnv hC st msg
    (fun hgt outA selfA msgA evs hevs => ?_)
    (fun hlt outA selfA msgA => ?_)
    (fun heq hno outA selfA msgA => ?_)
    (fun outA selfA msgA chunk st_cost oA sA heq hp hfits => ?_)
    (fun outA selfA msgA chunk oA sA evs heq hp hevs => ?_)
  · have hne : (msg.epoch == st.uc.epoch) = false :=
      beq_eq_false_iff_ne.mpr fun h => BitVec.lt_irrefl _ (h ▸ hgt)
    dsimp only [StatesRecvEkSentCt1ReceivedEnv]
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hgt]
    exact hevs
  · have hne : (msg.epoch == st.uc.epoch) = false :=
      beq_eq_false_iff_ne.mpr fun h => BitVec.lt_irrefl _ (h ▸ hlt)
    have hnot_gt : ¬ msg.epoch > st.uc.epoch :=
      fun hgt => BitVec.lt_irrefl _ (BitVec.lt_trans hlt hgt)
    dsimp only [StatesRecvEkSentCt1ReceivedEnv]
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hnot_gt]
  · cases hp : msg.payload with
    | ct2 c => exact False.elim (hno c hp)
    | none | hdr _ | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ =>
      dsimp only [StatesRecvEkSentCt1ReceivedEnv]
      simp only [beq_iff_eq.mpr heq, hp, ↓reduceIte]
  · have heq_b : (msg.epoch == st.uc.epoch) = true := beq_iff_eq.mpr heq
    have henv_eq :
        StatesRecvEkSentCt1ReceivedEnv ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩ =
          RecvCt2ChunkEnv ⟨oA, sA, st, st.uc.epoch, msgA + 10#64, chunk⟩ := by
      funext evs
      dsimp only [StatesRecvEkSentCt1ReceivedEnv, RecvCt2ChunkEnv]
      simp only [heq_b, ↓reduceIte, hp]
    exact Eq.mp (congrArg (FitsEnv M lim st_cost) henv_eq) hfits
  · have heq_b : (msg.epoch == st.uc.epoch) = true := beq_iff_eq.mpr heq
    dsimp only [statesRecvCalleeEnvs, RecvCt2ChunkEnv] at hevs
    dsimp only [StatesRecvEkSentCt1ReceivedEnv, RecvCt2ChunkEnv]
    simp only [heq_b, ↓reduceIte, hp]
    exact hevs

abbrev states_recv_ekSentCt1Received_exact_placed_ok_ext :=
  @states_recv_ekSentCt1Received_placed_ok_ext

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudget
