/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ekReceivedCt1Sampled` Arm (Budget-Threaded)

Allocator-event envelopes (`StatesRecvEkReceivedCt1SampledPreEnv` /
`StatesRecvEkReceivedCt1SampledPostEnv`), `<EkReceivedCt1Sampled>::recv_ct1_ack` call composition,
and top-level `[LibsignalPlacement]` contracts for `.ekReceivedCt1Sampled` (tag `10#64`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget

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
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_base_add)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  EkReceivedCt1SampledRecvCt1AckPostEnv EkReceivedCt1SampledRecvCt1AckPreEnv
  SendCt2EncoderBytesPreEnv ekReceivedCt1SampledRecvCt1AckPlacedSpec
  ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv
  sendCt2EncoderBytesPreEnv_nonempty unchunkedSendCt2Env_nonempty
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget (UnchunkedSendCt2Env)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv
  statesRecvCalleeEnvs statesRecvVariantPlacedSpecOfEnv statesRecvVariantPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_prologue_pool_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudgetAux (
  sepWPp_seq_vm_clean sepWPp_seq_vm_lscl
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332

/-! ## 1. Allocation-Event Envelopes for `.ekReceivedCt1Sampled` -/

/-- Boolean predicate matching the `.ct1Ack true` and `.ekCt1Ack _` payload arms of
    `<States>::recv` on `.ekReceivedCt1Sampled`. -/
def isEkAckPayload (p : MessagePayload spqrPolyApi) : Bool :=
  match p with
  | .ct1Ack true => true
  | .ekCt1Ack _ => true
  | _ => false

/-- Exact allocation-phase prefix envelope of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`)
    on state `st`: sequences `UnchunkedSendCt2Env` with
    `SendCt2EncoderBytesPreEnv ct2.length mac.length` when `st.uc.send_ct2 K = .ok (outUc, ct2, mac)`,
    and `[]` otherwise. -/
def EkReceivedCt1SampledAckPreEnv {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (evs : List AllocEvent) : Prop :=
  match st.uc.send_ct2 K with
  | .error _ => evs = []
  | .ok (outUc, ct2, mac) =>
    SeqEnv
      (UnchunkedSendCt2Env ⟨0#64, 0#64, st.uc, outUc, ct2, mac⟩)
      (SendCt2EncoderBytesPreEnv ct2.length mac.length)
      evs

/-- Postcondition envelope of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`) on state `st`:
    `EkReceivedCt1SampledAckPreEnv K st` followed by `FreeOnlyEvs`. -/
def EkReceivedCt1SampledAckPostEnv {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (EkReceivedCt1SampledAckPreEnv K st) FreeOnlyEvs evs

theorem ekReceivedCt1SampledAckPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    ∃ evs, EkReceivedCt1SampledAckPreEnv K st evs := by
  unfold EkReceivedCt1SampledAckPreEnv
  cases hsc : st.uc.send_ct2 K with
  | error _ => exact ⟨[], rfl⟩
  | ok val =>
    rcases val with ⟨outUc, ct2, mac⟩
    obtain ⟨e1, h1⟩ := unchunkedSendCt2Env_nonempty ⟨0#64, 0#64, st.uc, outUc, ct2, mac⟩
    obtain ⟨e2, h2⟩ := sendCt2EncoderBytesPreEnv_nonempty ct2.length mac.length
    exact ⟨e1 ++ e2, SeqEnv.append h1 h2⟩

theorem ekReceivedCt1SampledAckPostEnv_nonempty {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    ∃ evs, EkReceivedCt1SampledAckPostEnv K st evs :=
  let ⟨evs, h⟩ := ekReceivedCt1SampledAckPreEnv_nonempty K st
  ⟨evs, Or.inl h⟩

/-- Exact allocation-phase prefix envelope for the `.ekReceivedCt1Sampled` arm of `<States>::recv`
    (Block `332`): `EkReceivedCt1SampledAckPreEnv K st` on same-epoch `.ct1Ack true` / `.ekCt1Ack _`,
    and `[]` on all non-allocating branches (`msg.epoch > st.uc.epoch`, `msg.epoch < st.uc.epoch`,
    or non-ack payload). -/
def StatesRecvEkReceivedCt1SampledPreEnv {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .ekReceivedCt1Sampled st =>
    if x.msg.epoch = st.uc.epoch ∧ isEkAckPayload x.msg.payload = true then
      EkReceivedCt1SampledAckPreEnv K st evs
    else
      evs = []
  | _ => evs = []

/-- Exact postcondition envelope for the `.ekReceivedCt1Sampled` arm of `<States>::recv`
    (Block `332`): `FreeOnlyEvs` on `msg.epoch > st.uc.epoch` (state drop),
    `EkReceivedCt1SampledAckPostEnv K st` on same-epoch `.ct1Ack true` / `.ekCt1Ack _`,
    and `[]` on all no-op branches. -/
def StatesRecvEkReceivedCt1SampledPostEnv {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .ekReceivedCt1Sampled st =>
    if x.msg.epoch > st.uc.epoch then
      FreeOnlyEvs evs
    else if x.msg.epoch = st.uc.epoch ∧ isEkAckPayload x.msg.payload = true then
      EkReceivedCt1SampledAckPostEnv K st evs
    else
      evs = []
  | _ => evs = []

abbrev StatesRecvEkReceivedCt1SampledEnv {F : ShaCompress} (K : MlKem) :=
  @StatesRecvEkReceivedCt1SampledPostEnv F K

private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] (hc : c) (t e : α) :
    (if c then t else e) = t := by
  split <;> [rfl; contradiction]

private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] (hc : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  split <;> [contradiction; rfl]

theorem statesRecvEkReceivedCt1SampledPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) :
    ∃ evs, StatesRecvEkReceivedCt1SampledPreEnv K x evs := by
  rcases x with ⟨outA, selfA, msgA, self, msg⟩
  cases self with
  | ekReceivedCt1Sampled st =>
    dsimp only [StatesRecvEkReceivedCt1SampledPreEnv]
    by_cases hack : msg.epoch = st.uc.epoch ∧ isEkAckPayload msg.payload = true
    · obtain ⟨evs, hevs⟩ := ekReceivedCt1SampledAckPreEnv_nonempty K st
      exact ⟨evs, by rw [ite_pos hack]; exact hevs⟩
    · exact ⟨[], by rw [ite_neg hack]⟩
  | _ => exact ⟨[], rfl⟩

theorem statesRecvEkReceivedCt1SampledPostEnv_of_pre {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) {evs : List AllocEvent}
    (h : StatesRecvEkReceivedCt1SampledPreEnv K x evs) :
    StatesRecvEkReceivedCt1SampledPostEnv K x evs := by
  rcases x with ⟨outA, selfA, msgA, self, msg⟩
  cases self with
  | ekReceivedCt1Sampled st =>
    dsimp only [StatesRecvEkReceivedCt1SampledPreEnv] at h
    dsimp only [StatesRecvEkReceivedCt1SampledPostEnv]
    by_cases hgt : msg.epoch > st.uc.epoch
    · rw [ite_pos hgt]
      have hne : msg.epoch ≠ st.uc.epoch := fun heq => by
        rw [heq] at hgt
        exact BitVec.lt_irrefl _ hgt
      rw [ite_neg (fun ha : msg.epoch = st.uc.epoch ∧ _ => hne ha.1)] at h
      subst h
      exact FreeOnlyEvs.nil
    · rw [ite_neg hgt]
      by_cases hack : msg.epoch = st.uc.epoch ∧ isEkAckPayload msg.payload = true
      · rw [ite_pos hack] at h ⊢
        exact Or.inl h
      · rw [ite_neg hack] at h ⊢
        exact h
  | _ => exact h

theorem statesRecvEkReceivedCt1SampledPostEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) :
    ∃ evs, StatesRecvEkReceivedCt1SampledPostEnv K x evs :=
  let ⟨evs, h⟩ := statesRecvEkReceivedCt1SampledPreEnv_nonempty K x
  ⟨evs, statesRecvEkReceivedCt1SampledPostEnv_of_pre K x h⟩

/-! ## 2. `SepWP` / `SepWPp` Sequencing & `withLsCodeRoLoaded` Helpers -/

private theorem seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hent, hq⟩ hclm =>
      SepWP.weaken_pre hent (h2 sm hpc hrun hvm hq hclm))

private theorem sepWPp_seq_vm_lscl_dep [LibsignalPlacement]
    {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post post_panic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeLoaded lsmpl sm.mem →
      SepWPp prog target_pc sm (P_mid sm) post post_panic) :
    SepWPp prog target_pc s P post post_panic :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hvm, hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hq hclm))

theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_spec {α : Type}
    {prog : Program} {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcro.1, hpre0⟩
  exact h.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

/-! ## 3. Same-Epoch Ack Call & Writeback Exit (`+9344 -> s0.x30`) -/

theorem ek_ack_9344_ok_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePreEnv CalleePostEnv : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop}
    {PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 343)
      (withLsCodeLoaded lsmpl
        (ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K
          CalleePreEnv CalleePostEnv)))
    (st_cost : M.σ)
    (s0 s1 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (w : Words66) (sp : SendEkSpills)
    (hcl : LibsignalCodeLoaded lsmpl s1.mem)
    (heq : msg.epoch = st.uc.epoch)
    (hack : isEkAckPayload msg.payload = true)
    (hok : st.recv_ct1_ack K st.uc.epoch = .ok outSt)
    (hfit : FitsEnv M lim st_cost
      (CalleePreEnv ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, st, outSt⟩))
    (hpost_ack : ∀ evs : List AllocEvent,
      CalleePostEnv ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, st, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ evs)
    (hsp0_align : s0.spAligned = true)
    (hpc : s1.pc = lsmpl.base 332 + 9344#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx3 : s1.readReg64 .x3 = w.b0.w3) (hx4 : s1.readReg64 .x4 = w.b1.w5)
    (hx5 : s1.readReg64 .x5 = w.b4.w4) (hx6 : s1.readReg64 .x6 = w.b4.w0)
    (hx7 : s1.readReg64 .x7 = w.b3.w1) (hx10 : s1.readReg64 .x10 = w.b2.w5)
    (hx11 : s1.readReg64 .x11 = w.b4.w1) (hx12 : s1.readReg64 .x12 = w.b1.w8)
    (hx13 : s1.readReg64 .x13 = w.b4.w3) (hx14 : s1.readReg64 .x14 = w.b3.w9)
    (hx15 : s1.readReg64 .x15 = w.b3.w5) (hx17 : s1.readReg64 .x17 = w.b1.w3)
    (hx18 : s1.readReg64 .x18 = w.b2.w7) (hx19 : s1.readReg64 .x19 = outA)
    (hx20 : s1.readReg64 .x20 = w.b1.w6) (hx21 : s1.readReg64 .x21 = w.b0.w7)
    (hx22 : s1.readReg64 .x22 = w.b0.w4) (hx23 : s1.readReg64 .x23 = w.b5.w2)
    (hx25 : s1.readReg64 .x25 = st.uc.epoch) (hx26 : s1.readReg64 .x26 = w.b1.w0)
    (hx27 : s1.readReg64 .x27 = w.b1.w2) (hx28 : s1.readReg64 .x28 = w.w65)
    (hx30 : s1.readReg64 .x30 = w.b2.w3) (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      ((selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A.repAlloc dst st)
          (wordsBytes (words66List w)) ∗
        memRegion (selfA + 536#64) 392 ∗ sendEkSpillsAt (s0.sp - 4240#64) (ekLoadSpills sp w) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (((s0.sp - 4240#64) + 2752#64) ↦₁₂₈ w.q60) ∗ (((s0.sp - 4240#64) + 3856#64) ↦₁₂₈ w.q63) ∗
        ekUnusedRestAt (s0.sp - 4240#64) ∗
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
         A.pool lim st_cost s1 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0))
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA
              ((States.ekReceivedCt1Sampled st).recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine seq_vm_lscl hcl
    (ArmEkReceivedCt1SampledPlacedBudgetAux.ek_step_9344_to_call_entry_placed
      (A := A.repAlloc) s0 s1 outA selfA st w sp
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
       A.pool lim st_cost s1 ∗ stackAt fsp statesRecvCalleeStackX ∗
       memRegion (fsp + 576#64) 376 ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp
      hx3 hx4 hx5 hx6 hx7 hx10 hx11 hx12 hx13 hx14 hx15 hx17 hx18 hx19 hx20 hx21 hx22 hx23
      hx25 hx26 hx27 hx28 hx30 htr)
    ?_
  intro s2 hpc2 hrun2 hvm12 ⟨hsp2, h0_2, h1_2, h2_2, h19_2, h30_2, htr2⟩ hcl2
  let F_call : SepProp :=
    messageAt spqrPolyApi msgA msg ∗
    statesRecvJumpTablePlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
    memRegion outA v1RecvSize ∗
    memRegion selfA chunkedStatesSize ∗
    memRegion (fsp + 1432#64) 424 ∗
    memRegion (fsp + 2384#64) 352 ∗
    memRegion (fsp - 19552#64) 1920 ∗
    sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
    memRegion (fsp + 576#64) 376 ∗
    sendEkUnusedAt fsp ∗
    statesRecvSavedCells s0
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    (memRegion (fsp + 976#64) chunkedCt2SampledSize ∗
     chunkedEkReceivedCt1SampledAt A.repAlloc (fsp + 1856#64) st ∗
     unchunkedSendCt2PlacedRoAt ∗
     A.pool lim st_cost s2 ∗
     stackAt fsp ekReceivedCt1SampledRecvCt1AckStack) ∗ F_call by
      dsimp only [statesRecvRoPlacedAt, F_call, fsp]
      rw [← A.pool_of_vmPreserved hvm12,
          stackAt_statesRecvCallee_eq_ekReceivedCt1SampledRecvCt1Ack (s0.sp - 4240#64)]
      sep_ac_rfl)) ?_
  have hsp2_align : s2.spAligned = true := by
    rw [State.spAligned, hsp2]; exact hfsp_align
  refine SepWP.call_subroutine_frame hcall
    (x := (⟨fsp + 976#64, fsp + 1856#64, st, outSt⟩, st_cost))
    (F := F_call)
    hpc2 hrun2 hsp2_align h30_2 ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeLoaded, ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv]
    rw [hsp2]
    have hm' : s2.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s2.mem⌝ ∗
        ⌜s2.readReg64 .x0 = fsp + 976#64 ∧
          s2.readReg64 .x1 = fsp + 1856#64 ∧
          s2.readReg64 .x2 = st.uc.epoch ∧
          st.recv_ct1_ack K st.uc.epoch = .ok outSt ∧
          FitsEnv M lim st_cost (CalleePreEnv ⟨fsp + 976#64, fsp + 1856#64, st, outSt⟩) ∧
          LsRetAddr624 (s2.readReg64 .lr)⌝ ∗
        ((memRegion (fsp + 976#64) chunkedCt2SampledSize ∗
          chunkedEkReceivedCt1SampledAt A.repAlloc (fsp + 1856#64) st ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim st_cost s2 ∗
          stackAt fsp ekReceivedCt1SampledRecvCt1AckStack) ∗ F_call ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl2, by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨h0_2, h1_2, h2_2, hok, hfit, by
          dsimp only [Reg.lr]
          rw [h30_2]
          exact lsRetAddr624_base_add 332 9788#64 (by decide) (by decide)⟩,
          by simpa [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · intro _ _ _ hp
    unfold withLsCodeLoaded ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv at hp
    dsimp only at hp
    exact ((satisfies_pure_sepConj _ _ _).mp hp).1
  · intro _ _ _ _ he
    unfold withLsCodeLoaded ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv at he
    dsimp only at he
    exact ((satisfies_pure_sepConj _ _ _).mp he).1
  · intro s3 hpc3 hrun3 hsp3 hcs3
    dsimp only [withLsCodeLoaded, ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv]
    rw [hsp2, sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr_s3, hevs⟩ => ?_
    have hsp3' : s3.sp = s0.sp - 4240#64 := hsp3.trans hsp2
    have h19_3 : s3.readReg64 .x19 = outA := hcs3.1.trans h19_2
    have htr3 : TraceCalleeSaved s3 s0 :=
      ⟨htr_s3.trans htr2.1, hcs3.2.2.2.2.2.2.2.2.2.2.2.trans htr2.2⟩
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
       A.pool lim (M.stepEvents evs st_cost) s3) ∗
      memRegion outA v1RecvSize ∗
      memRegion selfA chunkedStatesSize ∗
      chunkedCt2SampledAt A.repAlloc (fsp + 976#64) outSt ∗
      memRegion (fsp + 1432#64) 424 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
      memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 1856#64) 880 ∗
      sendEkUnusedAt fsp ∗
      statesRecvSavedCells s0 by
        dsimp only [statesRecvRoPlacedAt, chunkedEkReceivedCt1SampledSize, F_call, fsp]
        rw [stackAt_statesRecvCallee_eq_ekReceivedCt1SampledRecvCt1Ack (s0.sp - 4240#64),
            memRegion_880_split_528_352 (s0.sp - 4240#64)]
        sep_ac_rfl)) ?_
    have hexit := ArmEkReceivedCt1SampledPlacedBudgetAux.ek_ack_9788_ret_placed
      (A := A.repAlloc) hmemcpy s0 s3 outA selfA outSt (ekLoadSpills sp w)
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
       A.pool lim (M.stepEvents evs st_cost) s3)
      hsp0_align hpc3 hrun3 hsp3' h19_3 htr3
    have hrecv := states_recv_ekReceivedCt1Sampled_eq_ack_ok K st outSt msg heq hack hok
    refine SepWP.mono hexit ?_
    intro sf Pf _ _ ⟨hvm_ret, hPf, hsp_sf, hcs_sf, htr_sf⟩
    refine ⟨⟨evs, hpost_ack evs hevs, Entails.trans hPf ?_⟩, hsp_sf, hcs_sf, htr_sf⟩
    rw [hrecv, A.pool_of_vmPreserved hvm_ret]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro _ _ _ ho
    unfold withLsCodeLoaded ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv at ho
    dsimp only at ho
    exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

/-! ## 4. Top-Level Budget-Threaded `.ekReceivedCt1Sampled` Arm Contracts (Block `332`) -/

/-- Envelope-parametric budget-threaded relocatable `.ekReceivedCt1Sampled` variant contract
    under `withLsCodeLoaded`. -/
theorem states_recv_ekReceivedCt1Sampled_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPreAck : ∀ (outA selfA msgA fsp : BitVec 64)
      (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (st_cost : M.σ),
      msg.epoch = st.uc.epoch →
      isEkAckPayload msg.payload = true →
      st.recv_ct1_ack K st.uc.epoch = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ekReceivedCt1SampledRecvCt1AckPre ⟨fsp + 976#64, fsp + 1856#64, st, outSt⟩))
    (hPostGt : ∀ (outA selfA msgA : BitVec 64) (evs : List AllocEvent),
      msg.epoch > st.uc.epoch →
      FreeOnlyEvs evs →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ evs)
    (hPostLt : ∀ (outA selfA msgA : BitVec 64),
      msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ [])
    (hPostAck : ∀ (outA selfA msgA fsp : BitVec 64)
      (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (evs : List AllocEvent),
      msg.epoch = st.uc.epoch →
      isEkAckPayload msg.payload = true →
      st.recv_ct1_ack K st.uc.epoch = .ok outSt →
      envs.ekReceivedCt1SampledRecvCt1AckPost ⟨fsp + 976#64, fsp + 1856#64, st, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ evs)
    (hPostNoAck : ∀ (outA selfA msgA : BitVec 64),
      msg.epoch = st.uc.epoch →
      isEkAckPayload msg.payload = false →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
          (.ekReceivedCt1Sampled st) msg PreEnv PostEnv)) := by
  have hmemcpy := hC.hmemcpy_sat
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv, hfit0, _hlr_ls⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗
       chunkedStatesAt A.repAlloc selfA (.ekReceivedCt1Sampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue_pool_placed (M := M) (A := A) (lim := lim) (ext := ext)
    st_cost s0
    (memRegion outA v1RecvSize ∗
     chunkedStatesAt A.repAlloc selfA (.ekReceivedCt1Sampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
    hsp0_align hpc0 hrun0
  refine sepWPp_seq_vm_lscl_dep hcl0 hpro ?_
  intro s1 hpc1 hrun1 _hvm01 ⟨_hacp01, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcl1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := ArmEkReceivedCt1SampledStepsPlacedBudget.states_recv_dispatch_ekReceivedCt1Sampled_placed
    (ext := ext) s1 (s0.sp - 4240#64) selfA
    (chunkedEkReceivedCt1SampledAt A.repAlloc (selfA + 8#64) st ∗
     memRegion (selfA + 536#64) 392 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     A.pool lim st_cost s1 ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_vm_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hvm12
    ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcl2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  set fsp := s0.sp - 4240#64
  have hpre_split :
      (selfA ↦₆₄ 10#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedEkReceivedCt1SampledAt A.repAlloc (selfA + 8#64) st ∗
       memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       A.pool lim st_cost s1 ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words66, ∃∗ sp : SendEkSpills, ∃∗ qac0 : BitVec 128, ∃∗ qf10 : BitVec 128,
        ⌜w.w65 = st.uc.epoch⌝ ∗
        (words66At (selfA + 8#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
         sendEkSpillsAt fsp sp ∗ ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗
         ((selfA ↦₆₄ 10#64) ∗
          relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A.repAlloc dst st)
            (wordsBytes (words66List w)) ∗
          memRegion (selfA + 536#64) 392 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
          statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
          stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          ekUnusedRestAt fsp ∗ statesRecvSavedCells s0))) := by
    unfold messageAt
    rw [← A.pool_of_vmPreserved hvm12]
    have hex66 := chunkedEkReceivedCt1SampledAt_extract66 A.repAlloc (selfA + 8#64) st
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills, ∃∗ qac0 : BitVec 128, ∃∗ qf10 : BitVec 128,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗ ekUnusedRestAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Arm64.Entails.sepExists_elim; intro sp
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sendEkUnusedAt_split_ek fsp))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply Arm64.Entails.sepExists_elim; intro qac0
      apply Arm64.Entails.sepExists_elim; intro qf10
      exact Entails.sepExists_right sp (Entails.sepExists_right qac0
        (Entails.sepExists_right qf10 (Entails.of_eq (by sep_ac_rfl))))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedEkReceivedCt1SampledAt A.repAlloc (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      ((selfA ↦₆₄ 10#64) ∗ statesRecvRoPlacedAt ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗
       ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
       A.pool lim st_cost s2 ∗ stackAt fsp statesRecvCalleeStackX ∗
       statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hex66 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Arm64.Entails.sepExists_elim; intro sp
    apply Arm64.Entails.sepExists_elim; intro qac0
    apply Arm64.Entails.sepExists_elim; intro qf10
    apply Arm64.Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp
      (Entails.sepExists_right qac0 (Entails.sepExists_right qf10 (Entails.of_eq (by sep_ac_rfl)))))
  refine SepWPp.weaken_pre hpre_split ?_
  apply sepWPp_intro_ex hrun2; intro w
  apply sepWPp_intro_ex hrun2; intro sp
  apply sepWPp_intro_ex hrun2; intro qac0
  apply sepWPp_intro_ex hrun2; intro qf10
  apply SepWPp.pure_left; intro hw65
  refine sepWPp_seq_vm_lscl hcl2
    (ArmEkReceivedCt1SampledPlacedBudgetAux.ek_step_3392_3732_placed
      (ext := ext) s2 fsp outA selfA msgA msg.epoch w sp qac0 qf10
      ((selfA ↦₆₄ 10#64) ∗
       relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A.repAlloc dst st)
         (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
       ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s3 hpc3 hrun3 hvm23 ⟨hsp3, h3_0, h3_1, h3_3, h3_4, h3_5, h3_6, h3_7, h3_10, h3_11,
    h3_12, h3_13, h3_14, h3_15, h3_17, h3_18, h3_19, h3_20, h3_21, h3_22, h3_23,
    h3_24, h3_25, h3_26, h3_27, h3_28, h3_30, h3_8, h3_z, htr3⟩ hcl3
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr20
  rw [hw65] at h3_8 h3_z
  by_cases hgt : msg.epoch > st.uc.epoch
  · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 1#32 := ekCmpW8_of_gt hgt
    rw [hcmp] at h3_8 h3_z
    have hz_f : s3.pstate.z = false := h3_z
    have hrecv := states_recv_ekReceivedCt1Sampled_gt K st msg hgt
    have hexit := ArmEkReceivedCt1SampledPlacedBudgetAux.ek_gt_3732_ret_placed
      hC.hdealloc_sat st_cost s0 s3 outA selfA msg.epoch st
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      hcl3 hsp0_align hpc3 hrun3 hsp3 hz_f h3_8 h3_0 h3_19 h3_25 htr30
    refine sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      s0 s3 outA selfA msgA (.ekReceivedCt1Sampled st) msg st_cost _ R ?_
    refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
    · have hself := selfA_recompose_528 A.repAlloc selfA st w
      have hstk := ek_frame_entails_memRegion_4144 fsp (ekLoadSpills sp w) w.q60 w.q63
      unfold messageAt
      rw [← A.pool_of_vmPreserved hvm23]
      refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 10#64) ∗
         (words66At (selfA + 8#64) w ∗
          relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A.repAlloc dst st)
            (wordsBytes (words66List w))) ∗
         memRegion (selfA + 536#64) 392) ∗
        (sendEkSpillsAt fsp (ekLoadSpills sp w) ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ ekUnusedRestAt fsp) ∗
        (((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
         statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s3 ∗
         stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hself (sepConj_mono_left hstk))
        (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl))
    · intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, _hacp_sf, hcs_sf, htr_sf⟩
      refine ⟨⟨evs, hPostGt outA selfA msgA evs hgt hevs, Entails.trans hPf ?_⟩,
        hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]
      exact Entails.of_eq (by sep_ac_rfl)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 255#32 := ekCmpW8_of_lt hlt
      rw [hcmp] at h3_8 h3_z
      have hz_f : s3.pstate.z = false := h3_z
      have hrecv := states_recv_ekReceivedCt1Sampled_lt K st msg hlt
      refine sepWPp_seq_vm_clean
        (ArmEkReceivedCt1SampledStepsPlacedBudget.ek_step_3732_lt_10136_placed (ext := ext)
          s3 fsp _ hpc3 hrun3 hsp3 hz_f h3_8) ?_
      intro s4 hpc4 hrun4 hvm34 ⟨hsp4, h4_1, h4_3, h4_4, h4_5, h4_6, h4_7, h4_10, h4_11,
        h4_12, h4_13, h4_14, h4_15, h4_17, h4_18, h4_19, h4_20, h4_21, h4_22, h4_23,
        h4_26, h4_27, _, h4_30, htr4⟩
      have hexit := ArmEkReceivedCt1SampledPlacedBudgetAux.ek_noop_10136_ret_placed
        (A := A.repAlloc) hmemcpy s0 s4 outA selfA st w sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s4)
        hsp0_align hpc4 hrun4 hsp4
        (h4_1.trans h3_1) (h4_3.trans h3_3) (h4_4.trans h3_4) (h4_5.trans h3_5)
        (h4_6.trans h3_6) (h4_7.trans h3_7) (h4_10.trans h3_10) (h4_11.trans h3_11)
        (h4_12.trans h3_12) (h4_13.trans h3_13) (h4_14.trans h3_14) (h4_15.trans h3_15)
        (h4_17.trans h3_17) (h4_18.trans h3_18) (h4_19.trans h3_19) (h4_20.trans h3_20)
        (h4_21.trans h3_21) (h4_22.trans h3_22) (h4_23.trans h3_23) (h4_26.trans h3_26)
        (h4_27.trans h3_27) (h4_30.trans h3_30) (htr4.trans htr30)
      refine sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        s0 s4 outA selfA msgA (.ekReceivedCt1Sampled st) msg st_cost _ R ?_
      refine SepWP.weaken_pre
        (Entails.of_eq (by
          unfold messageAt
          dsimp only [fsp]
          rw [← A.pool_of_vmPreserved (hvm23.trans hvm34)]
          sep_ac_rfl))
        (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hvm4f, hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨⟨[], hPostLt outA selfA msgA hlt, Entails.trans hPf ?_⟩, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm4f]
      exact Entails.of_eq (by sep_ac_rfl)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 0#32 := ekCmpW8_of_eq heq
      rw [hcmp] at h3_z
      have hz_t : s3.pstate.z = true := h3_z
      refine sepWPp_seq_vm_lscl hcl3
        (ArmEkReceivedCt1SampledStepsPlacedBudget.ek_step_3732_eq_9064_placed (ext := ext)
          s3 fsp _ hpc3 hrun3 hsp3 hz_t) ?_
      intro s4 hpc4 hrun4 hvm34 ⟨hsp4, h4_1, h4_3, h4_4, h4_5, h4_6, h4_7, h4_10, h4_11,
        h4_12, h4_13, h4_14, h4_15, h4_17, h4_18, h4_19, h4_20, h4_21, h4_22, h4_23,
        h4_24, h4_25, h4_26, h4_27, h4_28, _, h4_30, htr4⟩ hcl4
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      by_cases hack : isEkAckPayload msg.payload = true
      · obtain ⟨outSt, hok⟩ := ekReceivedCt1Sampled_recv_ct1_ack_ok_of_preInv K st hinv
        have hstep_ack := ArmEkReceivedCt1SampledStepsPlacedBudget.ek_step_9064_ack_9344_placed
          (ext := ext) s4 fsp msgA msg.payload
          (words66At (selfA + 8#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
           sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
           ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
           (selfA ↦₆₄ 10#64) ∗
           relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A.repAlloc dst st)
             (wordsBytes (words66List w)) ∗
           memRegion (selfA + 536#64) 392 ∗
           statesRecvJumpTablePlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
           memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
           stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
           ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
          hack hpc4 hrun4 hsp4 (h4_24.trans h3_24)
        refine sepWPp_seq_vm_lscl hcl4
          (SepWP.weaken_pre (Entails.of_eq (by dsimp only [statesRecvRoPlacedAt]; sep_ac_rfl))
            hstep_ack) ?_
        intro s5 hpc5 hrun5 hvm45 ⟨hsp5, _h5_1, h5_3, h5_4, h5_5, h5_6, h5_7, h5_10, h5_11,
          h5_12, h5_13, h5_14, h5_15, h5_17, h5_18, h5_19, h5_20, h5_21, h5_22, h5_23,
          h5_25, h5_26, h5_27, h5_28, _, h5_30, htr5⟩ hcl5
        have h25_eq : s5.readReg64 .x25 = st.uc.epoch := by
          rw [h5_25, h4_25, h3_25, heq]
        have hvm25 : VmPreserved s2 s5 := hvm23.trans (hvm34.trans hvm45)
        refine sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          s0 s5 outA selfA msgA (.ekReceivedCt1Sampled st) msg st_cost _ R ?_
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (ek_ack_9344_ok_ret_placed
            (M := M) (A := A) (lim := lim) (F := F) (K := K)
            (CalleePreEnv := envs.ekReceivedCt1SampledRecvCt1AckPre)
            (CalleePostEnv := envs.ekReceivedCt1SampledRecvCt1AckPost)
            (PostEnv := PostEnv)
            hmemcpy hC.ekReceivedCt1SampledRecvCt1Ack_ok st_cost
            s0 s5 outA selfA msgA st outSt msg w sp
            hcl5 heq hack hok
            (hPreAck outA selfA msgA (s0.sp - 4240#64) outSt st_cost heq hack hok hfit0)
            (fun evs hevs => hPostAck outA selfA msgA (s0.sp - 4240#64) outSt evs heq hack hok hevs)
            hsp0_align hpc5 hrun5 hsp5
            (h5_3.trans (h4_3.trans h3_3)) (h5_4.trans (h4_4.trans h3_4))
            (h5_5.trans (h4_5.trans h3_5)) (h5_6.trans (h4_6.trans h3_6))
            (h5_7.trans (h4_7.trans h3_7)) (h5_10.trans (h4_10.trans h3_10))
            (h5_11.trans (h4_11.trans h3_11)) (h5_12.trans (h4_12.trans h3_12))
            (h5_13.trans (h4_13.trans h3_13)) (h5_14.trans (h4_14.trans h3_14))
            (h5_15.trans (h4_15.trans h3_15)) (h5_17.trans (h4_17.trans h3_17))
            (h5_18.trans (h4_18.trans h3_18)) (h5_19.trans (h4_19.trans h3_19))
            (h5_20.trans (h4_20.trans h3_20)) (h5_21.trans (h4_21.trans h3_21))
            (h5_22.trans (h4_22.trans h3_22)) (h5_23.trans (h4_23.trans h3_23))
            h25_eq (h5_26.trans (h4_26.trans h3_26))
            (h5_27.trans (h4_27.trans h3_27)) (h5_28.trans (h4_28.trans h3_28))
            (h5_30.trans (h4_30.trans h3_30)) (htr5.trans htr40))
        unfold messageAt
        dsimp only [statesRecvRoPlacedAt, fsp]
        rw [← A.pool_of_vmPreserved hvm25]
        sep_ac_rfl
      · have hno : isEkAckPayload msg.payload = false := Bool.eq_false_iff.mpr hack
        have hrecv := states_recv_ekReceivedCt1Sampled_eq_no_ack K st msg heq hno
        have hstep_no := ArmEkReceivedCt1SampledStepsPlacedBudget.ek_step_9064_no_ack_10136_placed
          (ext := ext) s4 fsp msgA msg.payload
          (words66At (selfA + 8#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
           sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
           ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
           (selfA ↦₆₄ 10#64) ∗
           relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A.repAlloc dst st)
             (wordsBytes (words66List w)) ∗
           memRegion (selfA + 536#64) 392 ∗ statesRecvRoPlacedAt ∗
           memRegion outA v1RecvSize ∗ A.pool lim st_cost s2 ∗
           stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
           ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
          hno hpc4 hrun4 hsp4 (h4_24.trans h3_24)
        refine sepWPp_seq_vm_clean
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep_no) ?_
        intro s5 hpc5 hrun5 hvm45 ⟨hsp5, h5_1, h5_3, h5_4, h5_5, h5_6, h5_7, h5_10, h5_11,
          h5_12, h5_13, h5_14, h5_15, h5_17, h5_18, h5_19, h5_20, h5_21, h5_22, h5_23,
          h5_26, h5_27, _, h5_30, htr5⟩
        have hvm25 : VmPreserved s2 s5 := hvm23.trans (hvm34.trans hvm45)
        have hexit := ArmEkReceivedCt1SampledPlacedBudgetAux.ek_noop_10136_ret_placed
          (A := A.repAlloc) hmemcpy s0 s5 outA selfA st w sp
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s5)
          hsp0_align hpc5 hrun5 hsp5
          (h5_1.trans (h4_1.trans h3_1)) (h5_3.trans (h4_3.trans h3_3))
          (h5_4.trans (h4_4.trans h3_4)) (h5_5.trans (h4_5.trans h3_5))
          (h5_6.trans (h4_6.trans h3_6)) (h5_7.trans (h4_7.trans h3_7))
          (h5_10.trans (h4_10.trans h3_10)) (h5_11.trans (h4_11.trans h3_11))
          (h5_12.trans (h4_12.trans h3_12)) (h5_13.trans (h4_13.trans h3_13))
          (h5_14.trans (h4_14.trans h3_14)) (h5_15.trans (h4_15.trans h3_15))
          (h5_17.trans (h4_17.trans h3_17)) (h5_18.trans (h4_18.trans h3_18))
          (h5_19.trans (h4_19.trans h3_19)) (h5_20.trans (h4_20.trans h3_20))
          (h5_21.trans (h4_21.trans h3_21)) (h5_22.trans (h4_22.trans h3_22))
          (h5_23.trans (h4_23.trans h3_23)) (h5_26.trans (h4_26.trans h3_26))
          (h5_27.trans (h4_27.trans h3_27)) (h5_30.trans (h4_30.trans h3_30))
          (htr5.trans htr40)
        refine sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          s0 s5 outA selfA msgA (.ekReceivedCt1Sampled st) msg st_cost _ R ?_
        refine SepWP.weaken_pre
          (Entails.of_eq (by
            unfold messageAt
            dsimp only [fsp]
            rw [← A.pool_of_vmPreserved hvm25]
            sep_ac_rfl))
          (SepWP.mono hexit ?_)
        intro sf Pf _ _ ⟨hvm5f, hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨⟨[], hPostNoAck outA selfA msgA heq hno, Entails.trans hPf ?_⟩,
          hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm5f]
        exact Entails.of_eq (by sep_ac_rfl)

/-- Envelope-parametric budget-threaded relocatable `.ekReceivedCt1Sampled` variant contract
    under `withLsCodeRoLoaded` (ready for `states_recv_placed_ok_ext_of_variants_ofPrePostEnv`). -/
theorem states_recv_ekReceivedCt1Sampled_placed_cro_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPreAck : ∀ (outA selfA msgA fsp : BitVec 64)
      (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (st_cost : M.σ),
      msg.epoch = st.uc.epoch →
      isEkAckPayload msg.payload = true →
      st.recv_ct1_ack K st.uc.epoch = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ekReceivedCt1SampledRecvCt1AckPre ⟨fsp + 976#64, fsp + 1856#64, st, outSt⟩))
    (hPostGt : ∀ (outA selfA msgA : BitVec 64) (evs : List AllocEvent),
      msg.epoch > st.uc.epoch →
      FreeOnlyEvs evs →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ evs)
    (hPostLt : ∀ (outA selfA msgA : BitVec 64),
      msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ [])
    (hPostAck : ∀ (outA selfA msgA fsp : BitVec 64)
      (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (evs : List AllocEvent),
      msg.epoch = st.uc.epoch →
      isEkAckPayload msg.payload = true →
      st.recv_ct1_ack K st.uc.epoch = .ok outSt →
      envs.ekReceivedCt1SampledRecvCt1AckPost ⟨fsp + 976#64, fsp + 1856#64, st, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ evs)
    (hPostNoAck : ∀ (outA selfA msgA : BitVec 64),
      msg.epoch = st.uc.epoch →
      isEkAckPayload msg.payload = false →
      PostEnv ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
          (.ekReceivedCt1Sampled st) msg PreEnv PostEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_spec
    (states_recv_ekReceivedCt1Sampled_placed_ok_ext_ofPrePostEnv A lim F K ext hC st msg
      hPreAck hPostGt hPostLt hPostAck hPostNoAck)

/-- Canonical exact-envelope budget-threaded relocatable `.ekReceivedCt1Sampled` variant contract
    under `withLsCodeLoaded` (`StatesRecvEkReceivedCt1SampledPreEnv` /
    `StatesRecvEkReceivedCt1SampledPostEnv`). -/
theorem states_recv_ekReceivedCt1Sampled_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
          (.ekReceivedCt1Sampled st) msg
          (StatesRecvEkReceivedCt1SampledPreEnv K)
          (StatesRecvEkReceivedCt1SampledPostEnv K))) := by
  refine states_recv_ekReceivedCt1Sampled_placed_ok_ext_ofPrePostEnv A lim F K ext hC st msg
    ?_ ?_ ?_ ?_ ?_
  · intro outA selfA msgA fsp outSt st_cost heq hack _hok hfit evs hevs
    apply hfit evs
    dsimp only [StatesRecvEkReceivedCt1SampledPreEnv]
    rw [ite_pos ⟨heq, hack⟩]
    exact hevs
  · intro outA selfA msgA evs hgt hevs
    dsimp only [StatesRecvEkReceivedCt1SampledPostEnv]
    rw [ite_pos hgt]
    exact hevs
  · intro outA selfA msgA hlt
    dsimp only [StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := fun hgt =>
      BitVec.lt_irrefl _ (BitVec.lt_trans hlt hgt)
    have hne : msg.epoch ≠ st.uc.epoch := fun heq => by
      rw [heq] at hlt
      exact BitVec.lt_irrefl _ hlt
    rw [ite_neg hnotgt,
        ite_neg (fun ha : msg.epoch = st.uc.epoch ∧ _ => hne ha.1)]
  · intro outA selfA msgA fsp outSt evs heq hack _hok hevs
    dsimp only [StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos ⟨heq, hack⟩]
    exact hevs
  · intro outA selfA msgA heq hno
    dsimp only [StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    have hnotack : ¬ (msg.epoch = st.uc.epoch ∧ isEkAckPayload msg.payload = true) := fun ha => by
      rw [hno] at ha
      exact Bool.false_ne_true ha.2
    rw [ite_neg hnotgt, ite_neg hnotack]

/-- Canonical exact-envelope budget-threaded relocatable `.ekReceivedCt1Sampled` variant contract
    under `withLsCodeRoLoaded`. -/
theorem states_recv_ekReceivedCt1Sampled_placed_cro_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
          (.ekReceivedCt1Sampled st) msg
          (StatesRecvEkReceivedCt1SampledPreEnv K)
          (StatesRecvEkReceivedCt1SampledPostEnv K))) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_spec
    (states_recv_ekReceivedCt1Sampled_placed_ok_ext A lim F K ext hC st msg)

/-- Single-envelope (`StatesRecvEkReceivedCt1SampledEnv K`) budget-threaded relocatable
    `.ekReceivedCt1Sampled` variant contract under `withLsCodeLoaded`. -/
theorem states_recv_ekReceivedCt1Sampled_placed_ofEnv_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (statesRecvVariantPlacedSpecOfEnv M A lim F K
          (.ekReceivedCt1Sampled st) msg
          (StatesRecvEkReceivedCt1SampledEnv K))) := by
  refine states_recv_ekReceivedCt1Sampled_placed_ok_ext_ofPrePostEnv A lim F K ext hC st msg
    ?_ ?_ ?_ ?_ ?_
  · intro outA selfA msgA fsp outSt st_cost heq hack _hok hfit evs hevs
    apply hfit evs
    dsimp only [StatesRecvEkReceivedCt1SampledEnv, StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos ⟨heq, hack⟩]
    exact Or.inl hevs
  · intro outA selfA msgA evs hgt hevs
    dsimp only [StatesRecvEkReceivedCt1SampledEnv, StatesRecvEkReceivedCt1SampledPostEnv]
    rw [ite_pos hgt]
    exact hevs
  · intro outA selfA msgA hlt
    dsimp only [StatesRecvEkReceivedCt1SampledEnv, StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := fun hgt =>
      BitVec.lt_irrefl _ (BitVec.lt_trans hlt hgt)
    have hne : msg.epoch ≠ st.uc.epoch := fun heq => by
      rw [heq] at hlt
      exact BitVec.lt_irrefl _ hlt
    rw [ite_neg hnotgt,
        ite_neg (fun ha : msg.epoch = st.uc.epoch ∧ _ => hne ha.1)]
  · intro outA selfA msgA fsp outSt evs heq hack _hok hevs
    dsimp only [StatesRecvEkReceivedCt1SampledEnv, StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    rw [ite_neg hnotgt, ite_pos ⟨heq, hack⟩]
    exact hevs
  · intro outA selfA msgA heq hno
    dsimp only [StatesRecvEkReceivedCt1SampledEnv, StatesRecvEkReceivedCt1SampledPostEnv]
    have hnotgt : ¬ (msg.epoch > st.uc.epoch) := by
      rw [heq]
      exact BitVec.lt_irrefl _
    have hnotack : ¬ (msg.epoch = st.uc.epoch ∧ isEkAckPayload msg.payload = true) := fun ha => by
      rw [hno] at ha
      exact Bool.false_ne_true ha.2
    rw [ite_neg hnotgt, ite_neg hnotack]

/-- Single-envelope (`StatesRecvEkReceivedCt1SampledEnv K`) budget-threaded relocatable
    `.ekReceivedCt1Sampled` variant contract under `withLsCodeRoLoaded`. -/
theorem states_recv_ekReceivedCt1Sampled_placed_ofEnv_cro_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfEnv M A lim F K
          (.ekReceivedCt1Sampled st) msg
          (StatesRecvEkReceivedCt1SampledEnv K))) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_spec
    (states_recv_ekReceivedCt1Sampled_placed_ofEnv_ok_ext A lim F K ext hC st msg)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget
