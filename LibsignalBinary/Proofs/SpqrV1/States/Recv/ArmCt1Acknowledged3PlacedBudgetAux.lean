/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ct1Acknowledged` Arm, Part 3 Aux (Budget-Threaded)

Allocation-event envelopes (`StatesRecvCt1AcknowledgedPreEnv` / `StatesRecvCt1AcknowledgedPostEnv`),
`VmPreserved` `.done` path (`+4468 -> +4924 -> s0.x30`), and budget-threaded Branch C composition
for `.ct1Acknowledged`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
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
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkSlotsEnv addChunkSlotsEnv_nil
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  DecodedMessageEnv decodedMessageEnv_nonempty
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  Ct1AckRecvEkTailPreEnv Ct1AcknowledgedRecvEkChunkPostEnv Ct1AcknowledgedRecvEkChunkPreEnv
  ct1AckRecvEkTailPreEnv_nonempty ct1AcknowledgedRecvEkChunkPlacedSpec
  ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv ct1AcknowledgedRecvEkChunkPreEnv_nonempty
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean seq_vm_cont step_adrp_vm
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv statesRecvVariantPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  lsmpl_base_332_eq
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
  addChunkTotal decodedMessageTotal DecodedMessageEnv Ct1AckRecvEkTailPreEnv
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48
  Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Allocation-Event Envelopes for `.ct1Acknowledged` -/

/-- Extract the concrete `Chunk` from the `.ek` and `.ekCt1Ack` payload arms of `<States>::recv`
    on `.ct1Acknowledged`, and `none` on all other payload variants. -/
def ct1AckPayloadChunk? (p : MessagePayload spqrPolyApi) : Option Chunk :=
  match p with
  | .ek chunk => some chunk
  | .ekCt1Ack chunk => some chunk
  | _ => none

theorem ct1AckPayloadChunk?_eq_none_of_ne {p : MessagePayload spqrPolyApi}
    (hek : ∀ c, p ≠ .ek c) (hekAck : ∀ c, p ≠ .ekCt1Ack c) :
    ct1AckPayloadChunk? p = none := by
  cases p with
  | ek c => exact False.elim (hek c rfl)
  | ekCt1Ack c => exact False.elim (hekAck c rfl)
  | _ => rfl

/-- Exact allocation-phase prefix envelope of `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`)
    on `(st, chunk)`: `add_chunk` on `st.receiving_ek`, followed by `decoded_message`, followed by
    `Ct1AckRecvEkTailPreEnv`. -/
def Ct1AcknowledgedChunkPreEnv {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (evs : List AllocEvent) : Prop :=
  let dec1 := addChunkTotal st.receiving_ek chunk
  SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
    (SeqEnv (DecodedMessageEnv dec1)
      (Ct1AckRecvEkTailPreEnv K st.uc (decodedMessageTotal dec1)))
    evs

/-- Postcondition envelope of `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`) on `(st, chunk)`:
    `Ct1AcknowledgedChunkPreEnv K st chunk` followed by `FreeOnlyEvs`. -/
def Ct1AcknowledgedChunkPostEnv {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (evs : List AllocEvent) : Prop :=
  SeqEnv (Ct1AcknowledgedChunkPreEnv K st chunk) FreeOnlyEvs evs

abbrev Ct1AcknowledgedChunkEnv {F : ShaCompress} (K : MlKem) :=
  @Ct1AcknowledgedChunkPostEnv F K

theorem ct1AcknowledgedChunkPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) :
    ∃ evs, Ct1AcknowledgedChunkPreEnv K st chunk evs :=
  ct1AcknowledgedRecvEkChunkPreEnv_nonempty K
    ⟨0#64, 0#64, 0#64, st, chunk, .error .erroneousDataReceived⟩

theorem ct1AcknowledgedChunkPostEnv_nonempty {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) :
    ∃ evs, Ct1AcknowledgedChunkPostEnv K st chunk evs :=
  let ⟨evs, h⟩ := ct1AcknowledgedChunkPreEnv_nonempty K st chunk
  ⟨evs, Or.inl h⟩

/-- Exact allocation-phase prefix envelope for the `.ct1Acknowledged` arm of `<States>::recv`
    (Block `332`): `Ct1AcknowledgedChunkPreEnv K st chunk` on same-epoch `.ek chunk` /
    `.ekCt1Ack chunk`, and `[]` on all non-allocating branches (`msg.epoch > st.uc.epoch`,
    `msg.epoch < st.uc.epoch`, or non-ek payload). -/
def StatesRecvCt1AcknowledgedPreEnv {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .ct1Acknowledged st =>
    if x.msg.epoch = st.uc.epoch then
      match ct1AckPayloadChunk? x.msg.payload with
      | some chunk => Ct1AcknowledgedChunkPreEnv K st chunk evs
      | none => evs = []
    else
      evs = []
  | _ => evs = []

/-- Exact postcondition envelope for the `.ct1Acknowledged` arm of `<States>::recv`
    (Block `332`): `FreeOnlyEvs` on `msg.epoch > st.uc.epoch` (state drop),
    `Ct1AcknowledgedChunkPostEnv K st chunk` on same-epoch `.ek chunk` / `.ekCt1Ack chunk`,
    and `[]` on all no-op branches. -/
def StatesRecvCt1AcknowledgedPostEnv {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .ct1Acknowledged st =>
    if x.msg.epoch > st.uc.epoch then
      FreeOnlyEvs evs
    else if x.msg.epoch = st.uc.epoch then
      match ct1AckPayloadChunk? x.msg.payload with
      | some chunk => Ct1AcknowledgedChunkPostEnv K st chunk evs
      | none => evs = []
    else
      evs = []
  | _ => evs = []

abbrev StatesRecvCt1AcknowledgedEnv {F : ShaCompress} (K : MlKem) :=
  @StatesRecvCt1AcknowledgedPostEnv F K

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

theorem statesRecvCt1AcknowledgedPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) :
    ∃ evs, StatesRecvCt1AcknowledgedPreEnv K x evs := by
  rcases x with ⟨outA, selfA, msgA, self, msg⟩
  unfold StatesRecvCt1AcknowledgedPreEnv
  cases self <;> dsimp only
  all_goals try exact ⟨[], rfl⟩
  rename_i st
  by_cases heq : msg.epoch = st.uc.epoch
  · cases ct1AckPayloadChunk? msg.payload with
    | some chunk =>
      obtain ⟨evs, hevs⟩ := ct1AcknowledgedChunkPreEnv_nonempty K st chunk
      refine ⟨evs, ?_⟩
      rw [ite_pos heq]
      exact hevs
    | none =>
      refine ⟨[], ?_⟩
      rw [ite_pos heq]
  · refine ⟨[], ?_⟩
    rw [ite_neg heq]

theorem statesRecvCt1AcknowledgedPostEnv_of_pre {F : ShaCompress} (K : MlKem)
    {x : StatesRecvGhost F} {evs : List AllocEvent}
    (h : StatesRecvCt1AcknowledgedPreEnv K x evs) :
    StatesRecvCt1AcknowledgedPostEnv K x evs := by
  rcases x with ⟨outA, selfA, msgA, self, msg⟩
  unfold StatesRecvCt1AcknowledgedPreEnv at h
  unfold StatesRecvCt1AcknowledgedPostEnv
  cases self <;> dsimp only at h ⊢
  all_goals try exact h
  rename_i st
  by_cases hgt : msg.epoch > st.uc.epoch
  · have hne : msg.epoch ≠ st.uc.epoch := fun heq => by
      rw [heq] at hgt; exact BitVec.lt_irrefl _ hgt
    rw [ite_neg hne] at h
    rw [ite_pos hgt, h]
    exact FreeOnlyEvs.nil
  · rw [ite_neg hgt]
    by_cases heq : msg.epoch = st.uc.epoch
    · rw [ite_pos heq] at h ⊢
      cases hch : ct1AckPayloadChunk? msg.payload with
      | some chunk =>
        rw [hch] at h
        exact Or.inl h
      | none =>
        rw [hch] at h
        exact h
    · rw [ite_neg heq] at h ⊢
      exact h

theorem statesRecvCt1AcknowledgedPostEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) :
    ∃ evs, StatesRecvCt1AcknowledgedPostEnv K x evs :=
  let ⟨evs, h⟩ := statesRecvCt1AcknowledgedPreEnv_nonempty K x
  ⟨evs, statesRecvCt1AcknowledgedPostEnv_of_pre K h⟩

/-! ## 2. `VmPreserved`-Strengthened `.done` Path (`+4468 -> +4924 -> s0.x30`) -/

theorem sepWPp_seq_vm_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hvm hQ hcro'))))

theorem sepWPp_seq_vm_lscro_dep [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp}
    {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm (P_mid sm) post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hvm hQ hcro'))))

local elab "by_vm_steps_nest " tac:Lean.Parser.Tactic.tacticSeq : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
    let rem ← Lean.Elab.Tactic.getGoals
    unless rem.isEmpty do
      Lean.Meta.throwTacticEx `by_vm_steps_nest g m!"inner tactic left {rem.length} unsolved goal(s)"
    Lean.Elab.Tactic.setGoals savedGoals.tail!
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.isAppOfArity ``Arm64.Program.withSvc 2 then some sub
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2

private abbrev ct1AckDoneAdrpOff : BitVec 64 := 18152#64
private abbrev ct1AckDonePostAdrpOff : BitVec 64 := 18156#64

set_option maxHeartbeats 2400000 in
theorem ct1Ack_step_4468_done_4924_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp d58 d59 dw62 dw65 we50 : BitVec 64)
    (dq60 dq63 qe40 qe60 : BitVec 128)
    (w : Words57) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 4468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = fsp + 1856#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4924#64) s
      (((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
       ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
       ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
       ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗
       sendEkSpillsAt fsp sp ∗
       ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗ ((fsp + 3680#64) ↦₁₂₈ qe60) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
          ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
          ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
          ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗
          sendEkSpillsAt fsp (ct1AckSpillsDone4924 sp w d58 d59 dw62) ∗
          ((fsp + 3648#64) ↦₁₂₈ dq63) ∗ ((fsp + 3664#64) ↦₆₄ dw65) ∗ ((fsp + 3680#64) ↦₁₂₈ dq60) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = w.w55 ∧ sm.readReg64 .x1 = w.b0.w0 ∧
        sm.readReg64 .x2 = w.b1.w2 ∧ sm.readReg64 .x3 = w.b2.w9 ∧
        sm.readReg64 .x4 = w.b4.w9 ∧ sm.readReg64 .x5 = w.b4.w8 ∧
        sm.readReg64 .x6 = w.w50 ∧ sm.readReg64 .x7 = w.b1.w9 ∧
        sm.readReg64 .x10 = w.b1.w6 ∧ sm.readReg64 .x11 = w.w54 ∧
        sm.readReg64 .x12 = w.b4.w0 ∧ sm.readReg64 .x13 = w.w51 ∧
        sm.readReg64 .x15 = w.b2.w7 ∧ sm.readReg64 .x16 = w.b4.w7 ∧
        sm.readReg64 .x17 = w.b4.w5 ∧ sm.readReg64 .x18 = w.w53 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x22 = w.w52 ∧
        sm.readReg64 .x24 = w.b3.w1 ∧ sm.readReg64 .x25 = w.b3.w9 ∧
        sm.readReg64 .x26 = w.b0.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = w.b3.w8 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_cont (mid := (blkPl_332).base + ct1AckDoneAdrpOff) ?_
  dsimp only [ct1AckDoneAdrpOff]
  by_vm_steps_nest (
    wp_simp_pre [words57At, sendEkSpillsAt, ct1AckSpillsDone4924, words10At, pointsTo128, noneCap,
      bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_steps 200
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
    refine step_adrp_vm (rd := 8#5)
      (v := Arm64.Obj.pageOf (blkPl_332.ρ "_RNvCs4Dv7yoBiUx4_3log20MAX_LOG_LEVEL_FILTER"))
      (next_pc := (blkPl_332).base + ct1AckDonePostAdrpOff) hvmm ?_ ?_
    · apply blkPC_332_pairStep_0x46e8
      · rfl
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm, hrun]
    · dsimp only [ct1AckDonePostAdrpOff]
      by_vm_steps_nest (
        wp_steps 200
        simp only [words57At, sendEkSpillsAt, ct1AckSpillsDone4924, words10At, pointsTo128, noneCap,
          bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
        wp_done
      )
  )

theorem ct1Ack_done_4468_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = lsmpl.base 332 + 4468#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        ct1AcknowledgedRecvEkChunkResAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.ok (.done outSt)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ (P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (ct1Ack_done_1856_split (A := A) (F := F) fsp outSt) (by sep_focus) ?_
  wp_pull_exists; rename_i w d58 d59 dq60 dw62 dq63 dw65
  refine SepWP.fold (sendEkUnusedAt_split_e40 fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i qe40 we50 qe60
  set sp1 := ct1AckSpillsDone4924 sp w d58 d59 dw62
  refine seq_vm_clean (mid := lsmpl.base 332 + 4924#64)
    (P_mid := (P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.w55 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b1.w2 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.w50 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.w54 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.w51 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.w53 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.w52 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b3.w8 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4468_done_4924_placed (ext := ext) s1 fsp d58 d59 dw62 dw65 we50
      dq60 dq63 qe40 qe60 w sp
      (P_rest ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
       memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx20
    refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep1 ?_)
    · dsimp only [unchunkedSendCt2PlacedRoAt]; sep_ac_rfl
    · intro s2 Pm _ _ ⟨hvm1, hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
        h2_24, h2_25, h2_26, _, h2_30, htr2⟩
      refine ⟨hvm1, Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
        h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
      have h880 := ct1Ack_done_1856_rejoin_880 fsp d58 d59 dw62 dw65 dq60 dq63 w
      have hunused := ct1AckUnusedRest_entails_sendEkUnusedAt fsp dq63 dw65 dq60
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
         ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
         ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
         ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗ memRegion (fsp + 2384#64) 352) ∗
        (((fsp + 3648#64) ↦₁₂₈ dq63) ∗ ((fsp + 3664#64) ↦₆₄ dw65) ∗
         ((fsp + 3680#64) ↦₁₂₈ dq60) ∗ ct1AckUnusedRestAt fsp) ∗
        ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗ statesRecvSavedCells s0) by
          dsimp only [unchunkedSendCt2PlacedRoAt, sp1]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono h880 (sepConj_mono_left hunused))
        (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hvm1 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine seq_vm_clean (mid := lsmpl.base 332 + 18996#64)
      (P_mid := ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
            b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
            q60 := sp.q3c0, w62 := dw62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ArmCt1Acknowledged2PlacedBudget.ct1Ack_step_4924_18996_placed (ext := ext) s2 fsp sp1
        ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hvm2, hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_done s2 s3 sp w d58 d59 dw62
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨hvm2, Entails.trans hPm (Entails.of_eq (by dsimp only [sp2]; sep_ac_rfl)),
        hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 hvm2 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed
        hmemcpy_sat (Relocatable.of_memRegion 376) s0 s3 outA sp2
        ((P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)))
        hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hvm3, hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨hvm1.trans (hvm2.trans hvm3), Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 12#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ek_ack_out_entails_resultV1RecvAt A (F := F) outA outSt w
        w.b1.w2 d58 w.b3.w8 sp.q3c0 dw62 (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        (P_rest ∗ unchunkedSendCt2PlacedRoAt) ∗ ((outA ↦₆₄ 12#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
             b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
             q60 := sp.q3c0, w62 := dw62 } ∗
         memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_right (sepConj_mono_left hout)) (Entails.of_eq (by sep_ac_rfl))

theorem ct1Ack_step_608_632_words66_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep : BitVec 64) (w : Words66) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 632#64) s
      (words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg_ep) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg_ep) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = w.b1.w5 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.b1.w5)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.b1.w5) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  have h1056 : (fsp + 976#64) + 80#64 = fsp + 1056#64 := by bv_omega
  have hstep := ArmCt1Acknowledged1PlacedBudget.ct1Ack_step_608_632_placed (ext := ext) s fsp out selfA msgA msg_ep w.b1
    (words10At (fsp + 976#64) w.b0 ∗
     words10At ((fsp + 976#64) + 160#64) w.b2 ∗
     words10At ((fsp + 976#64) + 240#64) w.b3 ∗
     words10At ((fsp + 976#64) + 320#64) w.b4 ∗
     words10At ((fsp + 976#64) + 400#64) w.b5 ∗
     (((fsp + 976#64) + 480#64) ↦₁₂₈ w.q60) ∗
     (((fsp + 976#64) + 496#64) ↦₆₄ w.w62) ∗
     (((fsp + 976#64) + 504#64) ↦₁₂₈ w.q63) ∗
     (((fsp + 976#64) + 520#64) ↦₆₄ w.w65) ∗
     Frame)
    hfsp_align hpc hrun hsp hx19 hx20 hx24
  refine SepWP.weaken_pre ?_ (SepWP.mono hstep ?_)
  · dsimp only [words66At]; rw [h1056]; exact Entails.of_eq (by sep_ac_rfl)
  · intro sm Pm _ _ ⟨hvm, hPm, hrest⟩
    refine ⟨hvm, Entails.trans hPm ?_, hrest⟩
    dsimp only [words66At]; rw [h1056]; exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Budget-Threaded Branch C Composition (`+4448 -> BL recv_ek_chunk -> s0.x30`) -/

theorem ct1Ack_ek_4448_ret_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePreEnv CalleePostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl
        (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K CalleePreEnv CalleePostEnv)))
    (st_cost : M.σ)
    (s0 s4 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words66) (sp : SendEkSpills) (P_msg_rest R : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s4.mem)
    (hlen : st.receiving_ek.pts.length = 16)
    (hinv : statesRecvPreInv (F := F) (.ct1Acknowledged st))
    (hfit_callee : ∀ res, st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      FitsEnv M lim st_cost
        (CalleePreEnv ⟨(s0.sp - 4240#64) + 1856#64, selfA + 8#64, msgA + 10#64, st, chunk, res⟩))
    (hpost_callee : ∀ res evs, st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      CalleePostEnv ⟨(s0.sp - 4240#64) + 1856#64, selfA + 8#64, msgA + 10#64, st, chunk, res⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ evs)
    (hrecv_eq : ∀ res, st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res)
    (hmsg_recomp : chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ⊢ messageAt spqrPolyApi msgA msg)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 332 + 4448#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 4240#64)
    (hx2_4 : s4.readReg64 .x2 = st.uc.epoch)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (hx20_4 : s4.readReg64 .x20 = selfA)
    (hx24_4 : s4.readReg64 .x24 = msgA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s4
      (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
       (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       words66At ((s0.sp - 4240#64) + 976#64) w ∗ memRegion ((s0.sp - 4240#64) + 1504#64) 352 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s4 ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
       sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
       statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
                (.ct1Acknowledged st) msg PreEnv PostEnv)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
                (.ct1Acknowledged st) msg PreEnv PostEnv)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  set fsp := s0.sp - 4240#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  obtain ⟨res, hrecv, herr⟩ :=
    ct1Acknowledged_recv_ek_chunk_cases_of_preInv K st chunk hlen hinv
  have hres_eq : States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res :=
    hrecv_eq res hrecv
  refine sepWPp_seq_vm_lscro hcro
    (ArmCt1Acknowledged2PlacedBudget.ct1Ack_step_4448_call_placed (ext := ext)
      s4 fsp selfA msgA st.uc.epoch _ hpc4 hrun4 hsp4 hx2_4 hx20_4 hx24_4) ?_
  intro s5 hpc5 hrun5 hvm45 ⟨hsp5, hx0_5, hx1_5, hx2_5, hx3_5, hx19_5, hx20_5, _, _, hx30_5, htr5⟩ hcro5
  have hx19_5' : s5.readReg64 .x19 = outA := hx19_5.trans hx19_4
  have htr5' : TraceCalleeSaved s5 s0 := htr5.trans htr4
  have hpre_call :
      chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
      (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
      memRegion (selfA + 536#64) 392 ∗
      words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352 ∗
      statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s4 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗
      statesRecvSavedCells s0 ⊢
      (memRegion (fsp + 1856#64) 528 ∗
       chunkedCt1AcknowledgedAt A.repAlloc (selfA + 8#64) st ∗ chunkAt (msgA + 10#64) chunk ∗
       unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       A.pool lim st_cost s5 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
      (P_msg_rest ∗ statesRecvJumpTablePlacedAt ∗
       memRegion outA v1RecvSize ∗
       (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion (fsp - 19552#64) 336 ∗
       sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) := by
    have hrecomp := recompose66_ct1Acknowledged A.repAlloc (selfA + 8#64) w st
    have h976 := words66At_976_352_entails_memRegion_880 fsp w
    dsimp only [statesRecvRoPlacedAt]
    rw [← A.pool_of_vmPreserved hvm45,
        stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk fsp,
        memRegion_880_split_528_352 fsp]
    refine Entails.trans (Entails.of_eq (show _ =
      ((words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w))) ∗
       (words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352)) ∗
      (memRegion (fsp + 1856#64) 528 ∗ chunkAt (msgA + 10#64) chunk ∗
       unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       A.pool lim st_cost s5 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack ∗
       P_msg_rest ∗ statesRecvJumpTablePlacedAt ∗
       memRegion outA v1RecvSize ∗
       (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion (fsp - 19552#64) 336 ∗
       sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 2384#64) 352 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (sepConj_mono hrecomp h976)) (Entails.of_eq (by sep_ac_rfl))
  refine SepWPp.weaken_pre hpre_call ?_
  refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv)
    s0 s5 outA selfA msgA (.ct1Acknowledged st) msg st_cost _ R ?_
  refine ArmCt1Acknowledged2PlacedBudget.call_ct1AcknowledgedRecvEkChunk_placed_ofPrePostEnv
    hcall st_cost (fsp + 1856#64) (selfA + 8#64) (msgA + 10#64) st chunk res
    hinv.1 hrecv (hfit_callee res hrecv)
    hcro5 hpc5 hrun5 hsp5 hfsp_align hx30_5 htr5' hx0_5 hx1_5 hx2_5 hx3_5 rfl ?_
  intro s6 evs hpc6 hrun6 hsp6 hcs6 htr6 hevs
  have hx19_6 : s6.readReg64 .x19 = outA := hcs6.1.trans hx19_5'
  have hx20_6 : s6.readReg64 .x20 = fsp + 1856#64 := hcs6.2.1.trans hx20_5
  have hself := selfA_11_528_392_entails_memRegion selfA
  have hpost_evs : PostEnv ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ evs :=
    hpost_callee res evs hrecv hevs
  cases res with
  | error err =>
    have he : err = .erroneousDataReceived := herr err rfl
    subst he
    have hret := ArmCt1Acknowledged2PlacedBudget.ct1Ack_err_4468_ret_placed
      (A := A.repAlloc) (F := F) (ext := ext) s0 s6 outA selfA .erroneousDataReceived sp
      (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) s6)
      hsp0_align hpc6 hrun6 hsp6 hx19_6 htr6
    refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
    · refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
        (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
        ((statesRecvJumpTablePlacedAt ∗ unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
         A.pool lim (M.stepEvents evs st_cost) s6 ∗ memRegion outA v1RecvSize ∗
         ct1AcknowledgedRecvEkChunkResAt A.repAlloc (F := F) (fsp + 1856#64) (.error .erroneousDataReceived) ∗
         (memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
         sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
        (Entails.of_eq (by
          rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (s0.sp - 4240#64)]
          dsimp only [statesRecvRoPlacedAt, fsp]; sep_ac_rfl))
    · intro sf Pf _ _ ⟨hvm6f, hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨⟨evs, hpost_evs, Entails.trans hPf ?_⟩, hsp_sf, hcs_sf, htr_sf⟩
      rw [hres_eq, A.pool_of_vmPreserved hvm6f]
      dsimp only [ct1AckRecvChunkToStatesResult]
      exact Entails.of_eq (by sep_ac_rfl)
  | ok chunkRes =>
    cases chunkRes with
    | stillReceiving outSt =>
      have hret := ArmCt1Acknowledged2PlacedBudget.ct1Ack_still_4468_ret_placed
        (A := A.repAlloc) (F := F) hmemcpy_sat s0 s6 outA selfA outSt sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) s6)
        hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 htr6
      refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
          (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
          ((statesRecvJumpTablePlacedAt ∗ unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
           A.pool lim (M.stepEvents evs st_cost) s6 ∗ memRegion outA v1RecvSize ∗
           ct1AcknowledgedRecvEkChunkResAt A.repAlloc (F := F) (fsp + 1856#64) (.ok (.stillReceiving outSt)) ∗
           (memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
           sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
           sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
          (Entails.of_eq (by
            rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (s0.sp - 4240#64)]
            dsimp only [statesRecvRoPlacedAt, fsp]; sep_ac_rfl))
      · intro sf Pf _ _ ⟨hvm6f, hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨⟨evs, hpost_evs, Entails.trans hPf ?_⟩, hsp_sf, hcs_sf, htr_sf⟩
        rw [hres_eq, A.pool_of_vmPreserved hvm6f]
        dsimp only [ct1AckRecvChunkToStatesResult]
        exact Entails.of_eq (by sep_ac_rfl)
    | done outSt =>
      have hret := ct1Ack_done_4468_ret_placed
        (A := A.repAlloc) (F := F) hmemcpy_sat s0 s6 outA selfA outSt sp
        (messageAt spqrPolyApi msgA msg ∗ statesRecvJumpTablePlacedAt ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) s6)
        hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 htr6
      refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
          (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
          ((statesRecvJumpTablePlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) s6) ∗
           unchunkedSendCt2PlacedRoAt ∗
           memRegion outA v1RecvSize ∗
           ct1AcknowledgedRecvEkChunkResAt A.repAlloc (F := F) (fsp + 1856#64) (.ok (.done outSt)) ∗
           (memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack) ∗
           sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
           sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
          (Entails.of_eq (by
            rw [stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (s0.sp - 4240#64)]
            dsimp only [fsp]; sep_ac_rfl))
      · intro sf Pf _ _ ⟨hvm6f, hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨⟨evs, hpost_evs, Entails.trans hPf ?_⟩, hsp_sf, hcs_sf, htr_sf⟩
        rw [hres_eq, A.pool_of_vmPreserved hvm6f]
        dsimp only [ct1AckRecvChunkToStatesResult, statesRecvRoPlacedAt]
        exact Entails.of_eq (by sep_ac_rfl)

theorem ct1Ack_ek_4448_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 349)
      (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec M A lim F K)))
    (st_cost : M.σ)
    (s0 s4 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words66) (sp : SendEkSpills) (P_msg_rest R : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s4.mem)
    (hlen : st.receiving_ek.pts.length = 16)
    (hinv : statesRecvPreInv (F := F) (.ct1Acknowledged st))
    (hfit_callee : FitsEnv M lim st_cost (Ct1AcknowledgedChunkPreEnv K st chunk))
    (hpost_callee : ∀ evs, Ct1AcknowledgedChunkPostEnv K st chunk evs →
      StatesRecvCt1AcknowledgedPostEnv K ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩ evs)
    (hrecv_eq : ∀ res, st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res)
    (hmsg_recomp : chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ⊢ messageAt spqrPolyApi msgA msg)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 332 + 4448#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 4240#64)
    (hx2_4 : s4.readReg64 .x2 = st.uc.epoch)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (hx20_4 : s4.readReg64 .x20 = selfA)
    (hx24_4 : s4.readReg64 .x24 = msgA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s4
      (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
       (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A.repAlloc dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       words66At ((s0.sp - 4240#64) + 976#64) w ∗ memRegion ((s0.sp - 4240#64) + 1504#64) 352 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ A.pool lim st_cost s4 ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
       sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
       statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
                (.ct1Acknowledged st) msg
                (StatesRecvCt1AcknowledgedPreEnv K)
                (StatesRecvCt1AcknowledgedPostEnv K))).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K
                (.ct1Acknowledged st) msg
                (StatesRecvCt1AcknowledgedPreEnv K)
                (StatesRecvCt1AcknowledgedPostEnv K))).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) :=
  ct1Ack_ek_4448_ret_placed_ofPrePostEnv hmemcpy_sat hcall st_cost
    s0 s4 outA selfA msgA st msg chunk w sp P_msg_rest R hcro hlen hinv
    (fun _ _ => hfit_callee)
    (fun _ evs _ hevs => hpost_callee evs hevs)
    hrecv_eq hmsg_recomp hsp0_align hpc4 hrun4 hsp4 hx2_4 hx19_4 hx20_4 hx24_4 htr4

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux
