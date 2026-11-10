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
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.keysSampled` Arm, Part 2 (Budget-Threaded)

Allocator-event envelopes (`KeysSampledArmPreEnv` / `KeysSampledArmPostEnv`), `StatesRecvEnv`
subsumption, budget-threaded `<KeysSampled>::recv_ct1_chunk` (`.ct1`) branch, and top-level
`[LibsignalPlacement]` `.keysSampled` contracts (`+1796`, Block `332`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Unchunked CryptoVerification.SpqrV1.States CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Top CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustAllocEvents rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkSlotEnv AddChunkSlotsEnv addChunkSlotsEnv_nil growOnePtEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv
  keysSampledRecvCt1ChunkSpec keysSampledRecvCt1ChunkSpecOfPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (seq_vm_cont)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs StatesRecvEnv sepWPp_of_statesRecv_exit_placed_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_dispatch_pool_placed states_recv_prologue_pool_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

export LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux (
  addChunkSlotEnv_new_bounded addChunkSlotsEnv_replicate_new_bounded freeOnlyEvs_sub_statesRecvEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

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

private theorem sepWPp_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post onPanic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog target sm (P_mid sm) post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (CryptoVerification.sepWP_seq_lscl hcl
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcl' =>
      SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hvm hQ hcl'))))

/-! ## 1. Arm Envelopes & `StatesRecvEnv` Subsumption -/

theorem encodeBytesEnv_1152_bounded {evs : List AllocEvent} (h : EncodeBytesEnv 1152 evs) :
    SpqrBoundedEvs 16 1152 evs := by
  unfold EncodeBytesEnv at h; subst h
  have hev : encodeBytesAllocEvents 1152 = List.replicate 16 (.alloc 1152) := by decide
  rw [hev]; refine ⟨by decide, fun ev hm => ?_⟩
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hm
  exact ⟨by unfold AllocEvent.withinMaxAlloc; decide, Nat.le_refl 1152,
    (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem seq_addChunk16_encode1152_bounded {evs : List AllocEvent}
    (h : SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) (EncodeBytesEnv 1152) evs) :
    SpqrBoundedEvs 32 1152 evs := by
  rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
  · exact SpqrBoundedEvs.mono (by omega) (by omega)
      (addChunkSlotsEnv_replicate_new_bounded 16 evs h1)
  · exact SpqrBoundedEvs.mono (by omega) (by omega)
      (SpqrBoundedEvs.append (addChunkSlotsEnv_replicate_new_bounded 16 evs₁ h1)
        (encodeBytesEnv_1152_bounded h2))

theorem keysSampledRecvCt1ChunkPreEnv_bounded {F : ShaCompress}
    {y : KeysSampledRecvCt1ChunkGhost F} {evs : List AllocEvent}
    (hek : y.st.uc.ek.length = 1152) (h : KeysSampledRecvCt1ChunkPreEnv y evs) :
    SpqrBoundedEvs 32 1152 evs := by
  unfold KeysSampledRecvCt1ChunkPreEnv at h; rw [hek] at h
  exact seq_addChunk16_encode1152_bounded h

theorem keysSampledRecvCt1ChunkPostEnv_bounded {F : ShaCompress}
    {y : KeysSampledRecvCt1ChunkGhost F} {evs : List AllocEvent}
    (hek : y.st.uc.ek.length = 1152) (h : KeysSampledRecvCt1ChunkPostEnv y evs) :
    SpqrBoundedEvs 32 1152 evs := by
  unfold KeysSampledRecvCt1ChunkPostEnv at h
  rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
  · exact keysSampledRecvCt1ChunkPreEnv_bounded hek h1
  · exact SpqrBoundedEvs.mono (by omega) (by omega)
      (SpqrBoundedEvs.append (keysSampledRecvCt1ChunkPreEnv_bounded hek h1)
        (SpqrBoundedEvs.of_freeOnly h2))

theorem keysSampledRecvCt1ChunkPreEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) {y : KeysSampledRecvCt1ChunkGhost F} {evs : List AllocEvent}
    (h : KeysSampledRecvCt1ChunkPreEnv y evs) (hek : y.st.uc.ek.length = 1152) :
    StatesRecvEnv x evs := by
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  exact SpqrBoundedEvs.mono (by omega) (by omega) (keysSampledRecvCt1ChunkPreEnv_bounded hek h)

theorem keysSampledRecvCt1ChunkPostEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) {y : KeysSampledRecvCt1ChunkGhost F} {evs : List AllocEvent}
    (h : KeysSampledRecvCt1ChunkPostEnv y evs) (hek : y.st.uc.ek.length = 1152) :
    StatesRecvEnv x evs := by
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  exact SpqrBoundedEvs.mono (by omega) (by omega) (keysSampledRecvCt1ChunkPostEnv_bounded hek h)

/-- Allocation-phase prefix envelope for the `.keysSampled` arm of `<States>::recv`. -/
def KeysSampledArmPreEnv {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then evs = []
  else if msg.epoch < st.uc.epoch then evs = []
  else match msg.payload with
    | .ct1 _ =>
        SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
          (EncodeBytesEnv st.uc.ek.length) evs
    | _ => evs = []

/-- Postcondition allocation envelope for the `.keysSampled` arm of `<States>::recv`. -/
def KeysSampledArmPostEnv {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then FreeOnlyEvs evs
  else if msg.epoch < st.uc.epoch then evs = []
  else match msg.payload with
    | .ct1 _ =>
        SeqEnv
          (SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
            (EncodeBytesEnv st.uc.ek.length))
          FreeOnlyEvs evs
    | _ => evs = []

theorem keysSampledArmPreEnv_nil {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    KeysSampledArmPreEnv st msg [] := by
  unfold KeysSampledArmPreEnv; split
  · rfl
  · split
    · rfl
    · cases msg.payload <;>
        first | rfl | exact Or.inl (addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new))

theorem keysSampledArmPostEnv_nil {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    KeysSampledArmPostEnv st msg [] := by
  unfold KeysSampledArmPostEnv; split
  · exact FreeOnlyEvs.nil
  · split
    · rfl
    · cases msg.payload <;>
        first | rfl | exact Or.inl (Or.inl (addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new)))

theorem keysSampledArmPreEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs, KeysSampledArmPreEnv st msg evs := ⟨[], keysSampledArmPreEnv_nil st msg⟩

theorem keysSampledArmPostEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs, KeysSampledArmPostEnv st msg evs := ⟨[], keysSampledArmPostEnv_nil st msg⟩

theorem keysSampledArmPreEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hek : st.uc.ek.length = 1152)
    {evs : List AllocEvent} (h : KeysSampledArmPreEnv st msg evs) :
    StatesRecvEnv x evs := by
  unfold KeysSampledArmPreEnv at h
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  split at h
  · subst h; exact SpqrBoundedEvs.nil _ _
  · split at h
    · subst h; exact SpqrBoundedEvs.nil _ _
    · cases hp : msg.payload <;> rw [hp] at h
      case ct1 =>
        rw [hek] at h
        exact SpqrBoundedEvs.mono (by omega) (by omega) (seq_addChunk16_encode1152_bounded h)
      all_goals subst h; exact SpqrBoundedEvs.nil _ _

theorem keysSampledArmPostEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hek : st.uc.ek.length = 1152)
    {evs : List AllocEvent} (h : KeysSampledArmPostEnv st msg evs) :
    StatesRecvEnv x evs := by
  unfold KeysSampledArmPostEnv at h; split at h
  · exact freeOnlyEvs_sub_statesRecvEnv x h
  · unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv; split at h
    · subst h; exact SpqrBoundedEvs.nil _ _
    · cases hp : msg.payload <;> rw [hp] at h
      case ct1 =>
        rw [hek] at h
        rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
        · exact SpqrBoundedEvs.mono (by omega) (by omega) (seq_addChunk16_encode1152_bounded h1)
        · exact SpqrBoundedEvs.mono (by omega) (by omega)
            (SpqrBoundedEvs.append (seq_addChunk16_encode1152_bounded h1) (SpqrBoundedEvs.of_freeOnly h2))
      all_goals subst h; exact SpqrBoundedEvs.nil _ _

/-! ## 2. `<` and `= ∧ ¬ .ct1` Arms (`+1796 -> s0.x30`, Block `332`) -/

theorem keysSampled_arm_lt_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp) (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          A.pool lim st_cost sf ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  SepWP.weaken_pre
    (Entails.of_eq (by
      simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (ArmKeysSampled1PlacedBudget.keysSampled_arm_lt_placed (A := A.repAlloc)
        hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

set_option maxHeartbeats 1200000 in
/-- Relocatable `.keysSampled` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    (`+1796 -> s0.x30`, Block `332`) with `VmPreserved s sf`. -/
theorem keysSampled_arm_eq_other_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch) (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_5_of_not_ct1 hct1
  have hcond_tag2 := messagePayloadTag_bne_5_of_not_ct1 hct1
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine seq_vm_cont (mid := (blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 256
    subst hsp0
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    let sp1 : SendEkSpills :=
      { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
               sp.b0.w8, sp.b0.w9⟩
        b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9,
               w.b1.w5, w.b1.w6⟩
        b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 3#64,
               noneCap, w.b4.w2⟩
        b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
               w.b3.w0, w.b2.w8⟩
        b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
               w.b2.w0, w.b2.w3⟩
        b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
               w.b4.w6, w.b5.w4⟩
        w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
        q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
    have hfold_unused :
        ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
        memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
        memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢ sendEkUnusedAt (s0.sp - 4240#64) :=
      sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
    have hfold_self_unused :
        ((selfA ↦₆₄ 3#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
         memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
         memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 3#64 w)
        (sepConj_mono_left hfold_unused)
    refine SepWP.fold
      (F := P_rest ∗
        relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0)
      hfold_self_unused ?_ ?_
    · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
      rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      sep_ac_rfl
    · rw [show (memRegion selfA chunkedStatesSize ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
          (P_rest ∗
            relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
            memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0) =
          (P_rest ∗
            relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
            memRegion selfA chunkedStatesSize ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by sep_ac_rfl]
      refine SepWP.mono
        (hwb _ outA sp1
          (P_rest ∗
            relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
            memRegion selfA chunkedStatesSize ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
          rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hsp_align
          (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
          ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
           by simp only [wp_norm, arm64_norm]; exact htr.2⟩)
        (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨hvm1.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
      refine Entails.trans hPf ?_
      have hrec := writeback_keysSampled_entails_resultV1RecvAt A (F := F) outA st w w.b5.w9 sp.q200
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left hrec))
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30]
      simp only [wp_norm, arm64_norm, hx1]; sep_ac_rfl
  )

theorem keysSampled_arm_eq_other_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch) (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          A.pool lim st_cost sf ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  SepWP.weaken_pre
    (Entails.of_eq (by
      simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (keysSampled_arm_eq_other_placed (A := A.repAlloc)
        hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 3. Budget-Threaded `<KeysSampled>::recv_ct1_chunk` Call & `.ct1` Arm (`+1796 -> s0.x30`) -/

/-- Relocatable framed `SepWP` call rule for `keysSampledRecvCt1ChunkSpecOfPrePostEnv` (Block `370`). -/
theorem call_keysSampledRecvCt1Chunk_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {CalleePre CalleePost : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (st_cost : M.σ) (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt)
    (hfit : FitsEnv M lim st_cost (CalleePre ⟨outA, stA, chunkA, st, chunk, outSt⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 .x1 = stA)
    (hx2 : s.readReg64 .x2 = st.uc.epoch) (hx3 : s.readReg64 .x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      A.pool lim st_cost s ∗ stackAt sp_call keysSampledRecvCt1ChunkStack) ∗ Frame)
    (hnext : ∀ (evs : List AllocEvent),
      CalleePost ⟨outA, stA, chunkA, st, chunk, outSt⟩ evs →
      ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
        sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
        SepWP prog target_pc sf
          ((chunkedHeaderSentAt A.repAlloc outA outSt ∗
            memRegion stA 504 ∗ chunkAt chunkA chunk ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt sp_call keysSampledRecvCt1ChunkStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post := by
  have hsp_align_s : s.spAligned = true := by rw [State.spAligned, hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame hcall
    (x := (⟨outA, stA, chunkA, st, chunk, outSt⟩, st_cost)) (F := Frame)
    hpc hrun hsp_align_s hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    dsimp only [keysSampledRecvCt1ChunkSpecOfPrePostEnv]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv, hfit, by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hp
    unfold withLsCodeLoaded keysSampledRecvCt1ChunkSpecOfPrePostEnv at hp; dsimp only at hp
    exact ((satisfies_pure_sepConj _ _ _).mp hp).1
  · intro _ _ _ _ he
    unfold withLsCodeLoaded keysSampledRecvCt1ChunkSpecOfPrePostEnv at he; dsimp only at he
    exact ((satisfies_pure_sepConj _ _ _).mp he).1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [withLsCodeLoaded, keysSampledRecvCt1ChunkSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro evs
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr_sf, hevs⟩ => ?_
    exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext evs hevs sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr_sf.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩)
  · intro _ _ _ ho
    unfold withLsCodeLoaded keysSampledRecvCt1ChunkSpecOfPrePostEnv at ho; dsimp only at ho
    exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

set_option maxHeartbeats 1600000 in
/-- Budget-threaded relocatable `.keysSampled` arm when `msg.epoch = st.uc.epoch` and
    `msg.payload = .ct1 chunk` (`+1796 -> s0.x30`, Block `332`). -/
theorem keysSampled_arm_eq_ct1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {CalleePre CalleePost : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (P_rest : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct1 chunk)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt)
    (hfit : FitsEnv M lim st_cost
      (CalleePre ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, msgA + 10#64,
        st, chunk, outSt⟩))
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          CalleePost ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, msgA + 10#64,
            st, chunk, outSt⟩ evs ∧
          (Pf ⊢ P_rest ∗
            resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
            memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hpost := @ArmKeysSampled1PlacedBudget.keysSampled_post_call_57298_placed _ A.repAlloc F ext hmemcpy_sat s0
  rw [lsmpl_base_332_eq] at hpc hpost
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hcall hpost ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := lsmpl.base 370) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (memRegion_880_entails_words63_376
    ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)) (by sep_focus) ?_
  wp_pull_exists; rename_i w_arg
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_332).rebase (blkPl_332).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    CryptoVerification.blkLib_eq_332 (mid := lsmpl.base 370)
  intro _m_strip
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr]
    rw [hw62, heq, hpay, messagePayloadAt_ct1 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  subst hsp0
  refine SepWP.done rfl (by assumption) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s _ := _hnsp.toVmPreserved (by wp_norm_lhs)
  refine SepWP.done rfl (by assumption) fun hcl1 => ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             msgA, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, sp.b4.w1, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, sp.b5.w1, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, sp.b5.w6, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
      memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
      memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢ sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_pre_call :
      ((selfA ↦₆₄ 3#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (words63At ((s0.sp - 4240#64) + 976#64) w ∗
       relocatedHeap (fun dst => chunkedKeysSampledAt A.repAlloc dst st) (wordsBytes (words63List w))) ∗
      (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        chunkedKeysSampledAt A.repAlloc ((s0.sp - 4240#64) + 976#64) st ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 3#64 w)
      (sepConj_mono (recompose63 ((s0.sp - 4240#64) + 976#64) w)
        (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st_cost s ∗ memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0)
    hfold_pre_call ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl
  · refine ProofLib.SepWP.transport_budgetPool (A := A) (lim := lim) (st := st_cost) hvm1 (hnext := ?_)
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_keysSampledRecvCt1 (s0.sp - 4240#64)))
      (by sep_focus) ?_
    refine call_keysSampledRecvCt1Chunk_placed hcall
      ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 976#64) (msgA + 10#64)
      st chunk outSt st_cost hrecv hfit
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := (blkPl_332).base + 7748#64)
      (Frame :=
        P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) - 19552#64) 1632 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hcl1 rfl (by assumption)
      (by simp only [wp_norm, arm64_norm, hsp])
      hfsp_align
      (by simp only [Reg.lr, wp_norm, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩
      (by simp only [Reg.x0, wp_norm, arm64_norm])
      (by simp only [Reg.x1, wp_norm, arm64_norm])
      (by simp only [Reg.x2, wp_norm, arm64_norm])
      (by simp only [Reg.x3, wp_norm, arm64_norm])
      (by
        dsimp only [chunkedHeaderSentSize, statesRecvCalleeStackX, recvCt2ChunkStackX,
          recvCt2ChunkFrameBytes, polyDecodedMessageStackX, extHookStack,
          keysSampledRecvCt1ChunkStack, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]; sep_ac_rfl)
      ?_
    intro evs hevs sf_c hpc_c hrun_c hsp_c hcs_c htr_c
    have hrejoin_976 :
        memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ⊢
          memRegion ((s0.sp - 4240#64) + 976#64) 880 :=
      Entails.of_eq (memRegion_880_split_504_376
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)).symm
    refine SepWP.focus_weaken hrejoin_976 (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_keysSampledRecvCt1 (s0.sp - 4240#64)).symm)
      (by sep_focus) ?_
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct1 msgA chunk]
    have hx19_c : sf_c.readReg64 .x19 = outA := by
      rw [hcs_c.1]; simp only [Reg.x19, wp_norm, arm64_norm, hx19]
    have hx20_c : sf_c.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64 := by
      rw [hcs_c.2.1]; simp only [Reg.x20, wp_norm, arm64_norm, hsp]
    refine SepWP.weaken_pre (Entails.of_eq ?_)
      (SepWP.mono
        (hpost sf_c outA outSt sp1
          (P_rest ∗ memRegion selfA chunkedStatesSize ∗
           ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st_cost) sf_c)
          hpc_c hrun_c hsp_c hsp_align hx19_c hx20_c htr_c)
        (fun sf Pf _ _ ⟨hvm_post, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by
            rw [← A.pool_transport lim (M.stepEvents evs st_cost) sf_c sf hvm_post]
            sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩))
    rw [← hmsg_eq]; simp only [arm64_norm]; sep_ac_rfl

/-! ## 4. Complete Relocatable `.keysSampled` Arm & Top-Level `subroutine_ok` Contracts -/

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable `.keysSampled` arm of `<States>::recv`
    (`+1796 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_keysSampled_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl
        (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp) (hinv : statesRecvPreInv (.keysSampled st))
    (hFit : FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩))
    (hPre_ct1 : ∀ chunk outSt, msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩) →
      FitsEnv M lim st_cost
        (CalleePre ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, msgA + 10#64,
          st, chunk, outSt⟩))
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch → PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ [])
    (hPost_ct1 : ∀ chunk outSt evs, msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt →
      CalleePost ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, msgA + 10#64,
        st, chunk, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ evs)
    (hPost_other : msg.epoch = st.uc.epoch → (∀ c, msg.payload ≠ .ct1 c) →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ [])
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg PreEnv PostEnv).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg PreEnv PostEnv).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.keysSampled st) msg
      st_cost _ R ?_
    rw [states_recv_keysSampled_gt K st msg hgt]
    refine SepWP.weaken_pre
      (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (ArmKeysSampled1PlacedBudget.keysSampled_arm_gt_placed
          hdealloc st_cost s0 s outA selfA msgA st msg statesRecvRoPlacedAt
          hgt hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, _, hcs_sf, htr_sf⟩ =>
          ⟨⟨evs, hPost_gt hgt evs hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
           hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.keysSampled st) msg
        st_cost _ R ?_
      rw [states_recv_keysSampled_lt K st msg hlt]
      refine SepWP.weaken_pre
        (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
          chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
          messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0)
        (Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono
          (keysSampled_arm_lt_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
            statesRecvRoPlacedAt hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨⟨[], hPost_lt hlt, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
             hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct1 chunk =>
        obtain ⟨outSt, hrecv⟩ := keysSampled_recv_ct1_ok_of_preInv st hinv chunk
        refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.keysSampled st) msg
          st_cost _ R ?_
        rw [states_recv_keysSampled_eq_ct1_ok K st msg chunk outSt heq hpay hrecv]
        refine SepWP.weaken_pre
          (P' := (statesRecvJumpTablePlacedAt ∗
              ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
            memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
            messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0)
          (Entails.of_eq (by dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; sep_ac_rfl))
          (SepWP.mono
            (keysSampled_arm_eq_ct1_placed hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg
              chunk outSt
              (statesRecvJumpTablePlacedAt ∗
                ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt)
              hcl heq hpay hrecv (hPre_ct1 chunk outSt heq hpay hrecv hFit)
              hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
            fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨⟨evs, hPost_ct1 chunk outSt evs heq hpay hrecv hevs,
                Entails.trans hPf (Entails.of_eq (by
                  dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; sep_ac_rfl))⟩,
               hsp_sf, hcs_sf, htr_sf⟩)
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
        have hct1 : ∀ c, msg.payload ≠ .ct1 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.keysSampled st) msg
          st_cost _ R ?_
        rw [states_recv_keysSampled_eq_other K st msg heq hct1]
        refine SepWP.weaken_pre
          (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
            chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
            messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0)
          (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (keysSampled_arm_eq_other_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
              statesRecvRoPlacedAt heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
            fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨⟨[], hPost_other heq hct1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
               hsp_sf, hcs_sf, htr_sf⟩)

/-- Exact-envelope (`KeysSampledArmPreEnv` / `KeysSampledArmPostEnv`) relocatable `.keysSampled` arm
    of `<States>::recv` (`+1796 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_keysSampled_exact_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec M A lim F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp) (hinv : statesRecvPreInv (.keysSampled st))
    (hFit : FitsEnv M lim st_cost (KeysSampledArmPreEnv st msg))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg
              (fun _ => KeysSampledArmPreEnv st msg)
              (fun _ => KeysSampledArmPostEnv st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg
              (fun _ => KeysSampledArmPreEnv st msg)
              (fun _ => KeysSampledArmPostEnv st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  refine states_recv_arm_keysSampled_placed_ofPrePostEnv
    (PreEnv := fun _ => KeysSampledArmPreEnv st msg)
    (PostEnv := fun _ => KeysSampledArmPostEnv st msg)
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R hinv hFit
    ?_ ?_ (fun _ => keysSampledArmPostEnv_nil st msg) ?_
    (fun _ _ => keysSampledArmPostEnv_nil st msg)
    hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr
  · intro chunk outSt heq hpay _ hF
    have hEqEnv : KeysSampledArmPreEnv st msg =
        KeysSampledRecvCt1ChunkPreEnv
          ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, msgA + 10#64,
            st, chunk, outSt⟩ := by
      funext evs; unfold KeysSampledArmPreEnv KeysSampledRecvCt1ChunkPreEnv
      have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      simp only [hngt, hnlt, ↓reduceIte, hpay]
    rwa [← hEqEnv]
  · intro hgt evs hevs; unfold KeysSampledArmPostEnv; simp only [hgt, ↓reduceIte]; exact hevs
  · intro chunk outSt evs heq hpay _ hevs
    unfold KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv at hevs
    unfold KeysSampledArmPostEnv
    have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    simp only [hngt, hnlt, ↓reduceIte, hpay]; exact hevs

/-- Default `StatesRecvEnv` relocatable `.keysSampled` arm of `<States>::recv`
    (`+1796 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_keysSampled_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 370)
      (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec M A lim F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp) (hinv : statesRecvPreInv (.keysSampled st))
    (hFit : FitsEnv M lim st_cost (StatesRecvEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1796#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.keysSampled st) msg).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.keysSampled st) msg).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) :=
  let hek : st.uc.ek.length = 1152 := hinv
  states_recv_arm_keysSampled_placed_ofPrePostEnv
    (PreEnv := StatesRecvEnv) (PostEnv := StatesRecvEnv)
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R hinv hFit
    (fun _ _ _ _ _ hF => FitsEnv.mono
      (fun _ h => keysSampledRecvCt1ChunkPreEnv_sub_statesRecvEnv _ h hek) hF)
    (fun _ _ hevs => freeOnlyEvs_sub_statesRecvEnv _ hevs)
    (fun _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)
    (fun _ _ _ _ _ _ hevs => keysSampledRecvCt1ChunkPostEnv_sub_statesRecvEnv _ hevs hek)
    (fun _ _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)
    hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- Envelope-parametric top-level relocatable `subroutine_ok` theorem for `<States>::recv`
    (Block `332`) on the `.keysSampled` variant (`tag = 3#64`) with `withLsCodeLoaded lsmpl`. -/
theorem states_recv_keysSampled_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hPre_ct1 : ∀ (outA selfA msgA fsp : BitVec 64) (st_cost : M.σ) chunk outSt,
      statesRecvPreInv (.keysSampled st) → msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.keysSampledRecvCt1Pre ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64,
          st, chunk, outSt⟩))
    (hPost_gt : ∀ outA selfA msgA, msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ evs)
    (hPost_lt : ∀ outA selfA msgA, msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ [])
    (hPost_ct1 : ∀ (outA selfA msgA fsp : BitVec 64) chunk outSt evs,
      statesRecvPreInv (.keysSampled st) → msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt →
      envs.keysSampledRecvCt1Post ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64,
        st, chunk, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ evs)
    (hPost_other : ∀ outA selfA msgA, msg.epoch = st.uc.epoch → (∀ c, msg.payload ≠ .ct1 c) →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg PreEnv PostEnv)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv, hfit, _hlr_ls⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) hsp0_align hpc0 hrun0
  refine sepWPp_seq_vm_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 _ ⟨_, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcl1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s1
    (s0.sp - 4240#64) selfA 3#64
    (chunkedKeysSampledAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_vm_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 _ ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcl2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have hpre2 :
      (selfA ↦₆₄ 3#64) ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      (chunkedKeysSampledAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre2 ?_
  exact states_recv_arm_keysSampled_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv)
    hC.hdealloc_sat hC.keysSampledRecvCt1Chunk_ok hC.hmemcpy_sat st_cost
    s0 s2 outA selfA msgA st msg R hinv hfit
    (fun chunk outSt => hPre_ct1 outA selfA msgA (s0.sp - 4240#64) st_cost chunk outSt hinv)
    (hPost_gt outA selfA msgA) (hPost_lt outA selfA msgA)
    (fun chunk outSt evs => hPost_ct1 outA selfA msgA (s0.sp - 4240#64) chunk outSt evs hinv)
    (hPost_other outA selfA msgA)
    hcl2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1)

abbrev states_recv_keysSampled_arm2_placed_ok_ext_ofPrePostEnv := @states_recv_keysSampled_placed_ok_ext_ofPrePostEnv

/-- Exact-envelope (`KeysSampledArmPreEnv` / `KeysSampledArmPostEnv`) top-level relocatable
    `subroutine_ok` theorem for `<States>::recv` (Block `332`) on the `.keysSampled` variant. -/
theorem states_recv_keysSampled_exact_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg
          (fun _ => KeysSampledArmPreEnv st msg) (fun _ => KeysSampledArmPostEnv st msg))) := by
  refine states_recv_keysSampled_placed_ok_ext_ofPrePostEnv hC st msg ?_ ?_
    (fun _ _ _ _ => keysSampledArmPostEnv_nil st msg) ?_
    (fun _ _ _ _ _ => keysSampledArmPostEnv_nil st msg)
  · intro _ _ msgA fsp st_cost chunk outSt _ heq hpay _ hF
    have hEqEnv : KeysSampledArmPreEnv st msg =
        KeysSampledRecvCt1ChunkPreEnv ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64, st, chunk, outSt⟩ := by
      funext evs; unfold KeysSampledArmPreEnv KeysSampledRecvCt1ChunkPreEnv
      have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      simp only [hngt, hnlt, ↓reduceIte, hpay]
    dsimp only [DefsPlacedBudget.statesRecvCalleeEnvs]; rwa [← hEqEnv]
  · intro _ _ _ hgt evs hevs; unfold KeysSampledArmPostEnv; simp only [hgt, ↓reduceIte]; exact hevs
  · intro _ _ _ _ chunk outSt evs _ heq hpay _ hevs
    dsimp only [DefsPlacedBudget.statesRecvCalleeEnvs] at hevs
    unfold KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv at hevs
    unfold KeysSampledArmPostEnv
    have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    simp only [hngt, hnlt, ↓reduceIte, hpay]; exact hevs

abbrev states_recv_keysSampled_arm2_exact_placed_ok_ext := @states_recv_keysSampled_exact_placed_ok_ext

/-- Default `StatesRecvEnv` top-level relocatable `subroutine_ok` theorem for `<States>::recv`
    (Block `332`) on the `.keysSampled` variant (`tag = 3#64`) with `withLsCodeLoaded lsmpl`. -/
theorem states_recv_keysSampled_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.keysSampled st) msg)) :=
  states_recv_keysSampled_placed_ok_ext_ofPrePostEnv (PreEnv := StatesRecvEnv) (PostEnv := StatesRecvEnv)
    hC st msg
    (fun _ _ msgA fsp _ chunk outSt hinv _ _ _ hF => FitsEnv.mono
      (fun _ (h : KeysSampledRecvCt1ChunkPreEnv
          ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64, st, chunk, outSt⟩ _) =>
        keysSampledRecvCt1ChunkPreEnv_sub_statesRecvEnv _ h (show st.uc.ek.length = 1152 from hinv)) hF)
    (fun _ _ _ _ _ hevs => freeOnlyEvs_sub_statesRecvEnv _ hevs)
    (fun _ _ _ _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)
    (fun _ _ msgA fsp chunk outSt _ hinv _ _ _
        (hevs : KeysSampledRecvCt1ChunkPostEnv
          ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64, st, chunk, outSt⟩ _) =>
      keysSampledRecvCt1ChunkPostEnv_sub_statesRecvEnv _ hevs (show st.uc.ek.length = 1152 from hinv))
    (fun _ _ _ _ _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)

abbrev states_recv_keysSampled_arm2_placed_ok_ext := @states_recv_keysSampled_placed_ok_ext

theorem states_recv_keysSampled_cro_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hPre_ct1 : ∀ (outA selfA msgA fsp : BitVec 64) (st_cost : M.σ) chunk outSt,
      statesRecvPreInv (.keysSampled st) → msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.keysSampledRecvCt1Pre ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64,
          st, chunk, outSt⟩))
    (hPost_gt : ∀ outA selfA msgA, msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ evs)
    (hPost_lt : ∀ outA selfA msgA, msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ [])
    (hPost_ct1 : ∀ (outA selfA msgA fsp : BitVec 64) chunk outSt evs,
      statesRecvPreInv (.keysSampled st) → msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt →
      envs.keysSampledRecvCt1Post ⟨fsp + 1856#64, fsp + 976#64, msgA + 10#64,
        st, chunk, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ evs)
    (hPost_other : ∀ outA selfA msgA, msg.epoch = st.uc.epoch → (∀ c, msg.payload ≠ .ct1 c) →
      PostEnv ⟨outA, selfA, msgA, .keysSampled st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysSampled st) msg PreEnv PostEnv)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_keysSampled_placed_ok_ext_ofPrePostEnv
      hC st msg hPre_ct1 hPost_gt hPost_lt hPost_ct1 hPost_other)

theorem states_recv_keysSampled_cro_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.keysSampled st) msg)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_keysSampled_placed_ok_ext M A lim F K ext hC st msg)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2PlacedBudget
