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
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WP.Apply
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ct1Acknowledged` Arm, Part 1 (Budget-Threaded)

`VmPreserved` jump-table/branch dispatch and `RustCliAllocBudget` (`FreeOnlyEvs`) `msg.epoch >
st.uc.epoch` deallocation exit for `.ct1Acknowledged` (`lsmpl.base 332 + 588#64`, tag `11#64`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1PlacedBudget

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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.AddChunk
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
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean states_recv_dispatch_placed states_recv_epilogue_19324_acp_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Relocatable Dispatch (`+36 -> +588`, Block `332`) -/

theorem states_recv_dispatch_ct1Acknowledged_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 588#64)
      s1
      ((st_ptr ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
        (P2 ⊢ (st_ptr ↦₆₄ 11#64) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧ s2.readReg64 .x0 = s1.readReg64 .x0 ∧ s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧ s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 9#64 ∧ s2.readReg64 .x12 = 11#64 ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧ s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧ s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved s2 s1) :=
  ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_dispatch_placed (ext := ext) s1 fsp st_ptr 11#64 Rest
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1

/-! ## 2. Relocatable Entry Stepping (`+588 -> +644 / +4516 / +4432`) -/

theorem call_memcpy_words66_cs_stack {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved (sessionMemcpySpec 4096)))
    (dst src : BitVec 64) (w : Words66)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = 528)
    (hsplit : P = (memRegion dst 528 ∗ words66At src w ∗ stackAt sp_call 4096) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → VmPreserved s sf → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((words66At dst w ∗ words66At src w ∗ stackAt sp_call 4096) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  let bs := wordsBytes (words66List w)
  have hlen : bs.length = 528 := length_wordsBytes_words66List w
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack]
    rw [hlen, hsp, ← words66At_eq_pointsToBytes src w, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · dsimp only [withVmPreserved, sessionMemcpySpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm_sf => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← words66At_eq_pointsToBytes dst w, ← words66At_eq_pointsToBytes src w]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((words66At dst w ∗ words66At src w ∗ stackAt sp_call 4096) ∗ Frame) by sep_ac_rfl)) ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hvm_sf hcs_sf (htr.trans htrace)

theorem ct1Ack_step_588_608_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s : State) (fsp out selfA msgA : BitVec 64) (w : Words66) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 608#64) s
      (memRegion (fsp + 976#64) 528 ∗
       words66At (selfA + 8#64) w ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          words66At (fsp + 976#64) w ∗
          words66At (selfA + 8#64) w ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc ⊢
  rw [stackAt_statesRecvCallee_eq_allocHook s.sp]
  dsimp only [lsProg_332, lsρ, memcpyName, allocHookStack, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  wp_steps
  refine call_memcpy_words66_cs_stack (s0 := s) (ret_pc := (blkPl_332).base + 608#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 976#64) (s.readReg64 .x1 + 8#64) w
    rfl hrun rfl hfsp_align rfl rfl rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hvm1 hcs1 htr1
  have hvm_01 : VmPreserved s sf1 :=
    (show VmPreserved s _ by simp [wp_norm, arm64_norm]).trans hvm1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x1 := hcs1.2.1
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hcs1.2.2.2.2.2.1
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hcs1.2.2.2.2.2.2.2.2.2.2.1
  refine SepWP.done hpc1 hrun1 ⟨hvm_01, Entails.of_eq (by sep_ac_rfl), hsp1,
    hx19_1, hx20_1, hx24_1, hx29_1, htr1, hcs1.2.2.2.2.2.2.2.2.2.2.2⟩

theorem ct1Ack_step_608_632_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep : BitVec 64) (b1 : Words10) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 632#64) s
      (words10At (fsp + 1056#64) b1 ∗
       (msgA ↦₆₄ msg_ep) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          words10At (fsp + 1056#64) b1 ∗
          (msgA ↦₆₄ msg_ep) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = b1.w5 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep b1.w5)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep b1.w5) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20 hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_simp_pre [words10At, BitVec.ofNat_eq_ofNat, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_steps
    simp only [words10At, ekCmpW8, subsPState64, BitVec.ofNat_eq_ofNat, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_done
  )

/-! ## 3. Epoch & Payload Branch Dispatch (`+632 -> +644 / +4516 / +4432 -> +4448 / +4516`) -/

theorem ct1Ack_step_632_644_gt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep ep : BitVec 64) (Frame : SepProp)
    (hgt : msg_ep > ep)
    (hpc : s.pc = lsmpl.base 332 + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep ep)))
    (hz : s.pstate.z = (ekCmpW8 (subsPState64 msg_ep ep) == 0#32)) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 644#64) s
      Frame
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx9 hx19 hx20 hx24
  have hcmp := ekCmpW8_of_gt hgt
  rw [hcmp] at hx8 hz
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hx8 hz ⊢
  wp_steps_vm

theorem ct1Ack_step_632_4516_lt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep ep : BitVec 64) (Frame : SepProp)
    (hlt : msg_ep < ep)
    (hpc : s.pc = lsmpl.base 332 + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep ep)))
    (hz : s.pstate.z = (ekCmpW8 (subsPState64 msg_ep ep) == 0#32)) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4516#64) s
      Frame
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx9 hx19 hx20 hx24
  have hcmp := ekCmpW8_of_lt hlt
  rw [hcmp] at hx8 hz
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hx8 hz ⊢
  wp_steps_vm

theorem ct1Ack_step_632_4432_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA msg_ep ep : BitVec 64) (Frame : SepProp)
    (heq : msg_ep = ep)
    (hpc : s.pc = lsmpl.base 332 + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep ep)))
    (hz : s.pstate.z = (ekCmpW8 (subsPState64 msg_ep ep) == 0#32)) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4432#64) s
      Frame
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx9 hx19 hx20 hx24
  have hcmp := ekCmpW8_of_eq heq
  rw [hcmp] at hx8 hz
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hx8 hz ⊢
  wp_steps_vm

theorem ct1Ack_step_4432_4516_not_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA ep : BitVec 64)
    (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hek : ∀ c, p ≠ .ek c)
    (hekAck : ∀ c, p ≠ .ekCt1Ack c)
    (hpc : s.pc = lsmpl.base 332 + 4432#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4516#64) s
      (((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx9 hx19 hx20 hx24
  have hcond := messagePayloadTag_and6_bne_2_of_not_ek hek hekAck
  have hcond_eq := messagePayloadTag_and6_eq_2_of_not_ek hek hekAck
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hcond hcond_eq ⊢
  wp_steps_vm

theorem ct1Ack_step_4432_4448_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out selfA msgA ep : BitVec 64)
    (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag p) &&& 25769803782#64) != 2#32) = false)
    (hpc : s.pc = lsmpl.base 332 + 4432#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx2 : s.readReg64 .x2 = ep)
    (hx9 : s.readReg64 .x9 = ep)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = selfA)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4448#64) s
      (((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((msgA + 8#64) ↦₈ ct1AckPayloadTag p) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x2 = ep ∧
        sm.readReg64 .x9 = ep ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx19 hx20 hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hcond ⊢
  wp_steps_vm

/-! ## 4. Branch A (`msg.epoch > st.uc.epoch`: `+644 -> +764 -> +19324 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
/-- Writes `Err(EpochOutOfRange(msg_ep))` to `outA` (`x19`) and deallocates the 5 `Vec<u8>`s
    of `st.uc` at `fsp + 976#64..+1104#64` (`+644 -> +764`), threading `A.pool lim st_cost`. -/
theorem ct1Ack_write_err_and_dealloc5_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s3 : State) (fsp outA msg_ep : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 332 + 644#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx2 : s3.readReg64 .x2 = msg_ep)
    (hx19 : s3.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 764#64)
      s3
      (memRegion outA v1RecvSize ∗
        unchunkedCt1SentAt A.repAlloc (fsp + 976#64) uc ∗
        A.pool lim st_cost s3 ∗
        stackAt fsp allocHookStack ∗
        Rest)
      (fun s8 P8 =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P8 ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            memRegion (fsp + 976#64) 128 ∗
            A.pool lim (M.stepEvents evs st_cost) s8 ∗
            stackAt fsp allocHookStack ∗
            Rest) ∧
          s8.sp = fsp ∧
          AllocCallPreserved s3 s8 ∧
          TraceCalleeSaved s8 s3) := by
  have hdealloc_fo := DropChunkedClPlacedBudgetAux.subroutine_ok_deallocFreeOnly
    (spqr_hook_ok_of_mem (prog := lsProg_332 (Rust.withPanics ext)) (sym := spqrDeallocSym) hdealloc)
  simp only [lsProg_332, lsρ, spqrDeallocSym, DropChunkedClPlacedBudgetAux.deallocFreeOnlySpec,
    rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [lsmpl_base_332_eq] at hpc3 ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc3 ⊢
  wp_conv_pre =>
    rw [memRegion_out_960_split_err outA]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v16_out
  apply ProofLib.SepWP.exists_left; intro b8_out
  apply ProofLib.SepWP.exists_left; intro v0_out
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        unchunkedCt1SentAt A.repAlloc (fsp + 976#64) uc ∗
        ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
         memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
         A.pool lim st_cost s3 ∗ stackAt fsp allocHookStack ∗ Rest) by sep_ac_rfl))
      (sepConj_mono_left (unchunkedCt1Sent976_entails_dealloc A.repAlloc fsp uc))) ?_
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro g
  refine SepWP.mono
    (post := fun s8 P8 =>
      ∃ evs, FreeOnlyEvs evs ∧
        (P8 ⊢
          (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
           memRegion (fsp + 976#64) 128) ∗
          A.pool lim (M.stepEvents evs st_cost) s8 ∗ stackAt fsp allocHookStack ∗ Rest) ∧
        (s8.sp = fsp ∧ AllocCallPreserved s3 s8 ∧ TraceCalleeSaved s8 s3))
    ?_
    (fun _ _ _ _ ⟨evs, hevs, hP8, hq8⟩ =>
      ⟨evs, hevs, Entails.trans hP8 (Entails.of_eq (by sep_ac_rfl)), hq8⟩)
  refine DropChunkedClPlacedBudgetAux.seq_evs_step (mid := (blkPl_332).base + 684#64)
    (P_mid := fun st1 sm =>
      (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
        (fiveVec976HeadersAt fsp g ∗
         vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
      A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗ Rest)
    (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧ TraceCalleeSaved sm s3)
    ?_ ?_
  · have hstep1 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
        ((blkPl_332).base + 684#64) s3
        ((fiveVec976HeadersAt fsp g ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
         ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
          memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
          A.pool lim st_cost s3 ∗ stackAt fsp allocHookStack ∗ Rest))
        (fun sm Pm =>
          ∃ evs1, FreeOnlyEvs evs1 ∧
            (Pm ⊢ (((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
              memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
              (fiveVec976HeadersAt fsp g ∗
               vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
              A.pool lim (M.stepEvents evs1 st_cost) sm ∗ stackAt fsp allocHookStack ∗ Rest) ∧
            (sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧ TraceCalleeSaved sm s3)) := by
      dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc, noneCap,
        LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine DropChunkedClPlacedBudgetAux.sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine DropChunkedClPlacedBudgetAux.align_pre_vm
            (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, hsp3, hx2, hx19, beq_iff_eq, wp_norm, arm64_norm]; sep_ac_rfl) ?_
          simp only [hsp3, wp_norm, arm64_norm]
          wp_done)
      · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc g.v1.cap.toNat 1
        refine DropChunkedClPlacedBudgetAux.seq_vm_clean (mid := lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st_cost s3 ∗ A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat ∗
            stackAt fsp allocHookStack ∗
            (((outA ↦₆₄ 0xffffffffffffffff#64) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
              memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
             (fiveVec976HeadersAt fsp g ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗ Rest))
          (Q := fun sc => sc.sp = fsp ∧ AllocCallPreserved s3 sc ∧ TraceCalleeSaved sc s3 ∧
            sc.readReg64 .x0 = g.v1.ptr ∧ sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_332).base + 684#64) ?_ ?_
        · by_vm_steps (
            wp_steps
            dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            refine DropChunkedClPlacedBudgetAux.align_pre_vm
              (by simp only [hsp3, hx2, hx19, beq_iff_eq, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            simp only [hsp3, hx2, hx19, wp_norm, arm64_norm]
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hsp_c, hacp_c, ⟨htr_c1, htr_c2⟩, hx0_c, hx1_c, hx2_c, hlr_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
          wp_call hdealloc_fo (g.v1.ptr, g.v1.cap.toNat, 1, st_cost)
          rw [hsp_c, hlr_c]
          have hacp' : AllocCallPreserved s3 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [TraceCalleeSaved, htr_c1, htr_c2]
          wp_done
    refine SepWP.mono hstep1 fun sm Pm _ _ ⟨evs1, hevs1, hPm1, hq1⟩ =>
      ⟨evs1, hevs1, Entails.trans hPm1 (sepConj_mono_left (sepConj_mono_left
        (err_epochOutOfRange_entails_resultV1RecvAt A.repAlloc (F := F) outA msg_ep))), hq1⟩
  · intro st1 s4 hpc4 hrun4 ⟨hsp4, hacp4, htr41, htr42⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp4
    refine DropChunkedClPlacedBudgetAux.seq_evs_step (mid := (blkPl_332).base + 704#64)
      (P_mid := fun st2 sm =>
        (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          (fiveVec976HeadersAt fsp g ∗
           vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
        A.pool lim st2 sm ∗ stackAt fsp allocHookStack ∗ Rest)
      (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧ TraceCalleeSaved sm s3)
      ?_ ?_
    · dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc,
        LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply DropChunkedClPlacedBudgetAux.sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        simp only [AllocCallPreserved, TraceCalleeSaved, hsp4, htr41, htr42, wp_norm, arm64_norm]
        wp_done
      · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply
        rw [hsp4]
        have hacp' : AllocCallPreserved s3 sf := hacp4.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        simp only [TraceCalleeSaved, htr41, htr42]
        wp_done
    · intro st2 s5 hpc5 hrun5 ⟨hsp5, hacp5, htr51, htr52⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp5
      refine DropChunkedClPlacedBudgetAux.seq_evs_step (mid := (blkPl_332).base + 724#64)
        (P_mid := fun st3 sm =>
          (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            (fiveVec976HeadersAt fsp g ∗
             vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
             vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
          A.pool lim st3 sm ∗ stackAt fsp allocHookStack ∗ Rest)
        (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧ TraceCalleeSaved sm s3)
        ?_ ?_
      · dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply DropChunkedClPlacedBudgetAux.sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, TraceCalleeSaved, hsp5, htr51, htr52, wp_norm, arm64_norm]
          wp_done
        · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply
          rw [hsp5]
          have hacp' : AllocCallPreserved s3 sf := hacp5.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [TraceCalleeSaved, htr51, htr52]
          wp_done
      · intro st3 s6 hpc6 hrun6 ⟨hsp6, hacp6, htr61, htr62⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp6
        refine DropChunkedClPlacedBudgetAux.seq_evs_step (mid := (blkPl_332).base + 744#64)
          (P_mid := fun st4 sm =>
            (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
              (fiveVec976HeadersAt fsp g ∗
               vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
            A.pool lim st4 sm ∗ stackAt fsp allocHookStack ∗ Rest)
          (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧ TraceCalleeSaved sm s3)
          ?_ ?_
        · dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply DropChunkedClPlacedBudgetAux.sepWP_evs_nil
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps
            refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            simp only [AllocCallPreserved, TraceCalleeSaved, hsp6, htr61, htr62, wp_norm, arm64_norm]
            wp_done
          · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply
            rw [hsp6]
            have hacp' : AllocCallPreserved s3 sf := hacp6.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            simp only [TraceCalleeSaved, htr61, htr62]
            wp_done
        · intro st4 s7 hpc7 hrun7 ⟨hsp7, hacp7, htr71, htr72⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp7
          have hstep5 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
              ((blkPl_332).base + 764#64) s7
              ((resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                (fiveVec976HeadersAt fsp g ∗
                 vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
                A.pool lim st4 s7 ∗ stackAt fsp allocHookStack ∗ Rest)
              (fun s8 P8 =>
                ∃ evs5, FreeOnlyEvs evs5 ∧
                  (P8 ⊢ (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                    fiveVec976HeadersAt fsp g) ∗
                    A.pool lim (M.stepEvents evs5 st4) s8 ∗ stackAt fsp allocHookStack ∗ Rest) ∧
                  s8.sp = fsp ∧ AllocCallPreserved s3 s8 ∧ TraceCalleeSaved s8 s3) := by
            dsimp only [fiveVec976HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply DropChunkedClPlacedBudgetAux.sepWP_evs_nil
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              wp_steps
              refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              simp only [AllocCallPreserved, TraceCalleeSaved, hsp7, htr71, htr72, wp_norm, arm64_norm]
              wp_done
            · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc g.v5.cap.toNat 1
              wp_steps; wp_apply
              rw [hsp7]
              have hacp' : AllocCallPreserved s3 sf := hacp7.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine DropChunkedClPlacedBudgetAux.align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              simp only [TraceCalleeSaved, htr71, htr72]
              wp_done
          refine SepWP.mono hstep5 fun s8 P8 _ _ ⟨evs5, hevs5, hP8, hq8⟩ =>
            ⟨evs5, hevs5, Entails.trans hP8
              (Entails.trans
                (sepConj_mono_left (sepConj_mono_right (fiveVec976HeadersAt_entails_memRegion_128 fsp g)))
                (Entails.of_eq (by sep_ac_rfl))), hq8⟩

/-- Calls `drop_glue::<[SortedSet<Pt>; 16]>` (`lsmpl.base 264`) on `fsp + 1104#64`, folds
    `memRegion (fsp + 976#64) 528`, and jumps to `+19324` (`+764 -> +19324`), threading
    `A.pool lim st_cost`. -/
theorem ct1Ack_drop_decoder_to_19324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s8 : State) (fsp : BitVec 64)
    (dec : PolyDecoder)
    (Rest : SepProp)
    (hcl8 : LibsignalCodeLoaded lsmpl s8.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc8 : s8.pc = lsmpl.base 332 + 764#64)
    (hrun8 : s8.status = .Running)
    (hsp8 : s8.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64)
      s8
      (memRegion (fsp + 976#64) 128 ∗
        polyDecoderAt A.repAlloc (fsp + 1104#64) dec ∗
        A.pool lim st_cost s8 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun s9 P9 =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P9 ⊢
            memRegion (fsp + 976#64) 528 ∗
            A.pool lim (M.stepEvents evs st_cost) s9 ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest) ∧
          s9.sp = fsp ∧
          AllocCallPreserved s8 s9 ∧
          TraceCalleeSaved s9 s8) := by
  subst hsp8
  rw [lsmpl_base_332_eq] at hpc8 ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc8 ⊢
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        polyDecoderAt A.repAlloc (s8.sp + 1104#64) dec ∗
        (memRegion (s8.sp + 976#64) 128 ∗
         A.pool lim st_cost s8 ∗
         stackAt s8.sp statesRecvCalleeStackX ∗
         Rest) by sep_ac_rfl))
      (sepConj_mono_left (polyDecoderAt_entails_vecs_tail A.repAlloc (s8.sp + 1104#64) dec))) ?_
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_dropGluePoly16' s8.sp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro dec_vecs
  wp_focus_pure; intro hdec_len
  refine CryptoVerification.sepWP_seq_lscl hcl8 (mid := lsmpl.base 264) ?_
  wp_steps
  refine SepWP.done rfl hrun8 (fun hcl9 => ?_)
  have hpt16_raw := DropChunkedClPlacedBudget.drop_glue_sorted_set_pt16_mem_on
    (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hcl9
  dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget.dropGlueSortedSetPt16Spec,
    BitVec.ofNat_eq_ofNat] at hpt16_raw
  wp_call hpt16_raw (⟨s8.sp + 1104#64, dec_vecs⟩, st_cost)
  have hacp_cf : AllocCallPreserved s8 sf := by assumption
  have hevs_w : FreeOnlyEvs w := by assumption
  wp_steps
  let szDec : Nat := 400
  have hjoin528 :
      memRegion (s8.sp + 976#64) 128 ∗
        (memRegion (s8.sp + 1104#64) polyArrayBytes ∗
         memRegion ((s8.sp + 1104#64) + 384#64) 16) ⊢
      memRegion (s8.sp + 976#64) 528 := by
    refine Entails.trans (sepConj_mono_right (polyDecoder_post_join (s8.sp + 1104#64))) ?_
    unfold polyDecoderSize
    rw [show (528 : Nat) = 128 + szDec from rfl,
        ProofLib.memRegion_split' (b := s8.sp + 976#64) (n := 128) (k := szDec)
          (b' := s8.sp + 1104#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hstack_fold := stackAt_statesRecvCallee_from_dropGluePoly16 s8.sp
  refine SepWP.mono
    (post := fun s9 P9 =>
      (P9 ⊢
        memRegion (s8.sp + 976#64) 528 ∗
        A.pool lim (M.stepEvents w st_cost) s9 ∗
        stackAt s8.sp statesRecvCalleeStackX ∗
        Rest) ∧
      (s9.sp = s8.sp ∧ AllocCallPreserved s8 s9 ∧ TraceCalleeSaved s9 s8))
    ?_
    (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
  refine SepWP.weaken_pre
    (P' := memRegion (s8.sp + 976#64) 528 ∗
      A.pool lim (M.stepEvents w st_cost) sf ∗
      stackAt s8.sp statesRecvCalleeStackX ∗
      Rest)
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s8.sp + 976#64) 128 ∗
          (memRegion (s8.sp + 1104#64) polyArrayBytes ∗
           memRegion ((s8.sp + 1104#64) + 384#64) 16)) ∗
        (memRegion (s8.sp - 19552#64) 15424 ∗ stackAt s8.sp dropGluePoly16Stack) ∗
        (A.pool lim (M.stepEvents w st_cost) sf ∗ Rest) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hjoin528 (sepConj_mono_left hstack_fold))
        (Entails.of_eq (by sep_ac_rfl)))) ?_
  rcases hacp_cf with ⟨_, _, _, _, _, _, _⟩
  wp_done

/-- Full budget-threaded `EpochOutOfRange` return theorem (`+644 -> s0.readReg64 .x30`)
    for `.ct1Acknowledged`. -/
theorem ct1Ack_gt_644_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 644#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hx2 : s.readReg64 .x2 = msg_ep)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        memRegion selfA chunkedStatesSize ∗
        chunkedCt1AcknowledgedAt A.repAlloc (s0.sp - 4240#64 + 976#64) st ∗
        memRegion (s0.sp - 4240#64 + 1504#64) 352 ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 976 ∗
        memRegion (s0.sp - 4240#64 + 1856#64) 2288 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            P_rest ∗
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  set fsp := s0.sp - 4240#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  dsimp only [chunkedCt1AcknowledgedAt, spqrPolyApi]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  refine SepWP.mono
    (post := fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢
          (P_rest ∗
           resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
           memRegion selfA chunkedStatesSize) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        (sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
    ?_
    (fun _ _ _ _ ⟨evs, hevs, hPf, hq⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hq⟩)
  refine DropChunkedClPlacedBudgetAux.seq_evs_step_lscl hcl (mid := lsmpl.base 332 + 764#64)
    (P_mid := fun st1 s8 =>
      memRegion (fsp + 976#64) 128 ∗
      polyDecoderAt A.repAlloc (fsp + 1104#64) st.receiving_ek ∗
      A.pool lim st1 s8 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (P_rest ∗
       resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
       memRegion selfA chunkedStatesSize ∗
       memRegion fsp 976 ∗
       memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 2288 ∗
       statesRecvSavedCells s0))
    (Q_mid := fun s8 => s8.sp = fsp ∧ AllocCallPreserved s s8 ∧ TraceCalleeSaved s8 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_write_err_and_dealloc5_placed hdealloc st_cost s fsp outA msg_ep st.uc
      (polyDecoderAt A.repAlloc (fsp + 1104#64) st.receiving_ek ∗
       memRegion (fsp - 19552#64) 15456 ∗
       P_rest ∗
       memRegion selfA chunkedStatesSize ∗
       memRegion fsp 976 ∗
       memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 2288 ∗
       statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx2 hx19
    refine SepWP.weaken_pre ?_ (SepWP.mono hstep1 ?_)
    · rw [stackAt_statesRecvCallee_eq_allocHook fsp]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s8 P8 _ _ ⟨evs1, hevs1, hP8, hsp8, hacp8, htr8⟩
      refine ⟨evs1, hevs1, Entails.trans hP8 ?_, hsp8, hacp8, ⟨htr8.1.trans htr.1, htr8.2.trans htr.2⟩⟩
      rw [stackAt_statesRecvCallee_eq_allocHook fsp]
      exact Entails.of_eq (by sep_ac_rfl)
  · intro st1 s8 hpc8 hrun8 hcl8 ⟨hsp8, hacp8, htr8⟩
    refine DropChunkedClPlacedBudgetAux.seq_evs_step (mid := lsmpl.base 332 + 19324#64)
      (P_mid := fun st2 s9 =>
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        statesRecvSavedCells s0 ∗
        (P_rest ∗
         resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗
         A.pool lim st2 s9))
      (Q_mid := fun s9 => s9.sp = fsp ∧ AllocCallPreserved s s9 ∧ TraceCalleeSaved s9 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_drop_decoder_to_19324_placed hdealloc st1 s8 fsp st.receiving_ek
        (P_rest ∗
         resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗
         memRegion fsp 976 ∗
         memRegion (fsp + 1504#64) 352 ∗
         memRegion (fsp + 1856#64) 2288 ∗
         statesRecvSavedCells s0)
        hcl8 hfsp_align hpc8 hrun8 hsp8
      refine SepWP.mono hstep2 ?_
      intro s9 P9 _ _ ⟨evs2, hevs2, hP9, hsp9, hacp9, htr9⟩
      refine ⟨evs2, hevs2, Entails.trans hP9 ?_, hsp9, hacp8.trans hacp9,
        ⟨htr9.1.trans htr8.1, htr9.2.trans htr8.2⟩⟩
      have hjoin4144 :
          memRegion fsp 976 ∗
          (memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352) ∗
          memRegion (fsp + 1856#64) 2288 ⊢
          memRegion fsp 4144 := by
        rw [← memRegion_976_880_split_528_352 fsp,
            show (4144 : Nat) = 976 + 3168 from rfl,
            ProofLib.memRegion_split' (b := fsp) (n := 976) (k := 3168) (b' := fsp + 976#64) rfl rfl (by decide),
            show (3168 : Nat) = 880 + 2288 from rfl,
            ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide)]
        exact Entails.of_eq (by sep_ac_rfl)
      refine Entails.trans (Entails.of_eq (show _ =
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion fsp 976 ∗
         (memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352) ∗
         memRegion (fsp + 1856#64) 2288) ∗
        statesRecvSavedCells s0 ∗
        (P_rest ∗
         resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs2 st1) s9) by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hjoin4144)
    · intro st2 s9 hpc9 hrun9 ⟨hsp9, hacp9, htr9⟩
      refine DropChunkedClPlacedBudgetAux.sepWP_vm_evs_nil
        (fun sf hvm => by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      refine SepWP.mono
        (ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_epilogue_19324_acp_placed s0 s9
          (P_rest ∗
           resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
           memRegion selfA chunkedStatesSize ∗
           A.pool lim st2 s9)
          hsp0_align hpc9 hrun9 hsp9 htr9)
        (fun sf Pf _ _ ⟨hvm_ep, hPf, hsp_sf, hacp_ep, hcs_sf, htr_sf⟩ => ?_)
      refine ⟨hvm_ep, ?_, hsp_sf, hacp9.trans hacp_ep, hcs_sf, htr_sf⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1PlacedBudget
