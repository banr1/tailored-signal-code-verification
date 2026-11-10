/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.DecodesBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Drop Glue for PB Chunked States (`EkSentCt1Received`, `HeaderSent`)

Proves `RustCliAllocBudget`-threaded `[LibsignalPlacement]` subroutine contracts (`FreeOnlyEvs`)
for `chunked::EkSentCt1Received` (Block `285`) and `chunked::HeaderSent` (Block `281`),
re-exporting `chunked::HeaderReceived` (Block `283`) from `ProtoChunked2BudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (
  LibsignalPlacement blkPC_281 blkPC_283 blkPC_285 blkPl_281 blkPl_283 blkPl_285 lsmpl lsρ
)
open CryptoVerification.LibsignalSpqrV1 (pbToProtoPolyDecoder pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (
  DropProtoChunkedEkSentCt1ReceivedGhost DropProtoChunkedHeaderReceivedGhost
  DropProtoChunkedHeaderSentGhost Saved48Preserved
  add_24_add_8 auth24HeadersAt auth24HeadersAt_entails_memRegion_48
  auth48HeadersAt auth48HeadersAt_entails_memRegion_48
  cap_add_one_beq_zero_false cap_mul_24 cons_len_mul
  dropStack48 dropStack96 header_cells_entails_memRegion_24
  none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
  optProtoAuthenticatorAt_24_none optProtoAuthenticatorAt_24_none_entails_memRegion_48
  optProtoAuthenticatorAt_48_none optProtoAuthenticatorAt_48_none_entails_memRegion_48
  optProtoAuthenticatorAt_some
  optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialDecoderAt_none' optProtoPolynomialDecoderAt_some'
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  optProtoUnchunked1Vec_none_entails_memRegion_80
  optProtoUnchunked2Vec_none_entails_memRegion_104
  optProtoUnchunkedEkSentAt_none optProtoUnchunkedEkSentAt_some
  optProtoUnchunkedEkSentCt1ReceivedAt_none optProtoUnchunkedEkSentCt1ReceivedAt_some
  optProtoUnchunkedHeaderReceivedAt_none optProtoUnchunkedHeaderReceivedAt_some
  protoAuthenticatorAt_entails_dealloc
  protoChunkedEkSentCt1ReceivedAt protoChunkedEkSentCt1ReceivedSize
  protoChunkedHeaderReceivedAt protoChunkedHeaderReceivedSize
  protoChunkedHeaderSentAt protoChunkedHeaderSentSize
  protoPolyDecoderAt_entails_dealloc protoPolyDecoderHeaders_entails_memRegion_40
  protoPolynomialEncoderAt_expose_cap protoPolynomialEncoderAt_unexpose_cap
  protoUnchunked1VecHeadersAt protoUnchunked1VecHeadersAt_entails_memRegion_80'
  protoUnchunked2VecHeadersAt protoUnchunked2VecHeadersAt_entails_memRegion_104'
  protoUnchunkedEkSentAt_entails_dealloc protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc
  protoUnchunkedHeaderReceivedAt_entails_dealloc
  sep_pull_body sep_push_body sep_rejoin_loop
  stackAt_dropStack48_split stackAt_dropStack48_split_bottom
  stackAt_dropStack48_sub48_split_bottom
  stackAt_dropStack96_split stackAt_dropStack96_split_bottom
  stack_restore_48_allocHook stack_restore_96_allocHook
  tail_len_mul_lt twoVecHeadersAt twoVecHeadersAt_24_eq twoVecHeadersAt_48_eq
  vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialDecoderAt optProtoPolynomialEncoderAt
  protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget (
  dropProtoChunkedEkSentCt1ReceivedSpec dropProtoChunkedHeaderSentSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec
  drop_proto_chunked_ek_sent_ct1_received_loop_placed
  drop_proto_chunked_header_sent_loop_placed
  sepWP_close_drop sepWP_evs_dealloc sepWP_evs_inst sepWP_evs_nil
  sepWP_vm_evs_nil seq_clean_evs seq_vm_clean subroutine_ok_deallocFreeOnly
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2Budget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Block `285` (`EkSentCt1Received`) and Block `281` (`HeaderSent`) -/

export LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux (
  drop_proto_chunked_header_received_placed_ok
)

section PlacedEkSentCt1Received
variable [LibsignalPlacement]

/-- Relocatable `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>`
(Block `285`) satisfies `dropProtoChunkedEkSentCt1ReceivedSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_proto_chunked_ek_sent_ct1_received_placed_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_285).rebase (blkPl_285).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_285).rebase (blkPl_285).base H) (blkPl_285).base
      (dropProtoChunkedEkSentCt1ReceivedSpec M A lim) := by
  simp only [dropProtoChunkedEkSentCt1ReceivedSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop := drop_proto_chunked_ek_sent_ct1_received_loop_placed hdealloc
  dsimp only [protoChunkedEkSentCt1ReceivedSize] at *
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases x_st with ⟨⟨a, st_pb⟩, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [DropProtoChunkedEkSentCt1ReceivedGhost.a, DropProtoChunkedEkSentCt1ReceivedGhost.st,
    protoChunkedEkSentCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_evs (mid := (blkPl_285).base + 120#64)
    (P_evs := fun evs sm =>
      (memRegion a 104 ∗
        optProtoPolynomialDecoderAt A.repAlloc (a + 104#64) (st_pb.receivingCt2.map pbToProtoPolyDecoder)) ∗
      A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
      refine sepWP_vm_evs_nil (fun sm hvm => by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (optProtoUnchunked2Vec_none_entails_memRegion_104 a) (by sep_focus) ?_
        refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done)
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A.repAlloc a u)) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean_evs (mid := (blkPl_285).base + 80#64)
        (P_evs := fun evs sm =>
          ((protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
            optProtoPolynomialDecoderAt A.repAlloc (a + 104#64) (st_pb.receivingCt2.map pbToProtoPolyDecoder)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_48_none]; dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]
          refine sepWP_vm_evs_nil (fun sm hvm => by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
          by_vm_steps (
            wp_steps
            refine SepWP.focus_weaken (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc a) (by sep_focus) ?_
            refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 48#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_48_eq]; wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean_evs (mid := (blkPl_285).base + 60#64)
            (P_evs := fun evs sm =>
              ((protoUnchunked2VecHeadersAt a g ∗
                (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 96#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                optProtoPolynomialDecoderAt A.repAlloc (a + 104#64) (st_pb.receivingCt2.map pbToProtoPolyDecoder)) ∗
              A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
              simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · refine sepWP_vm_evs_nil (fun sm hvm => by
                simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
              by_vm_steps (
                wp_steps
                refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done)
            · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
              refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
                (P_mid :=
                  A.pool lim st s0 ∗ A.live ga.v1.ptr ga.v1.cap.toNat 1 ∗ memRegion ga.v1.ptr ga.v1.cap.toNat ∗
                  stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((protoUnchunked2VecHeadersAt a g ∗
                     (auth48HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                     memRegion (a + 96#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                     vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
                    optProtoPolynomialDecoderAt A.repAlloc (a + 104#64) (st_pb.receivingCt2.map pbToProtoPolyDecoder)) ∗
                   (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
                (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
                  sc.readReg64 .x0 = ga.v1.ptr ∧ sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
                  sc.readReg64 .lr = (blkPl_285).base + 60#64 ∧
                  sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.v1.cap)
                ?_ ?_
              · by_vm_steps (
                  wp_steps
                  dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc,
                    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                  refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                  wp_done)
              · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c⟩
                rcases hpres_c with ⟨hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
                have ⟨_, _, _, _, _, _, _⟩ := hacp_c
                rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
                have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
                  change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
                  simp (config := { decide := true }) only [arm64_norm, wp_norm]
                wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
                rw [hsp_c, hlr_c]
                have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
                rcases hacp' with ⟨_, _, _, _, _, _, _⟩
                dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc,
                  LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done
          · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1, hx20_a1⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
            dsimp only [auth48HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_inst evsa1 hevsa1
              wp_steps
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
            · apply sepWP_evs_inst (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1)
                (hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat))
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              wp_steps
              wp_apply
              rw [hsp_a1]
              have hacp' : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
      · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        let st1 := M.stepEvents evs1 st
        refine seq_clean_evs (mid := (blkPl_285).base + 100#64)
          (P_evs := fun evs sm =>
            ((protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialDecoderAt A.repAlloc (a + 104#64) (st_pb.receivingCt2.map pbToProtoPolyDecoder)) ∗
            A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;>
            simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps; wp_done
          · apply sepWP_evs_dealloc g.v1.cap.toNat 1
            wp_steps
            wp_apply
            rw [hsp_1]
            have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
        · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_2
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_inst (evs1 ++ evs2) (hevs1.append hevs2)
            simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            wp_steps
            refine SepWP.focus_weaken (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g) (by sep_focus) ?_
            wp_done
          · apply sepWP_evs_inst (evs1 ++ evs2 ++ rustDeallocEvents g.v2.cap.toNat 1)
              ((hevs1.append hevs2).append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v2.cap.toNat))
            simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            wp_steps
            wp_apply
            rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine SepWP.focus_weaken (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g) (by sep_focus) ?_
            refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
  · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_3
    let st3 := M.stepEvents evs3 st
    have hjoin144_from_40 : memRegion a 104 ∗ memRegion (a + 104#64) 40 ⊢ memRegion a 144 := by
      rw [ProofLib.memRegion_split' (b := a) (n := 104) (k := 40) (b' := a + 104#64) rfl rfl (by decide)]
      exact Entails.refl _
    have h112 : (a + 104#64) + 8#64 = a + 112#64 := BitVec.add_assoc a 104#64 8#64
    have h120 : (a + 104#64) + 16#64 = a + 120#64 := BitVec.add_assoc a 104#64 16#64
    have h128 : (a + 104#64) + 24#64 = a + 128#64 := BitVec.add_assoc a 104#64 24#64
    cases hct2 : st_pb.receivingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      rw [h112]
      refine sepWP_close_drop
        (fun sf => memRegion a 144 ∗ A.pool lim st3 sf ∗ stackAt s0.sp dropStack48)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        have hnone40 : ((a + 104#64) ↦₆₄ noneCap) ∗ memRegion (a + 112#64) 32 ⊢ memRegion (a + 104#64) 40 := by
          rw [← h112]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 104#64)
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin144_from_40 (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · rw [satisfies_sepExists]
        refine ⟨evs3, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs3⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (a + 104#64) pb) (by sep_focus) ?_
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      wp_pull_exists; rename_i g; rw [h112, h120, h128]
      wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 (cap : BitVec 64) :
          ((a + 104#64) ↦₆₄ cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
            ((a + 120#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 128#64) 16 ⊢
          memRegion (a + 104#64) 40 := by
        rw [← h112, ← h120, ← h128]
        exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 104#64) cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      refine seq_clean_evs (mid := (blkPl_285).base + 184#64)
        (P_evs := fun evs sm =>
          memRegion a 104 ∗ ((a + 104#64) ↦₆₄ g.cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
          ((a + 120#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 128#64) 16 ∗ A.pool lim (M.stepEvents evs st3) sm ∗
          stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
            BitVec.add_zero, arrayAt, emp_sepConj]
          refine sepWP_vm_evs_nil (fun sm hvm => by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
          by_vm_steps (
            wp_steps
            refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; sep_ac_rfl) ?_
            wp_done)
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_vm_clean (mid := (blkPl_285).base + 160#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
              A.pool lim st3 s3 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (memRegion a 104 ∗ ((a + 104#64) ↦₆₄ g.cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
               ((a + 120#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                 ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 128#64) 16 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64)
            ?_ ?_
          · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
          · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            rw [← A.pool_of_vmPreserved hvm_loop]
            refine SepWP.mono
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr st3 s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
                hx19_loop hx20_loop hx21_loop hx22_loop) ?_
            intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
            refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
            have hsplit : g.cap.toNat * 24 =
                (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
              rw [← hsplit]; omega
            have hmr_eq : memRegion g.ptr (g.cap.toNat * 24) =
                memRegion g.ptr ((bs :: tl).length * 24) ∗
                  memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                    ((g.cap.toNat - (bs :: tl).length) * 24) := by
              rw [hsplit]
              exact ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                ((g.cap.toNat - (bs :: tl).length) * 24) hbound
            simp only [hcap_ne, ↓reduceIte, hmr_eq]
            exact Entails.of_eq (by sep_ac_rfl)
      · intro evs4 s4 hevs4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4, hx20_4⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_4
        let st4 := M.stepEvents evs4 st3
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_4 ⊢
          refine sepWP_close_drop
            (fun sf => memRegion a 144 ∗ A.pool lim st4 sf ∗ stackAt s0.sp dropStack48)
            ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · wp_steps
            refine SepWP.focus_weaken (hhdr40 0) (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin144_from_40 (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            wp_done
          · rw [satisfies_sepExists]
            refine ⟨evs3 ++ evs4, ?_⟩
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, hevs3.append hevs4⟩, ?_⟩
            have heq_st : M.stepEvents (evs3 ++ evs4) st = st4 := by
              simp only [st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]
          refine sepWP_close_drop
            (fun sf => memRegion a 144 ∗
              A.pool lim (M.stepEvents (evs3 ++ evs4 ++ rustDeallocEvents (g.cap.toNat * 24) 8) st) sf ∗
              stackAt s0.sp dropStack48)
            ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · have heq_st5 : M.stepEvents (evs3 ++ evs4 ++ rustDeallocEvents (g.cap.toNat * 24) 8) st =
                M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st4 := by
              simp only [st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st5]
            have htail : SepWP ((blkPC_285).rebase (blkPl_285).base H) (s0.readReg64 .lr) s4
                (memRegion a 104 ∗ ((a + 104#64) ↦₆₄ g.cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
                  ((a + 120#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                  (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
                  memRegion (a + 128#64) 16 ∗ A.pool lim st4 s4 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
                (fun sf Pf =>
                  (Pf ⊢ memRegion a 144 ∗
                    A.pool lim (M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st4) sf ∗
                    stackAt s0.sp dropStack48) ∧
                  sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                  AllocCallPreserved s4 sf ∧ CalleeSavedPreserved s0 sf) := by
              wp_steps
              refine SepWP.focus_weaken (hhdr40 g.cap) (by sep_focus) ?_
              refine SepWP.focus_weaken hjoin144_from_40 (by sep_focus) ?_
              refine SepWP.focus_weaken
                (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                  (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
                (by sep_focus) ?_
              rw [stackAt_dropStack48_split_bottom s0.sp]
              wp_call hdealloc_fo (g.ptr, g.cap.toNat * 24, 8, st4)
              have hpost4 : AllocCallPreserved s4 sf := by assumption
              rcases hpost4 with ⟨_, _, _, _, _, _, _⟩
              wp_done
            exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_4f, hcs_f⟩ =>
              ⟨hp, hsp_f, htr_f, hacp_4.trans hacp_4f, hcs_f⟩
          · rw [satisfies_sepExists]
            refine ⟨evs3 ++ evs4 ++ rustDeallocEvents (g.cap.toNat * 24) 8, ?_⟩
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, (hevs3.append hevs4).append
              (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.cap.toNat * 24))⟩, ?_⟩
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end PlacedEkSentCt1Received

section PlacedHeaderSent
variable [LibsignalPlacement]

/-- Relocatable `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>`
(Block `281`) satisfies `dropProtoChunkedHeaderSentSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_proto_chunked_header_sent_placed_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpoly_enc_raw : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H)
      (lsmpl.base 271) (ProtoPolyBudget.dropProtoPolyEncoderSpec M A lim)) :
    subroutine_ok ((blkPC_281).rebase (blkPl_281).base H) (blkPl_281).base
      (dropProtoChunkedHeaderSentSpec M A lim) := by
  simp only [dropProtoChunkedHeaderSentSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop := drop_proto_chunked_header_sent_loop_placed hdealloc
  dsimp only [protoChunkedHeaderSentSize] at *
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases x_st with ⟨⟨a, st_pb⟩, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [DropProtoChunkedHeaderSentGhost.a, DropProtoChunkedHeaderSentGhost.st,
    protoChunkedHeaderSentAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_evs (mid := (blkPl_281).base + 100#64)
    (P_evs := fun evs sm =>
      (memRegion a 80 ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 80#64) (st_pb.sendingEk.map pbToProtoPolyEncoder) ∗
        optProtoPolynomialDecoderAt A.repAlloc (a + 136#64) (st_pb.receivingCt1.map pbToProtoPolyDecoder)) ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      rw [optProtoUnchunkedEkSentAt_none]
      refine sepWP_vm_evs_nil (fun sm hvm => by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (optProtoUnchunked1Vec_none_entails_memRegion_80 a) (by sep_focus) ?_
        refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done)
    | some u =>
      rw [optProtoUnchunkedEkSentAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (protoUnchunkedEkSentAt_entails_dealloc A.repAlloc a u)) ?_
      wp_pull_exists; rename_i v1; wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean_evs (mid := (blkPl_281).base + 80#64)
        (P_evs := fun evs sm =>
          ((protoUnchunked1VecHeadersAt a v1 ∗ memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 ∗
            vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
            optProtoPolynomialEncoderAt A.repAlloc (a + 80#64) (st_pb.sendingEk.map pbToProtoPolyEncoder) ∗
            optProtoPolynomialDecoderAt A.repAlloc (a + 136#64) (st_pb.receivingCt1.map pbToProtoPolyDecoder)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_24_none]; dsimp only [protoUnchunked1VecHeadersAt]
          refine sepWP_vm_evs_nil (fun sm hvm => by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
          by_vm_steps (
            wp_steps
            refine SepWP.focus_weaken (optProtoAuthenticatorAt_24_none_entails_memRegion_48 A.repAlloc a) (by sep_focus) ?_
            refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 24#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_24_eq]; wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean_evs (mid := (blkPl_281).base + 60#64)
            (P_evs := fun evs sm =>
              ((protoUnchunked1VecHeadersAt a v1 ∗
                (auth24HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 72#64) 8 ∗ vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
                optProtoPolynomialEncoderAt A.repAlloc (a + 80#64) (st_pb.sendingEk.map pbToProtoPolyEncoder) ∗
                optProtoPolynomialDecoderAt A.repAlloc (a + 136#64) (st_pb.receivingCt1.map pbToProtoPolyDecoder)) ∗
              A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
              simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · refine sepWP_vm_evs_nil (fun sm hvm => by
                simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
              by_vm_steps (
                wp_steps
                refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done)
            · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
              refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
                (P_mid :=
                  A.pool lim st s0 ∗ A.live ga.v1.ptr ga.v1.cap.toNat 1 ∗ memRegion ga.v1.ptr ga.v1.cap.toNat ∗
                  stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((protoUnchunked1VecHeadersAt a v1 ∗
                     (auth24HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                     memRegion (a + 72#64) 8 ∗ vecCapPtrDealloc A.repAlloc v1.cap v1.ptr) ∗
                    optProtoPolynomialEncoderAt A.repAlloc (a + 80#64) (st_pb.sendingEk.map pbToProtoPolyEncoder) ∗
                    optProtoPolynomialDecoderAt A.repAlloc (a + 136#64) (st_pb.receivingCt1.map pbToProtoPolyDecoder)) ∗
                   memRegion (s0.sp - 4192#64) 48 ∗
                   (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
                (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
                  sc.readReg64 .x0 = ga.v1.ptr ∧ sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64 ∧
                  sc.readReg64 .lr = (blkPl_281).base + 60#64 ∧
                  sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = v1.cap)
                ?_ ?_
              · by_vm_steps (
                  wp_steps
                  dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc,
                    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                  refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                  wp_done)
              · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c⟩
                rcases hpres_c with ⟨hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
                have ⟨_, _, _, _, _, _, _⟩ := hacp_c
                rw [← A.pool_of_vmPreserved hvmc, ← hsp_c, ← hlr_c]
                have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
                  change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
                  simp (config := { decide := true }) only [arm64_norm, wp_norm]
                wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
                rw [hsp_c, hlr_c]
                have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
                rcases hacp' with ⟨_, _, _, _, _, _, _⟩
                dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc,
                  LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
                wp_done
          · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1, hx20_a1⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
            dsimp only [auth24HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_inst evsa1 hevsa1
              wp_steps
              refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
            · apply sepWP_evs_inst (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1)
                (hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat))
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              wp_steps
              wp_apply
              rw [hsp_a1]
              have hacp' : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
      · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_1
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc1 : (v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_inst evs1 hevs1
          wp_steps
          refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_
          wp_done
        · apply sepWP_evs_inst (evs1 ++ rustDeallocEvents v1.cap.toNat 1)
            (hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 v1.cap.toNat))
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          wp_steps
          wp_apply
          rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
  · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_2
    let st2 := M.stepEvents evs2 st
    refine seq_clean_evs (mid := (blkPl_281).base + 120#64)
      (P_evs := fun evs sm =>
        (memRegion a 136 ∗
          optProtoPolynomialDecoderAt A.repAlloc (a + 136#64) (st_pb.receivingCt1.map pbToProtoPolyDecoder)) ∗
        A.pool lim (M.stepEvents evs st2) sm ∗
        (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a) ?_ ?_
    · cases hek : st_pb.sendingEk with
      | none =>
        simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
        have h88 : (a + 80#64) + 8#64 = a + 88#64 := BitVec.add_assoc a 80#64 8#64
        rw [h88]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        have hjoin136 : memRegion a 80 ∗ ((a + 80#64) ↦₆₄ noneCap) ∗ memRegion (a + 88#64) 48 ⊢ memRegion a 136 := by
          rw [← h88, ProofLib.memRegion_split' (b := a) (n := 80) (k := 56) (b' := a + 80#64) rfl rfl (by decide)]
          exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 80#64))
        refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_
        wp_done
      | some enc =>
        simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
        refine SepWP.focus_weaken
          (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 80#64) (pbToProtoPolyEncoder enc))
          (by sep_focus) ?_
        wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt
        wp_steps
        refine SepWP.focus_weaken
          (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 80#64) cap ptr (pbToProtoPolyEncoder enc))
          (by sep_focus) ?_
        have hstack_fold : memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack ⊢
            stackAt (s0.sp - 48#64) dropStack48 :=
          Entails.of_eq (stackAt_dropStack48_sub48_split_bottom s0.sp).symm
        refine SepWP.focus_weaken hstack_fold (by sep_focus) ?_
        wp_call hpoly_enc_raw (⟨a + 80#64, pbToProtoPolyEncoder enc⟩, st2)
        rw [hsp_2, stackAt_dropStack48_sub48_split_bottom s0.sp]
        have hevs_w : FreeOnlyEvs w := by assumption
        have hacp_f : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
        rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
        have hjoin136 : memRegion a 80 ∗ memRegion (a + 80#64) protoPolynomialEncoderSize ⊢ memRegion a 136 := by
          rw [show (136 : Nat) = 80 + protoPolynomialEncoderSize from rfl,
              ProofLib.memRegion_split a 80 protoPolynomialEncoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_
        apply sepWP_evs_inst w hevs_w
        refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done
    · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_3
      let st3 := M.stepEvents evs3 st2
      have hjoin176_from_40 : memRegion a 136 ∗ memRegion (a + 136#64) 40 ⊢ memRegion a 176 := by
        rw [ProofLib.memRegion_split' (b := a) (n := 136) (k := 40) (b' := a + 136#64) rfl rfl (by decide)]
        exact Entails.refl _
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      have h152 : (a + 136#64) + 16#64 = a + 152#64 := BitVec.add_assoc a 136#64 16#64
      have h160 : (a + 136#64) + 24#64 = a + 160#64 := BitVec.add_assoc a 136#64 24#64
      cases hct1 : st_pb.receivingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
        rw [h144]
        refine sepWP_close_drop
          (fun sf => memRegion a 176 ∗ A.pool lim st3 sf ∗ stackAt s0.sp dropStack96)
          ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · wp_steps
          have hnone40 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 32 ⊢ memRegion (a + 136#64) 40 := by
            rw [← h144]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 136#64)
          refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          wp_done
        · rw [satisfies_sepExists]
          refine ⟨evs2 ++ evs3, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, hevs2.append hevs3⟩, ?_⟩
          have heq_st : M.stepEvents (evs2 ++ evs3) st = st3 := by
            simp only [st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (a + 136#64) pb) (by sep_focus) ?_
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        wp_pull_exists; rename_i g; rw [h144, h152, h160]
        wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 (cap : BitVec 64) :
            ((a + 136#64) ↦₆₄ cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 160#64) 16 ⊢
            memRegion (a + 136#64) 40 := by
          rw [← h144, ← h152, ← h160]
          exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 136#64) cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        refine seq_clean_evs (mid := (blkPl_281).base + 184#64)
          (P_evs := fun evs sm =>
            memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            memRegion (a + 160#64) 16 ∗ A.pool lim (M.stepEvents evs st3) sm ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢
          cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
              BitVec.add_zero, arrayAt, emp_sepConj]
            refine sepWP_vm_evs_nil (fun sm hvm => by
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
            by_vm_steps (
              wp_steps
              refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; sep_ac_rfl) ?_
              wp_done)
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_vm_clean (mid := (blkPl_281).base + 160#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
                A.pool lim st3 s3 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                (memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
                 ((a + 152#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
                 A.live g.ptr (g.cap.toNat * 24) 8 ∗
                 memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                   ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 160#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
                 (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64)
              ?_ ?_
            · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
            · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              rw [← A.pool_of_vmPreserved hvm_loop]
              refine SepWP.mono
                (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr st3 s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
                  hx19_loop hx20_loop hx21_loop hx22_loop) ?_
              intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
              refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
              have hsplit : g.cap.toNat * 24 =
                  (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
                rw [← hsplit]; omega
              have hmr_eq : memRegion g.ptr (g.cap.toNat * 24) =
                  memRegion g.ptr ((bs :: tl).length * 24) ∗
                    memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                      ((g.cap.toNat - (bs :: tl).length) * 24) := by
                rw [hsplit]
                exact ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                  ((g.cap.toNat - (bs :: tl).length) * 24) hbound
              simp only [hcap_ne, ↓reduceIte, hmr_eq]
              exact Entails.of_eq (by sep_ac_rfl)
        · intro evs4 s4 hevs4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4, hx20_4⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_4
          let st4 := M.stepEvents evs4 st3
          by_cases hc : g.cap = 0
          · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_4 ⊢
            refine sepWP_close_drop
              (fun sf => memRegion a 176 ∗ A.pool lim st4 sf ∗ stackAt s0.sp dropStack96)
              ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · wp_steps
              refine SepWP.focus_weaken (hhdr40 0) (by sep_focus) ?_
              refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
              refine SepWP.focus_weaken
                (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                  (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
                (by sep_focus) ?_
              wp_done
            · rw [satisfies_sepExists]
              refine ⟨evs2 ++ evs3 ++ evs4, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, (hevs2.append hevs3).append hevs4⟩, ?_⟩
              have heq_st : M.stepEvents (evs2 ++ evs3 ++ evs4) st = st4 := by
                simp only [st2, st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
          · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpts_cap_lt
            simp only [hc, ↓reduceIte]
            refine sepWP_close_drop
              (fun sf => memRegion a 176 ∗
                A.pool lim (M.stepEvents (evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents (g.cap.toNat * 24) 8) st) sf ∗
                stackAt s0.sp dropStack96)
              ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st5 : M.stepEvents (evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents (g.cap.toNat * 24) 8) st =
                  M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st4 := by
                simp only [st2, st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st5]
              have htail : SepWP ((blkPC_281).rebase (blkPl_281).base H) (s0.readReg64 .lr) s4
                  (memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
                    ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                    (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
                    memRegion (a + 160#64) 16 ∗ A.pool lim st4 s4 ∗
                    (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
                    (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
                  (fun sf Pf =>
                    (Pf ⊢ memRegion a 176 ∗
                      A.pool lim (M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st4) sf ∗
                      stackAt s0.sp dropStack96) ∧
                    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                    AllocCallPreserved s4 sf ∧ CalleeSavedPreserved s0 sf) := by
                wp_steps
                refine SepWP.focus_weaken (hhdr40 g.cap) (by sep_focus) ?_
                refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
                refine SepWP.focus_weaken
                  (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
                  (by sep_focus) ?_
                rw [stackAt_dropStack96_split_bottom s0.sp]
                wp_call hdealloc_fo (g.ptr, g.cap.toNat * 24, 8, st4)
                have hpost4 : AllocCallPreserved s4 sf := by assumption
                rcases hpost4 with ⟨_, _, _, _, _, _, _⟩
                wp_done
              exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_4f, hcs_f⟩ =>
                ⟨hp, hsp_f, htr_f, hacp_4.trans hacp_4f, hcs_f⟩
            · rw [satisfies_sepExists]
              refine ⟨evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents (g.cap.toNat * 24) 8, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, ((hevs2.append hevs3).append hevs4).append
                (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.cap.toNat * 24))⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end PlacedHeaderSent

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2Budget
