/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `VerNe.Chain3` (Block `516`) Part B (`ChainKey` Slice)

Total-correctness (`RustCliAllocBudget M`) verification of the `ChainKey` (`tag = 3`) slice
(`chain3ChainKey_cro_placed_ok`) of `message::merge<Chain> [local#4]` (Block `516`) under
`StoreKit.LibsignalCodeRoLoaded`, re-exporting the `Srk` slice from `Chain3CroBPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
)
open CryptoVerification.RustHeap (RustAlloc vecOf vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarint_encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Record (pbBytes pbVarint pbVarintBody)
open CryptoVerification.E2E.Record.DeserializeSeed (
  ckEnc_length_bounds_seedChain memRegion24_split_ck_seedChain
  pbVarintBody_u32_eq_encodeVarint_seedChain sep_ac_seedChain
  sliceCursorAfter_append_eq_seedChain
)
open Proofs.libsignal.Hooks2 (
  ule_ofNat_of_gt_false_seedChain62 ult_ofNat_of_gt_true_seedChain62
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG ChainMergeGenGhost chainGAfter
  pbBytes_lt128_eq_seedChain pbBytes_ptr_advance_seedChain prostMsgKeyAt
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG (
  chainField_ck_enc_eq chainField_tag_three_info chainGAfter_succ combine_tag3_cursor
  payload_append_eq_pfx_rem pfx_k pfx_k_succ rem_k rem_k_eq_cons
)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_516 blkPl_516 lsProg_516)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  C3aKeep Chain3InnerLoopRegs SepWPp.of_sepWP_lscl_c3
  c3a_decodeVarint_1a c3a_decodeVarint_lt128 c3a_hdr_combine
  c3a_ofNat_add_sub_left c3a_ule_ofNat_add_right
  c3ck_pbVarint1_eq c3ck_pbVarint1_ptr_advance c3ck_pointsTo_08_combine
  c3ck_regs_after_call c3ck_zeroExtend64_setWidth32
  c3k3c_pointsTo_12_combine
  chain3GAt chain3GAt_apply_ck_eq_ext chain3GAt_ck_none_eq_ext
  chain3PCPlacedAtW chain3SavedRegs chain3VecAt chainMerge3SubStackX
  default_cells_entail_chain3VecAt sp0_aligned_of_sub_240_aligned
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (ChainPrefixEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux (
  sepWPp_mono_pre_c3
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget (
  Chain3CalleesCroPlacedW Chain3ChainKeyCroStmt SepWPp.bind_lscro
  c3_dv_call_cro segStepG_keep_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudgetAux (
  c3_bm_call_cro c3_bm_call_srk_cro c3_bm_call_vec_cro c3a_dv_cro
  chain3Srk_cro_placed_ok chainPrefixEnv_enc_le_payload chainPrefixEnv_step_field
  fitsEnv_rem_at_field pool_eq_of_vm_c3 sepWPp_focus_pre_false_c3
  step_chain3Tag1_cro step_chain3Tag2_cro
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudgetAux (
  c3_bm_call_cro c3_bm_call_srk_cro c3_bm_call_vec_cro c3a_dv_cro
  chain3Srk_cro_placed_ok chainPrefixEnv_enc_le_payload chainPrefixEnv_step_field
  fitsEnv_rem_at_field pool_eq_of_vm_c3 sepWPp_focus_pre_false_c3
  step_chain3Tag1_cro step_chain3Tag2_cro
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## VM-Preserving Straight-Line Segments for `ChainKey` (`tag = 3`) -/

private theorem c3a_phaseA_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64) (bs : List (BitVec 8)) (outer : Nat)
    (hgt : outer < bs.length) (hlen : bs.length < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 0xa8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 0xf0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 outer)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 → s1.status = .Running → s1.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl s1.mem → VmPreserved s0 s1 → s1.trace = s_init.trace →
      s1.readReg64 .lr = lsmpl.base 516 + 0xc0#64 → s1.readReg64 .x0 = bufRef →
      C3aKeep s0 s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hgt hlen
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hgt hlen
  change s0.pc = (blkPl_516).base + 0xa8#64 at hpc
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outer := hx21
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl1 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

private theorem c3a_phaseC_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (A_rep : RustAlloc) (a bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s_init s2 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s2.pc = lsmpl.base 516 + 0xc0#64)
    (hrun : s2.status = .Running)
    (hsp : s2.sp = sp0 - 0xf0#64)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (htr : s2.trace = s_init.trace)
    (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = 0x1a#64)
    (hx19 : s2.readReg64 .x19 = bufRef)
    (hx20 : s2.readReg64 .x20 = a)
    (hx23 : s2.readReg64 .x23 = 1#64)
    (hnext : ∀ (s3 : State),
      s3.pc = lsmpl.base 515 → s3.status = .Running → s3.sp = sp0 - 0xf0#64 →
      LibsignalCodeLoaded lsmpl s3.mem → VmPreserved s2 s3 → s3.trace = s_init.trace →
      s3.readReg64 .lr = lsmpl.base 516 + 0x224#64 → s3.readReg64 .x0 = bufRef →
      C3aKeep s2 s3 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s3
        ((chain3VecAt A_rep (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s2
      ((((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24) ∗ F) Q Qp := by
  change s2.pc = (blkPl_516).base + 0xc0#64 at hpc
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = 0x1a#64 := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = a := hx20
  have h23 : s2.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  rw [memRegion24_split_ck_seedChain a]
  unfold noneCap
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w50
  apply SepWP.exists_elim; intro w58
  apply SepWP.exists_elim; intro w60
  iterate 24 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl3
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl3 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  have hvec := default_cells_entail_chain3VecAt A_rep (a + 0x48#64)
  have h48_8 : (a + 0x48#64) + 8#64 = a + 0x50#64 := by bv_omega
  have h48_16 : (a + 0x48#64) + 16#64 = a + 0x58#64 := by bv_omega
  rw [h48_8, h48_16] at hvec
  refine Entails.trans (sep_ac_seedChain (Q :=
    (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
      (((a + 0x60#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x64#64) 4 ∗ F)) (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hvec) ?_
  exact sep_ac_seedChain (by ac_rfl)

private theorem c3a_phaseE_placed_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (ck after : List (BitVec 8))
    (hlen : ck.length + after.length < 2 ^ 62)
    {ret : BitVec 64} {s_init s4 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s4.pc = lsmpl.base 516 + 0x224#64)
    (hrun : s4.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (htr : s4.trace = s_init.trace)
    (hx0 : s4.readReg64 .x0 = 0#64)
    (hx1 : s4.readReg64 .x1 = BitVec.ofNat 64 ck.length)
    (hx19 : s4.readReg64 .x19 = bufRef)
    (hnext : ∀ (s5 : State),
      s5.pc = lsmpl.base 516 + 0x368#64 → s5.status = .Running → s5.sp = s4.sp →
      LibsignalCodeLoaded lsmpl s5.mem → VmPreserved s4 s5 → s5.trace = s_init.trace →
      s5.readReg64 .x25 = BitVec.ofNat 64 after.length →
      C3aKeep s4 s5 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s5
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (ck ++ after)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s4
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (ck ++ after)) ∗ F) Q Qp := by
  have hlen_app : (ck ++ after).length = ck.length + after.length := List.length_append
  have hule := c3a_ule_ofNat_add_right (m := ck.length) (k := after.length) hlen
  have hsub := c3a_ofNat_add_sub_left ck.length after.length
  change s4.pc = (blkPl_516).base + 0x224#64 at hpc
  have h0 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s4.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 ck.length := hx1
  have h19 : s4.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x368#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x368#64)
  intro m_strip
  unfold sliceCursorAt
  rw [hlen_app]
  simp only [sepConj_assoc]
  iterate 5 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s4 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl5
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    hcl5 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  rw [hlen_app]
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_c3ck_ihead_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a slot ptr : BitVec 64) (outerTailLen : Nat) (b0 : BitVec 8)
    (rem1 afterCk : List (BitVec 8))
    (hlen_gt : afterCk.length < (b0 :: rem1).length) (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {ret : BitVec 64} {s_init s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x368#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = lsmpl.base 516 + 0x380#64 → s1.readReg64 .x0 = bufRef →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_lt
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x368#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 afterCk.length := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_c3ck_key1_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x380#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x08#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = lsmpl.base 516 + 0x3d0#64 → s1.readReg64 .x0 = bufRef →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x380#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x08#64 := hx1
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  iterate 13 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩

private theorem step_c3ck_store_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat) (v : BitVec 64) (w : BitVec 32)
    {ret : BitVec 64} {s_init s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x3d0#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = v)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x368#64 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 (((a + 0x60#64) ↦₃₂ v.setWidth 32) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s (((a + 0x60#64) ↦₃₂ w) ∗ F) Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x3d0#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = v := hx1
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x368#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x368#64)
  intro m_strip
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

private theorem step_c3k3c_dispatch_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x380#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x12#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 514 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = lsmpl.base 516 + 0x3bc#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x380#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 15 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩

private theorem step_c3k3c_ret_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x3bc#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x368#64 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x3bc#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x368#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x368#64)
  intro m_strip
  iterate 4 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩

private theorem step_chain3_seg3d_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 0x368#64)
    (hrun : s0.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0xa8#64 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s0 s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s0.pc = (blkPl_516).base + 0x368#64 at hpc
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 afterCk.length := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s0.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s0.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0xa8#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0xa8#64)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 7 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

/-! ## Budget-Threaded `ChainKey` Sub-Slices and `chain3ChainKey_cro_placed_ok` -/

theorem step_seg3a_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hck_lt : ck_body.length < 128) (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : 2 + (ck_body.length + afterCk.length) < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx29 : s0.readReg64 .x29 = sp0 - 80#64) (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 outerTailLen)
    (hx22 : s0.readReg64 .x22 = sp0 - 232#64) (hx23 : s0.readReg64 .x23 = 1#64)
    (hx24 : s0.readReg64 .x24 = 104#64) (hx26 : s0.readReg64 .x26 = s_init.readReg64 .x26)
    (hx27 : s0.readReg64 .x27 = s_init.readReg64 .x27)
    (hx28 : s0.readReg64 .x28 = s_init.readReg64 .x28)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 72#64) [] ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
          memRegion (a + 100#64) 4 ∗ (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hlenA : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hgtA : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlenB : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hlenE : ck_body.length + afterCk.length < 2 ^ 62 := by omega
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      ((((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24) ∗ A.pool lim st_cur s0 ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine c3a_phaseA_placed_vm bufRef slot ptr sp0 _ outerTailLen hgtA hlenA
    hpc hrun hsp hcl htr hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hk1
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      A.pool lim st_cur s1 ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      ((((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24) ∗ F))
    (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact sep_ac_seedChain (by ac_rfl)) ?_
  refine c3a_dv_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x1a#64 0x1a#8
    (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) (c3a_decodeVarint_1a _) hlenA
    hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 ?_
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
  have hk2 : C3aKeep s0 s2 := hk1.trans (.of_calleeSaved hcs2)
  refine sepWPp_mono_pre_c3
    (P' := (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 24) ∗
      (((bufRef ↦₆₄ slot) ∗ (ptr ↦₈ 0x1a#8) ∗
        sliceCursorAt slot (ptr + 1#64) (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim st_cur s2 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine c3a_phaseC_placed_vm A.repAlloc a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
    (hk2.1.trans hx19) (hk2.2.1.trans hx20) (hk2.2.2.2.2.1.trans hx23) ?_
  intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hk3'
  have hk3 : C3aKeep s0 s3 := hk2.trans hk3'
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot (ptr + 1#64) (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      A.pool lim st_cur s3 ∗
      stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      ((ptr ↦₈ 0x1a#8) ∗ (chain3VecAt A.repAlloc (a + 72#64) [] ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
        memRegion (a + 100#64) 4) ∗ F))
    (by rw [pool_eq_of_vm_c3 A lim st_cur hvm3]; exact sep_ac_seedChain (by ac_rfl)) ?_
  refine c3a_dv_cro hC bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 548#64)
    (BitVec.ofNat 64 ck_body.length) (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
    (c3a_decodeVarint_lt128 ck_body.length hck_lt _) hlenB
    hpc3 hrun3 hsp3 halign hcl3 htr3 hlr3 hx0_3 ?_
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
  have hk4 : C3aKeep s0 s4 := hk3.trans (.of_calleeSaved hcs4)
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 1#64 + 1#64) (ck_body ++ afterCk)) ∗
      (((ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        A.pool lim st_cur s4 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗
        (ptr ↦₈ 0x1a#8) ∗ (chain3VecAt A.repAlloc (a + 72#64) [] ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
          memRegion (a + 100#64) 4) ∗ F))
    (sep_ac_seedChain (by ac_rfl)) ?_
  refine c3a_phaseE_placed_vm bufRef slot (ptr + 1#64 + 1#64) ck_body afterCk hlenE
    hpc4 hrun4 hcl4 htr4 hx0_4 hx1_4 (hk4.1.trans hx19) ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hx25_5 hk5'
  have hk5 : C3aKeep s0 s5 := hk4.trans hk5'
  obtain ⟨k19, k20, k21, k22, k23, k24, k26, k27, k28, k29, kv⟩ := hk5
  refine sepWPp_mono_pre_c3 ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 (kv.trans hvregs)
    ⟨hsp5.trans hsp4, k29.trans hx29, k19.trans hx19, k20.trans hx20, k21.trans hx21,
     k22.trans hx22, k23.trans hx23, k24.trans hx24, hx25_5, k26.trans hx26, k27.trans hx27,
     k28.trans hx28⟩)
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by bv_omega
  rw [pool_eq_of_vm_c3 A lim st_cur hvm5, hptr2, ← c3a_hdr_combine ptr ck_body.length]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_seg3b_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 872#64) (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64) (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((a + 96#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((a + 96#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    have hlen0 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    rw [hpb0, List.nil_append]
    refine sepWPp_mono_pre_c3 ?_ (hnext s0 hpc hrun hcl htr hvregs hregs)
    rw [hpb0, pointsToBytes_nil, hlen0, BitVec.add_zero]
    simp only [emp_sepConj]
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ afterCk)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ afterCk) = 0x08#8 :: rem1 := by
      rw [c3ck_pbVarint1_eq i.toNat hi_pos]; simp [rem1, List.cons_append]
    have hlen_gt : afterCk.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x08#8 :: rem1)) ∗
        (((a + 96#64) ↦₃₂ 0#32) ∗ A.pool lim st_cur s0 ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3ck_ihead_placed_vm sp0 bufRef a slot ptr outerTailLen 0x08#8 rem1
      afterCk hlen_gt hlen_cons_lt hpc hrun hcl htr hvregs hregs ?_
    intro s1 hpc1 hrun1 hcl1 hvm1 htr1 hvregs1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x08#8] ++ rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (((a + 96#64) ↦₃₂ 0#32) ∗ F))
      (by
        rw [pool_eq_of_vm_c3 A lim st_cur hvm1, show (0x08#8 :: rem1) = [0x08#8] ++ rem1 from rfl]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 896#64)
      0x08#64 [0x08#8] rem1 rfl hlen_cons_lt hpc1 hrun1 hregs1.1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    obtain ⟨hregs2, hvregs2⟩ := c3ck_regs_after_call hregs1 hvregs1 hsp2 hcs2
    refine step_c3ck_key1_placed_vm sp0 bufRef a outerTailLen afterCk.length
      hpc2 hrun2 hcl2 htr2 hvregs2 hregs2 hx0_2 hx1_2 ?_
    intro s3 hpc3 hrun3 hcl3 hvm3 htr3 hvregs3 hlr3 hx0_3 hregs3
    have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    have hdv2 : decodeVarint (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)) =
        some (i.zeroExtend 64, rest ++ afterCk) := by
      rw [pbVarintBody_u32_eq_encodeVarint_seedChain i]
      exact decodeVarint_encodeVarint (i.zeroExtend 64) (rest ++ afterCk)
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)) ∗
        A.pool lim st_cur s3 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        ((ptr ↦ₛ [0x08#8]) ∗ ((a + 96#64) ↦₃₂ 0#32) ∗ F))
      (by
        rw [pool_eq_of_vm_c3 A lim st_cur hvm3,
          show BitVec.ofNat 64 ([0x08#8] : List (BitVec 8)).length = 1#64 from rfl]
        dsimp only [rem1]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 976#64) (i.zeroExtend 64) (pbVarintBody 5 i.toNat) (rest ++ afterCk)
      hdv2 hrem1_lt hpc3 hrun3 hregs3.1 halign hcl3 htr3 hlr3 hx0_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hx1_4
    obtain ⟨hregs4, hvregs4⟩ := c3ck_regs_after_call hregs3 hvregs3 hsp4 hcs4
    refine sepWPp_mono_pre_c3
      (P' := ((a + 96#64) ↦₃₂ 0#32) ∗
        ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x08#8]) ∗ ((ptr + 1#64) ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot
            (ptr + 1#64 + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) (rest ++ afterCk) ∗
          A.pool lim st_cur s4 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3ck_store_placed_vm sp0 bufRef a outerTailLen afterCk.length
      (i.zeroExtend 64) 0#32 hpc4 hrun4 hcl4 htr4 hvregs4 hregs4 hx0_4 hx1_4 ?_
    intro s5 hpc5 hrun5 hcl5 hvm5 htr5 hvregs5 hregs5
    refine sepWPp_mono_pre_c3 ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5)
    rw [pool_eq_of_vm_c3 A lim st_cur hvm5, c3ck_zeroExtend64_setWidth32 i,
      c3ck_pbVarint1_ptr_advance ptr i.toNat hi_pos, ← c3ck_pointsTo_08_combine ptr i.toNat hi_pos]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_seg3c_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : k.length < 128) (hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st_cur (BoundedRustEvs 3 (2 * k.length + 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 872#64) (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64) (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (sm : State) (evs_bm : List AllocEvent),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      BoundedRustEvs 3 (2 * k.length + 8) evs_bm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A.repAlloc (a + 72#64) k ∗ (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 72#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ afterCk
  have hcons_eq : pbBytes 2 k ++ afterCk = 0x12#8 :: rem1 := by
    rw [pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt]
    simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => LibsignalCodeLoaded lsmpl s3.mem ∧ s3.trace = s_init.trace ∧
      calleeSavedVRegs s3 = calleeSavedVRegs s_init ∧
      s3.readReg64 .lr = lsmpl.base 516 + 956#64 ∧ (s3.readReg64 .x0).setWidth 8 = 2#8 ∧
      s3.readReg64 .x1 = a + 72#64 ∧ s3.readReg64 .x2 = bufRef ∧
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s3 ∧
      (P3 ⊢ (chain3VecAt A.repAlloc (a + 72#64) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦ₛ [0x12#8]) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x12#8 :: rem1)) ∗
        (chain3VecAt A.repAlloc (a + 72#64) [] ∗ A.pool lim st_cur s0 ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (sep_ac_seedChain (by ac_rfl)) ?_
    refine step_c3ck_ihead_placed_vm sp0 bufRef a slot ptr outerTailLen 0x12#8 rem1
      afterCk hlen_gt hlen_cons_lt hpc hrun hcl htr hvregs hregs ?_
    intro s1 hpc1 hrun1 hcl1 hvm1 htr1 hvregs1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x12#8] ++ rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc (a + 72#64) [] ∗ F))
      (by
        rw [pool_eq_of_vm_c3 A lim st_cur hvm1, show (0x12#8 :: rem1) = [0x12#8] ++ rem1 from rfl]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 896#64)
      0x12#64 [0x12#8] rem1 rfl hlen_cons_lt hpc1 hrun1 hregs1.1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    obtain ⟨hregs2, hvregs2⟩ := c3ck_regs_after_call hregs1 hvregs1 hsp2 hcs2
    refine step_c3k3c_dispatch_placed_vm sp0 bufRef a outerTailLen afterCk.length
      hpc2 hrun2 hcl2 htr2 hvregs2 hregs2 hx0_2 hx1_2 ?_
    intro s3 hpc3 hrun3 hcl3 hvm3 htr3 hvregs3 hlr3 hx0_3 hx1_3 hx2_3 hregs3
    refine SepWPp.done hpc3 hrun3 ⟨hcl3, htr3, hvregs3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3,
      show BitVec.ofNat 64 ([0x12#8] : List (BitVec 8)).length = 1#64 from rfl]
    exact sep_ac_seedChain (by ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hcl3, htr3, hvregs3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ afterCk).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3_bm_call_vec_cro hC (a + 72#64) bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 956#64)
      k afterCk hk_lt hrem1_lt hfit hcro3 hpc3 hrun3 hregs3.1 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 evs_bm hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4 hbnd_bm
    obtain ⟨hregs4, hvregs4⟩ := c3ck_regs_after_call hregs3 hvregs3 hsp4 hcs4
    refine step_c3k3c_ret_placed_vm sp0 bufRef a outerTailLen afterCk.length
      hpc4 hrun4 hcl4 htr4 hvregs4 hregs4 hx0_4 ?_
    intro s5 hpc5 hrun5 hcl5 hvm5 htr5 hvregs5 hregs5
    refine sepWPp_mono_pre_c3 ?_ (hnext s5 evs_bm hpc5 hrun5 hcl5 htr5 hvregs5 hregs5 hbnd_bm)
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents evs_bm st_cur) hvm5,
      pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← c3k3c_pointsTo_12_combine ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem chain3ChainKey_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks) :
    Chain3ChainKeyCroStmt M A lim ext := by
  intro hC x st R s0 k s hk htag ⟨hcro, hs⟩
  refine segStepG_keep_cro hcro ?_
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen_lt, hfit, evs, hevs_pfx, hmem⟩
  intro hL
  have hfit_fld := fitsEnv_rem_at_field hk hevs_pfx hfit
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_aligned hsp_sub_align
  obtain ⟨⟨i, key, hck_some, hfl_eq⟩, hck_none⟩ := chainField_tag_three_info x.c k hk htag
  have hkey_len : key.length = 32 := hcOk.2.2.1 (i, key) hck_some
  have hkey_lt : key.length < 128 := by omega
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey_len
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 key
  let ck_body : List (BitVec 8) := b3b ++ b3c
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body, b3b, b3c]; omega
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let pfx : List (BitVec 8) := pfx_k x.c k
  let afterCk : List (BitVec 8) := rem_k x.c (k + 1) x.tail
  have hfl_enc : (x.c.fields[k]'hk).enc = b3a ++ (b3b ++ b3c) := by
    rw [hfl_eq]; exact chainField_ck_enc_eq i hkey_len
  have h3_le : 3 ≤ 8 * (x.c.fields[k]'hk).enc.length := by
    rw [hfl_enc]
    simp only [b3a, List.length_append, List.length_cons, List.length_nil]
    omega
  have hsz_le : 2 * key.length + 8 ≤ 256 * (x.c.payload.length + 16) := by omega
  have hfit_bm : FitsEnv M lim (M.stepEvents evs st) (BoundedRustEvs 3 (2 * key.length + 8)) :=
    FitsEnv.mono (fun _ h => BoundedRustEvs.mono h3_le hsz_le h) hfit_fld
  have hrem_k : rem_k x.c k x.tail = 0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk) := by
    rw [rem_k_eq_cons x.c k x.tail hk, hfl_enc]; dsimp [b3a, ck_body]
  have hpay_eq : x.c.payload ++ x.tail = pfx ++ rem_k x.c k x.tail :=
    payload_append_eq_pfx_rem x.c k x.tail
  have houter_le : x.tail.length ≤ afterCk.length := by
    dsimp [afterCk, rem_k]; simp only [List.length_append]; omega
  have hlen_lt3a : 2 + (ck_body.length + afterCk.length) < 2 ^ 62 := by
    have h1 := hlen_lt; rw [hpay_eq, hrem_k] at h1
    simp only [List.length_append, List.length_cons] at h1; omega
  have hlen_lt3b : (b3b ++ b3c ++ afterCk).length < 2 ^ 62 := by
    have h1 : (b3b ++ b3c ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
    omega
  have hlen_lt3c : (b3c ++ afterCk).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_lt3b ⊢; omega
  let c0 : ChainG := chainGAfter x.c k
  let ptr3a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr3b : BitVec 64 := ptr3a + 2#64
  let ptr3c : BitVec 64 := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd : BitVec 64 := ptr3c + BitVec.ofNat 64 b3c.length
  have hcur_init :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) := by
    change sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rem_k x.c k x.tail) = _
    rw [hpay_eq, sliceCursorAfter_append_eq_seedChain x.slot x.ptr pfx (rem_k x.c k x.tail), hrem_k]
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 72#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 80#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 24#64) c0.priv ∗
          vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨ chain3GAt A.repAlloc x.a c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool lim (M.stepEvents evs st) s ∗
      stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R at hmem
    rw [chain3GAt_ck_none_eq_ext A.repAlloc x.a c0 hck_none, hcur_init] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 72#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 80#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 24#64) c0.priv ∗
          vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0))
      (fun sf Pf => ∃ evs_bm : List AllocEvent,
        ChainPrefixEnv x.c (k + 1) (evs ++ evs_bm) ∧
        LibsignalCodeLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 sf ∧
        (Pf ⊢ chain3GAt A.repAlloc x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          A.pool lim (M.stepEvents (evs ++ evs_bm) st) sf ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      (fun _ _ => False) := by
    refine SepWPp.bind_lscro (mid := lsmpl.base 516 + 872#64)
      (Q1 := fun s5 P5 => LibsignalCodeLoaded lsmpl s5.mem ∧ s5.trace = s0.trace ∧
        calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 s5 ∧
        (P5 ⊢ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 72#64) [] ∗
          sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
          A.pool lim (M.stepEvents evs st) s5 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4 ∗
            chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 24#64) c0.priv ∗
            vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64) c0.keys ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))) hcro ?_ ?_
    · refine step_seg3a_cro hC x.a x.bufRef x.slot ptr3a s0.sp ck_body afterCk x.tail.length
        hck_lt houter_le hlen_lt3a hpc hrun hsp hsp0_align hcl htr hvregs
        hx29 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 ?_
      intro s4 hpc4 hrun4 hcl4 htr4 hvregs4 hregs4
      refine sepWPp_mono_pre_c3
        (P' := (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 96#64) ↦₃₂ 0#32) ∗
          sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
          A.pool lim (M.stepEvents evs st) s4 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ chain3VecAt A.repAlloc (x.a + 72#64) [] ∗ memRegion (x.a + 100#64) 4 ∗
            chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 24#64) c0.priv ∗
            vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64) c0.keys ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))
        (by
          have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
            simp [ck_body, b3b, b3c, List.append_assoc]
          dsimp only [ptr3b, b3a]; rw [hck_eq]; exact sep_ac_seedChain (by ac_rfl)) ?_
      refine step_seg3b_cro hC x.a x.bufRef x.slot ptr3b s0.sp i b3c afterCk x.tail.length
        hlen_lt3b hpc4 hrun4 hsp0_align hcl4 htr4 hvregs4 hregs4 ?_
      intro s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5
      refine SepWPp.done hpc5 hrun5 ⟨hcl5, htr5, hvregs5, hregs5, ?_⟩
      dsimp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)
    · intro s5 P5 hpc5 hrun5 hcro5 ⟨hcl5, htr5, hvregs5, hregs5, hent5⟩
      refine sepWPp_mono_pre_c3 hent5 ?_
      refine step_seg3c_cro hC x.a x.bufRef x.slot ptr3c s0.sp key afterCk x.tail.length
        hkey_lt hlen_lt3c hfit_bm hcro5 hpc5 hrun5 hsp0_align hcl5 htr5 hvregs5 hregs5 ?_
      intro s6 evs_bm hpc6 hrun6 hcl6 htr6 hvregs6 hregs6 hbnd_bm
      have hevs_next : ChainPrefixEnv x.c (k + 1) (evs ++ evs_bm) :=
        chainPrefixEnv_step_field hk hevs_pfx (BoundedRustEvs.mono h3_le hsz_le hbnd_bm)
      refine sepWPp_mono_pre_c3
        (P' := (((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot ptrEnd afterCk ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ (ptr3c ↦ₛ b3c) ∗ vecU8 A.repAlloc (x.a + 72#64) key ∗
            ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4 ∗ chain3VecAt A.repAlloc x.a c0.srk ∗
            chain3VecAt A.repAlloc (x.a + 24#64) c0.priv ∗
            vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64) c0.keys ∗
            A.pool lim (M.stepEvents evs_bm (M.stepEvents evs st)) s6 ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))
        (by dsimp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
      refine step_chain3_seg3d_placed_vm x.a x.bufRef x.slot ptrEnd s0.sp afterCk x.tail.length
        hpc6 hrun6 hcl6 htr6 hvregs6 hregs6 ?_
      intro sf hpcf hrunf hclf hvmf htrf hvregsf hregsf
      refine SepWPp.done hpcf hrunf ⟨evs_bm, hevs_next, hclf, htrf, hvregsf, hregsf, ?_⟩
      have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
        rw [chainGAfter_succ x.c k hk, hfl_eq]
      rw [hc_succ, chain3GAt_apply_ck_eq_ext A.repAlloc x.a c0 i key,
        pool_eq_of_vm_c3 A lim (M.stepEvents evs_bm (M.stepEvents evs st)) hvmf,
        ← M.stepEvents_append evs evs_bm st]
      have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
      dsimp only at hcur_end
      have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
        rw [← hfl_enc, ← pfx_k_succ x.c k hk]
        exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
      rw [htotal_end] at hcur_end
      change _ ⊢ (chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 24#64) c0.priv ∗
          vecOf A.repAlloc 104 8 (fun mk b => prostMsgKeyAt A.repAlloc mk b) (x.a + 48#64) c0.keys ∗
          vecU8 A.repAlloc (x.a + 72#64) key ∗ ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
        A.pool lim (M.stepEvents (evs ++ evs_bm) st) sf ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0
      rw [← hcur_end]; dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd]; exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, evs_bm, hevs_next, hclf, htrf, hvregsf, hregsf, hentf⟩ |
    ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, _, hx26f, hx27f, hx28f⟩
    have half : sf.spAligned = true := by rw [State.spAligned, hspf, ← hsp]; exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hclf, hspf, half, hx29f, hx19f, hx20f,
      hx21f, hx22f, hx23f, hx24f, hx26f, hx27f, hx28f, hcOk, hlen_lt, hfit,
      evs ++ evs_bm, hevs_next, hmemf⟩⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudget
