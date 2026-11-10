/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 `Authenticator` Tail

Relocatable Block-`333` `auth.macKey` cloning (`+8756 -> +9804`) and protobuf `auth` buffer
deallocation (`+9804 -> +4016`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (cap_add_one_beq_zero_false vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved ofNat_beq_zero_false sp_sub_2400_align stackAt_encoderFromPb_split_allocHook
   v1c_bv_add_add_lit v1c_bv_sub_sub_lit vecU8Payload_of_nil vecU8Payload_pos
   vecU8Payload_pos_dealloc vecU8Payload_pos_unpack)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st
   v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_placedHooks)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1c_bv_add_add_lit v1c_bv_sub_sub_lit

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## `Authenticator::from_pb` MAC-Key Clone (`+8756 -> +9804`) and Buffer Deallocation (`+9804 -> +4016`) -/

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+8756 -> +9804`) in Variant 1:
    clones `auth.macKey` into `[fsp + 184] := pa2` (or `1#64` if empty) under
    `FitsEvents M lim st (authKeyCloneEvents auth.macKey)` with zero OOM/panic branches. -/
theorem v1_auth_from_pb_step2_8756_9804_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA pa1 : BitVec 64)
    (u8 u56 u64 u80 u88 w184 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8756#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 9804#64) s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
       A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        ∃ pa2 : BitVec 64,
          (P2 ⊢
            stackAt fsp encoderFromPbStack ∗
            ((fsp + 184#64) ↦₆₄ pa2) ∗
            vecCapPtrDealloc A.repAlloc u80 u88 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame) ∧
          s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x21 = u8 ∧
          s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
          s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
          s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
          TraceCalleeSaved s2 s0) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents auth.macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hm_nil] at hx9 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx9 ⊢
    change s.pc = (blkPl_333).base + 8756#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9804#64) s _ _
    refine SepWP.mono
      (P := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
        vecU8Payload A.repAlloc u80 u88 [] ∗ A.pool lim st s ∗ Frame)
      (post := fun s2 P2 =>
        (P2 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
          vecCapPtrDealloc A.repAlloc u80 u88 ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          A.pool lim st s2 ∗ Frame) ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = u8 ∧
        s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
        s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
        TraceCalleeSaved s2 s0) ?_
      fun s2 P2 _ _ ⟨hP2, hregs⟩ => ⟨1#64, hP2, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 9804#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc u80 u88 []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc u80 u88 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        A.pool lim st sc ∗ Frame by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : auth.macKey.isEmpty = false := by
      cases h : auth.macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents auth.macKey = rustAllocEvents auth.macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (vecU8Payload_pos_unpack A.repAlloc u80 u88 auth.macKey hm_pos)))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
          (⌜auth.macKey.length ≤ u80.toNat ∧ u80.toNat < 2 ^ 63 ∧
            u88 ≠ 0#64 ∧ u80 ≠ 0#64⌝ ∗
           (A.repAlloc.live u88 u80.toNat 1 ∗ (u88 ↦ₛ auth.macKey) ∗
            memRegion (u88 + BitVec.ofNat 64 auth.macKey.length)
              (u80.toNat - auth.macKey.length))) ∗
          A.pool lim st s ∗ Frame =
        ⌜auth.macKey.length ≤ u80.toNat ∧ u80.toNat < 2 ^ 63 ∧
          u88 ≠ 0#64 ∧ u80 ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
         A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ auth.macKey) ∗
         memRegion (u88 + BitVec.ofNat 64 auth.macKey.length)
           (u80.toNat - auth.macKey.length) ∗
         A.pool lim st s ∗ Frame) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
      sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk auth.macKey.length 1 := ⟨⟨hm_pos, hpow1, hm_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s.pc = (blkPl_333).base + 8756#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9804#64) s _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (auth.macKey.length, 1, st)
    have hoom1 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom1_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom1
    have hacp_alloc : AllocCallPreserved s sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, u88, auth.macKey)
    have hacp_mc : AllocCallPreserved s sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := ‹sf.sp = s.sp›.trans hsp
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun s2 P2 =>
        (P2 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ sf_1.readReg64 .x0) ∗
          vecCapPtrDealloc A.repAlloc u80 u88 ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length)
            (sf_1.readReg64 .x0) auth.macKey ∗
          A.pool lim (M.stepEvents (rustAllocEvents auth.macKey.length 1) st) s2 ∗ Frame) ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = u8 ∧
        s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
        s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
        TraceCalleeSaved s2 s0) ?_
      fun s2 P2 _ _ ⟨hP2, hregs⟩ => ⟨sf_1.readReg64 .x0, hP2, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 9804#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc u80 u88 auth.macKey
      hm_le hm_cap hptr1 hcap1_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) auth.macKey
      hm_pos hm_lt63 hoom1
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      simp only [arm64_norm] at hd hp ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live u88 u80.toNat 1 ∗ (u88 ↦ₛ auth.macKey) ∗
         memRegion (u88 + BitVec.ofNat 64 auth.macKey.length)
           (u80.toNat - auth.macKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) auth.macKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ auth.macKey)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        ((fsp + 184#64) ↦₆₄ sf_1.readReg64 .x0) ∗
        A.pool lim (M.stepEvents (rustAllocEvents auth.macKey.length 1) st) sc ∗ Frame by
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Direct `SepWP` `auth.macKey` clone (`+8756 -> +9804`) under `FromPbAllocHooksBudget`. -/
theorem v1_auth_from_pb_step2_8756_9804_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA pa1 : BitVec 64)
    (u8 u56 u64 u80 u88 w184 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8756#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 9804#64) s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
       A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        ∃ pa2 : BitVec 64,
          (P2 ⊢
            stackAt fsp encoderFromPbStack ∗
            ((fsp + 184#64) ↦₆₄ pa2) ∗
            vecCapPtrDealloc A.repAlloc u80 u88 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame) ∧
          s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x21 = u8 ∧
          s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
          s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
          s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
          TraceCalleeSaved s2 s0) :=
  v1_auth_from_pb_step2_8756_9804_of_placedHooks hA.toPlacedBudget st s0 s fsp out pbA pa1
    u8 u56 u64 u80 u88 w184 auth Frame hfits hfsp_align hpc hrun hsp hx19 hx21 hx22 hx23
    hx24 hx25 hx26 hx27 hx28 hx9 htr

theorem v1_auth_from_pb_step2_8756_9804_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (target_pc fsp out pbA pa1 : BitVec 64)
    (u8 u56 u64 u80 u88 w184 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (post Qp : State → SepProp → Prop)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8756#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = lsmpl.base 333 + 9804#64 →
      s2.status = .Running →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x21 = u8 ∧
       s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
       s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
       s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         vecCapPtrDealloc A.repAlloc u80 u88 ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame)
        post Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
       A.pool lim st s ∗ Frame)
      post Qp := by
  have hstep2 := v1_auth_from_pb_step2_8756_9804_placed hA st s0 s fsp out pbA pa1
    u8 u56 u64 u80 u88 w184 auth Frame hfits hfsp_align hpc hrun hsp hx19 hx21 hx22 hx23
    hx24 hx25 hx26 hx27 hx28 hx9 htr
  exact SepWPp.seq_frozen (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
    (SepWP.mono hstep2 fun s2 _P2 hpc2 hrun2 ⟨pa2, hP2, hregs2⟩ _ =>
      SepWPp.weaken_pre hP2 (hnext pa2 s2 hpc2 hrun2 hregs2))

theorem v1_auth_from_pb_step2_8756_9804_placed_lscl_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (target_pc fsp out pbA pa1 : BitVec 64)
    (u8 u56 u64 u80 u88 w184 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (post Qp : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8756#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = lsmpl.base 333 + 9804#64 →
      s2.status = .Running →
      LibsignalCodeLoaded lsmpl s2.mem →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x21 = u8 ∧
       s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
       s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x26 = pa1 ∧
       s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = u64 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         vecCapPtrDealloc A.repAlloc u80 u88 ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame)
        post Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
       A.pool lim st s ∗ Frame)
      post Qp := by
  have hstep2 := v1_auth_from_pb_step2_8756_9804_placed hA st s0 s fsp out pbA pa1
    u8 u56 u64 u80 u88 w184 auth Frame hfits hfsp_align hpc hrun hsp hx19 hx21 hx22 hx23
    hx24 hx25 hx26 hx27 hx28 hx9 htr
  exact SepWPp.seq_frozen (fun _ _ => LibsignalCodeLoaded.of_keepsFrozen) hcl
    (SepWP.mono hstep2 fun s2 _P2 hpc2 hrun2 ⟨pa2, hP2, hregs2⟩ hcl2 =>
      SepWPp.weaken_pre hP2 (hnext pa2 s2 hpc2 hrun2 hcl2 hregs2))

/-- `Authenticator::from_pb` segment (`+9804 -> +4016`) in Variant 1:
    deallocates `auth.rootKey` and `auth.macKey` protobuf buffers under explicit
    Block-`333` `__rust_dealloc` contract (`FreeOnlyEvs`) and sets up registers for `+4016`. -/
theorem v1_auth_from_pb_step3_9804_4016_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out pbA pa1 : BitVec 64)
    (u8 u32 u56 u64 u80 u88 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4016#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗
        A.pool lim st s ∗
        Rest)
      (fun s4 P4 =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P4 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
            A.pool lim (M.stepEvents evs st) s4 ∗
            Rest) ∧
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x20 = pa1 >>> 8 ∧
          s4.readReg64 .x21 = u8 ∧
          s4.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
          s4.readReg64 .x26 = pa1 ∧
          s4.readReg64 .x27 = pbA ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hr_lt63
  have hcmn : (BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hr_toNat)
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9824#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      vecCapPtrDealloc A.repAlloc u80 u88 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = u8 ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
      s2.readReg64 .x23 = u80 ∧
      s2.readReg64 .x24 = u88 ∧
      s2.readReg64 .x26 = pa1 ∧
      s2.readReg64 .x27 = pbA ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    change s.pc = (blkPl_333).base + 9804#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9824#64) s _ _
    by_cases hc_r : (u56 == 0#64) = true <;>
      simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 9824#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc u56.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (u64, u56.toNat, 1, st)
      have hacp1 : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s.sp›.trans hsp
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2
      refine align_pre_st (by rw [hsp]; simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 4008#64)
      (P_evs := fun evs2 s3 =>
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        A.pool lim (M.stepEvents evs2 st1) s3 ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x20 = pa1 >>> 8 ∧
        s3.readReg64 .x21 = u8 ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
        s3.readReg64 .x26 = pa1 ∧
        s3.readReg64 .x27 = pbA ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
      change s2.pc = (blkPl_333).base + 9824#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4008#64) s2 _ _
      by_cases hc_m : (u80 == 0#64) = true <;>
        simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 4008#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · apply sepWP_evs_dealloc u80.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (u88, u80.toNat, 1, st1)
        have hacp2 : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        refine align_pre_st (by rw [hsp2]; simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
      have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
        dsimp only [st1]
        rw [M.stepEvents_append]
      rw [hst_eq]
      refine SepWP.mono
        (post := fun s4 P4 =>
          (P4 ⊢
            memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
            stackAt (s0.sp - 2400#64) allocHookStack ∗
            ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2) st) s4 ∗
            Rest) ∧
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x20 = pa1 >>> 8 ∧
          s4.readReg64 .x21 = u8 ∧
          s4.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
          s4.readReg64 .x26 = pa1 ∧
          s4.readReg64 .x27 = pbA ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0) ?_
        (fun s4 P4 _ _ ⟨hP4, hregs4⟩ =>
          ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2,
           Entails.trans hP4 (Entails.of_eq (by sep_ac_rfl)), hregs4⟩)
      change s3.pc = (blkPl_333).base + 4008#64 at hpc3
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4016#64) s3 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4016#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done

theorem v1_auth_from_pb_step3_9804_4016_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out pbA pa1 : BitVec 64)
    (u8 u32 u56 u64 u80 u88 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4016#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗
        A.pool lim st s ∗
        Rest)
      (fun s4 P4 =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P4 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
            A.pool lim (M.stepEvents evs st) s4 ∗
            Rest) ∧
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x20 = pa1 >>> 8 ∧
          s4.readReg64 .x21 = u8 ∧
          s4.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
          s4.readReg64 .x26 = pa1 ∧
          s4.readReg64 .x27 = pbA ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0) :=
  v1_auth_from_pb_step3_9804_4016_of_sub_placed (v1_dealloc_ok_of_placedHooks hA) st s0 s out pbA pa1
    u8 u32 u56 u64 u80 u88 auth Rest hr_lt63 hsp0_align hpc hrun hsp hx19 hx21 hx22 hx23 hx24
    hx25 hx26 hx27 hx28 htr

theorem v1_auth_from_pb_step3_9804_4016_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out pbA pa1 : BitVec 64)
    (u8 u32 u56 u64 u80 u88 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4016#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗
        A.pool lim st s ∗
        Rest)
      (fun s4 P4 =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P4 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
            A.pool lim (M.stepEvents evs st) s4 ∗
            Rest) ∧
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x20 = pa1 >>> 8 ∧
          s4.readReg64 .x21 = u8 ∧
          s4.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s4.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 ∧
          s4.readReg64 .x26 = pa1 ∧
          s4.readReg64 .x27 = pbA ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0) :=
  v1_auth_from_pb_step3_9804_4016_of_sub_placed (v1_dealloc_ok_at_statesFromPb_placed hA) st s0 s out pbA pa1
    u8 u32 u56 u64 u80 u88 auth Rest hr_lt63 hsp0_align hpc hrun hsp hx19 hx21 hx22 hx23 hx24
    hx25 hx26 hx27 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudgetAux
