/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part B

Relocatable Block-`333` `ProtoAuthenticator` key cloning and input-buffer deallocation
(`+3436 -> +8700 -> +8884 -> +8944`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudget

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (cap_add_one_beq_zero_false vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved ofNat_beq_zero_false sp_sub_2400_align stackAt_encoderFromPb_split_allocHook
   v1_bv_add_add_lit v2hs_bv_sub_sub_lit v2hs_vecU8Payload_of_nil v2hs_vecU8Payload_pos_dealloc
   v2hs_vecU8Payload_pos_unpack vecU8Payload_pos)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec seq_clean_st subroutine_ok_deallocFreeOnly)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v2hs_bv_sub_sub_lit

/-! ## Re-exports of Pure Block-`333` `SepWP` Segments (`Variant2hsbPlacedBudgetAux`) -/

alias v2hs_copy_pb_to_stack_508_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_copy_pb_to_stack_508_placed
alias v2hs_copy_pb_to_stack_508_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_copy_pb_to_stack_508_placed_budget
alias v2hs_check_ptsNeeded_592_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_check_ptsNeeded_592_placed
alias v2hs_check_ptsNeeded_592_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_check_ptsNeeded_592_placed_budget
alias v2hs_uc_none_3348_to_4392_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_uc_none_3348_to_4392_placed
alias v2hs_uc_none_3348_to_4392_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_uc_none_3348_to_4392_placed_budget
alias v2hs_validate_err_dk_3348_to_4660_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_validate_err_dk_3348_to_4660_placed
alias v2hs_validate_err_dk_3348_to_4660_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_validate_err_dk_3348_to_4660_placed_budget
alias v2hs_validate_err_auth_3348_to_4720_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_validate_err_auth_3348_to_4720_placed
alias v2hs_validate_err_auth_3348_to_4720_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_validate_err_auth_3348_to_4720_placed_budget
alias v2hs_validate_ok_3348_3436_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_validate_ok_3348_3436_placed
alias v2hs_validate_ok_3348_3436_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_validate_ok_3348_3436_placed_budget
alias v2hs_assemble_ekSent_8944_9032_placed :=
  Variant2hsbPlacedBudgetAux.v2hs_assemble_ekSent_8944_9032_placed
alias v2hs_assemble_ekSent_8944_9032_placed_budget :=
  Variant2hsbPlacedBudgetAux.v2hs_assemble_ekSent_8944_9032_placed_budget

/-! ## Exact Deallocation Event Sequences & Local Combinators -/

/-- Deterministic `AllocEvent` list emitted by conditional `Vec<u8>` buffer deallocation:
    `[]` when `cap == 0#64`, else `rustDeallocEvents cap.toNat 1`. -/
def vecCapDeallocEvents (cap : BitVec 64) : List AllocEvent :=
  if cap == 0#64 then [] else rustDeallocEvents cap.toNat 1

/-- Exact deterministic `AllocEvent` sequence emitted by `v2hs_auth_from_pb_step3_8884_8944_placed`:
    drops `rootKey` buffer `(u32, u40)` followed by `macKey` buffer `(u56, u64)`. -/
def v2hsAuthDeallocEvents (u32 u56 : BitVec 64) : List AllocEvent :=
  vecCapDeallocEvents u32 ++ vecCapDeallocEvents u56

theorem freeOnlyEvs_vecCapDeallocEvents (cap : BitVec 64) :
    FreeOnlyEvs (vecCapDeallocEvents cap) := by
  unfold vecCapDeallocEvents
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

theorem freeOnlyEvs_v2hsAuthDeallocEvents (u32 u56 : BitVec 64) :
    FreeOnlyEvs (v2hsAuthDeallocEvents u32 u56) :=
  FreeOnlyEvs.append (freeOnlyEvs_vecCapDeallocEvents u32) (freeOnlyEvs_vecCapDeallocEvents u56)

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

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

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

/-! ## Budget-Threaded `ProtoAuthenticator` Clone & Dealloc Steps (`+3436 -> +8700 -> +8884 -> +8944`) -/

set_option maxHeartbeats 800000 in
/-- Segment (`+3436 -> +8700`): clone `auth.rootKey` into `pa1` (`x23`) under
    `FitsEvents M lim st (authKeyCloneEvents auth.rootKey)` with zero OOM/panic branches. -/
theorem v2hs_auth_from_pb_step1_3436_8700_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out d_w0 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 3436#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8700#64) s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 216#64) ↦₆₄ u40) ∗
       vecU8Payload A.repAlloc u32 u40 auth.rootKey ∗
       A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        ∃ pa1 : BitVec 64,
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗
            ((fsp + 216#64) ↦₆₄ u40) ∗
            vecCapPtrDealloc A.repAlloc u32 u40 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame) ∧
          s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧
          s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = pa1 ∧
          s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
          s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = u80 ∧
          TraceCalleeSaved s1 s0) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents auth.rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hr_nil] at hx20 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20 ⊢
    change s.pc = (blkPl_333).base + 3436#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8700#64) s _ _
    refine SepWP.mono
      (P := stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        vecU8Payload A.repAlloc u32 u40 [] ∗ A.pool lim st s ∗ Frame)
      (post := fun s1 P1 =>
        (P1 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          vecCapPtrDealloc A.repAlloc u32 u40 ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = 0#64 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
        s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s1 s0) ?_
      fun s1 P1 _ _ ⟨hP1, hregs⟩ => ⟨1#64, hP1, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8700#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc u32 u40 []
    have hn := v2hs_vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc u32 u40 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        A.pool lim st sc ∗ Frame by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : auth.rootKey.isEmpty = false := by
      cases h : auth.rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents auth.rootKey = rustAllocEvents auth.rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (v2hs_vecU8Payload_pos_unpack A.repAlloc u32 u40 auth.rootKey hr_pos)))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          (⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
            u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
           (A.repAlloc.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
            memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length)
              (u32.toNat - auth.rootKey.length))) ∗
          A.pool lim st s ∗ Frame =
        ⌜auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧
          u40 ≠ 0#64 ∧ u32 ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
         A.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
         memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length)
           (u32.toNat - auth.rootKey.length) ∗
         A.pool lim st s ∗ Frame) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]; dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk auth.rootKey.length 1 := ⟨⟨hr_pos, hpow1, hr_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s.pc = (blkPl_333).base + 3436#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8700#64) s _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (auth.rootKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, u40, auth.rootKey)
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
      (post := fun s1 P1 =>
        (P1 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          vecCapPtrDealloc A.repAlloc u32 u40 ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length)
            (sf_1.readReg64 .x0) auth.rootKey ∗
          A.pool lim (M.stepEvents (rustAllocEvents auth.rootKey.length 1) st) s1 ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = sf_1.readReg64 .x0 ∧
        s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
        s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s1 s0) ?_
      fun s1 P1 _ _ ⟨hP1, hregs⟩ => ⟨sf_1.readReg64 .x0, hP1, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8700#64)
    simp only [State.setMem_setMem]
    have hd := v2hs_vecU8Payload_pos_dealloc A.repAlloc u32 u40 auth.rootKey
      hr_le hr_cap hptr0 hcap0_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) auth.rootKey
      hr_pos hr_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live u40 u32.toNat 1 ∗ (u40 ↦ₛ auth.rootKey) ∗
         memRegion (u40 + BitVec.ofNat 64 auth.rootKey.length)
           (u32.toNat - auth.rootKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) auth.rootKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ auth.rootKey)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗
        A.pool lim (M.stepEvents (rustAllocEvents auth.rootKey.length 1) st) sc ∗ Frame by
          dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v2hs_auth_from_pb_step1_3436_8700_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (target_pc fsp out d_w0 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (post onPanic : State → SepProp → Prop)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 333 + 3436#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = lsmpl.base 333 + 8700#64 →
      s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
       s1.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x21 = s.readReg64 .x21 ∧
       s1.readReg64 .x22 = d_w0 ∧ s1.readReg64 .x23 = pa1 ∧
       s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
       s1.readReg64 .x26 = u32 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
       s1.readReg64 .x28 = u80 ∧
       TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 216#64) ↦₆₄ u40) ∗
         vecCapPtrDealloc A.repAlloc u32 u40 ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame)
        post onPanic) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 216#64) ↦₆₄ u40) ∗
       vecU8Payload A.repAlloc u32 u40 auth.rootKey ∗
       A.pool lim st s ∗ Frame)
      post onPanic :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono
      (v2hs_auth_from_pb_step1_3436_8700_placed hA st s0 s fsp out d_w0
        u32 u40 u56 u64 u80 auth Frame hfits hfsp_align hpc hrun hsp
        hx19 hx20 hx22 hx24 hx25 hx26 hx28 htr)
      fun s1 _ hpc1 hrun1 ⟨pa1, hP1, hregs⟩ hcl1 =>
        SepWPp.weaken_pre hP1 (hnext pa1 s1 hpc1 hrun1 hcl1 hregs))

set_option maxHeartbeats 800000 in
/-- Segment (`+8700 -> +8884`): clone `auth.macKey` into `pa2` (`[fsp + 184]`) under
    `FitsEvents M lim st (authKeyCloneEvents auth.macKey)` with zero OOM/panic branches. -/
theorem v2hs_auth_from_pb_step2_8700_8884_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out d_w0 pa1 w184 : BitVec 64)
    (u32 u56 u64 u72 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8700#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8884#64) s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗
       vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
       A.pool lim st s ∗ Frame)
      (fun s2 P2 =>
        ∃ pa2 : BitVec 64,
          (P2 ⊢
            stackAt fsp encoderFromPbStack ∗
            ((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ u72) ∗
            vecCapPtrDealloc A.repAlloc u56 u64 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame) ∧
          s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s2.readReg64 .x21 = s.readReg64 .x21 ∧
          s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
          s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
          s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
          TraceCalleeSaved s2 s0) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents auth.macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil]
    subst hu72
    rw [hm_nil]
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hpc ⊢
    change s.pc = (blkPl_333).base + 8700#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8884#64) s _ _
    refine SepWP.mono
      (P := stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
        ((fsp + 232#64) ↦₆₄ 0#64) ∗
        vecU8Payload A.repAlloc u56 u64 [] ∗ A.pool lim st s ∗ Frame)
      (post := fun s2 P2 =>
        (P2 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
          ((fsp + 232#64) ↦₆₄ 0#64) ∗
          vecCapPtrDealloc A.repAlloc u56 u64 ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          A.pool lim st s2 ∗ Frame) ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
        s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0) ?_
      fun s2 P2 _ _ ⟨hP2, hregs⟩ => ⟨1#64, hP2, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8884#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc u56 u64 []
    have hn := v2hs_vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ 1#64) ∗
        ((fsp + 232#64) ↦₆₄ 0#64) ∗ A.pool lim st sc ∗ Frame by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · subst hu72
    have hne_nil : auth.macKey.isEmpty = false := by
      cases h : auth.macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents auth.macKey = rustAllocEvents auth.macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (v2hs_vecU8Payload_pos_unpack A.repAlloc u56 u64 auth.macKey hm_pos))))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          (⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
            u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.repAlloc.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.macKey.length)
              (u56.toNat - auth.macKey.length))) ∗
          A.pool lim st s ∗ Frame =
        ⌜auth.macKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
          u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗
         ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.macKey.length)
           (u56.toNat - auth.macKey.length) ∗
         A.pool lim st s ∗ Frame) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]; dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
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
    change s.pc = (blkPl_333).base + 8700#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8884#64) s _ _
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
    wp_call hmc (sf_1.readReg64 .x0, u64, auth.macKey)
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
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ sf_1.readReg64 .x0) ∗
          ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
          vecCapPtrDealloc A.repAlloc u56 u64 ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length)
            (sf_1.readReg64 .x0) auth.macKey ∗
          A.pool lim (M.stepEvents (rustAllocEvents auth.macKey.length 1) st) s2 ∗ Frame) ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
        s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0) ?_
      fun s2 P2 _ _ ⟨hP2, hregs⟩ => ⟨sf_1.readReg64 .x0, hP2, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8884#64)
    simp only [State.setMem_setMem]
    have hd := v2hs_vecU8Payload_pos_dealloc A.repAlloc u56 u64 auth.macKey
      hm_le hm_cap hptr1 hcap1_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) auth.macKey
      hm_pos hm_lt63 hoom1
    refine entails_pre_st ?_ ?_
    · intro sc hsc; rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.macKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.macKey.length)
           (u56.toNat - auth.macKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) auth.macKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ auth.macKey)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        ((fsp + 184#64) ↦₆₄ sf_1.readReg64 .x0) ∗
        ((fsp + 232#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        A.pool lim (M.stepEvents (rustAllocEvents auth.macKey.length 1) st) sc ∗ Frame by
          dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v2hs_auth_from_pb_step2_8700_8884_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (target_pc fsp out d_w0 pa1 w184 : BitVec 64)
    (u32 u56 u64 u72 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (post onPanic : State → SepProp → Prop)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.macKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 333 + 8700#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa2 : BitVec 64) (s2 : State),
      s2.pc = lsmpl.base 333 + 8884#64 →
      s2.status = .Running →
      LibsignalCodeLoaded lsmpl s2.mem →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
       s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x21 = s.readReg64 .x21 ∧
       s2.readReg64 .x22 = d_w0 ∧ s2.readReg64 .x23 = pa1 ∧
       s2.readReg64 .x24 = u56 ∧ s2.readReg64 .x25 = u64 ∧
       s2.readReg64 .x26 = u32 ∧ s2.readReg64 .x27 = s.readReg64 .x27 ∧
       TraceCalleeSaved s2 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ u72) ∗
         vecCapPtrDealloc A.repAlloc u56 u64 ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
         A.pool lim (M.stepEvents (authKeyCloneEvents auth.macKey) st) s2 ∗ Frame)
        post onPanic) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗
       vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
       A.pool lim st s ∗ Frame)
      post onPanic :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono
      (v2hs_auth_from_pb_step2_8700_8884_placed hA st s0 s fsp out d_w0 pa1 w184
        u32 u56 u64 u72 auth Frame hfits hfsp_align hpc hrun hsp
        hx19 hx20 hx22 hx23 hx24 hx25 hx26 hu72 htr)
      fun s2 _ hpc2 hrun2 ⟨pa2, hP2, hregs⟩ hcl2 =>
        SepWPp.weaken_pre hP2 (hnext pa2 s2 hpc2 hrun2 hcl2 hregs))

/-- Segment (`+8884 -> +8944`): deallocate input `rootKey` `(u32, u40)` and `macKey` `(u56, u64)`
    buffers under `FromPbAllocHooksPlacedBudget M A lim ext`, advancing the budget state by the
    exact deterministic sequence `v2hsAuthDeallocEvents u32 u56`. -/
theorem v2hs_auth_from_pb_step3_8884_8944_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out d_w0 pa1 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8944#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        A.pool lim st s ∗
        Rest)
      (fun s3 P3 =>
        (P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          A.pool lim (M.stepEvents (v2hsAuthDeallocEvents u32 u56) st) s3 ∗
          Rest) ∧
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = s.readReg64 .x21 ∧
        s3.readReg64 .x22 = d_w0 ∧
        s3.readReg64 .x23 = pa1 ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
        s3.readReg64 .x26 = pa1 >>> 8 ∧
        s3.readReg64 .x27 = s.readReg64 .x27 ∧
        s3.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s3 s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hr_lt63
  have hcmn : ¬((BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = true) :=
    cap_add_one_beq_zero_false hr_toNat
  have hcmn_false : (BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr hcmn
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hA.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  wp_simp_pre [arm64_norm, sepConj_assoc]
  let st1 := M.stepEvents (vecCapDeallocEvents u32) st
  refine seq_clean_st
    (mid := lsmpl.base 333 + 8912#64)
    (P_mid := fun s2 =>
      memRegion (s0.sp - 7552#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((s0.sp - 2184#64) ↦₆₄ u40) ∗
      ((s0.sp - 2176#64) ↦₆₄ u80) ∗
      vecCapPtrDealloc A.repAlloc u56 u64 ∗
      A.pool lim st1 s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = s.readReg64 .x21 ∧
      s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = pa1 ∧
      s2.readReg64 .x24 = u56 ∧
      s2.readReg64 .x25 = u64 ∧
      s2.readReg64 .x26 = pa1 >>> 8 ∧
      s2.readReg64 .x27 = s.readReg64 .x27 ∧
      s2.readReg64 .x28 = u80 ∧
      TraceCalleeSaved s2 s0) ?_ ?_
  · dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
    change s.pc = (blkPl_333).base + 8884#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8912#64) s _ _
    by_cases hc_r : (u32 == 0#64) = true <;>
      simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hev1 : st1 = st := by simp [st1, vecCapDeallocEvents, hc_r]
      rw [hev1]
      wp_steps_sync_333 ((blkPl_333).base + 8912#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hev1 : st1 = M.stepEvents (rustDeallocEvents u32.toNat 1) st := by
        simp [st1, vecCapDeallocEvents, hc_r]
      rw [hev1]
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (u40, u32.toNat, 1, st)
      have hacp1 : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2
      wp_steps_sync_333 ((blkPl_333).base + 8912#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    have hst_app : M.stepEvents (v2hsAuthDeallocEvents u32 u56) st =
        M.stepEvents (vecCapDeallocEvents u56) st1 := by
      unfold v2hsAuthDeallocEvents
      exact M.stepEvents_append (vecCapDeallocEvents u32) (vecCapDeallocEvents u56) st
    rw [hst_app]
    dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
    change s2.pc = (blkPl_333).base + 8912#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8944#64) s2 _ _
    by_cases hc_m : (u56 == 0#64) = true <;>
      simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hev2 : vecCapDeallocEvents u56 = [] := by simp [vecCapDeallocEvents, hc_m]
      rw [hev2, M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 8944#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc; rw [← hsc]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · rw [← hx21_2, ← hx27_2]
        wp_done
    · have hev2 : vecCapDeallocEvents u56 = rustDeallocEvents u56.toNat 1 := by
        simp [vecCapDeallocEvents, hc_m]
      rw [hev2]
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (u64, u56.toNat, 1, st1)
      have hacp2 : AllocCallPreserved s2 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
      wp_steps_sync_333 ((blkPl_333).base + 8944#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc; rw [← hsc, hsp2]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · rw [← hx21_2, ← hx27_2]
        wp_done

theorem v2hs_auth_from_pb_step3_8884_8944_placed_freeOnly [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out d_w0 pa1 : BitVec 64)
    (u32 u40 u56 u64 u80 : BitVec 64)
    (auth : ProtoAuthenticator) (Rest : SepProp)
    (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1)
    (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8944#64) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        A.pool lim st s ∗
        Rest)
      (fun s3 P3 =>
        ∃ evs_free : List AllocEvent,
          FreeOnlyEvs evs_free ∧
          (P3 ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
            ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
            ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
            A.pool lim (M.stepEvents evs_free st) s3 ∗
            Rest) ∧
          s3.sp = s0.sp - 2400#64 ∧
          s3.readReg64 .x19 = out ∧
          s3.readReg64 .x21 = s.readReg64 .x21 ∧
          s3.readReg64 .x22 = d_w0 ∧
          s3.readReg64 .x23 = pa1 ∧
          s3.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x26 = pa1 >>> 8 ∧
          s3.readReg64 .x27 = s.readReg64 .x27 ∧
          s3.readReg64 .x28 = u80 ∧
          TraceCalleeSaved s3 s0) :=
  SepWP.mono
    (v2hs_auth_from_pb_step3_8884_8944_placed hA st s0 s out d_w0 pa1
      u32 u40 u56 u64 u80 auth Rest hr_lt63 hsp0_align hpc hrun hsp
      hx19 hx22 hx23 hx24 hx25 hx26 htr)
    fun _ _ _ _ ⟨hP3, hregs⟩ =>
      ⟨v2hsAuthDeallocEvents u32 u56, freeOnlyEvs_v2hsAuthDeallocEvents u32 u56, hP3, hregs⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudget
