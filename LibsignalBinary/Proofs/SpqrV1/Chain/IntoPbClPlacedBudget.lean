/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Proof of `<spqr::chain::Chain>::into_pb` (Block `365`)

Budget-threaded, code-loaded `[LibsignalPlacement]` post-allocation paths and subroutine
contracts for `<spqr::chain::Chain>::into_pb` (`blkPC_365`) under `RustCliAllocBudget M`, with
`withLsCodeLoaded lsmpl` on cross-block drop-glue callee `287` (`dropChainEpochSliceSpec M A lim`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_365 blkPl_365 extract_withLsCodeLoaded
  lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainIntoPbCall TraceCalleeSaved add_m1_m2_sub_one add_m2_sub_one_m1
  calleeSavedFromPbAt cap_mul_112_shift_eq cap_sub_head_eq_ofNat chainAt_unpack chainEpochAt
  chainEpochIntoPb chainHeaderCellsAt chainIntoPbStack chainPBIntoPinnedAt_entails_protoRepr
  drop_zip_eq head_mul_112_eq_ofNat head_ult_cap intoPbLoopScratchAt intoPbScratchAt
  linksRawAllocAt madd_m1_112_add_52 memRegion_nonwrap_join memRegion_wrap_join
  mul_112_beq_zero_false mul_112_shift_eq nonwrap_head_ne_end nonwrap_hi_false
  nonwrap_min_eq_len nonwrap_ult_hi_false ofNat_beq_zero_false_of_lt ofNat_len_ule_max_112
  ofNat_sub_one_add_one stackAt_chainIntoPbX_split stackAt_chainIntoPb_split
  stackAt_dropStack32_split_allocHook take_zip_eq toChainEpochPBGhost
  umulh_div112_sub_112 umulh_div112_sub_112_norm vecDequeSlotsAt
  vecDequeSlots_nil_entails_dealloc vecDequeSlots_nonwrap_split vecDequeSlots_wrap_split
  vecU8BufAt wrap_hi_true wrap_len_sub_m1 wrap_ult_false wrap_ult_hi_true
)
open CryptoVerification.SpqrV1.Drop (dropStack32)
open CryptoVerification.SpqrV1.Top.ChainFrom (chainEpochPBAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (
  ChainIntoPbAllocEnv chainIntoPbPinnedSpec chainIntoPbPinnedSpecX
  chainIntoPbSpec chainIntoPbSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopBudget (
  intoPbPinnedRetPost intoPb_loop1_run_placed intoPb_loop2_run_placed
)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopClPlacedBudget (
  chainIntoPb_epilogue_cl_placed
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by
  cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre readReg64_setMem_pre readReg32_setMem_pre
  readReg_setMem_pre calleeSavedVRegs_setMem_pre

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem seq_vm_clean_lscl [LibsignalPlacement] {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ hcl' =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hcl' hvm hQ))

private theorem chain_sepWP_seq_lscl_mid [LibsignalPlacement] {prog : Program} {mid tgt : BitVec 64}
    {s : State} {P : SepProp} {Mid post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hmid hclm =>
    h2 sm Pm hpc hrun hclm hmid)
/-! ## Non-Wrapping and Wrapping Code-Loaded Post-Allocation Paths (`+156 .. lr`) -/

set_option maxHeartbeats 800000 in
/-- Code-loaded `[LibsignalPlacement]` non-wrapping post-allocation path (`+156 .. lr`). -/
theorem intoPb_post_alloc_nonwrap_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainIntoPbCall) (st : M.σ) (s0 s : State) (newLinksPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length) (hl_pos : 1 ≤ x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hnonwrap : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.repAlloc.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
          x.gChain.linksHead.toNat x.gChain.linksPtr
          (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents (rustAllocEvents (x.chain.links.length * 112) 8) st) s ∗
        intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost M A lim x st s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let srcBase := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  let evs_alloc := rustAllocEvents (len * 112) 8
  have hnil_ne : x.chain.links ≠ [] := List.length_pos_iff.mp (by omega)
  have hevs_alloc : ChainIntoPbAllocEnv x evs_alloc := by
    simp [ChainIntoPbAllocEnv, hnil_ne, evs_alloc, len]
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 (cap - head) :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hult_hi_false : BitVec.ult (BitVec.ofNat 64 (cap - head)) (BitVec.ofNat 64 len) = false :=
    nonwrap_ult_hi_false hnonwrap (by omega)
  have hhi_false :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head))) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 (cap - head))) = false :=
    nonwrap_hi_false hnonwrap (by omega)
  have hhead_ne_end : (x.gChain.linksHead == x.gChain.linksHead + BitVec.ofNat 64 len) = false :=
    nonwrap_head_ne_end x.gChain.linksHead hl_pos (by omega)
  have hmin_eq :
      (if BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head)) = true
       then BitVec.ofNat 64 len else BitVec.ofNat 64 (cap - head)) = BitVec.ofNat 64 len :=
    nonwrap_min_eq_len hnonwrap (by omega)
  have hlsl_len : (BitVec.ofNat 64 len <<< (7 : Nat)) - (BitVec.ofNat 64 len <<< (4 : Nat)) =
      BitVec.ofNat 64 (len * 112) := mul_112_shift_eq len hl_new_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh := umulh_div112_sub_112 hl_pos hl_new_lt
  have hadd1 := ofNat_sub_one_add_one hl_pos
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hslots := vecDequeSlots_nonwrap_split A.repAlloc cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt (by rw [hzlen]; exact hnonwrap)
  rw [hzlen] at hslots
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := @intoPb_loop1_run_placed _ A.repAlloc H x.chain.links x.gChain.epochs [] [] s0
  have hepilogue := @chainIntoPb_epilogue_cl_placed _ M A lim H hdealloc hdrop x st evs_alloc s0
  refine seq_vm_clean_lscl hcl (mid := (blkPl_365).base + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.repAlloc.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (len * 112) ∗
      A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A.repAlloc) 112 srcBase (x.gChain.epochs.zip x.chain.links) ∗
      memRegion x.gChain.linksPtr (head * 112) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
      vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool lim (M.stepEvents evs_alloc st) s ∗
      intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      AllocCallPreserved s0 s1 ∧
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 len ∧ s1.readReg64 .x9 = 0#64 ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x12 = BitVec.ofNat 64 (len * 112) ∧
      s1.readReg64 .x13 = s0.sp - 160#64 ∧ s1.readReg64 .x14 = s0.sp - 208#64 ∧
      s1.readReg64 .x15 = s0.sp - 260#64 ∧ s1.readReg64 .x16 = newLinksPtr + 52#64 ∧
      s1.readReg64 .x17 = srcBase + 56#64 ∧ s1.readReg64 .x19 = x.chainPtr ∧
      s1.readReg64 .x20 = x.out ∧ s1.readReg64 .x22 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 (cap - head)).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_false hhead_ne_end
      simp only [hult_hi_false, Bool.false_eq_true, ↓reduceIte, hhead_ne_end]
    have humulh_norm :
        BitVec.truncate 64
          ((BitVec.zeroExtend 128 ((BitVec.ofNat 64 (len * 112) - 112#64) >>> 4) *
            2635249153387078803#128) >>> 64) = BitVec.ofNat 64 (len - 1) := by
      simpa using umulh_div112_sub_112 hl_pos hl_new_lt
    dsimp only [len] at hult_hi_false hhi_false hhead_ne_end hmin_eq hlsl_len humulh humulh_norm hadd1
    by_vm_steps (
      wp_steps; dsimp only [srcBase]
      rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done)
  · rintro s1 hpc1 hrun1 hcl1 hvm1 ⟨hacp1, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase newLinksPtr hsp0_align
      hl_pos hlen rfl (by simpa using hl_new_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 hx12_1 hx13_1 hx14_1 hx15_1
      (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (chain_sepWP_seq_lscl_mid hcl1 (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.repAlloc.live newLinksPtr (len * 112) 8 ∗ A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗
          memRegion x.gChain.linksPtr (head * 112) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents evs_alloc st) s1 ∗
          calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hvm2, hacp_l1, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    have hacp2 : AllocCallPreserved s0 s2 := hacp1.trans hacp_l1
    rw [hx0_1] at hx0_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    have hjoin_old := memRegion_nonwrap_join x.gChain.linksPtr cap head len hl_cap_lt (Nat.le_of_lt hhead_lt) hnonwrap
    have hnew_raw : A.repAlloc.live newLinksPtr (len * 112) 8 ⊢
        linksRawAllocAt A.repAlloc (BitVec.ofNat 64 len) newLinksPtr len := by
      unfold linksRawAllocAt
      have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
        absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
      have htn : (BitVec.ofNat 64 len).toNat = len := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
      exact Entails.refl _
    refine SepWP.weaken_pre hP2 ?_
    rw [← A.pool_of_vmPreserved hvm2]
    refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase]; sep_focus) ?_
    refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
    refine seq_vm_clean_lscl hcl2 (mid := (blkPl_365).base + 820#64)
      (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A.repAlloc (BitVec.ofNat 64 len) newLinksPtr len ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents evs_alloc st) s2 ∗
        intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun s3 =>
        AllocCallPreserved s0 s3 ∧
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = 0#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x21 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 len ∧ s3.readReg64 .x23 = 0#64 ∧
        s3.readReg64 .x24 = newLinksPtr ∧ s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp2
      by_vm_steps (simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done)
    · rintro s3 hpc3 hrun3 hcl3 hvm3 ⟨hacp3, hsp3, htr3, hfp3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx28_3⟩
      rw [← A.pool_of_vmPreserved hvm3]
      exact hepilogue s3 newLinksPtr hcl3 hevs_alloc hacp3 hsp0_align hlen hl_cap_lt hl_cap_ne
        hl_new_lt hl_new_ne hn1 hn2 hn3 hpc3 hrun3 hsp3 htr3 hfp3 hx8_3 hx9_3 hx19_3 hx20_3
        hx21_3 hx22_3 hx23_3 hx24_3 hx26_3 hx28_3
set_option maxHeartbeats 800000 in
/-- Code-loaded `[LibsignalPlacement]` wrapping post-allocation path (`+156 .. lr`). -/
theorem intoPb_post_alloc_wrap_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainIntoPbCall) (st : M.σ) (s0 s : State) (newLinksPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hwrap : x.gChain.linksCap.toNat - x.gChain.linksHead.toNat < x.chain.links.length)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.repAlloc.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
          x.gChain.linksHead.toNat x.gChain.linksPtr
          (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents (rustAllocEvents (x.chain.links.length * 112) 8) st) s ∗
        intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost M A lim x st s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let m₁ := cap - head
  let m₂ := len - m₁
  let srcBase1 := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  let rem1 := x.chain.links.take m₁
  let rem1G := x.gChain.epochs.take m₁
  let rem2 := x.chain.links.drop m₁
  let rem2G := x.gChain.epochs.drop m₁
  let evs_alloc := rustAllocEvents (len * 112) 8
  have hm1_pos : 1 ≤ m₁ := by omega
  have hm2_pos : 1 ≤ m₂ := by omega
  have hm_sum : m₁ + m₂ = len := by omega
  have hnil_ne : x.chain.links ≠ [] := List.length_pos_iff.mp (by omega)
  have hevs_alloc : ChainIntoPbAllocEnv x evs_alloc := by
    simp [ChainIntoPbAllocEnv, hnil_ne, evs_alloc, len]
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hm1_lt : m₁ * 112 < 2 ^ 63 := by omega
  have hm2_lt : m₂ * 112 < 2 ^ 63 := by omega
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hhead_ne_cap : (x.gChain.linksHead == x.gChain.linksCap) = false := by
    rw [beq_eq_false_iff_ne]; intro heq; rw [heq] at hhead_lt; exact Nat.lt_irrefl _ hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 m₁ :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hlen_sub_m1 : BitVec.ofNat 64 len - BitVec.ofNat 64 m₁ = BitVec.ofNat 64 m₂ :=
    wrap_len_sub_m1 (Nat.le_of_lt hwrap) (by omega)
  have hlsl_m2 : (BitVec.ofNat 64 m₂ <<< (7 : Nat)) - (BitVec.ofNat 64 m₂ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₂ * 112) := mul_112_shift_eq m₂ hm2_lt
  have hult_hi_true : BitVec.ult (BitVec.ofNat 64 m₁) (BitVec.ofNat 64 len) = true :=
    wrap_ult_hi_true hwrap (by omega)
  have hhi_true :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁)) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 m₁)) = true := wrap_hi_true hwrap (by omega)
  have hult_false : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = false :=
    wrap_ult_false hwrap (by omega)
  have hlsl_m1 : (BitVec.ofNat 64 m₁ <<< (7 : Nat)) - (BitVec.ofNat 64 m₁ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₁ * 112) := mul_112_shift_eq m₁ hm1_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh1 := umulh_div112_sub_112 hm1_pos hm1_lt
  have humulh1_norm := umulh_div112_sub_112_norm hm1_pos hm1_lt
  have hadd1_m1 := ofNat_sub_one_add_one hm1_pos
  have hm2_cbz_false : (BitVec.ofNat 64 (m₂ * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hm2_lt
  have humulh2 := umulh_div112_sub_112 hm2_pos hm2_lt
  have humulh2_norm := umulh_div112_sub_112_norm hm2_pos hm2_lt
  have hmadd_dst := madd_m1_112_add_52 newLinksPtr m₁
  have hadd_x2 := add_m1_m2_sub_one hm2_pos hm_sum
  have hadd_x8 := add_m2_sub_one_m1 hm2_pos hm_sum
  have hrem1_len : rem1.length = m₁ := List.length_take_of_le (by omega)
  have hrem1G_len : rem1G.length = m₁ := List.length_take_of_le (by omega)
  have hrem2_len : rem2.length = m₂ := by dsimp [rem2]; rw [List.length_drop]
  have hrem2G_len : rem2G.length = m₂ := by dsimp [rem2G]; rw [List.length_drop, hlen]
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hzip_take : (x.gChain.epochs.zip x.chain.links).take m₁ = rem1G.zip rem1 :=
    take_zip_eq m₁ x.gChain.epochs x.chain.links
  have hzip_drop : (x.gChain.epochs.zip x.chain.links).drop m₁ = rem2G.zip rem2 :=
    drop_zip_eq m₁ x.gChain.epochs x.chain.links
  have hslots := vecDequeSlots_wrap_split A.repAlloc cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt
    (by rw [hzlen]; exact hl_le) (by rw [hzlen]; exact hwrap)
  rw [hzlen, hzip_take, hzip_drop] at hslots
  have hsplit_dst : memRegion newLinksPtr (len * 112) =
      memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) := by
    have hmul_sum : len * 112 = m₁ * 112 + m₂ * 112 := by rw [← Nat.add_mul, hm_sum]
    conv_lhs => rw [hmul_sum]
    exact ProofLib.memRegion_split' (b := newLinksPtr) (n := m₁ * 112) (k := m₂ * 112)
      (b' := newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) rfl rfl (by omega)
  rw [hsplit_dst]
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := @intoPb_loop1_run_placed _ A.repAlloc H rem1 rem1G [] [] s0
  have hloop2 := @intoPb_loop2_run_placed _ A.repAlloc H rem2 rem2G rem1G rem1 s0
  have hepilogue := @chainIntoPb_epilogue_cl_placed _ M A lim H hdealloc hdrop x st evs_alloc s0
  refine seq_vm_clean_lscl hcl (mid := (blkPl_365).base + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.repAlloc.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
      A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A.repAlloc) 112 srcBase1 (rem1G.zip rem1) ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
      vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool lim (M.stepEvents evs_alloc st) s ∗
      intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      AllocCallPreserved s0 s1 ∧
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧ s1.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x11 = 0x2492492492492493#64 ∧
      s1.readReg64 .x12 = BitVec.ofNat 64 (m₁ * 112) ∧ s1.readReg64 .x13 = s0.sp - 160#64 ∧
      s1.readReg64 .x14 = s0.sp - 208#64 ∧ s1.readReg64 .x15 = s0.sp - 260#64 ∧
      s1.readReg64 .x16 = newLinksPtr + 52#64 ∧ s1.readReg64 .x17 = srcBase1 + 56#64 ∧
      s1.readReg64 .x19 = x.chainPtr ∧ s1.readReg64 .x20 = x.out ∧
      s1.readReg64 .x22 = BitVec.ofNat 64 len ∧ s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 m₁).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_true; simp only [hult_hi_true, ↓reduceIte, hhead_ne_cap]
    dsimp only [len] at hlen_sub_m1 hult_hi_true hhi_true hult_false
    by_vm_steps (
      wp_steps; dsimp only [srcBase1]
      rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done)
  · rintro s1 hpc1 hrun1 hcl1 hvm1 ⟨hacp1, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase1 newLinksPtr hsp0_align
      (by rw [hrem1_len]; exact hm1_pos) (by rw [hrem1G_len, hrem1_len]) rfl
      (by rw [List.length_nil, Nat.zero_add, hrem1_len]; exact hm1_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 (by rw [hrem1_len]; exact hx12_1)
      hx13_1 hx14_1 hx15_1 (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append, hrem1_len] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (chain_sepWP_seq_lscl_mid hcl1 (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.repAlloc.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A.repAlloc) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents evs_alloc st) s1 ∗
          calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hvm2, hacp_l1, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    have hacp2 : AllocCallPreserved s0 s2 := hacp1.trans hacp_l1
    rw [hx0_1] at hx0_2; rw [hx3_1] at hx3_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2; rw [hx11_1] at hx11_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    refine SepWP.weaken_pre hP2 ?_
    rw [← A.pool_of_vmPreserved hvm2]
    refine seq_vm_clean_lscl hcl2 (mid := (blkPl_365).base + 512#64)
      (P_mid := memRegion srcBase1 (m₁ * 112) ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
          ((rem1G.map toChainEpochPBGhost).zip (rem1.map chainEpochIntoPb)) ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.repAlloc.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A.repAlloc) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents evs_alloc st) s2 ∗
          calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32))
      (Q := fun s3 =>
        AllocCallPreserved s0 s3 ∧
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x0 = newLinksPtr ∧ s3.readReg64 .x2 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x3 = x.gChain.linksCap ∧ s3.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧
        s3.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧ s3.readReg64 .x10 = s0.sp - 160#64 ∧
        s3.readReg64 .x11 = BitVec.ofNat 64 (m₂ - 1) ∧ s3.readReg64 .x12 = s0.sp - 160#64 ∧
        s3.readReg64 .x13 = s0.sp - 208#64 ∧ s3.readReg64 .x14 = s0.sp - 260#64 ∧
        s3.readReg64 .x15 = newLinksPtr + BitVec.ofNat 64 (m₁ * 112) + 52#64 ∧
        s3.readReg64 .x16 = x.gChain.linksPtr + 56#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x22 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp2
      by_vm_steps (wp_steps; wp_done)
    · rintro s3 hpc3 hrun3 hcl3 hvm3 ⟨hacp3, hsp3, htr3, hfp3, hx0_3, hx2_3, hx3_3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx14_3, hx15_3, hx16_3, hx19_3, hx20_3, hx22_3, hx25_3, hx26_3, hx28_3⟩
      rw [← A.pool_of_vmPreserved hvm3]
      have h0_bv : BitVec.ofNat 64 0 = 0#64 := rfl
      have hrun_l2 := hloop2 s3 x.gChain x.chain x.gChain.linksPtr newLinksPtr m₁ hsp0_align
        (by rw [hrem2_len]; exact hm2_pos) (by rw [hrem2G_len, hrem2_len])
        (by rw [hrem1G_len, hrem1_len]) (by rw [hrem1_len])
        (by rw [hrem1_len, hrem2_len, hm_sum]; exact hl_new_lt)
        hpc3 hrun3 hsp3 htr3 hfp3 (by rw [hrem2_len]; exact hx9_3)
        hx10_3 hx12_3 hx13_3 hx14_3 (by rw [hrem1_len]; exact hx15_3)
        (by rw [hrem1_len, Nat.sub_self, Nat.zero_mul, h0_bv, BitVec.add_zero]; exact hx16_3)
      have happG : rem1G ++ rem2G = x.gChain.epochs := List.take_append_drop m₁ x.gChain.epochs
      have happ : rem1 ++ rem2 = x.chain.links := List.take_append_drop m₁ x.chain.links
      simp only [hrem1_len, hrem2_len, Nat.sub_self, Nat.zero_mul, Nat.zero_add,
        memRegion_zero, emp_sepConj, h0_bv, BitVec.add_zero, happG, happ] at hrun_l2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (chain_sepWP_seq_lscl_mid hcl3 (SepWP.frame_post_entails (F :=
          memRegion srcBase1 (m₁ * 112) ∗ memRegion x.out 80 ∗
            chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
            A.repAlloc.live newLinksPtr (len * 112) 8 ∗ A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗
            memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
            vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
            A.pool lim (M.stepEvents evs_alloc st) s3 ∗
            calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l2) ?_)
      rintro s4 P4 hpc4 hrun4 hcl4 ⟨hP4, hvm4, hacp_l2, hsp4, htr4, hfp4, hx0_4, hx2_4, hx3_4, hx8_4, hx11_4, hcs4⟩
      have hacp4 : AllocCallPreserved s0 s4 := hacp3.trans hacp_l2
      rw [hx0_3] at hx0_4; rw [hx2_3] at hx2_4; rw [hx3_3] at hx3_4; rw [hx8_3] at hx8_4; rw [hx11_3] at hx11_4
      have hx19_4 : s4.readReg64 .x19 = x.chainPtr := (hcs4.1).trans hx19_3
      have hx20_4 : s4.readReg64 .x20 = x.out := (hcs4.2.1).trans hx20_3
      have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 len := (hcs4.2.2.2.1).trans hx22_3
      have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 len := (hcs4.2.2.2.2.2.2.1).trans hx25_3
      have hx26_4 : s4.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs4.2.2.2.2.2.2.2.1).trans hx26_3
      have hx28_4 : s4.readReg64 .x28 = x.gChain.linksPtr := (hcs4.2.2.2.2.2.2.2.2.2.1).trans hx28_3
      have hjoin_old := memRegion_wrap_join x.gChain.linksPtr cap head len hl_cap_lt hhead_lt hl_le hwrap
      have hnew_raw : A.repAlloc.live newLinksPtr (len * 112) 8 ⊢
          linksRawAllocAt A.repAlloc (BitVec.ofNat 64 len) newLinksPtr len := by
        unfold linksRawAllocAt
        have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
          absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
        have htn : (BitVec.ofNat 64 len).toNat = len := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
        exact Entails.refl _
      refine SepWP.weaken_pre hP4 ?_
      rw [← A.pool_of_vmPreserved hvm4]
      refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase1, m₁, m₂]; sep_focus) ?_
      refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
      refine seq_vm_clean_lscl hcl4 (mid := (blkPl_365).base + 820#64)
        (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A.repAlloc (BitVec.ofNat 64 len) newLinksPtr len ∗
          (if (x.gChain.linksCap == 0#64) = true then emp
           else A.repAlloc.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents evs_alloc st) s4 ∗
          intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun s5 =>
          AllocCallPreserved s0 s5 ∧
          s5.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s5 s0 ∧ s5.readReg64 .fp = s0.sp - 96#64 ∧
          s5.readReg64 .x8 = 0#64 ∧ s5.readReg64 .x9 = 0#64 ∧ s5.readReg64 .x19 = x.chainPtr ∧
          s5.readReg64 .x20 = x.out ∧ s5.readReg64 .x21 = BitVec.ofNat 64 len ∧
          s5.readReg64 .x22 = BitVec.ofNat 64 len ∧ s5.readReg64 .x23 = 0#64 ∧
          s5.readReg64 .x24 = newLinksPtr ∧ s5.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          s5.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
      · have ⟨_, _, _, _, _, _, _⟩ := hacp4
        by_vm_steps (simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done)
      · rintro s5 hpc5 hrun5 hcl5 hvm5 ⟨hacp5, hsp5, htr5, hfp5, hx8_5, hx9_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx26_5, hx28_5⟩
        rw [← A.pool_of_vmPreserved hvm5]
        exact hepilogue s5 newLinksPtr hcl5 hevs_alloc hacp5 hsp0_align hlen hl_cap_lt hl_cap_ne
          hl_new_lt hl_new_ne hn1 hn2 hn3 hpc5 hrun5 hsp5 htr5 hfp5 hx8_5 hx9_5 hx19_5 hx20_5
          hx21_5 hx22_5 hx23_5 hx24_5 hx26_5 hx28_5

/-! ## Prologue, Empty-Links Path, Allocation Step, and Top-Level Contracts -/

private theorem ofNat_len_mul_112_shift_eq {n : Nat} (hn : n * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 n <<< 7#64) - (BitVec.ofNat 64 n <<< 4#64) = BitVec.ofNat 64 (n * 112) := by
  have htn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h := cap_mul_112_shift_eq (BitVec.ofNat 64 n) (by rw [htn]; exact hn)
  rwa [htn] at h

private theorem ofNat_len_ls_cond {n : Nat} (hn : n * 112 < 2 ^ 63) :
    (!(!BitVec.ult (BitVec.ofNat 64 n) 82351536043346212#64 &&
      !(BitVec.ofNat 64 n - 82351536043346212#64 == 0#64))) = true := by
  have hn64 : n < 18446744073709551616 := by omega
  have hmax : (82351536043346212#64).toNat = 82351536043346212 := rfl
  rcases Nat.lt_or_eq_of_le (show n ≤ 82351536043346212 by omega) with hlt | rfl
  · have hu : BitVec.ult (BitVec.ofNat 64 n) 82351536043346212#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, hmax, decide_eq_true_eq]
      exact hlt
    simp [hu]
  · rfl

private theorem stackAt_chainIntoPb_split_prologue (s0 : State) :
    stackAt s0.sp chainIntoPbStack =
      stackAt (s0.sp - 288#64) dropStack32 ∗ intoPbLoopScratchAt s0 ∗
      (∃∗ s00 : BitVec 64, (s0.sp - 288#64) ↦₆₄ s00) ∗ (∃∗ s08 : BitVec 64, (s0.sp - 280#64) ↦₆₄ s08) ∗
      (∃∗ s10 : BitVec 64, (s0.sp - 272#64) ↦₆₄ s10) ∗ (∃∗ sc0 : BitVec 64, (s0.sp - 96#64) ↦₆₄ sc0) ∗
      (∃∗ sc8 : BitVec 64, (s0.sp - 88#64) ↦₆₄ sc8) ∗ (∃∗ sd0 : BitVec 64, (s0.sp - 80#64) ↦₆₄ sd0) ∗
      (∃∗ sd8 : BitVec 64, (s0.sp - 72#64) ↦₆₄ sd8) ∗ (∃∗ se0 : BitVec 64, (s0.sp - 64#64) ↦₆₄ se0) ∗
      (∃∗ se8 : BitVec 64, (s0.sp - 56#64) ↦₆₄ se8) ∗ (∃∗ sf0 : BitVec 64, (s0.sp - 48#64) ↦₆₄ sf0) ∗
      (∃∗ sf8 : BitVec 64, (s0.sp - 40#64) ↦₆₄ sf8) ∗ (∃∗ s100 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s100) ∗
      (∃∗ s108 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s108) ∗ (∃∗ s110 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s110) ∗
      (∃∗ s118 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s118) := by
  rw [stackAt_chainIntoPb_split s0.sp]; unfold intoPbLoopScratchAt; sep_ac_rfl

set_option maxHeartbeats 800000 in
private theorem intoPb_prologue_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (x : ChainIntoPbCall) (st : M.σ) (s0 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc : s0.pc = (blkPl_365).base) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.out) (hx0 : s0.readReg64 .x0 = x.chainPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      ((blkPl_365).base + 116#64) s0
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
             x.gChain.linksHead.toNat x.gChain.linksPtr
             (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim st s0 ∗ stackAt s0.sp chainIntoPbStack)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        ((P1 ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          (if x.gChain.linksCap = 0 then emp
           else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
               x.gChain.linksHead.toNat x.gChain.linksPtr
               (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim st s0 ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32) ∧
        AllocCallPreserved s0 s1 ∧
        s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
        s1.readReg64 .x3 = x.gChain.linksCap ∧ s1.readReg64 .x19 = x.chainPtr ∧
        s1.readReg64 .x20 = x.out ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s1.readReg64 .x27 = x.gChain.linksHead ∧ s1.readReg64 .x28 = x.gChain.linksPtr)) := by
  have hule := ofNat_len_ule_max_112 hl_new_lt
  have hls := ofNat_len_ls_cond hl_new_lt
  have hshift := ofNat_len_mul_112_shift_eq hl_new_lt
  by_vm_steps (
    rw [stackAt_chainIntoPb_split_prologue s0]; wp_pull_exists
    unfold chainHeaderCellsAt; wp_steps
    unfold intoPbScratchAt calleeSavedFromPbAt; wp_done)

/-- Code-loaded `[LibsignalPlacement]` empty-links fast path (`+116 .. lr` when `x.chain.links = []`). -/
theorem intoPb_empty_links_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainIntoPbCall) (st : M.σ) (s0 s1 : State)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hacp1 : AllocCallPreserved s0 s1)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hnil : x.chain.links = [])
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc1 : s1.pc = (blkPl_365).base + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
             x.gChain.linksHead.toNat x.gChain.linksPtr
             (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim st s1 ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost M A lim x st s0) := by
  have hevs_nil : ChainIntoPbAllocEnv x [] := by simp [ChainIntoPbAllocEnv, hnil]
  have hepilogue := @chainIntoPb_epilogue_cl_placed _ M A lim H hdealloc hdrop x st [] s0
  have hlen0 : x.chain.links.length = 0 := by rw [hnil]; rfl
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by rw [hlen0]; decide
  have hdealloc_buf := vecDequeSlots_nil_entails_dealloc A.repAlloc x.gChain.linksCap x.gChain.linksPtr
    x.gChain.linksHead x.gChain.epochs x.chain.links hnil hl_cap_lt
  have hraw0 : (emp : SepProp) ⊢
      arrayAt (chainEpochPBAt A.repAlloc) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length := by
    unfold linksRawAllocAt; simp [hnil, arrayAt]; exact Entails.refl _
  refine SepWP.focus_weaken hdealloc_buf (by sep_focus) ?_
  refine seq_vm_clean_lscl hcl1 (mid := (blkPl_365).base + 820#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool lim st s1 ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s2 =>
      AllocCallPreserved s0 s2 ∧
      s2.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s2 s0 ∧ s2.readReg64 .fp = s0.sp - 96#64 ∧
      s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x9 = 0#64 ∧ s2.readReg64 .x19 = x.chainPtr ∧
      s2.readReg64 .x20 = x.out ∧ s2.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧ s2.readReg64 .x23 = 0#64 ∧
      s2.readReg64 .x24 = 8#64 ∧ s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s2.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rw [hlen0] at hx23_1 hx25_1 ⊢
    simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat] at hx23_1 hx25_1 ⊢
    by_vm_steps (
      wp_steps; rw [← emp_sepConj (memRegion x.out 80 ∗ _)]
      refine SepWP.focus_weaken hraw0 (by sep_focus) ?_
      rw [hlen0]; wp_done)
  · rintro s2 hpc2 hrun2 hcl2 hvm2 ⟨hacp2, hsp2, htr2, hfp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx28_2⟩
    rw [← A.pool_of_vmPreserved hvm2]
    change SepWP _ _ _
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112 8#64
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents ([] : List AllocEvent) st) s2 ∗
        intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32) _
    exact hepilogue s2 8#64 hcl2 hevs_nil hacp2 hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt (by decide)
      hn1 hn2 hn3 hpc2 hrun2 hsp2 htr2 hfp2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2
      hx23_2 hx24_2 hx26_2 hx28_2

set_option maxHeartbeats 800000 in
private theorem intoPb_alloc_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (x : ChainIntoPbCall) (st : M.σ) (s0 s1 : State)
    (hFit : FitsEnv M lim st (ChainIntoPbAllocEnv x))
    (hacp1 : AllocCallPreserved s0 s1)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc1 : s1.pc = (blkPl_365).base + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = x.gChain.linksHead)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      ((blkPl_365).base + 148#64) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
             x.gChain.linksHead.toNat x.gChain.linksPtr
             (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim st s1 ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (fun sm Pm =>
        (Pm ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.repAlloc.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
          memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
          (if x.gChain.linksCap = 0 then emp
           else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
               x.gChain.linksHead.toNat x.gChain.linksPtr
               (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents (rustAllocEvents (x.chain.links.length * 112) 8) st) sm ∗
          intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32) ∧
        AllocCallPreserved s0 sm ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x0 ≠ 0#64 ∧
        sm.sp = s0.sp - 288#64 ∧ sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x3 = x.gChain.linksCap ∧ sm.readReg64 .x19 = x.chainPtr ∧
        sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        sm.readReg64 .x24 = 8#64 ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.gChain.linksHead ∧ sm.readReg64 .x28 = x.gChain.linksPtr) := by
  rcases htr1 with ⟨htr1_eq, hvr1⟩
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hcbz_23 : (BitVec.ofNat 64 (x.chain.links.length * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hl_new_lt
  have hnil : x.chain.links ≠ [] := List.length_pos_iff.mp (by omega)
  have hFit_alloc : FitsEvents M lim st (rustAllocEvents (x.chain.links.length * 112) 8) :=
    hFit _ (by simp [ChainIntoPbAllocEnv, hnil])
  have halign8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlayout : RustLayoutOk (x.chain.links.length * 112) 8 :=
    ⟨⟨by omega, halign8, by omega⟩, by decide⟩
  have hsz_tn : (BitVec.ofNat 64 (x.chain.links.length * 112)).toNat =
      x.chain.links.length * 112 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  have hsplit_stack : stackAt (s0.sp - 288#64) dropStack32 =
      stackAt (s0.sp - 288#64) allocHookStack ∗ memRegion (s0.sp - 4416#64) 32 := by
    rw [stackAt_dropStack32_split_allocHook, BitVec.sub_sub]; rfl
  have ⟨_, _, _, _, _, _, _⟩ := hacp1
  dsimp only [rustAllocShimVmSpec, rustCliAllocNoOomSpec, BitVec.ofNat_eq_ofNat, ↓reduceIte]
    at hshim halloc_nooom ⊢
  rw [hsplit_stack]; unfold intoPbScratchAt
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have hacp_sf : AllocCallPreserved s0 sf := by
    refine hacp1.trans (AllocCallPreserved.trans ?_ ‹AllocCallPreserved _ sf›)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm]
  have hsp_sf : sf.sp = s0.sp - 288#64 := by
    simp only [‹sf.sp = _›, wp_norm, arm64_norm, hsp1]
  have ⟨_, _, _, _, _, _, _⟩ := hacp_sf
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  simp only [State.setMem_setMem]
  wp_call halloc_nooom (x.chain.links.length * 112, 8, st)
  have hacp_sf1 : AllocCallPreserved s0 sf_1 := by
    refine hacp_sf.trans (AllocCallPreserved.trans ?_ ‹AllocCallPreserved _ sf_1›)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm]
  have hsp_sf1 : sf_1.sp = s0.sp - 288#64 := by
    simp only [‹sf_1.sp = _›, wp_norm, arm64_norm, hsp_sf]
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  rcases hacp_sf1 with ⟨_, _, _, _, _, _, _⟩
  simp only [wp_norm, arm64_norm, hsp_sf]
  wp_steps_sync_pool ((blkPl_365).base + 148#64)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Reg.x0, wp_norm, arm64_norm, RustCliAllocBudget.repAlloc_live]
    exact Entails.of_eq (by sep_ac_rfl)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · refine ⟨?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · simpa only [Reg.x0, wp_norm, arm64_norm] using hne0
  · simp only [wp_norm, arm64_norm, hsp_sf1]
  · simp only [Reg.fp, wp_norm, arm64_norm, *]
  · simp only [Reg.x3, wp_norm, arm64_norm, *]
  · simp only [Reg.x19, wp_norm, arm64_norm, *]
  · simp only [Reg.x20, wp_norm, arm64_norm, *]
  · simp only [Reg.x22, BitVec.ofNat_eq_ofNat, wp_norm, arm64_norm, *]
  · simp only [Reg.x23, BitVec.ofNat_eq_ofNat, wp_norm, arm64_norm, *]
  · simp only [Reg.x24, wp_norm, arm64_norm, *]
  · simp only [Reg.x25, BitVec.ofNat_eq_ofNat, wp_norm, arm64_norm, *]
  · simp only [Reg.x26, wp_norm, arm64_norm, *]
  · simp only [Reg.x27, wp_norm, arm64_norm, *]
  · simp only [Reg.x28, wp_norm, arm64_norm, *]

/-- Code-loaded `[LibsignalPlacement]` combined post-allocation path (`+148 .. lr`). -/
theorem intoPb_post_alloc_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainIntoPbCall) (st : M.σ) (s0 sm : State)
    (hclm : LibsignalCodeLoaded lsmpl sm.mem)
    (hacpm : AllocCallPreserved s0 sm)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_head : if x.gChain.linksCap = 0 then x.gChain.linksHead = 0
               else x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpcm : sm.pc = (blkPl_365).base + 148#64)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 288#64) (htrm : TraceCalleeSaved sm s0)
    (hfpm : sm.readReg64 .fp = s0.sp - 96#64) (hx0m_ne : sm.readReg64 .x0 ≠ 0#64)
    (hx3m : sm.readReg64 .x3 = x.gChain.linksCap) (hx19m : sm.readReg64 .x19 = x.chainPtr)
    (hx20m : sm.readReg64 .x20 = x.out)
    (hx22m : sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24m : sm.readReg64 .x24 = 8#64)
    (hx25m : sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26m : sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27m : sm.readReg64 .x27 = x.gChain.linksHead)
    (hx28m : sm.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) sm
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.repAlloc.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
        memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
        (if x.gChain.linksCap = 0 then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat
             x.gChain.linksHead.toNat x.gChain.linksPtr
             (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents (rustAllocEvents (x.chain.links.length * 112) 8) st) sm ∗
        intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost M A lim x st s0) := by
  have hcap_ne0 : x.gChain.linksCap ≠ 0#64 := by
    intro h0; rw [h0] at hl_le; change x.chain.links.length ≤ 0 at hl_le; omega
  have hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat := by
    simpa only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte] using hl_head
  simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte, sepConj_assoc]
  have hacpm_set : AllocCallPreserved s0 (sm.setPC ((blkPl_365).base + 156#64)) := by
    rcases hacpm with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hnonwrap_lem := intoPb_post_alloc_nonwrap_cl_placed (M := M) (A := A) (lim := lim) (H := H)
    hdealloc hdrop x st s0 (sm.setPC ((blkPl_365).base + 156#64)) (sm.readReg64 .x0) hclm hacpm_set
  have hwrap_lem := intoPb_post_alloc_wrap_cl_placed (M := M) (A := A) (lim := lim) (H := H)
    hdealloc hdrop x st s0 (sm.setPC ((blkPl_365).base + 156#64)) (sm.readReg64 .x0) hclm hacpm_set
  have hcbz_x0 : (sm.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hx0m_ne
  have hcbz_x25 : (BitVec.ofNat 64 x.chain.links.length == 0#64) = false :=
    ofNat_beq_zero_false_of_lt (by omega) (by omega)
  refine seq_vm_clean (mid := (blkPl_365).base + 156#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.repAlloc.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
      memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
      A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
      vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
        x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
      vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool lim (M.stepEvents (rustAllocEvents (x.chain.links.length * 112) 8) st)
        (sm.setPC ((blkPl_365).base + 156#64)) ∗
      intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 => s1 = sm.setPC ((blkPl_365).base + 156#64)) ?_ ?_
  · rw [A.pool_setPC]
    by_vm_steps (
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, Entails.refl _, rfl⟩)
  · rintro _ _ _ _ rfl
    by_cases hnw : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat
    · exact hnonwrap_lem hsp0_align hlen hlen_pos hl_le hl_cap_lt hl_cap_ne hhead_lt
        hnw hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
        hx24m hx25m hx26m hx27m hx28m
    · exact hwrap_lem hsp0_align hlen hl_le hl_cap_lt hl_cap_ne hhead_lt
        (by omega) hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
        hx24m hx25m hx26m hx27m hx28m

set_option maxHeartbeats 800000 in
/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbPinnedSpec M A lim)`. -/
theorem chain_into_pb_pinned_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim))) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbPinnedSpec M A lim)) := by
  refine subroutine_ok_of_sepWPp fun ⟨x, st⟩ R s0 hpc hrun hpre hsp_align => ?_
  obtain ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  refine ⟨(chainIntoPbPinnedSpec M A lim).pre (x, st) s0, R, hpre', ?_⟩
  dsimp only [State.spAligned] at hsp_align
  refine SepWPp.of_sepWP_ret ?_
  wp_conv_pre => dsimp only [chainIntoPbPinnedSpec]
  wp_focus_pure
  rintro ⟨hx8, hx0, hFit⟩
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (chainAt_unpack A.repAlloc x.chainPtr x.gChain x.chain))) ?_
  wp_focus_pure
  rintro ⟨hlen, hl_le, hl_cap_lt, hl_cap_ne, hl_head, hn1, hn2, hn3⟩
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by omega
  wp_simp_pre [sepConj_assoc]
  refine chain_sepWP_seq_lscl_mid hcl0 (intoPb_prologue_placed (A := A) (lim := lim) x st s0
    hsp_align hl_new_lt hpc hrun hx8 hx0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hvm1, hP1, hacp1, hsp1, htr1, hfp1, hx3_1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [← A.pool_of_vmPreserved hvm1]
  by_cases hnil : x.chain.links = []
  · refine SepWP.mono (intoPb_empty_links_cl_placed hdealloc hdrop x st s0 s1 hcl1 hacp1 hsp_align
      hnil hlen hl_cap_lt hl_cap_ne hn1 hn2 hn3 hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1
      hx25_1 hx26_1 hx28_1) ?_
    rintro sf P_f _ _ ⟨hP_f, hspf, _htrf, hcsf⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hP_f) hm, hspf, hcsf⟩
  · have hlen_pos : 1 ≤ x.chain.links.length := Nat.pos_of_ne_zero (List.length_pos_iff.mpr hnil).ne'
    refine chain_sepWP_seq_lscl_mid hcl1 (intoPb_alloc_step_placed hshim halloc x st s0 s1 hFit
      hacp1 hsp_align hlen_pos hl_new_lt hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1
      hx26_1 hx27_1 hx28_1) ?_
    rintro sm Pm hpcm hrunm hclm ⟨hPm, hacpm, htrm, hoom_ne, hspm, hfpm, hx3m, hx19m, hx20m, hx22m, _hx23m, hx24m, hx25m, hx26m, hx27m, hx28m⟩
    refine SepWP.weaken_pre hPm ?_
    refine SepWP.mono (intoPb_post_alloc_ok_cl_placed hdealloc hdrop x st s0 sm hclm hacpm hsp_align
      hlen_pos hlen hl_le hl_cap_lt hl_cap_ne hl_head hn1 hn2 hn3 hpcm hrunm hspm htrm hfpm
      hoom_ne hx3m hx19m hx20m hx22m hx24m hx25m hx26m hx27m hx28m) ?_
    rintro sf P_f _ _ ⟨hP_f, hspf, _htrf, hcsf⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hP_f) hm, hspf, hcsf⟩

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbSpec M A lim)`. -/
theorem chain_into_pb_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim))) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbSpec M A lim)) := by
  have hpinned := chain_into_pb_pinned_cl_placed_ok hshim halloc hdealloc hdrop
  refine subroutine_ok_mono hpinned (fun _ _ _ hp => hp) (fun ⟨x, st⟩ s0 sf _ hq => ?_)
  dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec, chainIntoPbSpec] at hq ⊢
  refine Satisfies.mono ?_ hq
  exact sepConj_mono_left (Entails.sepExists_elim fun evs =>
    Entails.sepExists_right evs
      (sepConj_mono_right (sepConj_mono_left
        (chainPBIntoPinnedAt_entails_protoRepr A.repAlloc x.gChain x.out x.chain))))

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbPinnedSpecX M A lim)`. -/
theorem chain_into_pb_pinned_cl_placed_ok_X [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim))) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbPinnedSpecX M A lim)) := by
  have hpinned := chain_into_pb_pinned_cl_placed_ok hshim halloc hdealloc hdrop
  refine LibsignalBinary.Heap.IfaceLemmas.subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - 16672#64) 12256) hpinned ?_ ?_
  · rintro ⟨x, st⟩ s0
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX]
    rw [stackAt_chainIntoPbX_split s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨x, st⟩ s0 sf
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    rw [stackAt_chainIntoPbX_split s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbSpecX M A lim)`. -/
theorem chain_into_pb_cl_placed_ok_X [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim))) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbSpecX M A lim)) := by
  have hpinned := chain_into_pb_pinned_cl_placed_ok_X hshim halloc hdealloc hdrop
  refine subroutine_ok_mono hpinned (fun _ _ _ hp => hp) (fun ⟨x, st⟩ s0 sf _ hq => ?_)
  dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpecX, chainIntoPbSpecX] at hq ⊢
  refine Satisfies.mono ?_ hq
  exact sepConj_mono_left (Entails.sepExists_elim fun evs =>
    Entails.sepExists_right evs
      (sepConj_mono_right (sepConj_mono_left
        (chainPBIntoPinnedAt_entails_protoRepr A.repAlloc x.gChain x.out x.chain))))

end LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbClPlacedBudget
