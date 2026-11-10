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
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Loop Error Cleanup Proofs for `Chain::from_pb` (Block `364`)

Budget-threaded, code-loaded `[LibsignalPlacement]` loop error-cleanup lemmas (`+380`, `+452`,
`+520`, `+644`, `+780`) for `<spqr::chain::Chain>::from_pb` (`blkPC_364`) under
`RustCliAllocBudget M`, threading `LibsignalCodeLoaded lsmpl` into `fromPb_join_err_cl_placed`.
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
  LibsignalCodeLoaded LibsignalPlacement blkPC_364 blkPl_364 lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Chain ChainEpoch ChainEpochPB)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost TraceCalleeSaved add_one_beq_zero_of_lt_pow63 calleeSavedFromPbAt
  chainEpochAt chainFromPbSubStack chainPBHeadersAt joinScratchAt linksRawAllocAt
  loopScratchAt loopScratchAt_entails_joinScratchAt stackAt_subStack_split_allocHook
  vecU8BufAt
)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Top.ChainFrom (ChainEpochPBGhost ChainFromPbCall chainEpochPBAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinBudget (fromPbRetPost)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudget (fromPb_join_err_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1 (
  deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil sepWP_prepend_evs
  seq_clean_evs_lscl seq_vm_clean_lscl subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoopBudget (
  fromPb_loop_err_452_to_520_placed fromPb_loop_err_644_to_704_placed
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoEpochSliceSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoopClPlacedBudget

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

private theorem sepWP_vm_transport {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {target : BitVec 64} {s : State} {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (htrans : ∀ sm, VmPreserved s sm → P_mid s = P_mid sm)
    (h : SepWP (P.rebase b Hk) target s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid s) ∧ Q sm)) :
    SepWP (P.rebase b Hk) target s Pre
      (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.mono h fun sm Pm _ _ ⟨hvm, hent, hQ⟩ => ⟨htrans sm hvm ▸ hent, hQ⟩

/-! ## Code-Loaded `[LibsignalPlacement]` Error Cleanup Helpers (Block `364`) -/

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+520` when `curPB.recv = none` (`x20 = 0xffffffffffffffff#64`). -/
theorem fromPb_loop_err_520_none_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have herr := @fromPb_join_err_cl_placed _ M A lim H hdealloc hchain_slice hproto_slice x
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  refine seq_vm_clean_lscl hcl (mid := (blkPl_364).base + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      A.pool lim st s ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    by_vm_steps (
      unfold loopScratchAt
      wp_steps
      refine SepWP.focus_weaken
        (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
        (by unfold loopScratchAt; sep_focus) ?_
      wp_done)
  · rintro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hacp1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    rw [← A.pool_transport lim st s s1 hvm1]
    exact herr st s0 s1 convG convEpochs remG remPB sp0_val hcl1 hacp1 hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+520` when `curPB.recv = some recvPb`. -/
theorem fromPb_loop_err_520_some_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (rncap rnptr rpcap rpptr sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc rncap rnptr ∗ vecCapPtrDealloc A.repAlloc rpcap rpptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have herr := @fromPb_join_err_cl_placed _ M A lim H hdealloc hchain_slice hproto_slice x
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hrn_cmn := add_one_beq_zero_of_lt_pow63 hrn_lt
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, BitVec.ofNat_eq_ofNat] at herr hdealloc_fo hpc ⊢
  refine seq_clean_evs_lscl hcl (mid := (blkPl_364).base + 596#64)
    (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A.repAlloc rpcap rpptr ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x12 = rpptr ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = rpcap) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    unfold vecCapPtrDealloc loopScratchAt
    by_cases hrn : rncap = 0
    · have hrnb : (rncap == 0#64) = true := beq_iff_eq.mpr hrn
      simp only [hrnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ _ sm hvm]) ?_
      by_vm_steps (wp_steps; wp_done)
    · have hrnb : (rncap == 0#64) = false := beq_eq_false_iff_ne.mpr hrn
      have hrn_pos : rncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrnb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      rw [stackAt_subStack_split_allocHook s0.sp]
      apply sepWP_evs_dealloc rncap.toNat 1
      wp_steps
      wp_call hdealloc_fo (rnptr, rncap.toNat, 1, st)
      have hacp_s0 : AllocCallPreserved s0 sf := by
        refine hacp.trans ?_
        simp only [wp_norm, arm64_norm] at *
        assumption
      rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
      refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ sf sm hvm]) ?_
      by_vm_steps (wp_steps; rw [hsp]; wp_done)
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx0_1, hx11_1, hx12_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1⟩
    apply sepWP_prepend_evs hevs1
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs_lscl hcl1 (mid := (blkPl_364).base + 792#64)
      (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
        sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp1
      unfold vecCapPtrDealloc loopScratchAt
      by_cases hrp : rpcap = 0
      · have hrpb : (rpcap == 0#64) = true := beq_iff_eq.mpr hrp
        simp only [hrpb, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ _ sm hvm]) ?_
        by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken
            (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
            (by unfold loopScratchAt; sep_focus) ?_
          wp_done)
      · have hrpb : (rpcap == 0#64) = false := beq_eq_false_iff_ne.mpr hrp
        have hrp_pos : rpcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hrp (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hrpb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        rw [stackAt_subStack_split_allocHook s0.sp]
        apply sepWP_evs_dealloc rpcap.toNat 1
        wp_steps
        wp_call hdealloc_fo (rpptr, rpcap.toNat, 1, st1)
        have hacp_s0 : AllocCallPreserved s0 sf := by
          refine hacp1.trans ?_
          simp only [wp_norm, arm64_norm] at *
          assumption
        rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
        refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ sf sm hvm]) ?_
        by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken
            (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
            (by unfold loopScratchAt; sep_focus) ?_
          rw [hsp1]
          wp_done)
    · rintro evs2 s2 hevs2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hacp2, hfp2, hx0_2, hx11_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2⟩
      apply sepWP_prepend_evs hevs2
      exact herr (M.stepEvents evs2 st1) s0 s2 convG convEpochs remG remPB sp0_val hcl2 hacp2
        hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx0_2 hx11_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Tail bridge at `+780 .. +792` into `fromPb_join_err_cl_placed`. -/
theorem fromPb_loop_err_780_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = 0#64)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have herr := @fromPb_join_err_cl_placed _ M A lim H hdealloc hchain_slice hproto_slice x
  dsimp only [BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  refine seq_vm_clean_lscl hcl (mid := (blkPl_364).base + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      A.pool lim st s ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    by_vm_steps (
      unfold loopScratchAt
      wp_steps
      refine SepWP.focus_weaken
        (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
        (by unfold loopScratchAt; sep_focus) ?_
      wp_done)
  · rintro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hacp1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    rw [← A.pool_transport lim st s s1 hvm1]
    exact herr st s0 s1 convG convEpochs remG remPB sp0_val hcl1 hacp1 hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+380` when `curPB.recv = none`. -/
theorem fromPb_loop_err_380_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 380#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = snptr) (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc sncap snptr ∗ vecCapPtrDealloc A.repAlloc spcap spptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have h780 := @fromPb_loop_err_780_cl_placed _ M A lim H hdealloc hchain_slice hproto_slice x
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, BitVec.ofNat_eq_ofNat] at h780 hdealloc_fo hpc ⊢
  refine seq_clean_evs_lscl hcl (mid := (blkPl_364).base + 408#64)
    (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A.repAlloc spcap spptr ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    unfold vecCapPtrDealloc loopScratchAt
    by_cases hsn : sncap = 0
    · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
      simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ _ sm hvm]) ?_
      by_vm_steps (wp_steps; wp_done)
    · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
      have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hsnb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      rw [stackAt_subStack_split_allocHook s0.sp]
      apply sepWP_evs_dealloc sncap.toNat 1
      wp_steps
      wp_call hdealloc_fo (snptr, sncap.toNat, 1, st)
      have hacp_s0 : AllocCallPreserved s0 sf := by
        refine hacp.trans ?_
        simp only [wp_norm, arm64_norm] at *
        assumption
      rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
      refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ sf sm hvm]) ?_
      by_vm_steps (wp_steps; rw [hsp]; wp_done)
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx11_1, hx23_1, hx27_1, hx28_1⟩
    apply sepWP_prepend_evs hevs1
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs_lscl hcl1 (mid := (blkPl_364).base + 780#64)
      (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = 0#64) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp1
      unfold vecCapPtrDealloc loopScratchAt
      by_cases hsp_cap : spcap = 0
      · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
        rw [hsp_cap] at hx27_1
        simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ _ sm hvm]) ?_
        by_vm_steps (wp_steps; wp_done)
      · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
        have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hspb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        rw [stackAt_subStack_split_allocHook s0.sp]
        apply sepWP_evs_dealloc spcap.toNat 1
        wp_steps
        wp_call hdealloc_fo (spptr, spcap.toNat, 1, st1)
        have hacp_s0 : AllocCallPreserved s0 sf := by
          refine hacp1.trans ?_
          simp only [wp_norm, arm64_norm] at *
          assumption
        rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
        refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ sf sm hvm]) ?_
        by_vm_steps (wp_steps; rw [hsp1]; wp_done)
    · rintro evs2 s2 hevs2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hacp2, hfp2, hx11_2, hx19_2, hx20_2, hx23_2, hx27_2⟩
      apply sepWP_prepend_evs hevs2
      exact h780 (M.stepEvents evs2 st1) s0 s2 convG convEpochs remG remPB sp0_val hcl2 hacp2
        hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx11_2
        hx19_2 hx20_2 hx23_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+644` when `curPB.recv = some recvPb` fails `tst`. -/
theorem fromPb_loop_err_644_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x22_val sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx12 : s.readReg64 .x12 = rpptr)
    (hx19 : s.readReg64 .x19 = rnptr) (hx20 : s.readReg64 .x20 = rncap)
    (hx21 : s.readReg64 .x21 = snptr) (hx22 : s.readReg64 .x22 = x22_val)
    (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) (hx27 : s.readReg64 .x27 = spcap)
    (hx28 : s.readReg64 .x28 = spptr)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc sncap snptr ∗ vecCapPtrDealloc A.repAlloc spcap spptr ∗
        vecCapPtrDealloc A.repAlloc rncap rnptr ∗ vecCapPtrDealloc A.repAlloc rpcap rpptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A.repAlloc sncap snptr ∗ vecCapPtrDealloc A.repAlloc spcap spptr ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_644_to_704_placed _ M A lim H hdealloc F_frame
    x st s0 s convEpochs.length rncap rnptr rpcap rpptr snptr x22_val sncap spcap spptr sp0_val
    hacp hsp0_align hrn_lt hrn_ne hrp_lt hrp_ne hpc hrun hsp htr hfp hx11 hx12 hx19 hx20 hx21 hx22
    hx24 hx25 hx26 hx27 hx28
  refine seq_clean_evs_lscl hcl (mid := (blkPl_364).base + 704#64)
    (P_evs := fun evs sm => F_frame ∗ A.pool lim (M.stepEvents evs st) sm ∗
      loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x21 = snptr ∧ sm.readReg64 .x22 = x22_val ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = sncap ∧ sm.readReg64 .x27 = spcap ∧
      sm.readReg64 .x28 = spptr) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; sep_ac_rfl)
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx11_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx28_1⟩
    apply sepWP_prepend_evs hevs1
    let st1 := M.stepEvents evs1 st
    refine SepWP.weaken_pre (Entails.of_eq (by
      dsimp only [F_frame]; sep_ac_rfl :
      F_frame ∗ A.pool lim st1 s1 ∗ loopScratchAt s0 x sp0_val ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack =
      memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc sncap snptr ∗ vecCapPtrDealloc A.repAlloc spcap spptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st1 s1 ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)) ?_
    have h780 := @fromPb_loop_err_780_cl_placed _ M A lim H hdealloc hchain_slice hproto_slice x
    have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
    have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 192#64 hsp0_align (by decide)
    dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, BitVec.ofNat_eq_ofNat] at h780 hdealloc_fo hpc1 ⊢
    refine seq_clean_evs_lscl hcl1 (mid := (blkPl_364).base + 732#64)
      (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc spcap spptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x22 = x22_val ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp1
      unfold vecCapPtrDealloc loopScratchAt
      by_cases hsn : sncap = 0
      · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
        simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ _ sm hvm]) ?_
        by_vm_steps (wp_steps; wp_done)
      · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
        have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hsnb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        rw [stackAt_subStack_split_allocHook s0.sp]
        apply sepWP_evs_dealloc sncap.toNat 1
        wp_steps
        wp_call hdealloc_fo (snptr, sncap.toNat, 1, st1)
        have hacp_s0 : AllocCallPreserved s0 sf := by
          refine hacp1.trans ?_
          simp only [wp_norm, arm64_norm] at *
          assumption
        rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
        refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ sf sm hvm]) ?_
        by_vm_steps (wp_steps; rw [hsp1]; wp_done)
    · rintro evs2 s2 hevs2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hacp2, hfp2, hx11_2, hx20_2, hx22_2, hx23_2, hx27_2, hx28_2⟩
      apply sepWP_prepend_evs hevs2
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs_lscl hcl2 (mid := (blkPl_364).base + 780#64)
        (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          arrayAt (chainEpochPBAt A.repAlloc) 112
            (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
          linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
          A.pool lim (M.stepEvents evs st2) sm ∗
          loopScratchAt s0 x x22_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          AllocCallPreserved s0 sm ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x19 = 0#64 ∧
          sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
          sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
          sm.readReg64 .x27 = 0#64) ?_ ?_
      · have ⟨_, _, _, _, _, _, _⟩ := hacp2
        unfold vecCapPtrDealloc loopScratchAt
        by_cases hsp_cap : spcap = 0
        · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
          rw [hsp_cap] at hx27_2
          simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
          apply sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ _ sm hvm]) ?_
          by_vm_steps (wp_steps; wp_done)
        · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
          have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
          simp only [hspb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          rw [stackAt_subStack_split_allocHook s0.sp]
          apply sepWP_evs_dealloc spcap.toNat 1
          wp_steps
          wp_call hdealloc_fo (spptr, spcap.toNat, 1, st2)
          have hacp_s0 : AllocCallPreserved s0 sf := by
            refine hacp2.trans ?_
            simp only [wp_norm, arm64_norm] at *
            assumption
          rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
          refine sepWP_vm_transport (fun sm hvm => by rw [A.pool_transport lim _ sf sm hvm]) ?_
          by_vm_steps (wp_steps; rw [hsp2]; wp_done)
      · rintro evs3 s3 hevs3 hpc3 hrun3 hcl3 ⟨hsp3, htr3, hacp3, hfp3, hx11_3, hx19_3, hx20_3, hx23_3, hx27_3⟩
        apply sepWP_prepend_evs hevs3
        exact h780 (M.stepEvents evs3 st2) s0 s3 convG convEpochs remG remPB x22_val hcl3 hacp3
          hsp0_align hfromPb_eq hconv_len hrem_len
          hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hfp3 hx11_3
          hx19_3 hx20_3 hx23_3 hx27_3

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_none_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr x9_val sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc sncap snptr ∗ vecCapPtrDealloc A.repAlloc spcap spptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520_placed _ M A lim H hdealloc F_frame
    x st s0 s sncap snptr spcap spptr x9_val (s.readReg64 .x12) (s.readReg64 .x19)
    0xffffffffffffffff#64 (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (s.readReg64 .x26) sp0_val
    hacp hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 rfl rfl hx20 hx21
    hx23 hx24 rfl hx27 hx28
  refine seq_clean_evs_lscl hcl (mid := (blkPl_364).base + 520#64)
    (P_evs := fun evs sm => F_frame ∗ A.pool lim (M.stepEvents evs st) sm ∗
      loopScratchAt s0 x x9_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
      sm.readReg64 .x20 = 0xffffffffffffffff#64 ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = s.readReg64 .x26) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; sep_ac_rfl)
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx11_1, _, _, hx20_1, hx23_1, _⟩
    apply sepWP_prepend_evs hevs1
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_none_cl_placed hdealloc hchain_slice hproto_slice x (M.stepEvents evs1 st)
        s0 s1 convG convEpochs remG remPB x9_val hcl1 hacp1
        hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx20_1 hx23_1)
    exact Entails.of_eq (by dsimp only [F_frame]; sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_some_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x9_val sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap) (hx26 : s.readReg64 .x26 = rpcap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A.repAlloc sncap snptr ∗ vecCapPtrDealloc A.repAlloc spcap spptr ∗
        vecCapPtrDealloc A.repAlloc rncap rnptr ∗ vecCapPtrDealloc A.repAlloc rpcap rpptr ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A.repAlloc rncap rnptr ∗ vecCapPtrDealloc A.repAlloc rpcap rpptr ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520_placed _ M A lim H hdealloc F_frame
    x st s0 s sncap snptr spcap spptr x9_val rpptr rnptr rncap
    (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) rpcap sp0_val
    hacp hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 hx12 hx19 hx20 hx21
    hx23 hx24 hx26 hx27 hx28
  refine seq_clean_evs_lscl hcl (mid := (blkPl_364).base + 520#64)
    (P_evs := fun evs sm => F_frame ∗ A.pool lim (M.stepEvents evs st) sm ∗
      loopScratchAt s0 x x9_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = rpptr ∧ sm.readReg64 .x19 = rnptr ∧
      sm.readReg64 .x20 = rncap ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = rpcap) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; sep_ac_rfl)
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1⟩
    apply sepWP_prepend_evs hevs1
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_some_cl_placed hdealloc hchain_slice hproto_slice x (M.stepEvents evs1 st)
        s0 s1 convG convEpochs remG remPB rncap rnptr rpcap rpptr x9_val hcl1 hacp1
        hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len
        hl_le hl_lt hl_ne hn_le hn_lt hn_ne hrn_lt hrn_ne hrp_lt hrp_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx12_1 hx19_1 hx20_1 hx23_1 hx26_1)
    exact Entails.of_eq (by dsimp only [F_frame]; sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoopClPlacedBudget
