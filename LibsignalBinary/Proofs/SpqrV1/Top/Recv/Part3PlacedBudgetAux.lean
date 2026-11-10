/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Version Dispatch Exits for `spqr::recv`

Envelope-parametric and default `SpqrRecvEnv` cleanup/error exits (`+752`, `+892`, `+912`, `+936`)
for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (MsgPreamble PqRatchetState SpqrRecvModel V1State VersionNegotiationPB msgPreamble
   recvResultExactKeyAt spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (cap_ne_zero_lt_one_false cap_ne_zero_slt_one_false dropStack96 optProtoInnerStateAt
   optProtoInnerStateSize optProtoPqRatchetInnerAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (TraceVRegs V1InnerHeapPred none2Cap optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Recv
  (InnerWordInv MsgRemValid SepWPpLS cap_ne_zero_one_sle_true optProtoPqRatchetInnerAt_eq_drop
   optProtoPqRatchetInnerAt_expose_word ownFrame_join_352_4544 pinnedPqRatchetStateAt
   recv_err_byte_foldX recv_ok_empty_foldX relocPinnedPqRatchetStateAt ret_48_split
   ret_48_split_byte8 sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvSavedRegs stackAt_spqrRecvCallee_split
   subroutine_ok_withMemEq_of_lscl vnHeader_sub4992_entails_memRegion_48 vnTail_some_entails_dealloc)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedPost0 spqrRecvPlacedPost0OfEnv
   step_epilogue_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly close_free_step deallocFreeOnlySpec
   freeOnlyWitness seq_free seq_free_lscl seq_vm_clean seq_vm_lscl step_drop_pre_952_placed_ofEnv
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec framelessMemcpySpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

/-! ## 1. Version Dispatch Exits (`+752`, `+892`, `+912`, `+936`, `+1028`, `+2540`) -/

/-- Envelope-parametric deallocation of non-empty `vn.authKey` at `+936 .. +948`, continuing to
    `step_drop_pre_952_placed_ofEnv`. -/
theorem step_drop_vn_936_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      memRegion (s0.sp - 4976#64) 32 ∗
      A.repAlloc.live w1 w0.toNat 1 ∗
      memRegion w1 w0.toNat ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr_eq, hvregs⟩
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hC.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  let st0 := MC.stepEvents evs0 st_cost
  refine seq_free_lscl hcl (mid := (blkPl_329).base + 952#64)
    (P_evs := fun evs_vn sm =>
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs_vn st0) sm ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
    ?_ ?_
  · refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
      (by sep_focus) ?_
    wp_steps
    wp_call hdealloc_fo (w1, w0.toNat, 1, st0)
    have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
    refine close_free_step (rustDeallocEvents w0.toNat 1) (FreeOnlyEvs.singleton 1 w0.toNat)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (Entails.of_eq (by sep_ac_rfl))
      ?_
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · intro evs_vn s1 hevs_vn hpc1 hrun1 hcl1 ⟨hsp1, htr1, hx26_1⟩
    have heq_pool : MC.stepEvents evs_vn st0 = MC.stepEvents (evs0 ++ evs_vn) st_cost := by
      dsimp only [st0]
      exact (MC.stepEvents_append evs0 evs_vn st_cost).symm
    rw [heq_pool]
    exact step_drop_pre_952_placed_ofEnv A lim st_cost Env (evs0 ++ evs_vn)
      (fun evs_d hd => by rw [List.append_assoc]; exact hevs_free _ (hevs_vn.append hd))
      M ext hC st msg ret pre_pb w26 hw26 s0 s1 _ R post hpost
      hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1

theorem step_drop_vn_936_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      memRegion (s0.sp - 4976#64) 32 ∗
      A.repAlloc.live w1 w0.toNat 1 ∗
      memRegion w1 w0.toNat ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_drop_vn_936_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w0 w1 w26 hw26 s0 s P R post hpost hs0_align hpc hrun hsp htr hx20 hx26 hP hcl

/-- Envelope-parametric `Err(VersionMismatch)` exit at `+892 .. +908` (`-> +952`). -/
theorem step_err_versionMismatch_892_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 892#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
  refine seq_vm_lscl hcl (mid := (blkPl_329).base + 952#64)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
    ?_ ?_
  · by_vm_steps (
      refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
      wp_pull_exists; rename_i r0 b8 r2 r3
      wp_steps 5
      have hfold := recv_err_byte_foldX A.repAlloc ret r2 r3 7#8 false (by decide)
      rw [← herr] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx26_1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
    exact step_drop_pre_952_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
      pre_pb w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1

theorem step_err_versionMismatch_892_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 892#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_err_versionMismatch_892_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w26 hw26 herr s0 s P R post hpost
    hs0_align hpc hrun hsp htr hx19 hx26 hP hcl

/-- Envelope-parametric `Err(MinVersion)` exit at `+752 .. +776` (`-> +936 / +952`). -/
theorem step_err_minVersion_752_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 752#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  have hfold := recv_err_byte_foldX A.repAlloc ret r2 r3 8#8 false (by decide)
  rw [← herr] at hfold
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    refine seq_vm_lscl hcl (mid := (blkPl_329).base + 952#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 48 ∗
        optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
        memRegion (s0.sp - 4640#64) 4544 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
      ?_ ?_
    · by_vm_steps (
        wp_steps 7
        refine SepWP.fold hfold (by sep_focus) ?_
        refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx26_1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
      exact step_drop_pre_952_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
        pre_pb w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1
  | some vn =>
    have hvn_dealloc :
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ⊢
        ⌜w0.toNat < 2 ^ 63⌝ ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
          vecCapPtrDealloc A.repAlloc w0 w1 := by
      have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
      have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
      rw [← h8, ← h16]
      exact vnTail_some_entails_dealloc A.repAlloc (s0.sp - 4992#64) w0 w1 vn
    refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      refine seq_vm_lscl hcl (mid := (blkPl_329).base + 952#64)
        (P_mid :=
          spqrRecvRoPlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs0 st_cost) s ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4992#64) 48 ∗
          optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
          optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
          memRegion (s0.sp - 4640#64) 4544 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
        ?_ ?_
      · by_vm_steps (
          wp_steps 7
          refine SepWP.fold hfold (by sep_focus) ?_
          refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
          refine align_pre_wp (by sep_ac_rfl) ?_
          wp_done
        )
      · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx26_1⟩
        rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
        exact step_drop_pre_952_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
          pre_pb w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1
    · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
      refine seq_vm_lscl hcl (mid := (blkPl_329).base + 936#64)
        (P_mid :=
          spqrRecvRoPlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs0 st_cost) s ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗
          ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          memRegion (s0.sp - 4976#64) 32 ∗
          A.repAlloc.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
          optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
          memRegion (s0.sp - 4640#64) 4544 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun sm =>
          sm.sp = s0.sp - 4992#64 ∧
          TraceVRegs sm s0 ∧
          sm.readReg64 .x20 = w0 ∧
          sm.readReg64 .x26 = w26)
        ?_ ?_
      · by_vm_steps (
          wp_steps 6
          refine SepWP.fold hfold (by sep_focus) ?_
          refine align_pre_wp (by sep_ac_rfl) ?_
          wp_done
        )
      · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx20_1, hx26_1⟩
        rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
        exact step_drop_vn_936_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
          pre_pb w0 w1 w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx20_1 hx26_1 rfl hcl1

theorem step_err_minVersion_752_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 752#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_err_minVersion_752_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w0 w1 w26 hw26 herr s0 s P R post hpost
    hs0_align hpc hrun hsp htr hx19 hx20 hx26 hP hcl

/-- Envelope-parametric `Ok((Vec::new(), None))` exit at `+912 .. +932` (`-> +936 / +952`). -/
theorem step_ok_none_912_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hok : M.recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 912#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  have hfold := recv_ok_empty_foldX A.repAlloc ret
  rw [← hok] at hfold
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hslt : BitVec.slt noneCap 1#64 = true := rfl
    refine seq_vm_lscl hcl (mid := (blkPl_329).base + 952#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 48 ∗
        optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
        memRegion (s0.sp - 4640#64) 4544 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
      ?_ ?_
    · by_vm_steps (
        wp_steps 6
        refine SepWP.fold hfold (by sep_focus) ?_
        refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx26_1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
      exact step_drop_pre_952_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
        pre_pb w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1
  | some vn =>
    have hvn_dealloc :
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ⊢
        ⌜w0.toNat < 2 ^ 63⌝ ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
          vecCapPtrDealloc A.repAlloc w0 w1 := by
      have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
      have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
      rw [← h8, ← h16]
      exact vnTail_some_entails_dealloc A.repAlloc (s0.sp - 4992#64) w0 w1 vn
    refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      refine seq_vm_lscl hcl (mid := (blkPl_329).base + 952#64)
        (P_mid :=
          spqrRecvRoPlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs0 st_cost) s ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4992#64) 48 ∗
          optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
          optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
          memRegion (s0.sp - 4640#64) 4544 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
        ?_ ?_
      · by_vm_steps (
          wp_steps 6
          refine SepWP.fold hfold (by sep_focus) ?_
          refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
          refine align_pre_wp (by sep_ac_rfl) ?_
          wp_done
        )
      · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx26_1⟩
        rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
        exact step_drop_pre_952_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
          pre_pb w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1
    · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
      have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
      refine seq_vm_lscl hcl (mid := (blkPl_329).base + 936#64)
        (P_mid :=
          spqrRecvRoPlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs0 st_cost) s ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗
          ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          memRegion (s0.sp - 4976#64) 32 ∗
          A.repAlloc.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
          optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
          memRegion (s0.sp - 4640#64) 4544 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun sm =>
          sm.sp = s0.sp - 4992#64 ∧
          TraceVRegs sm s0 ∧
          sm.readReg64 .x20 = w0 ∧
          sm.readReg64 .x26 = w26)
        ?_ ?_
      · by_vm_steps (
          wp_steps 6
          refine SepWP.fold hfold (by sep_focus) ?_
          refine align_pre_wp (by sep_ac_rfl) ?_
          wp_done
        )
      · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx20_1, hx26_1⟩
        rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
        exact step_drop_vn_936_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
          pre_pb w0 w1 w26 hw26 s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 hx20_1 hx26_1 rfl hcl1

theorem step_ok_none_912_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hok : M.recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 912#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_ok_none_912_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb w0 w1 w26 hw26 hok s0 s P R post hpost
    hs0_align hpc hrun hsp htr hx19 hx20 hx26 hP hcl

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudgetAux
