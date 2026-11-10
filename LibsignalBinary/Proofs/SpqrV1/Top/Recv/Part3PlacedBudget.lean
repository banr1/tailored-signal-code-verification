/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Cleanup Tail & `Ordering::Equal` Transition for `spqr::recv`

Re-exports version-dispatch exits from `Part3PlacedBudgetAux` and proves the `+1028`/`+2540`
cleanup tails, `Ordering::Equal` transition (`+792..+820 -> +1532`), and `SepWPpLS.call_lscro`
for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (MsgPreamble PqRatchetState SpqrRecvModel V1State VersionNegotiationPB msgPreamble
   recvResultExactKeyAt spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded VecArg withLsCodeRoLoaded)
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

open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudgetAux
  (step_drop_vn_936_placed_ofEnv)

export LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudgetAux
  (step_drop_vn_936_placed_ofEnv step_drop_vn_936_placed
   step_err_versionMismatch_892_placed_ofEnv step_err_versionMismatch_892_placed
   step_err_minVersion_752_placed_ofEnv step_err_minVersion_752_placed
   step_ok_none_912_placed_ofEnv step_ok_none_912_placed)

/-! ## 1b. Version Dispatch Cleanup Tail (`+1028`, `+2540`) -/

/-- Envelope-parametric drop of `optProtoInnerStateAt` at `s0.sp - 4864#64` (`sp + 0x80`) via
    `+1028 .. +1036`, returning via `step_epilogue_placed_ofEnv` (`+1040 .. +1072`). -/
theorem step_drop_inner_1028_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (optSt : Option V1State.InnerState)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4864#64) optSt ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr_eq, hvregs⟩
  have hinner_mem := subroutine_ok_withMemEq_of_lscl hC.dropOptProtoInnerState_ok hcl
  simp only [withMemEq, dropOptProtoInnerStatePlacedSpec] at hinner_mem
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, optProtoInnerStateSize,
    BitVec.ofNat_eq_ofNat] at hinner_mem hpc ⊢
  let st0 := MC.stepEvents evs0 st_cost
  have hjoin352 : memRegion (s0.sp - 4992#64) 128 ∗ memRegion (s0.sp - 4864#64) 224 ⊢
      memRegion (s0.sp - 4992#64) 352 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 128) (k := 224)
        (b' := s0.sp - 4864#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine seq_free (mid := (blkPl_329).base + 1040#64)
    (P_evs := fun evs_in sm =>
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs_in st0) sm ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
    ?_ ?_
  · unfold spqrRecvRoPlacedAt v1StateJumpTablesPlacedAt
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)))
      (by sep_focus) ?_
    wp_call hinner_mem (⟨s0.sp - 4864#64, optSt⟩, st0)
    have hevs_in := ‹FreeOnlyEvs _›
    have hsp_eq : stackAt s.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
    refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
    refine close_free_step (freeOnlyWitness hevs_in) hevs_in
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (Entails.of_eq (by sep_ac_rfl))
      ?_
    refine ⟨?_, ⟨?_, ?_⟩⟩ <;> simp only [wp_norm, arm64_norm, *]
  · intro evs_in s1 hevs_in hpc1 hrun1 ⟨hsp1, htr1⟩
    have heq_pool : MC.stepEvents evs_in st0 = MC.stepEvents (evs0 ++ evs_in) st_cost := by
      dsimp only [st0]
      exact (MC.stepEvents_append evs0 evs_in st_cost).symm
    rw [heq_pool]
    exact step_epilogue_placed_ofEnv A lim st_cost Env (evs0 ++ evs_in)
      (hevs_free evs_in hevs_in) M ext st msg ret s0 s1 _ R post hpost
      hpc1 hrun1 hsp1 hs0_align htr1 rfl

theorem step_drop_inner_1028_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (optSt : Option V1State.InnerState)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4864#64) optSt ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_drop_inner_1028_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret optSt s0 s P R post hpost hs0_align hpc hrun hsp htr hP hcl

/-- Envelope-parametric drop of `pre_pb.versionNegotiation` (`some vn` at `s0.sp - 4992#64`,
    capacity `w0` in `x20`) at `+2540 .. +2564`, jumping to `+1028`
    (`step_drop_inner_1028_placed_ofEnv`). -/
theorem step_drop_pre_2540_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2540#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
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
  have hjoin128 : memRegion (s0.sp - 4992#64) 48 ∗ memRegion (s0.sp - 4944#64) 80 ⊢
      memRegion (s0.sp - 4992#64) 128 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 48) (k := 80)
        (b' := s0.sp - 4944#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, optProtoPqRatchetInnerAt,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
  wp_focus_pure; intro hcap_lt
  dsimp only [vecCapPtrDealloc]
  by_cases hc0 : (w0 == 0#64) = true <;>
    simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
  · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
    subst hw0
    refine seq_vm_lscl hcl (mid := (blkPl_329).base + 1028#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 128 ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4864#64) pb.innerState ∗
        memRegion (s0.sp - 4640#64) 4544 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
      exact step_drop_inner_1028_placed_ofEnv A lim st_cost Env evs0 hevs_free M ext hC st msg ret
        pb.innerState s0 s1 _ R post hpost hs0_align hpc1 hrun1 hsp1 htr1 rfl hcl1
  · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
    have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
    let st0 := MC.stepEvents evs0 st_cost
    refine seq_free_lscl hcl (mid := (blkPl_329).base + 1028#64)
      (P_evs := fun evs_vn sm =>
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
        A.pool lim (MC.stepEvents evs_vn st0) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 128 ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4864#64) pb.innerState ∗
        memRegion (s0.sp - 4640#64) 4544 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
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
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      wp_steps
      refine close_free_step (rustDeallocEvents w0.toNat 1) (FreeOnlyEvs.singleton 1 w0.toNat)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by
          simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl))
        ?_
      refine ⟨?_, ⟨?_, ?_⟩⟩ <;> simp only [wp_norm, arm64_norm, *]
    · intro evs_vn s1 hevs_vn hpc1 hrun1 hcl1 ⟨hsp1, htr1⟩
      have heq_pool : MC.stepEvents evs_vn st0 = MC.stepEvents (evs0 ++ evs_vn) st_cost := by
        dsimp only [st0]
        exact (MC.stepEvents_append evs0 evs_vn st_cost).symm
      rw [heq_pool]
      exact step_drop_inner_1028_placed_ofEnv A lim st_cost Env (evs0 ++ evs_vn)
        (fun evs_d hd => by rw [List.append_assoc]; exact hevs_free _ (hevs_vn.append hd))
        M ext hC st msg ret pb.innerState s0 s1 _ R post hpost
        hs0_align hpc1 hrun1 hsp1 htr1 rfl hcl1

theorem step_drop_pre_2540_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (vn : VersionNegotiationPB) (pb : V1State) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2540#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_drop_pre_2540_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret vn pb w0 w1 s0 s P R post hpost hs0_align hpc hrun hsp htr hx20 hP hcl

/-! ## 2. Relocatable `Ordering::Equal` Transition (`+792 .. +820 -> +1532`) -/

/-- Relocatable budget-threaded continuation contract at `+1532` for the V1 ratchet path
    (`Ordering::Equal`). -/
def V1RatchetPlacedTail {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (post : State → SepProp → Prop) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ none2Cap →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    s.pc = spqrRecvPlacedEntry + 1532#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x26 = 0#64 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post

/-- Relocatable budget-threaded `Ordering::Equal` transition at `+792 .. +820` (`-> +1532`). -/
theorem step_equal_792_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (htail : V1RatchetPlacedTail A lim st_cur ext st msg ret s0 post)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy_raw := hmemcpy_ok
  simp only [framelessMemcpySpec, framelessMemcpyBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  have hto :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4944#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ⊢
      ∃∗ bs352 : List (BitVec 8),
        ⌜bs352.length = 352⌝ ∗
        ((s0.sp - 4992#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).1 bs352 := by
    have h := (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).2.to_bytes (s0.sp - 4992#64)
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    have h48 : (s0.sp - 4992#64) + 48#64 = s0.sp - 4944#64 := bv_sub_add_lit s0.sp 4992 48
    have h128 : (s0.sp - 4992#64) + 128#64 = s0.sp - 4864#64 := bv_sub_add_lit s0.sp 4992 128
    rw [h8, h16, h48, h128] at h
    exact h
  have hsplit_4544 :
      memRegion (s0.sp - 4640#64) 4544 =
        memRegion (s0.sp - 4640#64) 352 ∗ memRegion (s0.sp - 4288#64) 4192 :=
    ProofLib.memRegion_split' (b := s0.sp - 4640#64) (n := 352) (k := 4192)
      (b' := s0.sp - 4288#64) rfl (by bv_omega) (by decide)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  refine SepWP.focus_weaken hto (by sep_focus) ?_
  wp_pull_exists; rename_i bs352
  wp_focus_pure; intro hlen352
  rw [hsplit_4544]
  have hof :
      ((s0.sp - 4640#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).1 bs352 ⊢
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4512#64) pre_pb.inner := by
    have h := (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).2.of_bytes (s0.sp - 4640#64) bs352 hlen352
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    have h8 : (s0.sp - 4640#64) + 8#64 = s0.sp - 4632#64 := bv_sub_add_lit s0.sp 4640 8
    have h16 : (s0.sp - 4640#64) + 16#64 = s0.sp - 4624#64 := bv_sub_add_lit s0.sp 4640 16
    have h48 : (s0.sp - 4640#64) + 48#64 = s0.sp - 4592#64 := bv_sub_add_lit s0.sp 4640 48
    have h128 : (s0.sp - 4640#64) + 128#64 = s0.sp - 4512#64 := bv_sub_add_lit s0.sp 4640 128
    rw [h8, h16, h48, h128] at h
    exact h
  have hsrc_mem : ((s0.sp - 4992#64) ↦ₛ bs352) ⊢ memRegion (s0.sp - 4992#64) 352 := by
    rw [← hlen352]
    exact ProofLib.pointsToBytes_entails_memRegion (s0.sp - 4992#64) bs352
  have hdst_mem : memRegion (s0.sp - 4640#64) 352 = memRegion (s0.sp - 4640#64) bs352.length := by
    rw [hlen352]
  have hlen_lt : bs352.length < 2 ^ 64 := by rw [hlen352]; decide
  have hlen_eq : (352#64 : BitVec 64).toNat = bs352.length := hlen352.symm
  refine seq_vm_clean (mid := lsρ "memcpy")
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦ₛ bs352) ∗
      (relocPinnedPqRatchetStateAt H_inner A.repAlloc w0 w1 pre_pb).1 bs352 ∗
      memRegion (s0.sp - 4640#64) bs352.length ∗
      memRegion (s0.sp - 4288#64) 4192 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = s0.sp - 4640#64 ∧
      s1.readReg64 .x1 = s0.sp - 4992#64 ∧
      s1.readReg64 .x2 = 352#64 ∧
      s1.readReg64 .x30 = (blkPl_329).base + 808#64 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x20 = w0 ∧
      s1.readReg64 .x21 = pre.index.zeroExtend 64 ∧
      s1.readReg64 .x22 = pre.epoch ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
      s1.readReg64 .x24 = remPtr ∧
      s1.readReg64 .x27 = s0.sp - 3056#64 ∧
      s1.readReg64 .x28 = s0.sp - 4288#64 ∧
      s1.readReg64 .x29 = s0.sp - 96#64)
    ?_ ?_
  · rw [hdst_mem]
    by_vm_steps (
      wp_steps 4
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx0_1, hx1_1, hx2_1, hlr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx28_1, hx29_1⟩
    rw [← A.pool_transport lim st_cur s s1 hvm1]
    have hs1_align : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact hfsp_align
    wp_call hmemcpy_raw ⟨s0.sp - 4640#64, s0.sp - 4992#64, bs352⟩
    have hvm2 := ‹VmPreserved s1 _›
    let s2 : State := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
    have hvm2' : VmPreserved s1 s2 := hvm2
    rw [← A.pool_transport lim st_cur s1 s2 hvm2']
    refine SepWP.focus_weaken hsrc_mem (by sep_focus) ?_
    refine SepWP.focus_weaken hof (by sep_focus) ?_
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A.repAlloc (s0.sp - 4512#64) pre_pb.inner)
      (by sep_focus) ?_
    wp_pull_exists; rename_i w8 P_inner
    wp_focus_pure; intro hw8
    wp_focus_pure; intro hunexp
    have hw8_bne3 : (w8 + 3#64 != 0#64) = true := by
      rw [hinner] at hw8
      dsimp [InnerWordInv] at hw8
      simp [bne, hw8]
    have hinner_eq_pb : optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4512#64) pre_pb.inner =
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState := by
      rw [hinner]; rfl
    refine seq_vm_clean (mid := (blkPl_329).base + 1532#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        memRegion ret 48 ∗
        A.pool lim st_cur s2 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
        memRegion (s0.sp - 4288#64) 4192 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s3 =>
        s3.sp = s0.sp - 4992#64 ∧
        TraceVRegs s3 s0 ∧
        s3.readReg64 .x19 = ret ∧
        s3.readReg64 .x20 = w0 ∧
        s3.readReg64 .x21 = pre.index.zeroExtend 64 ∧
        s3.readReg64 .x22 = pre.epoch ∧
        s3.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
        s3.readReg64 .x24 = remPtr ∧
        s3.readReg64 .x26 = 0#64 ∧
        s3.readReg64 .x27 = s0.sp - 3056#64 ∧
        s3.readReg64 .x28 = s0.sp - 4288#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 4
        refine SepWP.focus_weaken hunexp (by sep_focus) ?_
        rw [hinner_eq_pb]
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s3 hpc3 hrun3 hvm3 ⟨hsp3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
        hx26_3, hx27_3, hx28_3, hx29_3⟩
      rw [← A.pool_transport lim st_cur s2 s3 hvm3]
      exact htail pre remPtr pre_pb pb w0 w1 s3 _ hpre hvalid hdec hinner hw0_ne hmv hmin
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx28_3 hx29_3 rfl

/-! ## 3. Generic `withLsCodeRoLoaded` Call Wrapper (`SepWPpLS.call_lscro`) -/

theorem SepWPpLS.call_lscro {α : Type} {prog : Program}
    {M : SpqrRecvModel} {st msg : VecArg}
    {ret entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (x : α) {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s0.trace <+: s.trace)
    (hpan : ∀ sm, spec.onPanic x s sm ⊢
      ⌜M.recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap)
    (hexit : ∀ code sm, spec.onExit x code s sm = ⌜False⌝)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpost : ∀ sm,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPpLS prog ret sm (spec.post x s sm ∗ F) Q (spqrRecvBudgetPanicPost M st msg s0 R))
    (hoom : ∀ sm, spec.onOom x s sm = ⌜False⌝ := by intros; rfl) :
    SepWPpLS prog ret s P Q (spqrRecvBudgetPanicPost M st msg s0 R) := by
  intro hcrl R' hm hL
  have hm1 := Satisfies.mono (sepConj_mono_left hpre) hm
  have hpre_lscro : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F ∗ R')
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrl, by rw [← sepConj_assoc]; exact hm1⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_lscro halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost_m⟩ | ⟨hpan_st, hpost_m⟩ | ⟨code, _, hpost_m⟩ | ⟨_, hpost_m⟩
  · change sm.mem ⊨ spec.post x s sm ∗ (F ∗ R') at hpost_m
    rw [← sepConj_assoc] at hpost_m
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hpost sm hpcm hrunm hspm hcsm (hsteps.lsCodeRoLoaded hcrl) R' hpost_m (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ spec.onPanic x s sm ∗ (F ∗ R') at hpost_m
    have hpost_pan := Satisfies.mono (sepConj_mono_left (hpan sm)) hpost_m
    rw [← sepConj_assoc] at hpost_pan
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost_pan, ?_⟩)⟩
    intro hm''
    exact allowPanic_frame (fun ⟨hp, hsub⟩ => ⟨hp, htr.trans hsub⟩) hm''
  · change sm.mem ⊨ spec.onExit x code s sm ∗ (F ∗ R') at hpost_m
    rw [hexit code sm] at hpost_m
    exact (not_satisfies_false_sepConj hpost_m).elim
  · change sm.mem ⊨ spec.onOom x s sm ∗ (F ∗ R') at hpost_m
    rw [hoom sm] at hpost_m
    exact (not_satisfies_false_sepConj hpost_m).elim

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
