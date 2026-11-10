/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 5 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` proofs for the `<Ct1Sent>::recv_ek` call (`+11508 ->
+11528`), Path 5a (`recv_ek = .error`), `.ok uc_ek` staging, and Path 5b (`ack = false`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open Obj.MultiPlacedLib
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  unchunkedCt1SentRecvEkSpecOfEnv unchunkedCt1SentRecvEkSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean seq_vm_cont step_adrp_vm
)

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  sp_sub_4240_add_2752 sp_sub_4240_add_3696 sp_sub_4240_add_3832
  sp_sub_4240_add_3840 sp_sub_4240_add_3848
  lsmpl_base_332_eq
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

private theorem seq_vm_cont_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {mid tgt : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → SepWP prog tgt sm Pm post))) :
    SepWP prog tgt s Pre post :=
  SepWP.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl
    (SepWP.mono h fun _ _ _ _ ⟨hvm, hk⟩ hclm => hk hclm hvm)

/-! ## 1. Calling `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`+11508 -> +11528`) -/

theorem ct1Sampled_call_recv_ek_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (st_cost : M.σ) (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfits : FitsEnv M lim st_cost
      (PreEnv ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11508#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11528#64) s_in
      (memRegion (fsp + 1856#64) 128 ∗ unchunkedCt1SentAt A.repAlloc (fsp + 3696#64) uc ∗
        vecU8 A.repAlloc (fsp + 3832#64) decoded ∗ A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf => ∃ evs : List AllocEvent,
        PostEnv ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩ evs ∧
        (Pf ⊢ unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) res ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = uc.epoch ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  subst hsp
  have hsplit := stackAt_statesRecvCallee_eq_unchunkedRecvEk' s_in.sp
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hsplit ⊢
  rw [hsplit, ← hx20]
  refine seq_vm_cont_lscl hcl (mid := lsmpl.base 338) ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm => ?_⟩
    have hcall := subroutine_ok_withMemEq_of_withLsCodeLoaded hrecv_ek hclm
    dsimp only [lsProg_332, withMemEq,
      unchunkedCt1SentRecvEkSpecOfPrePostEnv,
      BitVec.ofNat_eq_ofNat] at hcall
    wp_conv_pre => rw [← A.pool_of_vmPreserved hvmm]
    wp_call hcall (⟨s_in.sp + 1856#64, s_in.sp + 3696#64, s_in.sp + 3832#64, uc, decoded, res⟩, st_cost)
    have hevs_w :
        PostEnv ⟨s_in.sp + 1856#64, s_in.sp + 3696#64, s_in.sp + 3832#64, uc, decoded, res⟩ w := by
      assumption
    refine SepWP.mono (post := fun sf2 Pf2 =>
      (Pf2 ⊢ unchunkedCt1SentRecvEkResAt A.repAlloc (s_in.sp + 1856#64) res ∗
        memRegion (s_in.sp + 3696#64) 128 ∗ memRegion (s_in.sp + 3832#64) 24 ∗
        A.pool lim (M.stepEvents w st_cost) sf2 ∗ stackAt s_in.sp statesRecvCalleeStackX ∗ Rest) ∧
      sf2.sp = s_in.sp ∧ sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf2.readReg64 .x20 = s_in.readReg64 .x20 ∧ sf2.readReg64 .x21 = s_in.readReg64 .x21 ∧
      sf2.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf2.readReg64 .x23 = s_in.readReg64 .x23 ∧
      sf2.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf2.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf2.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf2 s_in) ?_
      (fun _ _ _ _ ⟨hPf2, hrest2⟩ => ⟨w, hevs_w, by rwa [hsplit] at hPf2, hrest2⟩)
    rw [hsplit]
    wp_done
  )

theorem ct1Sampled_call_recv_ek_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpecOfEnv M A lim F K Env)))
    (st_cost : M.σ) (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfits : FitsEnv M lim st_cost
      (Env ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11508#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11528#64) s_in
      (memRegion (fsp + 1856#64) 128 ∗ unchunkedCt1SentAt A.repAlloc (fsp + 3696#64) uc ∗
        vecU8 A.repAlloc (fsp + 3832#64) decoded ∗ A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf => ∃ evs : List AllocEvent,
        Env ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩ evs ∧
        (Pf ⊢ unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) res ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = uc.epoch ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) :=
  ct1Sampled_call_recv_ek_placed_ofPrePostEnv hrecv_ek st_cost s_in fsp uc decoded res Rest
    hcl hres hfits hfsp_align hpc hrun hsp hx20

theorem ct1Sampled_call_recv_ek_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.unchunkedCt1SentRecvEkSpec
          M A lim F K)))
    (st_cost : M.σ) (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11508#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11528#64) s_in
      (memRegion (fsp + 1856#64) 128 ∗ unchunkedCt1SentAt A.repAlloc (fsp + 3696#64) uc ∗
        vecU8 A.repAlloc (fsp + 3832#64) decoded ∗ A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) res ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = uc.epoch ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) :=
  ct1Sampled_call_recv_ek_placed_ofPrePostEnv hrecv_ek st_cost s_in fsp uc decoded res Rest
    hcl hres (fun _ h => by cases h; trivial) hfsp_align hpc hrun hsp hx20

/-! ## 2. Path 5a (`recv_ek = .error (.err err)`): `+11528 -> +15716 -> +19324` -/

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_recv_ek_err_to_19324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s_in : State) (fsp stA outA : BitVec 64)
    (vecs : List (List GF16)) (hvecs_len : vecs.length = NUM_POLYS)
    (dec' : PolyDecoder) (err : Error)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (herr : err = .erroneousDataReceived)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19324#64) s_in
      (unchunkedCt1SentRecvEkResAt A.repAlloc (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A.repAlloc (stA + 8#64) vecs ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err err)) ∗
            memRegion (fsp + 1856#64) 128 ∗
            ((fsp + 232#64) ↦₆₄ stA) ∗
            memRegion (stA + 8#64) 384 ∗
            memRegion (fsp + 2752#64) 400 ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest) ∧
          sf.sp = fsp ∧
          AllocCallPreserved s_in sf ∧
          sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s_in) := by
  subst hsp hx19 herr
  have hout_split :
      memRegion (s_in.readReg64 .x19) v1RecvSize ⊢
        ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
          ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928 := by
    unfold v1RecvSize
    rw [ProofLib.memRegion_split (s_in.readReg64 .x19) 32 928 (by decide)]
    refine Entails.trans (sepConj_mono_left (memRegion_32_entails_words4 (s_in.readReg64 .x19))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro v24
    apply Entails.sepExists_elim; intro v16
    apply Entails.sepExists_elim; intro v8
    apply Entails.sepExists_elim; intro v0
    exact Entails.sepExists_right v0 (Entails.sepExists_right v8
      (Entails.sepExists_right v16 (Entails.sepExists_right v24 (Entails.refl _))))
  have hdec_entails :
      polyDecoderAt A.repAlloc (s_in.sp + 2752#64) dec' ⊢
        ∃∗ vecs_dec : List (List Pt),
          ⌜vecs_dec.length = NUM_POLYS⌝ ∗
          vecPtListOf A.repAlloc (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 := by
    have h3136 : (s_in.sp + 2752#64) + 384#64 = s_in.sp + 3136#64 := by bv_omega
    have h := polyDecoderAt_entails_vecs_tail A.repAlloc (s_in.sp + 2752#64) dec'
    rwa [h3136] at h
  have hpre :
      unchunkedCt1SentRecvEkResAt A.repAlloc (F := F) (s_in.sp + 1856#64)
          (.error .erroneousDataReceived) ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A.repAlloc (stA + 8#64) vecs ∗
        polyDecoderAt A.repAlloc (s_in.sp + 2752#64) dec' ∗
        memRegion (s_in.readReg64 .x19) v1RecvSize ∗
        A.pool lim st_cost s_in ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ bs7 : List (BitVec 8),
      ∃∗ vecs_dec : List (List Pt),
      ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
        ⌜bs7.length = 7 ∧ unpack64 w8 = 12#8 :: bs7⌝ ∗
        ⌜vecs_dec.length = NUM_POLYS⌝ ∗
        (((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96 ∗
          ((s_in.sp + 232#64) ↦₆₄ stA) ∗
          vecGF16ListOf A.repAlloc (stA + 8#64) vecs ∗
          vecPtListOf A.repAlloc (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 ∗
          ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928 ∗
          A.pool lim st_cost s_in ∗
          stackAt s_in.sp statesRecvCalleeStackX ∗
          Rest) := by
    refine Entails.trans
      (sepConj_mono (unchunkedCt1SentRecvEkResAt_error_entails A.repAlloc (s_in.sp + 1856#64) .erroneousDataReceived)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono hdec_entails (sepConj_mono_left hout_split))))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w16
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w24
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro bs7
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vecs_dec
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v8
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v16
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v24
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24
      (Entails.sepExists_right bs7 (Entails.sepExists_right vecs_dec
        (Entails.sepExists_right v0 (Entails.sepExists_right v8
          (Entails.sepExists_right v16 (Entails.sepExists_right v24 ?_))))))))
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro bs7
  apply ProofLib.SepWP.exists_left; intro vecs_dec
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v24
  wp_focus_pure; intro ⟨hlen7, hw8⟩
  wp_focus_pure; intro hvecs_dec_len
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        (Pf ⊢
          ((((s_in.readReg64 .x19) ↦₆₄ noneCap) ∗
            ((s_in.readReg64 .x19 + 8#64) ↦₆₄ w8) ∗
            ((s_in.readReg64 .x19 + 16#64) ↦₆₄ w16) ∗
            ((s_in.readReg64 .x19 + 24#64) ↦₆₄ w24) ∗
            memRegion (s_in.readReg64 .x19 + 32#64) 928) ∗
           (((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
            ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
            ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
            ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
            memRegion (s_in.sp + 1888#64) 96) ∗
           ((s_in.sp + 232#64) ↦₆₄ stA) ∗
           memRegion (stA + 8#64) 384 ∗
           (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16)) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          ((memRegion (s_in.sp - 19552#64) 15424 ∗ stackAt s_in.sp dropGluePoly16Stack) ∗
           Rest)) ∧
        (sf.sp = s_in.sp ∧
         AllocCallPreserved s_in sf ∧
         sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
         TraceCalleeSaved sf s_in)) ?_
    (fun sf Pf _ _ ⟨evs, hevs, hPf, hrest⟩ => ⟨evs, hevs, Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    refine DropChunkedClPlacedBudgetAux.seq_evs_step_lscl hcl
      (mid := (blkPl_332).base + 15736#64)
      (P_mid := fun st1 sm =>
        ((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
        ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
        ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
        ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
        memRegion (s_in.sp + 1888#64) 96 ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        memRegion (stA + 8#64) 384 ∗
        vecPtListOf A.repAlloc (s_in.sp + 2752#64) vecs_dec ∗
        memRegion (s_in.sp + 3136#64) 16 ∗
        ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
        ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
        ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
        ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
        memRegion (s_in.readReg64 .x19 + 32#64) 928 ∗
        A.pool lim st1 sm ∗
        memRegion (s_in.sp - 19552#64) 15424 ∗
        stackAt s_in.sp dropGluePoly16Stack ∗
        Rest)
      (Q_mid := fun sm =>
        sm.sp = s_in.sp ∧
        AllocCallPreserved s_in sm ∧
        sm.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sm.readReg64 .x20 = w16 ∧
        sm.readReg64 .x21 = w24 ∧
        sm.readReg64 .x25 = w8 ∧
        sm.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sm s_in) ?_ ?_
    · dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
      refine seq_vm_cont_lscl hcl (mid := lsmpl.base 265) ?_
      by_vm_steps_nest (
        wp_steps
        refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm => ?_⟩
        have hdrop_poly := DropChunkedClPlacedBudgetAux.drop_glue_poly16_mem_on
          (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hclm
        dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.dropGluePoly16Spec,
          polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop_poly
        wp_conv_pre => rw [← A.pool_of_vmPreserved hvmm]
        wp_call hdrop_poly (⟨stA + 8#64, vecs⟩, st_cost)
        have hacp1 : AllocCallPreserved s_in sf := by assumption
        have hevs1 : FreeOnlyEvs w := by assumption
        refine SepWP.mono (post := fun sm Pm =>
          (Pm ⊢
            ((s_in.sp + 1856#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
            ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
            ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
            memRegion (s_in.sp + 1888#64) 96 ∗
            ((s_in.sp + 232#64) ↦₆₄ stA) ∗
            memRegion (stA + 8#64) 384 ∗
            vecPtListOf A.repAlloc (s_in.sp + 2752#64) vecs_dec ∗
            memRegion (s_in.sp + 3136#64) 16 ∗
            ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
            ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
            ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
            ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
            memRegion (s_in.readReg64 .x19 + 32#64) 928 ∗
            A.pool lim (M.stepEvents w st_cost) sm ∗
            memRegion (s_in.sp - 19552#64) 15424 ∗
            stackAt s_in.sp dropGluePoly16Stack ∗
            Rest) ∧
          sm.sp = s_in.sp ∧
          AllocCallPreserved sf sm ∧
          sm.readReg64 .x19 = s_in.readReg64 .x19 ∧
          sm.readReg64 .x20 = w16 ∧
          sm.readReg64 .x21 = w24 ∧
          sm.readReg64 .x25 = w8 ∧
          sm.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sm s_in) ?_
          (fun _ _ _ _ ⟨hPm, hspm, hacp1b, hrestm⟩ =>
            ⟨w, hevs1, hPm, hspm, hacp1.trans hacp1b, hrestm⟩)
        dsimp only [AllocCallPreserved, TraceCalleeSaved, Reg.x19, Reg.x20, Reg.x21, Reg.x25, Reg.x29]
        wp_done
      )
    · intro st1 sm hpcm hrunm hclm ⟨hspm, hacp1, hx19m, hx20m, hx21m, hx25m, hx29m, htrm⟩
      dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      rw [← hspm]
      refine seq_vm_cont_lscl hclm (mid := lsmpl.base 264) ?_
      by_vm_steps_nest (
        wp_steps
        refine SepWP.done rfl hrunm ⟨by simp only [wp_norm, arm64_norm], fun hclm2 hvmm2 => ?_⟩
        have hdrop_ss := DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_mem_on
          (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hclm2
        dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget.dropGlueSortedSetPt16Spec,
          polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop_ss
        wp_conv_pre => rw [← A.pool_of_vmPreserved hvmm2]
        wp_call hdrop_ss (⟨sm.sp + 2752#64, vecs_dec⟩, st1)
        have hacp2 : AllocCallPreserved sm sf := by assumption
        have hevs2 : FreeOnlyEvs w := by assumption
        refine SepWP.mono (post := fun sf2 Pf2 =>
          VmPreserved sf sf2 ∧
          (Pf2 ⊢
            ((((s_in.readReg64 .x19) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((s_in.readReg64 .x19 + 8#64) ↦₆₄ w8) ∗
              ((s_in.readReg64 .x19 + 16#64) ↦₆₄ w16) ∗
              ((s_in.readReg64 .x19 + 24#64) ↦₆₄ w24) ∗
              memRegion (s_in.readReg64 .x19 + 32#64) 928) ∗
             (((sm.sp + 1856#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((sm.sp + 1864#64) ↦₆₄ w8) ∗
              ((sm.sp + 1872#64) ↦₆₄ w16) ∗
              ((sm.sp + 1880#64) ↦₆₄ w24) ∗
              memRegion (sm.sp + 1888#64) 96) ∗
             ((sm.sp + 232#64) ↦₆₄ stA) ∗
             memRegion (stA + 8#64) 384 ∗
             (memRegion (sm.sp + 2752#64) 384 ∗ memRegion (sm.sp + 3136#64) 16)) ∗
            A.pool lim (M.stepEvents w st1) sf ∗
            ((memRegion (sm.sp - 19552#64) 15424 ∗ stackAt sm.sp dropGluePoly16Stack) ∗
             Rest)) ∧
          sf2.sp = sm.sp ∧
          AllocCallPreserved sf sf2 ∧
          sf2.readReg64 .x29 = sm.readReg64 .x29 ∧
          TraceCalleeSaved sf2 sm) ?_
          (fun sf2 Pf2 _ _ ⟨hvm3, hPf2, hsp2, hacp3, hx29_2, htr2⟩ =>
            ⟨w, hevs2,
              by
                rw [A.pool_of_vmPreserved hvm3]
                exact hPf2,
              hsp2, hacp1.trans (hacp2.trans hacp3), hx29_2.trans hx29m, htr2.trans htrm⟩)
        by_vm_steps_nest (
          wp_steps
          dsimp only [AllocCallPreserved, TraceCalleeSaved, Reg.x29]
          wp_done
        )
      )
  · rw [← hsplit]
    have herr_out := err_words_entails_resultV1RecvAt_erroneous A.repAlloc (F := F)
      (s_in.readReg64 .x19) w8 w16 w24 hlen7 hw8
    have h1856_mr :
        ((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96 ⊢
        memRegion (s_in.sp + 1856#64) 128 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 1856#64) (n := 8) (k := 120)
            (b' := s_in.sp + 1864#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1864#64) (n := 8) (k := 112)
            (b' := s_in.sp + 1872#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1872#64) (n := 8) (k := 104)
            (b' := s_in.sp + 1880#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1880#64) (n := 8) (k := 96)
            (b' := s_in.sp + 1888#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))
    have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact Entails.trans
      (sepConj_mono_left
        (sepConj_mono herr_out
          (sepConj_mono h1856_mr
            (sepConj_mono_right (sepConj_mono_right h2752_mr)))))
      (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. `recv_ek = .ok uc_ek` Staging (`+11528 -> +11620`) & `ack` Branch (`+11620`) -/

theorem ct1Sampled_recv_ek_ok_copy_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp vb0 : BitVec 64) (c_ek : Words16) (Rest : SepProp)
    (hcap : c_ek.w0.toNat < 2 ^ 63) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11620#64) s_in
      (wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
        ((fsp + 176#64) ↦₆₄ vb0) ∗ Rest)
      (fun sf Pf => VmPreserved s_in sf ∧
        (Pf ⊢ wordsAt (fsp + 1856#64) c_ek.toList ∗ wordsAt (fsp + 3856#64) c_ek.toList ∗
          ((fsp + 176#64) ↦₆₄ c_ek.w1) ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x8 = c_ek.w0 ∧ sf.readReg64 .x9 = c_ek.w2 ∧
        sf.readReg64 .x10 = c_ek.w3 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x25 = c_ek.w1 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hcmn := Recv.cap_add_one_beq_zero_false hcap
  have hpre :
      wordsAt (s_in.sp + 1856#64) c_ek.toList ∗ memRegion (s_in.sp + 3856#64) 128 ∗
        ((s_in.sp + 176#64) ↦₆₄ vb0) ∗ Rest ⊢
      ∃∗ c_dst : Words16, wordsAt (s_in.sp + 1856#64) c_ek.toList ∗
        wordsAt (s_in.sp + 3856#64) c_dst.toList ∗ ((s_in.sp + 176#64) ↦₆₄ vb0) ∗ Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (memRegion_128_entails_words16 (s_in.sp + 3856#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c_dst
    exact Entails.sepExists_right c_dst (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst
  dsimp only [lsProg_332, Words16.toList, BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  by_vm_steps (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21,
      Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x28, Reg.x29]
    wp_done
  )

theorem ct1Sampled_recv_ek_ok_copy_sc_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (sc : CopyScratchStack) (c_ek : Words16) (Rest : SepProp)
    (hw0 : c_ek.w0.toNat < 2 ^ 63) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11620#64) s_in
      (wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
        copyScratchStackAt fsp sc ∗ Rest)
      (fun sf Pf => VmPreserved s_in sf ∧
        (Pf ⊢ wordsAt (fsp + 1856#64) c_ek.toList ∗ wordsAt (fsp + 3856#64) c_ek.toList ∗
          copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x8 = c_ek.w0 ∧ sf.readReg64 .x9 = c_ek.w2 ∧
        sf.readReg64 .x10 = c_ek.w3 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x25 = c_ek.w1 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hcmn := Recv.cap_add_one_beq_zero_false hw0
  have hpre :
      wordsAt (s_in.sp + 1856#64) c_ek.toList ∗ memRegion (s_in.sp + 3856#64) 128 ∗
        copyScratchStackAt s_in.sp sc ∗ Rest ⊢
      ∃∗ c_dst : Words16, wordsAt (s_in.sp + 1856#64) c_ek.toList ∗
        wordsAt (s_in.sp + 3856#64) c_dst.toList ∗ copyScratchStackAt s_in.sp sc ∗ Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (memRegion_128_entails_words16 (s_in.sp + 3856#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c_dst
    exact Entails.sepExists_right c_dst (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst
  dsimp only [lsProg_332, copyScratchStackAt, Words16.toList, BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  by_vm_steps (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21,
      Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x28, Reg.x29]
    wp_done
  )

theorem ct1Sampled_ok_branch_no_ack_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64) (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 15760#64) s_in Rest
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 15760#64)) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (wp_steps; wp_done)

theorem ct1Sampled_ok_branch_no_ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64) (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 15760#64) s_in Rest
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ Rest) ∧
        sf.sp = s_in.sp ∧ sf.readReg64 .x8 = s_in.readReg64 .x8 ∧
        sf.readReg64 .x9 = s_in.readReg64 .x9 ∧ sf.readReg64 .x10 = s_in.readReg64 .x10 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21,
      Reg.x23, Reg.x25, Reg.x29]
    wp_done
  )

theorem ct1Sampled_ok_branch_ack_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64) (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 1#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11624#64) s_in Rest
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 11624#64)) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (wp_steps; wp_done)

theorem ct1Sampled_ok_branch_ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64) (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 1#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11624#64) s_in Rest
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ Rest) ∧
        sf.sp = s_in.sp ∧ sf.readReg64 .x8 = s_in.readReg64 .x8 ∧
        sf.readReg64 .x9 = s_in.readReg64 .x9 ∧ sf.readReg64 .x10 = s_in.readReg64 .x10 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21,
      Reg.x23, Reg.x24, Reg.x25, Reg.x28, Reg.x29]
    wp_done
  )

/-! ## 4. Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`): `+15760 -> +18996` -/

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_no_ack_part1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s_in : State) (fsp stA : BitVec 64)
    (vecs_dec : List (List Pt)) (hvecs_dec_len : vecs_dec.length = NUM_POLYS)
    (c_enc : Words50) (c_ek : Words16)
    (bs352_mid : List (BitVec 8)) (tail5_mid : Words5)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 15760#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = c_ek.w0)
    (hx9 : s_in.readReg64 .x9 = c_ek.w2)
    (hx10 : s_in.readReg64 .x10 = c_ek.w3)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx23 : s_in.readReg64 .x23 = c_enc.c0.w0)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_mid tail5_mid
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16596#64) s_in
      (words50At stA c_enc ∗
        wordsAt (fsp + 3856#64) c_ek.toList ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        vecPtListOf A.repAlloc (fsp + 2752#64) vecs_dec ∗
        memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗
        ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗
        ((fsp + 4112#64) ↦₆₄ v4112) ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            words50At stA c_enc ∗
            memRegion (fsp + 3856#64) 128 ∗
            ((fsp + 232#64) ↦₆₄ stA) ∗
            memRegion (fsp + 2752#64) 400 ∗
            copyScratchStackAt fsp (copyFullScratch sc d) ∗
            epilogueStoreStackPart1At fsp
              { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
                we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
            ((fsp + 976#64) ↦₆₄ c_ek.w13) ∗
            ((fsp + 984#64) ↦₆₄ c_ek.w14) ∗
            ((fsp + 992#64) ↦₆₄ c_ek.w15) ∗
            ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
            ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
            memRegion (fsp + 4096#64) 24 ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest) ∧
          sf.sp = fsp ∧
          AllocCallPreserved s_in sf ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
          sf.readReg64 .x23 = 3#64 ∧
          sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = fsp + 4144#64 ∧
          TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        (Pf ⊢
          words50At stA c_enc ∗
          wordsAt (s_in.sp + 3856#64) c_ek.toList ∗
          ((s_in.sp + 232#64) ↦₆₄ stA) ∗
          (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
          copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At s_in.sp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          ((s_in.sp + 976#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 984#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 992#64) ↦₆₄ c_ek.w15) ∗
          ((s_in.sp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((s_in.sp + 3224#64) ↦₆₄ c_ek.w11) ∗
          (((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
            ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
            ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15)) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt s_in.sp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = s_in.sp ∧
        AllocCallPreserved s_in sf ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 3#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
        TraceCalleeSaved sf s_in) ?_
    (fun sf Pf _ _ ⟨evs, hevs, hPf, hrest⟩ => ⟨evs, hevs, Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    dsimp only [lsProg_332, d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd,
      hx8, hx9, hx10, hx21, hx23, hx29]
    refine seq_vm_cont_lscl hcl (mid := lsmpl.base 264) ?_
    by_vm_steps_nest (
      wp_steps
      refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm => ?_⟩
      have hdrop := DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_mem_on
        (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hclm
      dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget.dropGlueSortedSetPt16Spec,
        polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop
      wp_conv_pre => rw [← A.pool_of_vmPreserved hvmm]
      wp_call hdrop (⟨s_in.sp + 2752#64, vecs_dec⟩, st_cost)
      have hacp12 : AllocCallPreserved s_in sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      refine SepWP.mono (post := fun sf2 Pf2 =>
        VmPreserved sf sf2 ∧
        (Pf2 ⊢
          words50At stA c_enc ∗
          wordsAt (s_in.sp + 3856#64) c_ek.toList ∗
          ((s_in.sp + 232#64) ↦₆₄ stA) ∗
          (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
          copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At s_in.sp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          ((s_in.sp + 976#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 984#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 992#64) ↦₆₄ c_ek.w15) ∗
          ((s_in.sp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((s_in.sp + 3224#64) ↦₆₄ c_ek.w11) ∗
          (((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
            ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
            ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15)) ∗
          A.pool lim (M.stepEvents w st_cost) sf ∗
          (memRegion (s_in.sp - 19552#64) 15424 ∗ stackAt s_in.sp dropGluePoly16Stack) ∗
          Rest) ∧
        sf2.sp = s_in.sp ∧
        AllocCallPreserved sf sf2 ∧
        sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf2.readReg64 .x23 = 3#64 ∧
        sf2.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf2.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf2.readReg64 .x29 = s_in.sp + 4144#64 ∧
        TraceCalleeSaved sf2 s_in) ?_
        (fun _ _ _ _ ⟨hvm2, hPf2, hsp2, hacp3, hrest2⟩ =>
          ⟨w, hevs_w,
            by
              rw [A.pool_of_vmPreserved hvm2]
              dsimp only [d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
                epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList,
                BitVec.ofNat_eq_ofNat] at hPf2
              simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd] at hPf2
              exact hPf2,
            hsp2, hacp12.trans hacp3, hrest2⟩)
      dsimp only [d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
        epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList,
        BitVec.ofNat_eq_ofNat]
      simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
      by_vm_steps_nest (
        wp_steps
        dsimp only [AllocCallPreserved, TraceCalleeSaved, Reg.x19, Reg.x23, Reg.x24, Reg.x28, Reg.x29]
        wp_done
      )
    )
  · have h3856_mr := wordsAt_entails_memRegion c_ek.toList (s_in.sp + 3856#64) 128 rfl
    have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    have h4096_mr :
        ((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15) ⊢
        memRegion (s_in.sp + 4096#64) 24 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 4096#64) (n := 8) (k := 16)
            (b' := s_in.sp + 4104#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 4104#64) (n := 8) (k := 8)
            (b' := s_in.sp + 4112#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono h3856_mr (sepConj_mono_right (sepConj_mono h2752_mr
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left h4096_mr)))))))))))

theorem ct1Sampled_copy_some_no_ack_part2a_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 3#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = 2#64 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved (sessionMemcpySpec 4096)) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976,
      hsplit, ← hmid376_len]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [Words5.toList, withVmPreserved, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun _ => ?_⟩
    wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976)
    have hvm_all : VmPreserved s_in sf := by assumption
    refine SepWP.mono (post := fun sf2 Pf2 =>
      VmPreserved sf sf2 ∧
      (Pf2 ⊢ _) ∧
      sf2.sp = s_in.sp ∧
      sf2.readReg64 .x8 = 2#64 ∧
      sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf2.readReg64 .x28 = s_in.sp + 3272#64 ∧
      sf2.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf2 s_in) ?_
      (fun _ _ _ _ ⟨hvm2, hrest⟩ => ⟨hvm_all.trans hvm2, hrest⟩)
    by_vm_steps_nest (wp_steps; dsimp only [TraceCalleeSaved, Reg.x8, Reg.x19, Reg.x28, Reg.x29]; wp_done)
  )

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_no_ack_part2b_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (c_ek : Words16)
    (bs352_976 bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v576 v584 v592 vf10 vf18 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16800#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = 2#64)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_576 k.tail
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
        ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
        mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗
        ((fsp + 3864#64) ↦₆₄ vf18) ∗
        statesRecvRoPlacedAt ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
          mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3864#64) ↦₆₄ c_ek.w11) ∗
          statesRecvRoPlacedAt ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  dsimp only [lsProg_332, statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt,
    lsLogFilterAddr, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes c_ek.w13 c_ek.w14 c_ek.w15 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_576]
  dsimp only [d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx8, hx28]
  refine seq_vm_cont (mid := (blkPl_332).base + 16884#64) ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl (by simp only [wp_norm, arm64_norm]; exact hrun)
      ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
    refine step_adrp_vm hvmm (blkPC_332_pairStep_0x41f4 inferInstance (blkPl_332).base
      (Rust.withPanics ext) rfl rfl (by simp only [wp_norm, arm64_norm]; exact hrun)) ?_
    by_vm_steps_nest (wp_steps; dsimp only [TraceCalleeSaved, Reg.x19, Reg.x29]; wp_done)
  )

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5PlacedBudget
