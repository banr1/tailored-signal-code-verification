/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFastPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsSlowPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTailPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.ProofPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsSlow
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed Top-Level Proof

Composes all branches of `<PolyEncoder as Encoder>::next_chunk` under `[LibsignalPlacement]` with
`RustCliAllocBudget M`, `BudgetLimits`, and `PolyNextChunkEnv`, parameterized over
`PointsToPolysLoopPlacedProp M A lim ext` (`+976 -> +4424`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.ProofPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416
   extract_withLsCodeLoaded lsmpl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (NUM_POLYS Point Poly)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkDataOff chunkIndexOff chunkSize encoderStateAt pointListOf polyEncoderAt
   polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize polyEncoderPointsTag polyEncoderPolysTag
   polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize polyListOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareStack readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost chunkPointsBytes chunkPointsBytes_length chunkPolysBytes
   completePointsPolysPlacedAt firstSlowIdxAux firstSlowIdxAux_fast firstSlowIdxAux_le_16
   firstSlowIdxAux_slow localFramePointsRest localFramePointsRest_fold_slow
   localFramePointsRest_unfold_slow localFrameRest localFrameRest_fold_points
   localFrameRest_unfold_points memRegion_656_join_680 nextChunkCalleeStack
   nextChunk_points_slow_eq nextChunk_polys_eq pointToPolyPure pointToPolyPure_coefficients_length
   polyNextChunkStack savedCells sepWP_exists_left_sep sepWPp_of_sepWP_lscl
   sepWPp_seq_lscl sp_sub_1200_add_48 sp_sub_1200_add_48' sp_sub_1200_add_88 sp_sub_1200_add_88'
   sp_sub_1200_add_104 sp_sub_1200_add_104' sp_sub_1200_add_1104 stackAt_lagrangePrepare_fold_alloc
   stackAt_lagrangePrepare_split_alloc stackAt_nextChunkCallee_split_blockC
   stackAt_nextChunkCallee_split_lagrangePrepare)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (NextChunkEpilogueEnv NextChunkPolysLoopEnv NextChunkPolysTailByLenEnv NextChunkPrologueEnv
   PointsToPolysLoopEnv PolyNextChunkBlockOkX PolyNextChunkCallerOkX PolyNextChunkEnv
   PolyNextChunkPlacedOkExt computeAtEvents_satisfies_callEnv nextChunkBlockAEvents
   nextChunkEpilogueEvents nextChunkFirstSlowIdx nextChunkPrologueEvents
   polyNextChunkBlockOkX_of_placedOkExt polyNextChunkCallerOkX_of_placedOkExt
   polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv polyNextChunkRodataPlacedSpec
   polyNextChunkRodataPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced epilogue_placed_sepWP fitsEnv_nextChunkPrologue_iff
   prologue_lscl_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFastPlacedBudget
  (NextChunkPointsFastEnv nextChunkPointsFastEvents nextChunkPointsFastEvents_eq
   nextChunk_points_fast_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsSlowPlacedBudget
  (blockA_lscl_placed_sepWPp blockC_placed_sepWP pointsFastPrefix_placed_sepWP
   pointsSlowTrigger_placed_sepWP sepWPp_drop_frame_placed_gen)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedBBudget
  (BlockAEnv blockAEvents fitsEnv_blockA_iff)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlacedBudget
  (polysLoopEvents polysLoop_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTailPlacedBudget
  (polysTailLoop_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget
  (PolyNextChunkRodataPlacedOkExt polyNextChunkPlacedOkExt_of_rodata
   to_defsBudget_rodataPlacedOkExt_ofEnv)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
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
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero sp_sub_1200_add_1104
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  sp_sub_1200_add_48 sp_sub_1200_add_48'
  sp_sub_1200_add_88 sp_sub_1200_add_88'
  sp_sub_1200_add_104 sp_sub_1200_add_104'
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-! ## 1. Pure Index & Event Envelope Normalization Bridges -/

private theorem drop_map_pointToPolyPure :
    ∀ (pts : List Point) (i : Nat),
      (pts.map pointToPolyPure).drop i = (pts.drop i).map pointToPolyPure
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: pts, i + 1 => drop_map_pointToPolyPure pts i

private theorem nextChunkFirstSlowIdx_eq_firstSlowIdxAux (idxNat : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 →
      nextChunkFirstSlowIdx idxNat pts rem i = firstSlowIdxAux idxNat pts rem i
  | 0, i, h => by
    have hi : i = 16 := by omega
    subst hi
    rfl
  | rem + 1, i, h => by
    unfold nextChunkFirstSlowIdx firstSlowIdxAux
    have hlen_opt : (pts[i]?.map (·.value.length)).getD 0 = (pts[i]?.getD ⟨[]⟩).value.length := by
      cases pts[i]? <;> rfl
    rw [hlen_opt]
    by_cases hlt : idxNat < (pts[i]?.getD ⟨[]⟩).value.length
    · have hnot_le : ¬ (pts[i]?.getD ⟨[]⟩).value.length ≤ idxNat := by omega
      simp only [hlt, hnot_le, ↓reduceIte]
      exact nextChunkFirstSlowIdx_eq_firstSlowIdxAux idxNat pts rem (i + 1) (by omega)
    · have hle : (pts[i]?.getD ⟨[]⟩).value.length ≤ idxNat := by omega
      simp only [hlt, hle, ↓reduceIte]

private theorem firstSlowIdxAux_eq_of_fast_slow {idxNat : Nat} {pts : List Point}
    (hlen : pts.length = 16) (i0 : Nat) (hi0 : i0 < 16)
    (hfast : ∀ j (hj : j < pts.length), j < i0 → idxNat < (pts[j]'hj).value.length)
    (hslow : (pts[i0]'(by omega)).value.length ≤ idxNat) :
    firstSlowIdxAux idxNat pts 16 0 = i0 := by
  let k := firstSlowIdxAux idxNat pts 16 0
  have hk_le : k ≤ 16 := firstSlowIdxAux_le_16 idxNat pts 16 0 (by omega)
  rcases Nat.lt_trichotomy k i0 with hlt | heq | hgt
  · have hk16 : k < 16 := by omega
    have hk_len : k < pts.length := by omega
    have h1 := firstSlowIdxAux_slow idxNat pts 16 0 (by omega) hk16
    change (pts[k]?.getD ⟨[]⟩).value.length ≤ idxNat at h1
    rw [List.getElem?_eq_getElem hk_len] at h1
    dsimp only [Option.getD] at h1
    have h2 := hfast k hk_len hlt
    omega
  · exact heq
  · have hi0_len : i0 < pts.length := by omega
    have h1 := firstSlowIdxAux_fast idxNat pts 16 0 i0 (by omega) (by omega) hgt
    rw [List.getElem?_eq_getElem hi0_len] at h1
    dsimp only [Option.getD] at h1
    omega

private theorem epilogue_fitsEnv_prologue_of_defs {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEnv M lim st NextChunkPrologueEnv) :
    FitsEnv M lim st
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget.NextChunkPrologueEnv :=
  fitsEnv_nextChunkPrologue_iff.mpr (h (rustAllocEvents 32 1) rfl)

private theorem blockAEvents_eq_nextChunkBlockAEvents :
    blockAEvents = nextChunkBlockAEvents := rfl

private theorem fitsEnv_blockA_of_eq {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st (· = nextChunkBlockAEvents)) :
    FitsEnv M lim st BlockAEnv :=
  fitsEnv_blockA_iff.mpr (blockAEvents_eq_nextChunkBlockAEvents ▸ h nextChunkBlockAEvents rfl)

private theorem computeAtEvents_eq (len : Nat) :
    LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget.computeAtEvents len =
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.computeAtEvents len := by
  unfold LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget.computeAtEvents
    LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget.computeAtAllocEvents
    LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget.computeAtScratchCap
    LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.computeAtEvents
    LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget.computeAtAllocEvents
    LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.computeAtScratchCap
  rfl

theorem polysLoopEvents_satisfies_loopEnv :
    ∀ (polys : List Poly), NextChunkPolysLoopEnv polys (polysLoopEvents polys)
  | [] => rfl
  | p :: ps => by
    unfold polysLoopEvents NextChunkPolysLoopEnv
    rw [computeAtEvents_eq]
    exact SeqEnv.append
      (computeAtEvents_satisfies_callEnv p.coefficients.length)
      (polysLoopEvents_satisfies_loopEnv ps)

private theorem fitsEvents_polysLoop_of_loopEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {polys : List Poly}
    (h : FitsEnv M lim st (NextChunkPolysLoopEnv polys)) :
    FitsEvents M lim st (polysLoopEvents polys) :=
  h (polysLoopEvents polys) (polysLoopEvents_satisfies_loopEnv polys)

theorem polysLoopEvents_map_satisfies_tailByLenEnv :
    ∀ (pts : List Point),
      NextChunkPolysTailByLenEnv (pts.map (·.value.length))
        (polysLoopEvents (pts.map pointToPolyPure))
  | [] => rfl
  | pt :: pts => by
    simp only [List.map_cons, polysLoopEvents, NextChunkPolysTailByLenEnv,
      pointToPolyPure_coefficients_length, computeAtEvents_eq]
    exact SeqEnv.append
      (computeAtEvents_satisfies_callEnv pt.value.length)
      (polysLoopEvents_map_satisfies_tailByLenEnv pts)

private theorem fitsEvents_polysTail_of_tailByLenEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {pts : List Point} {i0 : Nat}
    (h : FitsEnv M lim st (NextChunkPolysTailByLenEnv ((pts.drop i0).map (·.value.length)))) :
    FitsEvents M lim st (polysLoopEvents ((pts.map pointToPolyPure).drop i0)) := by
  rw [drop_map_pointToPolyPure]
  exact h _ (polysLoopEvents_map_satisfies_tailByLenEnv (pts.drop i0))

private theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q₁ Q₂ Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q₁ Qp)
    (hq : ∀ sf P_f, Q₁ sf P_f → Q₂ sf P_f) :
    SepWPp prog ret s P Q₂ Qp := by
  intro R0 hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R0 hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hpost⟩ | hpan | hoom
  · exact Or.inl ⟨hpc, hrun, P_f, hmf, hq sf P_f hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

private theorem pack_post_of_evs [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : PolyNextChunkGhost} {st st_out : M.σ} {s0 sf1 : State} {R : SepProp}
    {evs : List AllocEvent} (hevs : Env x evs) (hstep : st_out = M.stepEvents evs st)
    (hm : sf1.mem ⊨
      ⌜sf1.trace = s0.trace⌝ ∗ chunkAt x.outA x.chunk ∗ polyEncoderAt A.repAlloc x.encA x.enc' ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_out sf1 ∗
        stackAt s0.sp polyNextChunkStack ∗ R) :
    sf1.mem ⊨ (polyNextChunkPlacedSpecOfEnv Env M A lim).post (x, st) s0 sf1 ∗ R := by
  rw [hstep, satisfies_pure_sepConj] at hm
  dsimp only [polyNextChunkPlacedSpecOfEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [show (⌜Env x evs ∧ sf1.trace = s0.trace⌝ ∗ chunkAt x.outA x.chunk ∗
        polyEncoderAt A.repAlloc x.encA x.enc' ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st) sf1 ∗ stackAt s0.sp polyNextChunkStack) ∗ R =
      ⌜Env x evs ∧ sf1.trace = s0.trace⌝ ∗ (chunkAt x.outA x.chunk ∗
        polyEncoderAt A.repAlloc x.encA x.enc' ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st) sf1 ∗ stackAt s0.sp polyNextChunkStack ∗ R) by sep_ac_rfl]
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hevs, hm.1⟩, hm.2⟩

/-! ## 2. Budget-Threaded Placed Interface for `points_to_polys` (`+976 -> +4424`) -/

/-- Envelope-parametric relocatable `[LibsignalPlacement]` contract for the 16-iteration
    `points_to_polys` conversion loop (`+976 -> +4424` in Block `416`), threading `RustCliAllocBudget M`
    and `LoopEnv pts`. -/
def PointsToPolysLoopPlacedPropOfEnv [LibsignalPlacement]
    (LoopEnv : List Point → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {Q Q_panic : State → SepProp → Prop} {st : M.σ}
    (s0 s : State) (_hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64) (_hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (_hlen : pts.length = 16)
    (_hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame _R : SepProp) (_hpc : s.pc = (blkPl_416).base + 976#64)
    (_hrun : s.status = .Running) (_hsp : s.sp = fsp) (_htrace : s.trace = s0.trace)
    (_hx19 : s.readReg64 .x19 = ptsBase) (_hx20 : s.readReg64 .x20 = 0#64)
    (_hx28 : s.readReg64 .x28 = 24#64) (_hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (_hfit : FitsEnv M lim st (LoopEnv pts)),
    (∀ s_out (evs_p2p : List AllocEvent)
       u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      LoopEnv pts evs_p2p → s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase → s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 → s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents evs_p2p st) s_out ∗ pointListOf A.repAlloc ptsBase pts ∗
         polyListOf A.repAlloc (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗ ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗ memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗ memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) →
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ pointListOf A.repAlloc ptsBase pts ∗
       polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗ ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗ memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗ memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic

/-- Canonical relocatable `[LibsignalPlacement]` contract for the 16-iteration `points_to_polys`
    conversion loop (`+976 -> +4424`) instantiated at `PointsToPolysLoopEnv`. -/
abbrev PointsToPolysLoopPlacedProp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PointsToPolysLoopPlacedPropOfEnv PointsToPolysLoopEnv M A lim ext

/-- Envelope weakening for `PointsToPolysLoopPlacedPropOfEnv`: if `LoopEnv₁ pts ⊆ LoopEnv₂ pts`
    pointwise, any loop proof meeting `LoopEnv₁` also meets `LoopEnv₂`. -/
theorem PointsToPolysLoopPlacedPropOfEnv.mono [LibsignalPlacement]
    {LoopEnv₁ LoopEnv₂ : List Point → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hsub : ∀ pts evs, LoopEnv₁ pts evs → LoopEnv₂ pts evs)
    (h1 : PointsToPolysLoopPlacedPropOfEnv LoopEnv₁ M A lim ext) :
    PointsToPolysLoopPlacedPropOfEnv LoopEnv₂ M A lim ext := by
  intro Q Q_panic st s0 s hcl fsp ptsBase hfsp_align pts hlen hbounds
    u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
    hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit hcont
  exact h1 s0 s hcl fsp ptsBase hfsp_align pts hlen hbounds
    u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
    hpc hrun hsp htrace hx19 hx20 hx28 hx29 (FitsEnv.mono (hsub pts) hfit)
    fun s_out evs_p2p u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
      hevs => hcont s_out evs_p2p u16' u24' u32' u40' u64' u72' u80' u96' u640' u648'
        u1040' u1048' u1056' (hsub pts evs_p2p hevs)

private theorem pointsToPolysLoop_lscl_of_prop [LibsignalPlacement]
    {LoopEnv : List Point → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (h_p2p : PointsToPolysLoopPlacedPropOfEnv LoopEnv M A lim ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (hlen : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp) (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase) (hx20 : s.readReg64 .x20 = 0#64)
    (hx28 : s.readReg64 .x28 = 24#64) (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (LoopEnv pts))
    (hcont : ∀ s_out (evs_p2p : List AllocEvent)
       u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s_out.mem → LoopEnv pts evs_p2p →
      s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase → s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 → s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents evs_p2p st) s_out ∗ pointListOf A.repAlloc ptsBase pts ∗
         polyListOf A.repAlloc (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗ ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗ memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗ memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ pointListOf A.repAlloc ptsBase pts ∗
       polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗ ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗ memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗ memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  let s0' : State := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_416).base + 4424#64)
  have hlr' : s0'.readReg64 (Reg.gpr 30#5) = (blkPl_416).base + 4424#64 := by
    simp [s0', arm64_norm, wp_norm]
  have htr' : s.trace = s0'.trace := by
    simpa [s0', arm64_norm, wp_norm] using htrace
  refine sepWPp_seq_lscl (mid := s0'.readReg64 (Reg.gpr 30#5)) hcl ?_
  refine h_p2p s0' s hcl fsp ptsBase hfsp_align pts hlen hbounds
    u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
    hpc hrun hsp htr' hx19 hx20 hx28 hx29 hfit ?_
  intro s_out evs_p2p u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hevs_p2p hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out
  refine SepWPp.done (hlr' ▸ hpc_out) hrun_out (fun hcl_out => ?_)
  have htr_out0 : s_out.trace = s0.trace := by simpa [s0', arm64_norm, wp_norm] using htr_out
  exact hcont s_out evs_p2p u16' u24' u32' u40' u64' u72' u80' u96' u640' u648'
    u1040' u1048' u1056' hcl_out hevs_p2p hpc_out hrun_out hsp_out htr_out0 hvregs_out
    hx19_out hx20_out hx27_out hx28_out hx29_out

/-! ## 3. `EncoderState::Polys` Branch under `PolyNextChunkEnv` -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded `EncoderState::Polys` branch of `<PolyEncoder as Encoder>::next_chunk` (Block `416`)
    producing `(polyNextChunkPlacedSpec M A lim).post` under arbitrary `Q_panic`. -/
theorem nextChunk_polys_polyEnv_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List Poly)
    (hs_polys : x.enc.s = .polys polys)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp)
    {Q_panic : State → SepProp → Prop}
    (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st (PolyNextChunkEnv x)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A.repAlloc x.encA x.enc ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨ (polyNextChunkPlacedSpec M A lim).post (x, st) s0 sf1 ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      Q_panic := by
  have hfit_seq1 :
      FitsEnv M lim st
        (SeqEnv NextChunkPrologueEnv (SeqEnv (NextChunkPolysLoopEnv polys) NextChunkEpilogueEnv)) := by
    unfold PolyNextChunkEnv at hfit
    rwa [hs_polys] at hfit
  have hfit_pro :
      FitsEnv M lim st
        LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget.NextChunkPrologueEnv :=
    epilogue_fitsEnv_prologue_of_defs hfit_seq1.seq_left
  have hfit_seq2 := hfit_seq1.seq_right (rfl : NextChunkPrologueEnv (rustAllocEvents 32 1))
  have hfit_loop : FitsEvents M lim (M.stepEvents (rustAllocEvents 32 1) st) (polysLoopEvents polys) :=
    fitsEvents_polysLoop_of_loopEnv hfit_seq2.seq_left
  unfold polyEncoderAt encoderStateAt
  rw [hs_polys]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; intro hlen_polys
  have hlen16 : polys.length = 16 := hlen_polys
  have henc_eq : x.enc = { idx := x.enc.idx, s := .polys polys } := by
    rw [← hs_polys]
  have hnc := nextChunk_polys_eq (idx := x.enc.idx) hlen16
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList = chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16 := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by
    rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by
    rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .polys polys := by
    rw [← henc'_eq]
  refine prologue_lscl_placed_sepWPp M A lim st ext hA x polyEncoderPolysTag
    (polyListOf A.repAlloc (x.encA + polyEncoderVecsOff) polys) R s0 hcl0 hpc hrun hsp0 hx0 hx8
    hfit_pro ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hx9_1 _hx19_1 hx24_1 hx27_1 _hx29_1
  change s1.readReg64 .x9 = 1#64 at hx9_1
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 136#64) hcl1 ?_
  apply sepWP_seg_416 (mid := (blkPl_416).base + 136#64)
  intro _m_strip0
  wp_steps 4
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl2
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPolysBytes, pointsToBytes_nil, emp_sepConj]
  refine SepWPp.weaken_pre ?_
    (polysLoop_placed_sepWPp M A lim ext hA x polys hlen16 out_ptr R s0 hsp0 15 0 rfl
      (M.stepEvents (rustAllocEvents 32 1) st) _ hcl2
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simpa [List.drop_zero] using hfit_loop) ?_)
  · apply Entails.of_eq
    rw [hinit_buf]
    simp only [arm64_norm]
    sep_ac_rfl
  · wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp1
  · simpa [arm64_norm, wp_norm] using htr1
  · simpa [arm64_norm, wp_norm] using hvregs1
  · simp [arm64_norm, wp_norm, hx24_1]
  · rfl
  · simpa [arm64_norm, wp_norm] using hx24_1
  · simpa [arm64_norm, wp_norm] using hx27_1
  intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _hcl_f hx20_f hx24_f hx27_f
  apply SepWPp.of_sepWP_ret
  have henc'_state :
      (x.encA ↦₆₄ polyEncoderPolysTag) ∗ polyListOf A.repAlloc (x.encA + 8#64) polys ⊢
        encoderStateAt A.repAlloc x.encA x.enc'.s := by
    rw [hs_enc']
    unfold encoderStateAt
    dsimp only [polyEncoderVecsOff]
    have htrue : (polys.length = NUM_POLYS) = True := propext ⟨fun _ => trivial, fun _ => hlen_polys⟩
    rw [htrue, pure_true, emp_sepConj]
    exact Entails.refl _
  apply SepWP.fold henc'_state (by sep_focus)
  rw [← hdata_eq, List.drop_zero]
  have hevs_polys :
      PolyNextChunkEnv x
        (rustAllocEvents 32 1 ++ (polysLoopEvents polys ++ rustDeallocEvents 32 1)) := by
    unfold PolyNextChunkEnv
    rw [hs_polys]
    exact SeqEnv.append rfl
      (SeqEnv.append (polysLoopEvents_satisfies_loopEnv polys) rfl)
  have hstep_final :
      M.stepEvents (rustDeallocEvents 32 1)
        (M.stepEvents (polysLoopEvents polys) (M.stepEvents (rustAllocEvents 32 1) st)) =
        M.stepEvents (rustAllocEvents 32 1 ++ (polysLoopEvents polys ++ rustDeallocEvents 32 1)) st := by
    rw [M.stepEvents_append, M.stepEvents_append]
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
      (epilogue_placed_sepWP M A lim
        (M.stepEvents (polysLoopEvents polys) (M.stepEvents (rustAllocEvents 32 1) st))
        ext hA x R s0 sf out_ptr hout_ne hidx_chunk hidx_enc'
        hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f))
    (fun sf1 P_f _ _ ⟨hm1, hsp_sf1, hcs_sf1⟩ =>
      ⟨fun hm => pack_post_of_evs hevs_polys hstep_final (hm1 hm), hsp_sf1, hcs_sf1⟩)
  rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
  rfl

/-! ## 4. Slow `EncoderState::Points` Path (`nextChunk_points_slow_placed_sepWPp`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded slow `EncoderState::Points` branch of `<PolyEncoder as Encoder>::next_chunk`
    (Block `416`): prologue + fast prefix `0..i0` + slow trigger at `i0` + Block A +
    `points_to_polys` loop (`h_p2p`) + Block C + polynomial tail `i0..15` + epilogue. -/
theorem nextChunk_points_slow_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext)
    (x : PolyNextChunkGhost) (pts : List Point)
    (hs_pts : x.enc.s = .points pts)
    (hlen_pts : pts.length = NUM_POLYS)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (i0 : Nat) (hi0 : i0 < 16)
    (hfast : ∀ j (hj : j < pts.length), j < i0 →
      (x.enc.idx.setWidth 16).toNat < (pts[j]'hj).value.length)
    (hslow : (pts[i0]'(by rw [hlen_pts]; exact hi0)).value.length ≤ (x.enc.idx.setWidth 16).toNat)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp)
    {PanicPost : State → SepProp}
    (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st (PolyNextChunkEnv x)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A.repAlloc x.encA x.enc ∗
       completePointsPolysPlacedAt ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨ (polyNextChunkPlacedSpec M A lim).post (x, st) s0 sf1 ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanicPost sf ∗ R)) := by
  have hlen16 : pts.length = 16 := hlen_pts
  have hfsi_eq : nextChunkFirstSlowIdx (x.enc.idx.setWidth 16).toNat pts 16 0 = i0 :=
    (nextChunkFirstSlowIdx_eq_firstSlowIdxAux (x.enc.idx.setWidth 16).toNat pts 16 0 (by omega)).trans
      (firstSlowIdxAux_eq_of_fast_slow hlen16 i0 hi0 hfast hslow)
  have hfit_seq1 :
      FitsEnv M lim st
        (SeqEnv NextChunkPrologueEnv
          (SeqEnv (· = nextChunkBlockAEvents)
            (SeqEnv (PointsToPolysLoopEnv pts)
              (SeqEnv FreeOnlyEvs
                (SeqEnv (NextChunkPolysTailByLenEnv ((pts.drop i0).map (·.value.length)))
                  NextChunkEpilogueEnv))))) := by
    intro evs hevs
    apply hfit evs
    unfold PolyNextChunkEnv
    rw [hs_pts]
    dsimp only
    simp only [hfsi_eq, hi0, ↓reduceIte]
    exact hevs
  have hfit_pro :
      FitsEnv M lim st
        LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget.NextChunkPrologueEnv :=
    epilogue_fitsEnv_prologue_of_defs hfit_seq1.seq_left
  have hfit_seq2 := hfit_seq1.seq_right (rfl : NextChunkPrologueEnv (rustAllocEvents 32 1))
  have hfit_ba : FitsEnv M lim (M.stepEvents (rustAllocEvents 32 1) st) BlockAEnv :=
    fitsEnv_blockA_of_eq hfit_seq2.seq_left
  have hfit_seq3 := hfit_seq2.seq_right (rfl : (· = nextChunkBlockAEvents) nextChunkBlockAEvents)
  have hfit_p2p :
      FitsEnv M lim
        (M.stepEvents nextChunkBlockAEvents (M.stepEvents (rustAllocEvents 32 1) st))
        (PointsToPolysLoopEnv pts) :=
    hfit_seq3.seq_left
  have hfsp_align : ((s0.sp - 1200#64) &&& 15#64 == 0#64) = true := by
    apply beq_iff_eq.mpr; revert hsp0; bv_bits
  conv => arg 4; unfold polyEncoderAt encoderStateAt; rw [hs_pts]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad P_ro Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ P_ro ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ (P_list ∗ P_ro) ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; intro _
  have henc_eq : x.enc = { idx := x.enc.idx, s := .points pts } := by rw [← hs_pts]
  have hnc := nextChunk_points_slow_eq hlen16 hbounds i0 hi0 hfast hslow
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList =
      chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0 ++
        chunkPolysBytes (x.enc.idx.setWidth 16) (pts.map pointToPolyPure) i0 (15 - i0 + 1) := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .polys (pts.map pointToPolyPure) := by rw [← henc'_eq]
  refine prologue_lscl_placed_sepWPp M A lim st ext hA x polyEncoderPointsTag
    (pointListOf A.repAlloc (x.encA + polyEncoderVecsOff) pts ∗ completePointsPolysPlacedAt)
    R s0 hcl0 hpc hrun hsp0 hx0 hx8 hfit_pro ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  change s1.readReg64 .x9 = 0#64 at hx9_1
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 288#64) hcl1 ?_
  apply sepWP_seg_416 (mid := (blkPl_416).base + 288#64)
  intro _m_strip0
  apply SepWP.fold (localFrameRest_unfold_points (s0.sp - 1200#64)) (by sep_focus)
  apply sepWP_exists_left_sep; intro u48
  apply sepWP_exists_left_sep; intro u88
  apply sepWP_exists_left_sep; intro u104
  wp_steps 9
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl_288
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 436#64) hcl_288 ?_
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPointsBytes, pointsToBytes_nil, emp_sepConj]
  refine SepWP.weaken_pre ?_
    (pointsFastPrefix_placed_sepWP M A lim (M.stepEvents (rustAllocEvents 32 1) st) ext x pts hlen16
      out_ptr (s0.sp - 1200#64) hfsp_align
      (A.live out_ptr 32 1 ∗ memRegion x.outA chunkSize ∗ (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       completePointsPolysPlacedAt ∗ ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗ (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗ savedCells s0 ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      i0 0 u104 _ (by omega) (fun j hj => hfast j (by omega) (by omega))
      (by wp_norm_goal) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      rfl (by simpa [arm64_norm, wp_norm] using hx19_1) rfl rfl
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1) rfl ?_)
  · rw [hinit_buf]
    exact Entails.of_eq (by
      conv => lhs; simp only [arm64_norm]
      conv => rhs; simp only [arm64_norm]
      sep_ac_rfl)
  intro s2 u104' hpc2 hrun2 hsp2 htr2 hvregs2 hx9_2 hx19_2 hx20_2 hx21_2 hx24_2 hx27_2 hx28_2 hx29_2
  simp only [Nat.zero_add] at hx9_2 hx20_2 ⊢
  refine SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
    (pointsSlowTrigger_placed_sepWP M A lim (M.stepEvents (rustAllocEvents 32 1) st) ext x pts hlen16
      i0 hi0 hslow (s0.sp - 1200#64) u104' hfsp_align
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗ (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗ memRegion x.outA chunkSize ∗ (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       completePointsPolysPlacedAt ∗ ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗ (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗ savedCells s0 ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      s2 hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx24_2 hx27_2 hx28_2 ?_)
  intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx24_3 hx27_3 hx29_3
  refine SepWP.done hpc3 hrun3 ?_
  intro hcl3
  have htr3_0 : s3.trace = s0.trace := by
    rw [htr3, htr2]; simpa [arm64_norm, wp_norm] using htr1
  have hx29_3_0 : s3.readReg64 .x29 = (s0.sp - 1200#64) + 1104#64 := by
    rw [hx29_3, hx29_2]; simpa [arm64_norm, wp_norm] using hx29_1
  apply SepWPp.fold (localFramePointsRest_unfold_slow (s0.sp - 1200#64)) (by sep_focus)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWPp.exists_elim; intro _)
  rename_i u8 u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
  rw [stackAt_nextChunkCallee_split_lagrangePrepare (s0.sp - 1200#64),
      stackAt_lagrangePrepare_split_alloc (s0.sp - 1200#64)]
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
    (blockA_lscl_placed_sepWPp hA s0 s3 hcl3 (s0.sp - 1200#64) (x.encA + 8#64) u8 hfsp_align
      (pointListOf A.repAlloc (x.encA + 8#64) pts ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
       (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗ (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗ memRegion x.outA chunkSize ∗ (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       completePointsPolysPlacedAt ∗ ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗ (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       memRegion (s0.sp - 1200#64) 8 ∗
       (((s0.sp - 1200#64) + 16#64) ↦₆₄ u16) ∗ (((s0.sp - 1200#64) + 24#64) ↦₆₄ u24) ∗
       (((s0.sp - 1200#64) + 32#64) ↦₆₄ u32) ∗ (((s0.sp - 1200#64) + 40#64) ↦₆₄ u40) ∗
       (((s0.sp - 1200#64) + 64#64) ↦₆₄ u64) ∗ (((s0.sp - 1200#64) + 72#64) ↦₆₄ u72) ∗
       (((s0.sp - 1200#64) + 80#64) ↦₆₄ u80) ∗ (((s0.sp - 1200#64) + 96#64) ↦₆₄ u96) ∗
       (((s0.sp - 1200#64) + 640#64) ↦₆₄ u640) ∗ (((s0.sp - 1200#64) + 648#64) ↦₆₄ u648) ∗
       memRegion ((s0.sp - 1200#64) + 656#64) 24 ∗ memRegion ((s0.sp - 1200#64) + 680#64) 360 ∗
       (((s0.sp - 1200#64) + 1040#64) ↦₆₄ u1040) ∗ (((s0.sp - 1200#64) + 1048#64) ↦₆₄ u1048) ∗
       (((s0.sp - 1200#64) + 1056#64) ↦₆₄ u1056) ∗ memRegion ((s0.sp - 1200#64) + 1064#64) 40 ∗
       savedCells s0 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       memRegion ((s0.sp - 1200#64) - 17232#64) 12928 ∗
       memRegion ((s0.sp - 1200#64) - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack))
      R hpc3 hrun3 hsp3 htr3_0 hfit_ba ?_)
  intro s4 hcl4 hpc4 hrun4 hsp4 htr4 hvregs4 hx19_4 hx20_4 hx27_4 hx28_4 hx29_4
  rw [hx24_3]
  rw [hx27_3] at hx27_4
  rw [hx29_3_0] at hx29_4
  rw [blockAEvents_eq_nextChunkBlockAEvents]
  apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc (s0.sp - 1200#64)) (by sep_focus)
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm, wp_norm]; sep_ac_rfl))
    (pointsToPolysLoop_lscl_of_prop h_p2p s0 s4 hcl4 (s0.sp - 1200#64) (x.encA + 8#64) hfsp_align
      pts hlen16 hbounds u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      ((((s0.sp - 1200#64) + 8#64) ↦₆₄ x.encA) ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
       (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗ (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗ memRegion x.outA chunkSize ∗ (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗ memRegion (s0.sp - 1200#64) 8 ∗
       memRegion ((s0.sp - 1200#64) + 680#64) 360 ∗ memRegion ((s0.sp - 1200#64) + 1064#64) 40 ∗
       savedCells s0 ∗ memRegion ((s0.sp - 1200#64) - 17232#64) 12928)
      R hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx28_4 hx29_4 hfit_p2p ?_)
  intro s5 evs_p2p u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hcl5 hevs_p2p hpc5 hrun5 hsp5 htr5 hvregs5 hx19_5 hx20_5 hx27_5 hx28_5 hx29_5
  rw [hx27_4] at hx27_5
  have hfit_seq4 := hfit_seq3.seq_right hevs_p2p
  have hfold_nc_stack :
      memRegion ((s0.sp - 1200#64) - 17232#64) 12928 ∗
        stackAt (s0.sp - 1200#64) lagrangePrepareStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [stackAt_nextChunkCallee_split_lagrangePrepare (s0.sp - 1200#64)]; exact Entails.refl _
  apply SepWPp.fold hfold_nc_stack (by sep_focus)
  apply SepWPp.fold (memRegion_656_join_680 (s0.sp - 1200#64)) (by sep_focus)
  rw [stackAt_nextChunkCallee_split_blockC (s0.sp - 1200#64)]
  have hlen_polys : (pts.map pointToPolyPure).length = 16 := by simp [hlen16]
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 296#64) hcl5 ?_
  refine SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm, wp_norm]; sep_ac_rfl))
    (blockC_placed_sepWP M A lim
      (M.stepEvents evs_p2p (M.stepEvents nextChunkBlockAEvents (M.stepEvents (rustAllocEvents 32 1) st)))
      ext hA x pts hlen16 (pts.map pointToPolyPure) hlen_polys i0
      (s0.sp - 1200#64) hfsp_align
      ((((s0.sp - 1200#64) + 16#64) ↦₆₄ u16') ∗ (((s0.sp - 1200#64) + 24#64) ↦₆₄ u24') ∗
       (((s0.sp - 1200#64) + 32#64) ↦₆₄ u32') ∗ (((s0.sp - 1200#64) + 40#64) ↦₆₄ u40') ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗ (((s0.sp - 1200#64) + 64#64) ↦₆₄ u64') ∗
       (((s0.sp - 1200#64) + 72#64) ↦₆₄ u72') ∗ (((s0.sp - 1200#64) + 80#64) ↦₆₄ u80') ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 96#64) ↦₆₄ u96') ∗ memRegion ((s0.sp - 1200#64) + 112#64) 120 ∗
       (((s0.sp - 1200#64) + 640#64) ↦₆₄ u640') ∗ (((s0.sp - 1200#64) + 648#64) ↦₆₄ u648') ∗
       (((s0.sp - 1200#64) + 1040#64) ↦₆₄ u1040') ∗ (((s0.sp - 1200#64) + 1048#64) ↦₆₄ u1048') ∗
       (((s0.sp - 1200#64) + 1056#64) ↦₆₄ u1056') ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗ (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗ memRegion x.outA chunkSize ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗ memRegion (s0.sp - 1200#64) 8 ∗
       memRegion ((s0.sp - 1200#64) + 1064#64) 40 ∗ savedCells s0 ∗
       memRegion ((s0.sp - 1200#64) - 17232#64) 13104)
      s5 hcl5 hpc5 hrun5 hsp5 hx19_5 hx27_5 hx28_5 ?_)
  intro s6 evs_c hevs_c hpc6 hrun6 hsp6 htr6 hvregs6 hx9_6 hx19_6 hx24_6 hx27_6 hx28_6 hx29_6
  refine SepWP.done hpc6 hrun6 ?_
  intro hcl6
  have hfit_seq5 := hfit_seq4.seq_right hevs_c
  have hfit_tail :
      FitsEvents M lim
        (M.stepEvents evs_c
          (M.stepEvents evs_p2p
            (M.stepEvents nextChunkBlockAEvents (M.stepEvents (rustAllocEvents 32 1) st))))
        (polysLoopEvents ((pts.map pointToPolyPure).drop i0)) :=
    fitsEvents_polysTail_of_tailByLenEnv hfit_seq5.seq_left
  have htr6_0 : s6.trace = s0.trace := htr6.trans htr5
  have hvregs6_0 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
    rw [hvregs6, hvregs5, hvregs4, hvregs3, hvregs2]
    simpa [arm64_norm, wp_norm] using hvregs1
  have hfold_bc_stack :
      memRegion ((s0.sp - 1200#64) - 17232#64) 13104 ∗
        memRegion ((s0.sp - 1200#64) - 4128#64) 32 ∗
        stackAt (s0.sp - 1200#64) allocHookStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [stackAt_nextChunkCallee_split_blockC (s0.sp - 1200#64)]; exact Entails.refl _
  apply SepWPp.fold hfold_bc_stack (by sep_focus)
  apply SepWPp.fold
    (localFramePointsRest_fold_slow (s0.sp - 1200#64)
      x.encA u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056')
    (by sep_focus)
  refine SepWPp.weaken_pre ?h_ent
    (sepWPp_drop_frame_placed_gen
      (F := completePointsPolysPlacedAt)
      (PostRest := fun sf1 => (polyNextChunkPlacedSpec M A lim).post (x, st) s0 sf1)
      (PanicPost := PanicPost)
      (polysTailLoop_placed_sepWPp M A lim ext hA x (pts.map pointToPolyPure) hlen_polys
        out_ptr 2#64 (completePointsPolysPlacedAt ∗ R) s0 hsp0
        (15 - i0) i0 (chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0)
        (M.stepEvents evs_c
          (M.stepEvents evs_p2p
            (M.stepEvents nextChunkBlockAEvents (M.stepEvents (rustAllocEvents 32 1) st))))
        s6 hcl6 (by omega) (chunkPointsBytes_length (x.enc.idx.setWidth 16) pts 0 i0)
        hpc6 hrun6 hsp6 htr6_0 hvregs6_0 hx9_6 hx19_6 hx24_6 hx27_6 hx28_6 hfit_tail ?h_tail))
  case h_ent =>
    exact Entails.of_eq (by simp only [arm64_norm, Nat.mul_comm 2 i0]; sep_ac_rfl)
  case h_tail =>
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _hcl_f hx20_f hx24_f hx27_f
    apply SepWPp.of_sepWP_ret
    have hlfr_fold :
        (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
          (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
          localFramePointsRest (s0.sp - 1200#64) ⊢ localFrameRest (s0.sp - 1200#64) :=
      localFrameRest_fold_points (s0.sp - 1200#64) 2#64 (x.encA + 8#64) 15#64
    apply SepWP.fold hlfr_fold (by sep_focus)
    have henc'_state :
        (x.encA ↦₆₄ polyEncoderPolysTag) ∗
          polyListOf A.repAlloc (x.encA + 8#64) (pts.map pointToPolyPure) ⊢
          encoderStateAt A.repAlloc x.encA x.enc'.s := by
      rw [hs_enc']; unfold encoderStateAt; dsimp only [polyEncoderVecsOff]
      have htrue : ((pts.map pointToPolyPure).length = NUM_POLYS) = True :=
        propext ⟨fun _ => trivial, fun _ => by simp [hlen_pts]⟩
      rw [htrue, pure_true, emp_sepConj]; exact Entails.refl _
    apply SepWP.fold henc'_state (by sep_focus)
    rw [← hdata_eq]
    have hevs_slow :
        PolyNextChunkEnv x
          (rustAllocEvents 32 1 ++ (nextChunkBlockAEvents ++ (evs_p2p ++ (evs_c ++
            (polysLoopEvents ((pts.map pointToPolyPure).drop i0) ++ rustDeallocEvents 32 1))))) := by
      unfold PolyNextChunkEnv; rw [hs_pts]; dsimp only
      simp only [hfsi_eq, hi0, ↓reduceIte, drop_map_pointToPolyPure]
      exact SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append hevs_p2p
        (SeqEnv.append hevs_c
          (SeqEnv.append (polysLoopEvents_map_satisfies_tailByLenEnv (pts.drop i0)) rfl))))
    have hstep_slow :
        M.stepEvents (rustDeallocEvents 32 1)
          (M.stepEvents (polysLoopEvents ((pts.map pointToPolyPure).drop i0))
            (M.stepEvents evs_c
              (M.stepEvents evs_p2p
                (M.stepEvents nextChunkBlockAEvents (M.stepEvents (rustAllocEvents 32 1) st))))) =
          M.stepEvents
            (rustAllocEvents 32 1 ++ (nextChunkBlockAEvents ++ (evs_p2p ++ (evs_c ++
              (polysLoopEvents ((pts.map pointToPolyPure).drop i0) ++ rustDeallocEvents 32 1)))))
            st := by
      rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append,
        M.stepEvents_append, M.stepEvents_append]
    refine SepWP.mono
      (SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
        (epilogue_placed_sepWP M A lim
          (M.stepEvents (polysLoopEvents ((pts.map pointToPolyPure).drop i0))
            (M.stepEvents evs_c
              (M.stepEvents evs_p2p
                (M.stepEvents nextChunkBlockAEvents (M.stepEvents (rustAllocEvents 32 1) st)))))
          ext hA x (completePointsPolysPlacedAt ∗ R) s0 sf out_ptr hout_ne
          hidx_chunk hidx_enc' hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f))
      (fun sf1 P_f _ _ ⟨hm1, hsp_sf1, hcs_sf1⟩ =>
        ⟨fun hm => pack_post_of_evs hevs_slow hstep_slow (hm1 hm), hsp_sf1, hcs_sf1⟩)
    rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
    rfl

/-! ## 5. Full `EncoderState::Points` Dispatcher (`nextChunk_points_placed_sepWPp`) -/

/-- Complete budget-threaded relocatable proof of `<PolyEncoder as Encoder>::next_chunk` (Block `416`)
    on `EncoderState::Points`, dispatching between `nextChunk_points_slow_placed_sepWPp`
    (`firstSlowIdx < 16`) and `nextChunk_points_fast_placed_sepWPp` (`firstSlowIdx = 16`). -/
theorem nextChunk_points_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext)
    (x : PolyNextChunkGhost) (pts : List Point)
    (hs_pts : x.enc.s = .points pts)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) {PanicPost : State → SepProp} (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base) (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA) (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st (PolyNextChunkEnv x)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0
      (memRegion x.outA chunkSize ∗ polyEncoderAt A.repAlloc x.encA x.enc ∗
       completePointsPolysPlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨ (polyNextChunkPlacedSpec M A lim).post (x, st) s0 sf1 ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanicPost sf ∗ R)) := by
  conv => arg 4; unfold polyEncoderAt encoderStateAt; rw [hs_pts]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; rintro ⟨hlen_pts, hbounds⟩
  have hrestore :
      memRegion x.outA chunkSize ∗ (x.encA ↦₆₄ polyEncoderPointsTag) ∗
        pointListOf A.repAlloc (x.encA + polyEncoderVecsOff) pts ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        completePointsPolysPlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack =
      memRegion x.outA chunkSize ∗ polyEncoderAt A.repAlloc x.encA x.enc ∗
        completePointsPolysPlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim st s0 ∗ stackAt s0.sp polyNextChunkStack := by
    unfold polyEncoderAt encoderStateAt; rw [hs_pts]; dsimp only []
    have htrue :
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)) = True :=
      propext ⟨fun _ => trivial, fun _ => ⟨hlen_pts, hbounds⟩⟩
    rw [htrue, pure_true, emp_sepConj]; sep_ac_rfl
  rw [hrestore]
  have hlen16 : pts.length = 16 := hlen_pts
  let i0 := firstSlowIdxAux (x.enc.idx.setWidth 16).toNat pts 16 0
  have hi0_le : i0 ≤ 16 := firstSlowIdxAux_le_16 (x.enc.idx.setWidth 16).toNat pts 16 0 (by omega)
  by_cases hi0 : i0 < 16
  · have hi0_len : i0 < pts.length := by omega
    have hslow : (pts[i0]'hi0_len).value.length ≤ (x.enc.idx.setWidth 16).toNat := by
      have h := firstSlowIdxAux_slow (x.enc.idx.setWidth 16).toNat pts 16 0 (by omega) hi0
      change (pts[i0]?.getD ⟨[]⟩).value.length ≤ (x.enc.idx.setWidth 16).toNat at h
      simpa [List.getElem?_eq_getElem hi0_len] using h
    have hfast : ∀ j (hj : j < pts.length), j < i0 →
        (x.enc.idx.setWidth 16).toNat < (pts[j]'hj).value.length := by
      intro j hj hjlt
      have h := firstSlowIdxAux_fast (x.enc.idx.setWidth 16).toNat pts 16 0 j (by omega) (by omega) hjlt
      simpa [List.getElem?_eq_getElem hj] using h
    exact nextChunk_points_slow_placed_sepWPp M A lim st ext hA h_p2p x pts hs_pts hlen_pts hbounds
      i0 hi0 hfast hslow hnext R s0 hcl0 hpc hrun hsp0 hx0 hx8 hfit
  · have hfsi_eq : nextChunkFirstSlowIdx (x.enc.idx.setWidth 16).toNat pts 16 0 = i0 :=
      nextChunkFirstSlowIdx_eq_firstSlowIdxAux (x.enc.idx.setWidth 16).toNat pts 16 0 (by omega)
    have hfast_all : ∀ k : Fin NUM_POLYS,
        (x.enc.idx.setWidth 16).toNat < (pts[k.val]'(by have := k.isLt; omega)).value.length := by
      intro k
      have hk_len : k.val < pts.length := by have := k.isLt; omega
      have hk_i0 : k.val < i0 := by have := k.isLt; change k.val < 16 at this; omega
      have h := firstSlowIdxAux_fast (x.enc.idx.setWidth 16).toNat pts 16 0 k.val (by omega) (by omega) hk_i0
      simpa [List.getElem?_eq_getElem hk_len] using h
    have hevs_fast : PolyNextChunkEnv x nextChunkPointsFastEvents := by
      unfold PolyNextChunkEnv; rw [hs_pts]; dsimp only
      simp only [hfsi_eq, hi0, ↓reduceIte]; exact nextChunkPointsFastEvents_eq
    have hfit_fast : FitsEnv M lim st NextChunkPointsFastEnv :=
      fun evs hevs => hfit evs ((hevs.trans nextChunkPointsFastEvents_eq.symm) ▸ hevs_fast)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (sepWPp_drop_frame_placed_gen
        (F := completePointsPolysPlacedAt)
        (PostRest := fun sf1 => (polyNextChunkPlacedSpec M A lim).post (x, st) s0 sf1)
        (PanicPost := PanicPost)
        (sepWPp_mono_post
          (nextChunk_points_fast_placed_sepWPp M A lim st ext hA x pts hs_pts hlen_pts hfast_all
            hnext (completePointsPolysPlacedAt ∗ R) s0 hpc hrun hsp0 hx0 hx8 hfit_fast)
          fun sf1 P_f ⟨hm1, hsp_sf1, hcs_sf1⟩ =>
            ⟨fun hm => pack_post_of_evs hevs_fast rfl (hm1 hm), hsp_sf1, hcs_sf1⟩))

/-! ## 6. Top-Level Budget-Threaded Relocatable Contracts (Block `416`) -/

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `RodataPlacedBudget.PolyNextChunkRodataPlacedOkExt M A lim ext` (`withLsCodeLoaded`)
    given `h_p2p`. -/
theorem poly_next_chunk_rodata_placed_ok_of_p2p [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext) :
    PolyNextChunkRodataPlacedOkExt M A lim ext := by
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [polyNextChunkRodataPlacedSpec, polyNextChunkRodataPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hnext, hfit⟩, hm⟩
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  refine ⟨_, hm, ?_⟩
  dsimp only [withLsCodeLoaded, polyNextChunkRodataPlacedSpec, polyNextChunkRodataPlacedSpecOfEnv]
  cases hs : x.enc.s with
  | polys polys =>
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (sepWPp_drop_frame_placed_gen
        (F := completePointsPolysPlacedAt)
        (PostRest := fun sf1 => (polyNextChunkPlacedSpec M A lim).post (x, st) s0 sf1)
        (PanicPost := fun _ => ⌜False⌝)
        (nextChunk_polys_polyEnv_placed_sepWPp M A lim st ext hA x polys hs hnext
          (completePointsPolysPlacedAt ∗ R) s0 hcl0 hpc hrun hsp0 hx0 hx8 hfit))
  | points pts =>
    exact nextChunk_points_placed_sepWPp M A lim st ext hA h_p2p x pts hs hnext
      R (PanicPost := fun _ => ⌜False⌝) s0 hcl0 hpc hrun hsp0 hx0 hx8 hfit

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `DefsBudget.PolyNextChunkRodataPlacedOkExt M A lim ext` (`withLsCodeRoLoaded`)
    given `h_p2p`. -/
theorem poly_next_chunk_rodata_ro_placed_ok_of_p2p [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext) :
    LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.PolyNextChunkRodataPlacedOkExt
      M A lim ext :=
  to_defsBudget_rodataPlacedOkExt_ofEnv
    (poly_next_chunk_rodata_placed_ok_of_p2p M A lim ext hA h_p2p)

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkPlacedOkExt M A lim ext` (`withLsCodeRoLoaded lsmpl
    (polyNextChunkPlacedSpec M A lim)`) given `h_p2p`. -/
theorem poly_next_chunk_placed_ok_of_p2p [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext) :
    PolyNextChunkPlacedOkExt M A lim ext :=
  polyNextChunkPlacedOkExt_of_rodata
    (poly_next_chunk_rodata_placed_ok_of_p2p M A lim ext hA h_p2p)

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkBlockOkX M A lim ext` (`blockProgram lsmpl 416`) given `h_p2p`. -/
theorem poly_next_chunk_block_ok_x_of_p2p [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext) :
    PolyNextChunkBlockOkX M A lim ext :=
  polyNextChunkBlockOkX_of_placedOkExt
    (poly_next_chunk_placed_ok_of_p2p M A lim ext hA h_p2p)

/-- Cross-block caller specialization of `poly_next_chunk_placed_ok_of_p2p` onto any
    `[IsLsBlockProg callerProg i (Rust.withPanics ext)]` (`i < 619`). -/
theorem poly_next_chunk_caller_ok_x_of_p2p [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hA : AllocContractsPlaced M A lim ext)
    (h_p2p : PointsToPolysLoopPlacedProp M A lim ext)
    (hi : i < 619 := by decide) :
    PolyNextChunkCallerOkX callerProg M A lim :=
  polyNextChunkCallerOkX_of_placedOkExt
    (poly_next_chunk_placed_ok_of_p2p M A lim ext hA h_p2p) hi

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.ProofPlacedBudget
