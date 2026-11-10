/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Cross-Block `ClPlacedX` Bridges & Zero-Capacity Step Helpers for `EpochDirectionPB::merge` (`Block 299`)

Proves `DecodeStateCalleeContractsPlacedX` weakening, cross-block `withLsCodeRoLoaded` transfer,
`bytesMerge3RawBudgetSpec` weakening, and canonical zero-capacity per-field step lemmas for
Block `299` (`EpochDirectionPB::merge`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesStepsR

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LsBlockBound
   libsignalMutatedBlocks libsignalSessionLib ls_externAt?_blockProgram_eq_of_externs_eq
   ls_subroutine_ok_cl_of_plain ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost HighCalleeSaved IsDropSuffix bv32_zeroExtend_ofNat
   bytesMergeCapOk_zero decodeVarint_suffix key_shr32_of_lt key_wt_some sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3 skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (WppPost blkPC_299 blkPl_299 cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   mergeBytes_length setWidth8_ofNat64_wt skipBelow3_bytesMerge3 skipBelow3_bytesMerge3_entails
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm)
open CryptoVerification.SpqrV1.Top.DecodeState
  (EpochDirectionMergeGhost V1InnerHeapPred epochDirectionMergeStack epochDirectionPBCapOkAt
   vecU8CapOkAt vecU8CapOkAt_mono)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_epochDirectionMergeTightSpecOfEnv tlb_epochDirectionZeroCapAt tlb_vecU8ZeroCapAt)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env WppBudgetPanic wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
  (e2ar_bytesMerge3_zero_tight32 e2ar_bytesMerge3_zero_tight79236 e2ar_decodeVarint2Env_some_nil)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)

private theorem e2ar_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2ar_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2ar_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2ar_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2ar_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2ar_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2ar_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2ar_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2ar_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm]
private theorem e2ar_bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem e2ar_bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local irreducible] Program.fetch Program.externAt?
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← Lean.getEnv
  for pfx in [`CryptoVerification.SpqrV1.Kdf,
      `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof] do
    for sfx in ["sp_sub_688_eq_hsp", "sp_add_neg688_eq_hsp",
        "sp_sub_96_eq_hsp_592", "sp_add_neg96_eq_hsp_592",
        "hsp_592_sub_592_eq_hsp", "hsp_592_add_neg592_eq_hsp",
        "hsp_add_688_sub_688", "hsp_592_add_96_eq_sp"] do
      let nm := Lean.Name.str pfx sfx
      if env.contains nm then
        try Lean.Attribute.erase nm `arm64_norm catch _ => pure ()
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2ar_sp_setMem_pre e2ar_pc_setMem_pre e2ar_status_setMem_pre e2ar_pstate_setMem_pre
  e2ar_trace_setMem_pre e2ar_readReg64_setMem_pre e2ar_readReg32_setMem_pre
  e2ar_readReg_setMem_pre e2ar_calleeSavedVRegs_setMem_pre

private theorem e2ar_vecU8At_entails_vecU8CapOkAt {A : RustAlloc} {v cap ptr : BitVec 64}
    {remLen : Nat} {bs : List (BitVec 8)} (h : BytesMergeCapOk cap remLen) :
    vecU8At A v cap ptr bs ⊢ vecU8CapOkAt A v remLen bs :=
  Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.pure_right h (Entails.refl _)))

/-! ## 1. `PlacedX` → `ClPlacedX` Weakening & Cross-Block `withLsCodeRoLoaded` Transfer -/

/-- Weaken `DecodeStateCalleeContractsPlacedX` to `DecodeStateCalleeContractsClPlacedX`. -/
theorem e2ar_contractsClPlacedX_of_placedX [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext) :
    DecodeStateCalleeContractsClPlacedX H_inner A lim ext where
  of_drop_inner := hc.of_drop_inner
  of_cap_inner := hc.of_cap_inner
  dealloc := hc.dealloc
  memcpy := hc.memcpy
  session_memcpy := hc.session_memcpy
  decodeErrorFrom := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeErrorFrom
  decodeErrorPush := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeErrorPush
  decodeVarint2 := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeVarint2
  skipField3 := subroutine_ok_withLsCodeLoaded_of_plain hc.skipField3
  chainParamsMerge := subroutine_ok_withLsCodeLoaded_of_plain hc.chainParamsMerge
  growOneChainEpoch := subroutine_ok_withLsCodeLoaded_of_plain hc.growOneChainEpoch
  dropOptProtoInnerState := ls_subroutine_ok_cl_of_plain hc.dropOptProtoInnerState
  dropProtoPqRatchetState := ls_subroutine_ok_cl_of_plain hc.dropProtoPqRatchetState
  bytesMerge3 := hc.bytesMerge3
  epochDirectionMerge := hc.epochDirectionMerge
  v1StateMerge := hc.v1StateMerge

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec)` from unmutated
block `j` to block `i`'s program `callerProg`. -/
theorem e2ar_ls_subroutine_ok_cro_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [hbj : LsBlockBound bj]
    (_hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcro0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcro0.1 j (Nat.lt_of_lt_of_le hj hbj.le_blocks) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ)
    (reaches_outcome.of_outcome hout)

/-- Weaken `SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim` to
`PolyCommonBudget.bytesMerge3RawBudgetSpec A lim` under `withLsCodeRoLoaded`. -/
theorem e2ar_polyBytesMerge_of_signed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun ⟨g, st⟩ R s0 sf hq => ?_)
  dsimp only [withLsCodeRoLoaded,
    LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec,
    LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec] at hq ⊢
  cases hmb : mergeBytes g.wt g.bs with
  | none =>
    simp only [hmb] at hq ⊢
    exact hq
  | some p =>
    rcases p with ⟨v, rest⟩
    simp only [hmb] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (Entails.sepExists_mono fun cap' => Entails.sepExists_mono fun ptr' =>
          Entails.pure_left fun hc => Entails.pure_right hc.1 (Entails.refl _))))))))) hq

/-! ## 2. Canonical Zero-Cap Step Helpers for Block `299` (`EpochDirection::merge`) -/

def e2ar_edLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (_msgPtr bufRef slot ptr : BitVec 64)
    (Hmsg : SepProp) (bs cur : List (BitVec 8)) : SepProp :=
  Hmsg ∗
    memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

theorem e2ar_ed_key_some_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R Hmsg : SepProp}
    {s0 s : State} {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : key.toNat < 2 ^ 32)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag_pos : 1 ≤ key.toNat / 8)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_299).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_edLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr Hmsg x.bs rest)
        (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (e2ar_edLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr Hmsg x.bs cur)
      (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env cur) := fun evs he => by
    rw [e2ar_decodeVarint2Env_some_nil hd he]; trivial
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [e2ar_edLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
    (ret_pc := (blkPl_299).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, hfits_dv⟩
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hk_ge : ¬ 2 ^ 32 ≤ key.toNat := by omega
  have hitag0 : ¬ key.toNat / 8 < 1 := by omega
  have hshr := key_shr32_of_lt hk_ge
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 212#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2ar_decodeVarint2Env_some_nil hd hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
  wp_steps_sync_pool ((blkPl_299).base + 212#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [e2ar_edLoopPre]; sep_entail)
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm1, hand_wt])
      (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_ed_tag1_some_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest rest' : List (BitVec 8)} {v : BitVec 64} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hdv : decodeVarint rest = some (v, rest'))
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_edLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr { m with ctr := v.truncate 32 })
          x.bs rest')
        (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 212#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (e2ar_edLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr
        (tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr m) x.bs rest)
      (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env rest) := fun evs he => by
    rw [e2ar_decodeVarint2Env_some_nil hdv he]; trivial
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 284#64) hinv
  (conv => arg 4; dsimp only [e2ar_edLoopPre])
  wp_steps_sync_pool ((blkPl_299).base + 284#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 296#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hrest_lt, hfits_dv⟩
    (by dsimp only [sliceCursorAt, restPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, tlb_epochDirectionZeroCapAt,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2ar_decodeVarint2Env_some_nil hdv hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_299).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [e2ar_edLoopPre, tlb_epochDirectionZeroCapAt]; sep_entail)
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_ed_tag2_zero_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest v rest' : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 32)
    (hFit_t2 : FitsEnv M lim st_cur (SpqrTightEvs 2 1476 32))
    (hcont : ∀ (evs_bm : List AllocEvent) (s' : State),
      SpqrTightEvs 2 1476 32 evs_bm →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_edLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (vecU8CapOkAt A.repAlloc x.msgPtr rest'.length v ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) m.prev ∗
            ((x.msgPtr + 0x30#64) ↦₃₂ m.ctr) ∗
            memRegion (x.msgPtr + 0x34#64) 4)
          x.bs rest')
        (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 212#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (e2ar_edLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr
        (tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr m) x.bs rest)
      (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 260#64) hinv
  (conv => arg 4; dsimp only [e2ar_edLoopPre])
  wp_steps_sync_pool ((blkPl_299).base + 260#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [tlb_epochDirectionZeroCapAt,
    show tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr m.next =
      (∃∗ v_ptr : BitVec 64, vecU8At A.repAlloc x.msgPtr 0#64 v_ptr m.next) from rfl,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_ptr
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  have hfits_bm : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, x.msgPtr, 0#64, v_ptr, m.next, x.bufRef, x.slot, restPtr, rest⟩) :=
    fun evs he => hFit_t2 evs (e2ar_bytesMerge3_zero_tight32 hmb hv_le he)
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro
    (spec := LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)
    (x := (⟨.lengthDelimited, x.msgPtr, 0#64, v_ptr, m.next, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 272#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, bytesMergeCapOk_zero, hfits_bm⟩
    (by dsimp only [sliceCursorAt, restPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
  (conv => arg 4; simp only [
    LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec, hmb,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_bm
  apply SepWP.exists_elim; intro cap'
  apply SepWP.exists_elim; intro ptr'
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_bm
  wp_focus_pure; intro hsm0
  wp_focus_pure; intro hcap'
  have ht2 : SpqrTightEvs 2 1476 32 evs_bm := e2ar_bytesMerge3_zero_tight32 hmb hv_le hevs_bm
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  apply SepWP.fold (e2ar_vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus)
  wp_steps_sync_pool ((blkPl_299).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [e2ar_edLoopPre]; sep_entail)
    (hcont evs_bm _ ht2
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_ed_tag3_zero_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest v rest' : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 79236)
    (hFit_t3 : FitsEnv M lim st_cur (SpqrTightEvs 2 180468 79236))
    (hcont : ∀ (evs_bm : List AllocEvent) (s' : State),
      SpqrTightEvs 2 180468 79236 evs_bm →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_edLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (epochDirectionPBCapOkAt A.repAlloc x.msgPtr rest'.length { m with prev := v })
          x.bs rest')
        (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 212#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 3#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (e2ar_edLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr
        (vecU8CapOkAt A.repAlloc x.msgPtr rest.length m.next ∗
          tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) m.prev ∗
          ((x.msgPtr + 0x30#64) ↦₃₂ m.ctr) ∗
          memRegion (x.msgPtr + 0x34#64) 4) x.bs rest)
      (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 236#64) hinv
  (conv => arg 4; dsimp only [e2ar_edLoopPre])
  wp_steps_sync_pool ((blkPl_299).base + 236#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [
    show tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) m.prev =
      (∃∗ v_ptr : BitVec 64, vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 v_ptr m.prev) from rfl,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_ptr
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  have hfits_bm : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, x.msgPtr + 0x18#64, 0#64, v_ptr, m.prev, x.bufRef, x.slot, restPtr, rest⟩) :=
    fun evs he => hFit_t3 evs (e2ar_bytesMerge3_zero_tight79236 hmb hv_le he)
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro
    (spec := LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)
    (x := (⟨.lengthDelimited, x.msgPtr + 0x18#64, 0#64, v_ptr, m.prev, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 248#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, bytesMergeCapOk_zero, hfits_bm⟩
    (by dsimp only [sliceCursorAt, restPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
  (conv => arg 4; simp only [
    LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec, hmb,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_bm
  apply SepWP.exists_elim; intro cap'
  apply SepWP.exists_elim; intro ptr'
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_bm
  wp_focus_pure; intro hsm0
  wp_focus_pure; intro hcap'
  have ht3 : SpqrTightEvs 2 180468 79236 evs_bm := e2ar_bytesMerge3_zero_tight79236 hmb hv_le hevs_bm
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  apply SepWP.fold (e2ar_vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus)
  apply SepWP.fold (@vecU8CapOkAt_mono A.repAlloc x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_299).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [e2ar_edLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    (hcont evs_bm _ ht3
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_ed_ret_exit [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    {evs : List AllocEvent}
    (heq_lim : cur.length = limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hsome : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur))
    (hevs : PostEnv x evs) (hst_eq : st_cur = M.stepEvents evs st0)
    (hpc : s.pc = (blkPl_299).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (e2ar_edLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr
        (epochDirectionPBCapOkAt A.repAlloc x.msgPtr cur.length m) x.bs cur)
      (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply SepWPp.of_sepWP_ret
  unfold WppPost tlb_epochDirectionMergeTightSpecOfEnv epochDirectionMergeSpecOfEnv
  simp only [hsome, epochDirectionMergeStack, stackAt_skipField3 _ 98 (by decide), e2ar_edLoopPre,
    sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hst_eq, arm64_norm, htr, hsp]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesStepsR
