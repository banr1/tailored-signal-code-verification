/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Handshake `bytes::merge [local#5]`

Verifies `[LibsignalPlacement]` `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#5]`
(Block `514`, `888` B) against `bytesMerge3RawSpecBoth A lim` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`)
under `RustCliAllocBudget`, specializing to `bytesMerge3RawSpec`, `bytesMerge3ProtoRawSpec`,
`bytesMerge3RawSpecW`, and cross-block caller contracts on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  blkPC_261 blkPl_261 blkPC_293 blkPl_293
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_externAt?_of_mem ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (
  KindNoHeap LibsignalCodeRoLoaded bytesPlacedDropFnAddr decodeErrorAtStackLen extHookStack
  extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost
  SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
  SepWPp.unfold_cells_64 SepWPp.unfold_memRegion_216
  SepWPp.unfold_memRegion_216_invalidWireType
  bm_HighCalleeSaved bm_decodeVarint_suffix decodeErrorHookStackX decodeVarintSliceStackX
  fold_memRegion_40_bytes fold_slot_16 mask_ff_32_of_setWidth8
  mergeBytes_lengthDelimited_underflow mergeBytes_ne_lengthDelimited mergeBytes_of_decodeVarint_none
  savedRegsStack sliceCursorAfter sliceCursorAfter_to_err sliceCursorAt spAligned_sub_224
  subroutine_ok_withLsCl_of_plain subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts (
  truncate32_zeroExtend64_and_255_eq
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  bytesMerge3Stack stackAt_bytesMerge3_entry stackAt_bytesMerge3_eq stackAt_varint2_to_slice
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  decodeVarint2StackX
)
open CryptoVerification.CliHandshake.Placed (
  blkLib_eq_514 blkPl_514 blkPl_515 lsProg_514 lsProg_515
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack subroutine_ok_rustCliAllocBudget_withStack
)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget (
  bytesFromVecPlacedSpec bytesVtableDropSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget (bytesVtableDrop_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget (bytesFromVec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bytesMergeEventsCore
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget (bytesVtableDropSpecBMGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget (
  bytesVtableDropSpecBMGen_of_spec_x
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux (
  decodeVarintSlowGen_lscl_ok_of_session2 decode_varint_slow_placed_ok_with_stack
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget (decode_error_from_placed_ok_x)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget (
  bytesMerge3ProtoRawSpec bytesMerge3RawSpec subroutine_ok_bytesMerge3Proto_of_codec_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget (
  bytesMerge3RawSpecW
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget (
  decodeVarint5_placed_ok decodeVarint5_placed_ok_of_contracts_x dv5_decodeErrorFrom_placed_of_alloc
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget (
  doReserve1VecSpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10PlacedBudget (
  do_reserve_10_vec1_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23PlacedBudget (
  MergePanicXBoth MergePostXBoth bytesMergeRawSpecXBoth
  epilogue6_decodeErrorFrom_0x074_placed epilogue6_err_0x07c_placed phase2_6_from_0x094_placed
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlacedBudget (
  bytesMerge3PlacedSpec
  bytesMerge3ProtoPlacedSpec
  BytesMerge6PlacedOkExt
  BytesMerge6ProtoPlacedOkExt
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget (
  bytesMerge3RawSpecBoth
  MergePost3Both
  subroutine_ok_bytesMerge3W_of_both
  subroutine_ok_bytesMerge3_of_both
  bytes_merge_6_cro_of_514
  subroutine_ok_withLsCl_of_cro
  bytes_merge_6_w_cro_of_514
  bytes_merge_6_w_cl_of_514
  bytes_merge_6_w_cro_of_both
  bytes_merge_6_w_cl_of_both
  BytesMerge6Placed514OkExtW
  bytesMerge3PlacedSpecW
  BytesMerge6PlacedOkExtW
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack-Lifting Helpers (`MergePanic3Both` & `SepWPp.lift_merge3Both`) -/

abbrev MergePanic3Both {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpecBoth A lim).onPanic (x, st) s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3Both [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePost3Both A lim x st s0 R) (MergePanic3Both A lim x st s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim))
        (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3Both {M : AllocCostModel} {prog : Program}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXBoth A lim x st s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))
      (MergePanicXBoth A lim x st s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 33120#64) 48 ∗ P)
      (MergePost3Both A lim x st s0 R) (MergePanic3Both A lim x st s0 R) := by
  intro F hm hL
  have hm' : s.mem ⊨ P ∗ (memRegion (s0.sp - 33120#64) 48 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h (memRegion (s0.sp - 33120#64) 48 ∗ F) hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmr
    have hp := hpost hmr'
    dsimp only [bytesMergeRawSpecXBoth, bytesMerge3RawSpecBoth] at hp ⊢
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmr
    exact False.elim (not_satisfies_false_sepConj (hpanic hmr'))
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## 2. Phase 1 (`+0x000..+0x074`) and `bytes_merge_6_both_placed_ok_of_contracts` (Block `514`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `514`) meets `withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)` under
`[LibsignalPlacement]`. -/
theorem bytes_merge_6_both_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (_hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp_align hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpecBoth, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapInv, hfits⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hfits_dv : FitsEnv M lim st (DecodeVarint2Env x.bs) := by
    intro evs hevs
    subst hevs
    unfold decodeVarintSliceEvents
    cases hdv : decodeVarint x.bs with
    | none =>
      have hm_none : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hdv
      exact hfits (rustAllocEvents 72 8) (by simp [BytesMergeEnv, bytesMergeEventsCore, hm_none])
    | some _ => trivial
  have hVtableDropBM : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim extHookStack tmpPtr v v.length)) :=
    fun tmpPtr v => bytesVtableDropSpecBMGen_of_spec_x (hVtableDrop tmpPtr v)
  have herr_exit := fun {st_cur : M.σ} {s : State}
      (hmerge : mergeBytes x.wt x.bs = none)
      (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st) =>
    @epilogue6_err_0x07c_placed _ M A lim H x st st_cur s0 s
      (memRegion (s0.sp - 33120#64) 48 ∗ R) hmerge hevs
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue6_decodeErrorFrom_0x074_placed _ M A lim H hdef x st s0 s
      (memRegion (s0.sp - 33120#64) 48 ∗ R) w hw hmerge hfits
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_6_from_0x094_placed _ M A lim H hmc hshim halloc hBytesFromVec hReserve
      hVtableDropBM x st s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R)
      len rest0 hwt hvar hle hbs_len hcapInv hfits
  clear hBytesFromVec hReserve hVtableDrop hVtableDropBM
  refine Exists.elim (SepWPp.to_subroutineOutcome3Both hsp_align hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s0 ∗
      stackAt (s0.sp - 224#64) decodeVarint2StackX ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 515)
    apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
      (mid := lsmpl.base 515)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl
      (x := (({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost), st))
      (φ := x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env x.bs))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st _ ∗
        stackAt (s0.sp - 224#64) decodeVarint2StackX)
      hDecodeVarint5 hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2SpecX, arm64_norm, hx2, true_and]; rfl)
      ⟨hbs_len, hfits_dv⟩
      (by (conv => lhs; simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [withLsCl, decodeVarint2SpecX] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_dv hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [decodeVarint2SpecX]
    simp (config := { decide := true }) only [arm64_norm,
      sepExists_sepConj_left, sepExists_sepConj_right]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.exists_elim fun evs => ?_
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.trace = s0.trace ∧ DecodeVarint2Env x.bs evs⌝ ∗
          ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            decodeErrorAtStackLen A.repAlloc (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗
            A.pool lim (M.stepEvents evs st) sf_dv ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun ⟨htr, hevs_dv⟩ => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      have hevs_bm : BytesMergeEnv x evs := by
        simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hvar,
          BytesMergeEnv, bytesMergeEventsCore, hmerge] using hevs_dv
      apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_514).base + 124#64)
      apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
        (mid := (blkPl_514).base + 124#64)
      intro _m_strip1
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        fun _m_real1 _hnsp1 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp1.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro _hcl2 _hro2
      let s_err := (((((sf_dv.writeReg64 (Reg.gpr 8#5) 1#64).writeReg64 (Reg.gpr 0#5)
        (sf_dv.readReg64 (Reg.gpr 1#5))).setPC ((blkPl_514).base + 124#64)).setMem
        _m_strip1).setMem _m_real1)
      refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both
        (herr_exit (s := s_err) hmerge ⟨evs, hevs_bm, rfl⟩
          (by simp (config := { decide := true }) only [s_err, wp_norm, arm64_norm, hpcf, hx0_sf])
          (by simp (config := { decide := true }) only [s_err, wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [s_err, wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [s_err, wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [s_err, wp_norm, arm64_norm]; exact hx1_sf)
          (by simp (config := { decide := true }) only [s_err, bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])))
      exact Entails.of_eq (by
        simp (config := { decide := true }) only [s_err, State.setMem_setMem, wp_norm, arm64_norm]
        sep_ac_rfl)
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗
          ⌜sf_dv.trace = s0.trace ∧ DecodeVarint2Env x.bs evs⌝ ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
            A.pool lim (M.stepEvents evs st) sf_dv ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      refine SepWPp.pure_elim fun ⟨htr, hevs_dv⟩ => ?_
      have hevs_nil : evs = [] := by
        simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hvar] using hevs_dv
      subst hevs_nil
      simp only [AllocCostModel.stepEvents_nil]
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf hrof
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_514).base + 148#64 else (blkPl_514).base + 80#64)
      apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_514).base + 148#64 else (blkPl_514).base + 80#64)
      intro _m_strip2
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        fun _m_real2 _hnsp2 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
      · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hcl2 hro2 ⊢
        have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
        have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
        refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
            A.pool lim st _ ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        refine SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_514).base + 116#64)
        apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
          (mid := (blkPl_514).base + 116#64)
        intro _m_strip3
        wp_steps
        refine SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          fun _m_real3 _hnsp3 => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp3.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
          (hnext := ?_)
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl3 hro3))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; sep_ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hcl2 hro2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])))
        exact Entails.of_eq (by sep_ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 33120#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_514).base + 116#64)
    apply sepWP_seg_ls_vm (Q := lsProg_514 (hooksException H)) blkLib_eq_514
      (mid := (blkPl_514).base + 116#64)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
      (hnext := ?_)
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; sep_ac_rfl)

/-! ## 3. Specializations (`CapOk`, `Proto`, `W`) & Leaf Closure from `HookSat` / `AllocContractsPlaced` -/

theorem bytes_merge_6_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) :=
  subroutine_ok_bytesMerge3_of_both
    (bytes_merge_6_both_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint5
      hBytesFromVec hReserve hVtableDrop)

theorem bytes_merge_6_proto_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) :=
  subroutine_ok_bytesMerge3Proto_of_codec_cro
    (bytes_merge_6_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint5
      hBytesFromVec hReserve hVtableDrop)

theorem bytes_merge_6_placed_ok_of_contractsW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)) :=
  subroutine_ok_bytesMerge3W_of_both
    (bytes_merge_6_both_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint5
      hBytesFromVec hReserve hVtableDrop)

private theorem bm6_sessionShim_of_noAllocShim {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym noAllocShimBudgetSpec) :
    HookSat H sym sessionShimBudgetSpec := by
  obtain ⟨f, hf, hsat⟩ := h
  refine ⟨f, hf, ?_⟩
  intro x R s0 hrun hpre hal
  dsimp only [sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hpre
  have hpre' : s0.mem ⊨ noAllocShimBudgetSpec.pre () s0 ∗ R := by
    dsimp only [noAllocShimBudgetSpec]
    exact hpre
  obtain ⟨hret, hcc, hout⟩ := hsat () R s0 hrun hpre' hal
  refine ⟨hret, hcc, ?_⟩
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    dsimp only [noAllocShimBudgetSpec] at hpost
    dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1.1, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp1, hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, ho2⟩))

theorem bm6_decodeErrorFrom_placed_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (decode_error_from_placed_ok_x (bm6_sessionShim_of_noAllocShim hshim) halloc)

theorem bm6_decodeVarint5_placed_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)) := by
  have hFrom := bm6_decodeErrorFrom_placed_of_hooks hshim halloc
  exact decodeVarint5_placed_ok_of_contracts_x hFrom
    (decodeVarintSlowGen_lscl_ok_of_session2
      (decode_varint_slow_placed_ok_with_stack
        (errStack := decodeErrorHookStackX) (by decide)
        (ls_subroutine_ok_cl_of_block
          (callerProg := (blkPC_293).rebase (blkPl_293).base H) hFrom)))

theorem bm6_vtableDrop_placed_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (tmpPtr : BitVec 64) (v : List (BitVec 8)) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecX M A lim tmpPtr v v.length)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded
    (bytesVtableDrop_placed_ok_x hdealloc hi tmpPtr v v.length)

theorem bytes_merge_6_both_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)) :=
  bytes_merge_6_both_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeErrorFrom_placed_of_hooks hshim halloc))
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hmc)
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hshim)
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_rustCliAllocBudget_withStack (by decide) (by decide)
        (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) halloc)))
    ((ls_externAt?_of_mem (prog := lsProg_514 H) (i := 514) (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeVarint5_placed_of_hooks hshim halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_514 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (do_reserve_10_vec1_placed_ok hpanic_raw hshim halloc hrealloc))
    (bm6_vtableDrop_placed_of_dealloc (callerProg := lsProg_514 H) hdealloc)

theorem bytes_merge_6_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) :=
  subroutine_ok_bytesMerge3_of_both
    (bytes_merge_6_both_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem bytes_merge_6_proto_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) :=
  subroutine_ok_bytesMerge3Proto_of_codec_cro
    (bytes_merge_6_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem bytes_merge_6_placed_ok_w [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)) :=
  subroutine_ok_bytesMerge3W_of_both
    (bytes_merge_6_both_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem bytes_merge_6_placed_ok_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) :=
  bytes_merge_6_cro_of_514
    (bytes_merge_6_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw) hi

theorem bytes_merge_6_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (bytesMerge3PlacedSpec A lim) :=
  subroutine_ok_withLsCl_of_cro
    (bytes_merge_6_placed_ok_cro hshim halloc hrealloc hdealloc hmc hpanic_raw hi)
    hro

theorem bytes_merge_6_proto_placed_ok_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) :=
  bytes_merge_6_cro_of_514
    (bytes_merge_6_proto_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw) hi

theorem bytes_merge_6_placed_ok_w_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)) :=
  bytes_merge_6_w_cro_of_both
    (bytes_merge_6_both_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw) hi

theorem bytes_merge_6_placed_ok_w_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (bytesMerge3PlacedSpecW A lim) :=
  bytes_merge_6_w_cl_of_both hro
    (bytes_merge_6_both_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw) hi

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for `bytes::merge [local#5]`
(Block `514`) on `lsProg_518 ext`. -/
def BytesMerge6Placed514OkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim))

/-- Relocatable `[LibsignalPlacement]` budget-threaded `Proto.mergeBytes` contract for
`bytes::merge [local#5]` (Block `514`) on `lsProg_518 ext`. -/
def BytesMerge6ProtoPlaced514OkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim))

abbrev bytesMerge6_placed_ok := @bytes_merge_6_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget
