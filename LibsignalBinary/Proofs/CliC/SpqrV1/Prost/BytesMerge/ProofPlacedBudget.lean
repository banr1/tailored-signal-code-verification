/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23PlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2PlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
import LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Proof of `CliC` `prost::encoding::bytes::merge`

Threads `RustCliAllocBudget M` across `CliC`
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]` (Block `558`), establishing
`bytesMerge3RawSpec` and `Proto.mergeBytes` contracts under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ProofPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl withLsCl
   ls_subroutine_ok_cl_of_plain ls_subroutine_ok_cl_of_block ls_hook_ok_of_mem
   lsMemcpySym lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym
   lsRustDeallocSym lsHandleErrorSym)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap bytesPlacedDropFnAddr decodeErrorAtStackLen decodeErrorHookStack
   withLsCodeRoLoaded extract_withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost DecodeVarintSlowGhost
   decodeVarintSliceStack
   SepWPp.bm_call_frame_lscl SepWPp.bm_of_sepWP_lscl
   SepWPp.unfold_cells_64 SepWPp.unfold_memRegion_216
   SepWPp.unfold_memRegion_216_invalidWireType
   bm_HighCalleeSaved bm_decodeVarint_suffix
   fold_memRegion_40_bytes fold_slot_16 mask_ff_32_of_setWidth8
   mergeBytes_lengthDelimited_underflow mergeBytes_ne_lengthDelimited
   mergeBytes_of_decodeVarint_none
   savedRegsStack sliceCursorAfter sliceCursorAfter_to_err sliceCursorAt
   spAligned_sub_224 subroutine_ok_withLsCl_of_plain
   subroutine_ok_withLsCl_of_withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.RecordCodecs.Placed
  (blkLib_eq_558 blkPC_558 blkPl_558 lsProg_558)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (BytesMergeProtoGhost
   protoWireTypeToCodec_toNat proto_mergeBytes_toOption
   stackAt_bytesMerge3_entry stackAt_varint2_to_slice)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget
  (do_reserve_7_placed_ok)
open LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23PlacedBudget
  (epilogue3_decodeErrorFrom_0x074_placed epilogue3_err_0x07c_placed phase2_from_0x094_placed)
open LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2PlacedBudget
  (decodeVarint2_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (SepWPp.lift_merge3 SepWPp.to_subroutineOutcome3_placed
   bytesMerge3ProtoRawSpec bytesMerge3ProtoRawSpecOfEnv2
   bytesMerge3RawSpec bytesMerge3RawSpecOfEnv bytesMerge3RawSpecOfEnv2
   subroutine_ok_bytesMerge3OfEnv2_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveSpec framelessMemcpyBudgetSpec noAllocShimBudgetSpec
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
   subroutine_ok_noAllocShim_of_sessionShimBudget)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
  (bytesFromVecPlacedSpec bytesVtableDropSpec)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget (bytesVtableDrop_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget (bytesFromVec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem fitsEnv_decodeVarint2_of_bytesMerge {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : BytesMergeGhost}
    (hfits : FitsEnv M lim st (BytesMergeEnv x)) :
    FitsEnv M lim st (DecodeVarint2Env x.bs) := by
  intro evs hevs
  rcases hdv : decodeVarint x.bs with _ | ⟨len, rest0⟩
  · have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hdv
    apply hfits
    simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents,
      BytesMergeEnv, bytesMergeEventsCore, hdv, hmerge] using hevs
  · have hnil : evs = [] := by
      simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] using hevs
    subst hnil
    trivial

private theorem subroutine_ok_withVmPreserved_of_noAllocShimBudget {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr noAllocShimBudgetSpec) :
    subroutine_ok P addr
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec,
    noAllocShimBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1, hq.2⟩

private theorem subroutine_ok_withVmPreserved_of_framelessMemcpyBudget
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr framelessMemcpyBudgetSpec) :
    subroutine_ok P addr
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun x _ _ _ hq => ?_)
  rcases x with ⟨dst, src, bs⟩
  dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
    framelessMemcpyBudgetSpec] at hq ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hq.1.2.2, ⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

private theorem hookSat_noAllocShim_of_sessionShimBudget
    {H : String → Option (State → State)} {name : String}
    (h : HookSat H name sessionShimBudgetSpec) :
    HookSat H name noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

theorem bytes_merge_3_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_558 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)))
    (hshim : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)))
    (halloc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false)))
    (hDecodeVarint2 : subroutine_ok (lsProg_558 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve7 : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_558 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp_align hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv, bytesMerge3RawSpecOfEnv2,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk, hfits⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  let R48 : SepProp := memRegion (s0.sp - 8544#64) 48 ∗ R
  have herr_exit := fun {st_cur : M.σ} {s : State} (hmerge : mergeBytes x.wt x.bs = none)
      (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st) =>
    @epilogue3_err_0x07c_placed _ M A lim H x st st_cur s0 s R48 hmerge hevs
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue3_decodeErrorFrom_0x074_placed _ M A lim H hdef x st s0 s R48 w hw hmerge hfits
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = WireType.lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_from_0x094_placed _ M A lim H hmc hshim halloc hBytesFromVec hReserve7
      hVtableDrop x st s0 s R48 len rest0 hwt hvar hle hfits hbs_len hcapOk
  clear hBytesFromVec hReserve7 hVtableDrop
  refine Exists.elim (SepWPp.to_subroutineOutcome3_placed hsp_align hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st s0 ∗
      stackAt (s0.sp - 224#64) decodeVarint2Stack ∗
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
    have hfits_dv : FitsEnv M lim st (DecodeVarint2Env x.bs) :=
      fitsEnv_decodeVarint2_of_bytesMerge hfits
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 559)
    apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
      (mid := lsmpl.base 559)
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
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool lim st _ ∗
        stackAt (s0.sp - 224#64) decodeVarint2Stack)
      hDecodeVarint2 hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by
        simp (config := { decide := true }) only [decodeVarint2Spec, decodeVarint2SpecGen,
          arm64_norm, hx2]
        rfl)
      (by exact ⟨hbs_len, hfits_dv⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen] at hm
          rw [sepConj_assoc] at hm
          exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_dv hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
    simp (config := { decide := true }) only [
      show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
      arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.exists_elim fun evs => ?_
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.trace = s0.trace ∧ DecodeVarint2Env x.bs evs⌝ ∗
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            decodeErrorAtStackLen A.repAlloc (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗
            A.pool lim (M.stepEvents evs st) sf_dv ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨htr, hevs_dv⟩ => ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      have hevs_bm : BytesMergeEnv x evs := by
        simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents,
          BytesMergeEnv, bytesMergeEventsCore, hvar, hmerge] using hevs_dv
      apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_558).base + 124#64)
      apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
        (mid := (blkPl_558).base + 124#64)
      intro _m_strip2
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        fun _m_real2 _hnsp2 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        (hnext := ?_)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (herr_exit hmerge ⟨evs, hevs_bm, rfl⟩
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; simpa [Reg.x1] using hx1_sf)
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25f, h26f, h27f, h28f, hvregsf, and_self])))
      exact Entails.of_eq (by
        dsimp only [Reg.x0, Reg.x1]
        simp (config := { decide := true }) only [wp_norm, arm64_norm]
        sep_ac_rfl)
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.exists_elim fun evs => ?_
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.trace = s0.trace ∧ DecodeVarint2Env x.bs evs⌝ ∗
        ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
            A.pool lim (M.stepEvents evs st) sf_dv ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          sep_ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨htr, hevs_dv⟩ => ?_
      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      have hevs_nil : evs = [] := by
        simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hvar] using hevs_dv
      subst hevs_nil
      dsimp only [AllocCostModel.stepEvents, List.foldl, sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf hrof
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_558).base + 148#64 else (blkPl_558).base + 80#64)
      apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_558).base + 148#64 else (blkPl_558).base + 80#64)
      intro _m_strip3
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        fun _m_real3 _hnsp3 => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp3.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
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
          (memRegion (s0.sp - 8544#64) 48 ∗
            vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool lim st _ ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        refine SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_558).base + 116#64)
        apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
          (mid := (blkPl_558).base + 116#64)
        intro _m_strip4
        wp_steps
        refine SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          fun _m_real4 _hnsp4 => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp4.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
          (hnext := ?_)
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
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
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (h094_exit len rest0 hwt hvar hle
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
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
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
      (memRegion (s0.sp - 8544#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_558).base + 116#64)
    apply sepWP_seg_ls_vm (Q := (blkPC_558).rebase (blkPl_558).base (hooksException H)) blkLib_eq_558
      (mid := (blkPl_558).base + 116#64)
    intro _m_strip5
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      fun _m_real5 _hnsp5 => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp5.toVmPreserved (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
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
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3 (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; sep_ac_rfl)

theorem bytes_merge_3_placed_ok_of_contracts_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {PreEnv PostEnv : BytesMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, BytesMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, BytesMergeEnv x evs → PostEnv x evs)
    (hdef : subroutine_ok (lsProg_558 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)))
    (hshim : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)))
    (halloc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false)))
    (hDecodeVarint2 : subroutine_ok (lsProg_558 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve7 : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_558 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecOfEnv2 A lim PreEnv PostEnv)) :=
  subroutine_ok_bytesMerge3OfEnv2_of_spec hPre hPost
    (bytes_merge_3_placed_ok_of_contracts hdef hmc hshim halloc hDecodeVarint2
      hBytesFromVec hReserve7 hVtableDrop)

theorem bytes_merge_3_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) :=
  bytes_merge_3_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_558 H)
      (decode_error_from_placed_ok hshim halloc))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_withVmPreserved_of_framelessMemcpyBudget
        (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
          (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) hmc))))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_withVmPreserved_of_noAllocShimBudget
        (subroutine_ok_noAllocShim_of_sessionShimBudget
          (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) hshim))))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_allocNoOom_of_budget
        (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) halloc)))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_558 H)
      (decodeVarint2_placed_ok hshim halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_558 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_558 H)
      (do_reserve_7_placed_ok hpanic_raw (hookSat_noAllocShim_of_sessionShimBudget hshim)
        halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok (callerProg := lsProg_558 H) (i := 558) hdealloc
          (by decide) tmpPtr v v.length))

theorem bytes_merge_3_placed_ok_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {PreEnv PostEnv : BytesMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, BytesMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, BytesMergeEnv x evs → PostEnv x evs)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecOfEnv2 A lim PreEnv PostEnv)) :=
  subroutine_ok_bytesMerge3OfEnv2_of_spec hPre hPost
    (bytes_merge_3_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem bytes_merge_3_proto_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_558 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hmc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsMemcpySym)
      (withLsCl lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)))
    (hshim : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)))
    (halloc : subroutine_ok (lsProg_558 H) ((blkPl_558).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false)))
    (hDecodeVarint2 : subroutine_ok (lsProg_558 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A lim)))
    (hBytesFromVec : subroutine_ok (lsProg_558 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A.repAlloc)))
    (hReserve7 : subroutine_ok (lsProg_558 H) (lsmpl.base 561)
      (withLsCl lsmpl (doReserveSpec M A lim)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_558 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec M A lim tmpPtr v v.length))) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) := by
  have hok := bytes_merge_3_placed_ok_of_contracts hdef hmc hshim halloc hDecodeVarint2
    hBytesFromVec hReserve7 hVtableDrop
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)).pre
      (x.toCodec, st) s0 ∗ R := by
    simpa only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3ProtoRawSpecOfEnv2,
      bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv, bytesMerge3RawSpecOfEnv2,
      BytesMergeProtoGhost.toCodec, protoWireTypeToCodec_toNat] using hpre
  refine subroutine_ok.mono_outcome hok (x.toCodec, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3ProtoRawSpecOfEnv2,
      bytesMerge3RawSpec, bytesMerge3RawSpecOfEnv, bytesMerge3RawSpecOfEnv2,
      BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

theorem bytes_merge_3_proto_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_558 H) (blkPl_558).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) :=
  bytes_merge_3_proto_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_558 H)
      (decode_error_from_placed_ok hshim halloc))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_withVmPreserved_of_framelessMemcpyBudget
        (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
          (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) hmc))))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_withVmPreserved_of_noAllocShimBudget
        (subroutine_ok_noAllocShim_of_sessionShimBudget
          (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) hshim))))
    (subroutine_ok_withLsCl_of_plain
      (subroutine_ok_allocNoOom_of_budget
        (ls_hook_ok_of_mem (prog := lsProg_558 H) (i := 558) halloc)))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_558 H)
      (decodeVarint2_placed_ok hshim halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_558 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_558 H)
      (do_reserve_7_placed_ok hpanic_raw (hookSat_noAllocShim_of_sessionShimBudget hshim)
        halloc hrealloc))
    (fun tmpPtr v =>
      subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok (callerProg := lsProg_558 H) (i := 558) hdealloc
          (by decide) tmpPtr v v.length))

end LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ProofPlacedBudget
