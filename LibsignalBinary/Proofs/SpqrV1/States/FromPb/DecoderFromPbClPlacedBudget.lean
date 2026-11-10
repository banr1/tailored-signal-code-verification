/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProofBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecoderFromPbClPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Closed `[LibsignalPlacement]` Contract for `<PolyDecoder>::from_pb`

Discharges the cross-block callee `core::ptr::drop_glue::<[spqr::encoding::polynomial::SortedSet<Pt>; 16]>`
(Block `264`) for `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (Block `376`) under
`withLsCodeLoaded lsmpl` and `RustCliAllocBudget M`, and lifts the resulting contract to
`lsProg_376`, `blockProgram 376`, caller blocks `idx < 619`, and `lsProg_333`
(`DefsBudget.DecoderFromPbPlacedOkExt`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecoderFromPbClPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_376 blkPl_376 extract_withLsCodeLoaded libsignalSessionLib
  lsProg_333 lsProg_376 ls_blockPlacement_base ls_subroutine_ok_of_block
  lscall_blk_cl lsmpl lsρ sepWP_mono_lscl sepWP_seq_lscl withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (
  CHUNK_SIZE NUM_POLYS PolyDecoder PolynomialError ProtoPolynomialDecoder SortedSetPt
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (memRegion_rejoin_vecBuf)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrMemmoveSym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (
  DropGlueSortedSetPt16Ghost dropGluePoly16Stack sortedSetPtListOf_eq_vecPtListOf vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyArrayBytes polyDecoderSize polynomialErrorByte
  protoPolynomialDecoderAt protoPolynomialDecoderSize
  resultPolyDecoderErrByteOff resultPolyDecoderErrTailSize
  resultPolyDecoderFromPbAt sortedSetPtListOf
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  FromPbDecGhost HiddenEq align_pre_wp cap_add_lsl1_lsl3_toNat cap_add_lsl1_ubfm_toNat
  cur_add8_add24 cur_add8_sub8 fromPbCoreStack
  fromPbDecResult fromPbDecResult_eq_decoderFromPbResult
  fromPbDecResult_eq_err_of_exists_mod4 fromPbDecResult_eq_err_of_len_ne_16
  fromPbDecResult_eq_ok_of_all_mod4 fromPb_stackAt_dropGluePoly16_split_bottom
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32 fsp_448_add_40 fsp_448_add_48
  fsp_448_add_56 fsp_448_add_64 fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8 fsp_488_add_8 fsp_496_add_8
  fsp_504_add_8 fsp_512_add_8 fsp_520_add_8 fsp_528_add_8
  fsp_rejoin_448 memRegion_400_split_err memRegion_448_split
  pbA_rejoin_40 pbA_tail_entails_memRegion_16 protoPolynomialDecoderAt_expose
  pushChunks4Total replace_sub_entails savedRegsAt spqrRustDeallocSym vecVecU8BufDealloc
)
open CryptoVerification.SpqrV1.States.FromPb (decoderFromPbStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget (
  fromPb_success_exit_876_placed_sepWP sessionMemcpyVmAcpSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget (
  FromPbDecAllocEnv FromPbDecEnv fromPbDecLoopAllocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget (
  fromPb_drop_vec_u8_776_placed_sepWP fromPb_error_exit_712_placed_sepWP
  fromPb_outer_loop_placed_wpp fromPb_tail_820_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerPlacedBudget (sessionMemmoveVmAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbProofBudget (
  fromPbDecSpecWithStack fromPb_header_err_placed_vm_sepWP fromPb_header_ok_placed_vm_sepWP
  fromPb_init_empty_headers_placed_vm_sepWP fromPb_save_regs_placed_vm_sepWP
  sepWPp_of_exit_core_placed sepWPp_seq_vm_clean
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32 fsp_448_add_40 fsp_448_add_48
  fsp_448_add_56 fsp_448_add_64 fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8 fsp_488_add_8 fsp_496_add_8
  fsp_504_add_8 fsp_512_add_8 fsp_520_add_8 fsp_528_add_8
  cap_add_lsl1_lsl3_toNat cap_add_lsl1_ubfm_toNat cur_add8_sub8 cur_add8_add24

/-! ## 1. `withLsCodeLoaded` & Pool/Event Sequencing Helpers -/

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

private theorem seq_vm_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s Pre post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hvm hcl' hQ))

private theorem sepWPp_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hvm, hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hclm hq))

private theorem sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := h1 R hm hL
  rcases hout with ⟨hpcm, hrunm, Pm, hpm, hQm⟩ | hpan | hoom
  · have hcl_m : LibsignalCodeLoaded lsmpl sm.mem :=
      LibsignalCodeLoaded.of_keepsFrozen hcl hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ := h2 sm Pm hpcm hrunm hcl_m hQm R hpm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

private theorem sync_pool_vm (s1 : State) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    {s2 : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hnext : VmPreserved s1 s2 → SepWP prog target s2 (A.pool lim st s2 ∗ F) post)
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hvm : VmPreserved s1 s2 := by simp [VmPreserved, Heap.PoolPreserved, wp_norm, arm64_norm]) :
    SepWP prog target s2 P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]; exact hnext hvm

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

/-- Bridges `HookSat _ spqrMemcpySym allocMemcpyVmSpec` to `sessionMemcpyVmAcpSpec`
    by framing `stackAt s0.sp hookStack`. -/
theorem hookSat_sessionMemcpyVmAcp_of_allocMemcpyVm {H : String → Option (State → State)}
    (hookStack : Nat := 4096)
    (h : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    HookSat H spqrMemcpySym (sessionMemcpyVmAcpSpec hookStack) := by
  rcases h with ⟨fn, hfn, hbody⟩
  refine ⟨fn, hfn, fun (dst, src, bs) R s0 hrun hpre hal => ?_⟩
  dsimp only [sessionMemcpyVmAcpSpec, CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
    ProofLib.libcMemcpySpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  let R' : SepProp := stackAt s0.sp hookStack ∗ R
  have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ R' := by
    dsimp only [allocMemcpyVmSpec, R']
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    ac_nf at hm ⊢
  obtain ⟨hkf, hsym, hout⟩ := hbody (dst, src, bs) R' s0 hrun hpre' hal
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, R'] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    dsimp only [sessionMemcpyVmAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0f, hacp.2.1, hacp, hvm⟩, ?_⟩
    ac_nf at hm' ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Budget-Threaded Error Exit B (`+740 -> s0.lr`) with `LibsignalCodeLoaded` -/

theorem fromPb_error_exit_740_cl_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (sets_err : List SortedSetPt) (hsets_len : sets_err.length = 16)
    (bss : List (List (BitVec 8))) (hbss_len : bss.length = 16)
    (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64) (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        sortedSetPtListOf A.repAlloc (fsp + 32#64) sets_err ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        ∃ evs, FreeOnlyEvs evs ∧
          (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc_sat
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  have hvecs_len : (sets_err.map SortedSetPt.vec).length = NUM_POLYS := by
    simp [hsets_len, NUM_POLYS, CHUNK_SIZE]
  refine align_pre_wp (seq_vm_clean_lscl hcl (mid := lsmpl.base 264)
      (Pre := (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ b8) ∗ memRegion (out + 9#64) 391 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        vecPtListOf A.repAlloc (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (P_mid := vecPtListOf A.repAlloc (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗
        (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
          (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗ Frame))
      (Q := fun sc => AllocCallPreserved s sc ∧ sc.sp = fsp ∧ sc.readReg64 .x0 = fsp + 32#64 ∧
        sc.readReg64 .x21 = ptsPtr ∧ sc.readReg64 .x24 = 16#64 ∧
        sc.readReg64 .x29 = fsp + 448#64 ∧ sc.readReg64 .x30 = (blkPl_376).base + 768#64 ∧
        calleeSavedVRegs sc = calleeSavedVRegs s0 ∧ sc.trace = s0.trace) ?_ ?_)
    (by rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; sep_ac_rfl)
  · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, Reg.x29, Reg.x30, BitVec.ofNat_eq_ofNat] at hpc hx21 hx24 hx29 ⊢
    by_vm_steps (
      wp_steps 7
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      unfold resultPolyDecoderFromPbAt noneCap
      dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte, BitVec.ofNat_eq_ofNat]
      exact Entails.of_eq (by sep_ac_rfl))
  · intro sc hpcc hrun_c hvm_c hcl_c ⟨hacp_c, hsp_c, hx0_c, hx21_c, hx24_c, hx29_c, hx30_c, hvregs_c, htr_c⟩
    rw [← A.pool_of_vmPreserved hvm_c]
    have hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
        (lsmpl.base 264) (withMemEq sc.mem (dropGlueSortedSetPt16Spec M A lim)) :=
      _root_.LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget.drop_glue_sorted_set_pt16_mem_on
        (callerProg := (blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) hdealloc_sat hcl_c
    simp only [withMemEq, dropGlueSortedSetPt16Spec] at hdrop
    refine seq_clean_evs
      (mid := (blkPl_376).base + 776#64)
      (P_evs := fun evs1 sm =>
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
            (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗
            (if cap_pts = 0 then emp
              else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
            memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm =>
        AllocCallPreserved sc sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, Reg.x29, Reg.x30, BitVec.ofNat_eq_ofNat] at hdrop hpcc hx0_c hx21_c hx24_c hx29_c hx30_c ⊢
      wp_call hdrop ((⟨fsp + 32#64, sets_err.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost), st)
      have hacp_drop' : AllocCallPreserved sc sf := by assumption
      rcases hacp_drop' with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine sync_pool_vm sf fun hvm_after => ?_
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
      refine ⟨_, ‹FreeOnlyEvs _›, ?_, ?_⟩
      · rw [← hsp_sf, hsp_sf.trans hsp_c, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
        dsimp only [polyArrayBytes]
        have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
        exact replace_sub_entails hfsp448
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
            A.pool lim (M.stepEvents _ st) _ ∗ stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame)) (by sep_ac_rfl) (by sep_ac_rfl)
      · rw [hbss_len]
        simp [AllocCallPreserved, wp_norm, arm64_norm, *]
    · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hacp1, hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
      have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss_len
      have hlen_bound : bss.length * 24 < 2 ^ 63 := by rw [hbss_len]; decide
      have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
      have hrejoin_buf := memRegion_rejoin_vecBuf A.repAlloc 24 8 cap_pts ptsPtr bss.length hle hcap_bound
      refine seq_clean_evs
        (fromPb_drop_vec_u8_776_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
          (M.stepEvents evs1 st) s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
      intro evs2 s2 hevs2 hpc2 hrun2 ⟨hacp2, hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
      have hpre_820 :
          memRegion ptsPtr (bss.length * 24) ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗
            stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
          (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗ savedRegsAt fsp s0 ∗
            memRegion fsp 448 ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗
            stackAt fsp dropGluePoly16Stack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame) := by
        rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; unfold vecVecU8BufDealloc
        exact replace_sub_entails hrejoin_buf
          ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗ memRegion (fsp - 4128#64) 32 ∗
            stackAt fsp allocHookStack ∗ resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame)
          (by sep_ac_rfl) (by sep_ac_rfl)
      refine SepWP.weaken_pre hpre_820 (SepWP.mono
        (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2)
        fun sf _Pf _ _ ⟨evs3, hevs3, hPf, hspf, hacp3, hcsf, htrf⟩ => ?_)
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sf ∗
            stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗ memRegion pbA 40 ∗
            A.pool lim (M.stepEvents ((evs1 ++ evs2) ++ evs3) st) sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame := by
        rw [M.stepEvents_append, M.stepEvents_append]
        exact replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)
      exact ⟨(evs1 ++ evs2) ++ evs3, (hevs1.append hevs2).append hevs3, Entails.trans hPf hpost_final,
        hspf, ((hacp_c.trans hacp1).trans hacp2).trans hacp3, hcsf, htrf⟩

/-! ## 3. Closed `[LibsignalPlacement]` Contract for `<PolyDecoder>::from_pb` (Block `376`) -/

set_option maxHeartbeats 800000 in
theorem fromPbDec_cl_placed_ok_core [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0)) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack M A lim fromPbCoreStack)) := by
  have hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc_sat
  have hmemcpy : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpyVmAcpSpec :=
    spqr_hook_ok_of_mem hmemcpy_sat
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA, pb⟩, st0⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [fromPbDecSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfits, hlr_ls⟩, hmem⟩
  have hlr_gpr30 : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr_ls
  refine ⟨stackAt s0.sp fromPbCoreStack ∗
      (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A.repAlloc pbA pb ∗ A.pool lim st0 s0),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  dsimp only [withLsCodeLoaded, fromPbDecSpecWithStack]
  have hpro := fromPb_save_regs_placed_vm_sepWP (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A.repAlloc pbA pb ∗ A.pool lim st0 s0)
    hpc0 hrun0 hx0 hx1
  refine sepWPp_seq_vm_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 hvm1 hcl1 ⟨hacp1, hsp1, hx0_1, hx1_1, hx29_1, hvregs1, htr1⟩
  rw [← A.pool_of_vmPreserved hvm1]
  let fsp := s0.sp - 544#64
  have hfsp : HiddenEq fsp (s0.sp - 544#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (protoPolynomialDecoderAt_expose A.repAlloc pbA pb
        (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
          memRegion out polyDecoderSize ∗ A.pool lim st0 s1))) ?_
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.pure_elim; rintro ⟨hle, hcap_bound, hlen_bound, _⟩
  by_cases hlen16 : pb.pts.length = 16
  · have hhdr := fromPb_header_ok_placed_vm_sepWP (ext := ext) s1 fsp out pbA
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool lim st0 s1)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (by rw [hlen16]; exact Entails.of_eq (by sep_ac_rfl))
      (sepWPp_seq_vm_lscl hcl1 hhdr ?_)
    intro s2 hpc2 hrun2 hvm2 hcl2 ⟨hacp2, hsp2, hx0_2, hx20_2, hx24_2, hx29_2, hvregs2, htr2⟩
    rw [← A.pool_of_vmPreserved hvm2]
    conv => arg 4; rw [memRegion_448_split fsp, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v432
    apply SepWPp.exists_elim; intro v424
    apply SepWPp.exists_elim; intro v416
    apply SepWPp.exists_elim; intro v24
    apply SepWPp.exists_elim; intro v16
    apply SepWPp.exists_elim; intro v8
    have hinit := fromPb_init_empty_headers_placed_vm_sepWP (ext := ext)
      s2 fsp out pbA ptsPtr v8 v16 v24 hfsp_align
      (memRegion fsp 8 ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
        memRegion out polyDecoderSize ∗ A.pool lim st0 s2)
      hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 hx29_2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_vm_lscl hcl2 hinit ?_)
    intro s3 hpc3 hrun3 hvm3 hcl3 ⟨hacp3, hsp3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3, htr3⟩
    rw [← A.pool_of_vmPreserved hvm3]
    have hacp03 : AllocCallPreserved s0 s3 := (hacp1.trans hacp2).trans hacp3
    have halloc_loop : FromPbDecAllocEnv pb (fromPbDecLoopAllocEvents pb.pts) :=
      Or.inr ⟨hlen16, rfl⟩
    have hfit_loop : FitsEvents M lim st0 (fromPbDecLoopAllocEvents pb.pts) :=
      hfits _ halloc_loop
    have hpts_ne : pb.pts ≠ [] := by intro h; simp [h] at hlen16
    let Frame3 : SepProp :=
      ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
        memRegion fsp 8 ∗ memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ memRegion out polyDecoderSize
    by_cases hall_pts : ∀ bs ∈ pb.pts, bs.length % 4 = 0
    · refine SepWPp.weaken_pre
        (by
          dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, Frame3]
          rw [BitVec.add_zero, BitVec.add_zero, hlen16]
          exact Entails.of_eq (by sep_ac_rfl))
        (fromPb_outer_loop_placed_wpp hshim_sat halloc_sat hmemmove_sat
          s0 fsp ptsPtr hfsp_align pb.pts hpts_ne 0
          (by omega) st0 hfit_loop v416 v424 v432 s3 Frame3
          hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
          (by rw [htr3, htr2, htr1]) (by rw [hvregs3, hvregs2, hvregs1])
          (fun sm w416 w424 w432 hall hpcm hrunm hacpm hspm hx21m _ _ htrm hvregsm => ?_)
          (fun _ _ _ _ _ ⟨bs, hbs, hne⟩ _ _ _ _ _ _ _ _ _ _ => (hne (hall_pts bs hbs)).elim))
      rw [fromPbDecResult_eq_ok_of_all_mod4 pb hlen16 hall]
      have hout_len : (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }).length = 16 := by
        simp [hlen16]
      have hok := fromPb_success_exit_876_placed_sepWP hdealloc hmemcpy s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align pb hlen16
        (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }) hout_len hle hcap_bound
        (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm emp
        hpcm hrunm hspm hx21m hvregsm htrm
      have hok' := SepWP.mono
        (post' := fun sf P' =>
          ∃ evs_free, FreeOnlyEvs evs_free ∧
            (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out
                (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete,
                       pts := pb.pts.map fun bs => pushChunks4Total bs { vec := [] } }) ∗
              memRegion pbA 40 ∗
              A.pool lim (M.stepEvents evs_free (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0)) sf ∗
              stackAt s0.sp fromPbCoreStack ∗ emp) ∧
            sf.sp = s0.sp ∧ AllocCallPreserved sm sf ∧
            CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
        hok fun sf P' _ _ ⟨evs_f, hf, hP', hacp_f, hsp_f, hcs_f, htr_f⟩ =>
          ⟨evs_f, hf, hP', hsp_f, hacp_f, hcs_f, htr_f⟩
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA pb _ st0
          (fromPbDecLoopAllocEvents pb.pts) halloc_loop (hacp03.trans hacpm) _ R hok')
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize, Frame3]
      rw [BitVec.add_zero, BitVec.add_zero]
      exact Entails.of_eq (by sep_ac_rfl)
    · let s0' : State := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_376).base + 740#64)
      have hr30 : s0'.readReg64 (Reg.gpr 30#5) = (blkPl_376).base + 740#64 := by
        simp [s0', wp_norm, arm64_norm]
      refine sepWPp_bind_lscl hcl3
        (Q_mid := fun sm Pm =>
          ∃ (sets_err : List SortedSetPt) (w416 w424 w432 : BitVec 64),
            (∃ bs ∈ pb.pts, bs.length % 4 ≠ 0) ∧ sets_err.length = pb.pts.length ∧
            AllocCallPreserved s3 sm ∧
            sm.sp = fsp ∧ sm.readReg64 .x21 = ptsPtr ∧
            sm.readReg64 .x24 = 16#64 ∧ sm.readReg64 .x29 = fsp + 448#64 ∧
            sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
            (Pm ⊢ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
              ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
              sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * 0)) sets_err ∗
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * 0)) pb.pts ∗
              A.pool lim (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm ∗
              stackAt fsp allocHookStack ∗ Frame3))
        (SepWPp.weaken_pre
          (by
            dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, Frame3]
            rw [BitVec.add_zero, BitVec.add_zero, hlen16]
            exact Entails.of_eq (by sep_ac_rfl))
          (fromPb_outer_loop_placed_wpp hshim_sat halloc_sat hmemmove_sat
            s0' fsp ptsPtr hfsp_align pb.pts hpts_ne 0
            (by omega) st0 hfit_loop v416 v424 v432 s3 Frame3
            hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
            (by change s3.trace = s0.trace; rw [htr3, htr2, htr1])
            (by change calleeSavedVRegs s3 = calleeSavedVRegs s0; rw [hvregs3, hvregs2, hvregs1])
            (fun _ _ _ _ hall _ _ _ _ _ _ _ _ _ => (hall_pts hall).elim)
            (fun sm sets_err w416 w424 w432 hex hsets_len hpcm hrunm hacpm hspm hx21m hx24m hx29m htrm hvregsm =>
              SepWPp.done (hpcm.trans hr30.symm) hrunm
                ⟨sets_err, w416, w424, w432, hex, hsets_len, hacpm, hspm, hx21m, hx24m, hx29m, htrm, hvregsm, Entails.refl _⟩)))
        ?_
      intro sm Pm hpcm' hrunm hclm ⟨sets_err, w416, w424, w432, hex, hsets_len, hacpm, hspm, hx21m, hx24m, hx29m, htrm, hvregsm, hPm⟩
      have hpcm : sm.pc = (blkPl_376).base + 740#64 := hpcm'.trans hr30
      refine SepWPp.weaken_pre hPm ?_
      rw [fromPbDecResult_eq_err_of_exists_mod4 pb hlen16 hex]
      have hsets_len16 : sets_err.length = 16 := hsets_len.trans hlen16
      have herr := fromPb_error_exit_740_cl_placed_sepWP hdealloc_sat s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align sets_err hsets_len16 pb.pts hlen16 hle hcap_bound
        (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm hclm emp
        hpcm hrunm hspm hx21m hx24m hx29m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA pb (.error .serializationInvalid) st0
          (fromPbDecLoopAllocEvents pb.pts) halloc_loop (hacp03.trans hacpm) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize, Frame3]
      rw [BitVec.add_zero, BitVec.add_zero]
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      exact replace_sub_entails hpb16
        (memRegion out 400 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          sortedSetPtListOf A.repAlloc (fsp + 32#64) sets_err ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
          (if cap_pts = 0 then emp
            else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗
          A.pool lim (M.stepEvents (fromPbDecLoopAllocEvents pb.pts) st0) sm ∗
          stackAt fsp allocHookStack)
        (by sep_ac_rfl) (by sep_ac_rfl)
  · rw [fromPbDecResult_eq_err_of_len_ne_16 pb hlen16]
    have hnPts : pb.pts.length < 2 ^ 64 := by omega
    have hhdr := fromPb_header_err_placed_vm_sepWP (ext := ext) s1 fsp out pbA
      pb.pts.length hnPts hlen16
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool lim st0 s1)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_vm_clean hhdr ?_)
    intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx0_2, hx20_2, hx24_2, _, hvregs2, htr2⟩
    rw [← A.pool_of_vmPreserved hvm2]
    have halloc_nil : FromPbDecAllocEnv pb [] := Or.inl rfl
    have herr := fromPb_error_exit_712_placed_sepWP hdealloc s0 fsp out pbA cap_pts ptsPtr
      hfsp hsp0_align hfsp_align pb.pts hle hcap_bound hlen_bound
      (M.stepEvents [] st0) s2 emp hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2
      (by rw [hvregs2, hvregs1]) (by rw [htr2, htr1])
    refine SepWPp.weaken_pre ?_
      (sepWPp_of_exit_core_placed s0 s2 out pbA pb (.error .serializationInvalid) st0
        [] halloc_nil (hacp1.trans hacp2) _ R herr)
    dsimp only [polyDecoderSize, AllocCostModel.stepEvents]
    have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
    exact replace_sub_entails hpb16
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st0 s2 ∗ stackAt fsp dropGluePoly16Stack)
      (by sep_ac_rfl) (by sep_ac_rfl)

private theorem withLsCodeLoaded_fromPbDecSpecWithStack_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64} {stk1 stk2 : Nat}
    (hle : stk1 ≤ stk2) (hmax : stk1 + (stk2 - stk1) ≤ 2 ^ 64)
    (h : subroutine_ok P entry (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack M A lim stk1))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack M A lim stk2)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  have hsplit : stackAt s0.sp stk2 =
      memRegion (s0.sp - BitVec.ofNat 64 stk2) (stk2 - stk1) ∗ stackAt s0.sp stk1 := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp stk1 (stk2 - stk1) hmax
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk2) (stk2 - stk1) ∗ R
  have hpre1 : s0.mem ⊨ (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack M A lim stk1)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    dsimp only [fromPbDecSpecWithStack, R'] at hpre0 ⊢
    rw [hsplit] at hpre0
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre0
  refine h.mono_outcome x R' s0 hpc hrun hpre1 hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, fromPbDecSpecWithStack, R'] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpecWithStack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack M A lim decoderFromPbStack))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  let xg : FromPbDecGhost := ⟨x.out, x.pbA, x.pb⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (fromPbDecSpecWithStack M A lim decoderFromPbStack)).pre (xg, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre0⟩
  refine h.mono_outcome (xg, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, DefsBudget.decoderFromPbSpec, fromPbDecSpecWithStack, xg] at hpost ⊢
    rwa [← fromPbDecResult_eq_decoderFromPbResult x.pb]
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Closed `[LibsignalPlacement]` budget-threaded contract for `<PolyDecoder>::from_pb` (Block `376`) on `lsProg_376`. -/
theorem decoder_from_pb_cl_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0)) :
    subroutine_ok (lsProg_376 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 376)]
  exact withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpecWithStack
    (withLsCodeLoaded_fromPbDecSpecWithStack_mono (by decide) (by decide)
      (fromPbDec_cl_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat))

theorem decoder_from_pb_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 376 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) :=
  ls_to_blockProgram (decoder_from_pb_cl_placed_ok_ext halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat)

theorem decoder_from_pb_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) :=
  ls_subroutine_ok_of_block
    (decoder_from_pb_cl_placed_ok_ext halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat) hidx

theorem decoder_from_pb_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 376)
      (withMemEq m (DefsBudget.decoderFromPbSpec M A lim)) :=
  lscall_blk_cl
    (decoder_from_pb_cl_placed_ok_ext halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat) hcl hidx

/-- Lifted `[LibsignalPlacement]` budget-threaded contract for `<PolyDecoder>::from_pb` (Block `376`)
    on `lsProg_333` (`DefsBudget.DecoderFromPbPlacedOkExt M A lim ext`). -/
theorem decoder_from_pb_on_333_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyVmAcpSpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0)) :
    DefsBudget.DecoderFromPbPlacedOkExt M A lim ext :=
  decoder_from_pb_cl_on (callerProg := lsProg_333 (Rust.withPanics ext))
    halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecoderFromPbClPlacedBudget
