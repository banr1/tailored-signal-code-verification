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
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Exit
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbExitClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Top-Level Proof for `<PolyEncoder>::from_pb` (Block `374`)

Proves the `.polys` and `.points` success exits and top-level `subroutine_ok` contracts for
`<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`, lifted to `lsProg_333`) under
`[LibsignalPlacement]` with `LibsignalCodeLoaded` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_374 blkPl_374 extract_withLsCodeLoaded libsignalSessionLib
  lsProg_333 lsProg_374 ls_subroutine_ok_of_block lscall_blk_cl
  lsmpl lsρ sepWP_mono_lscl sepWP_seq_lscl withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalSpqrV1 (
  GF16 NUM_POLYS Point Poly PolyEncoder PolynomialError ProtoPolynomialEncoder
)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (
  dropGluePoly16Stack pointListOf_eq_vecGF16ListOf polyListOf_eq_vecGF16ListOf vecGF16ListOf
)
open CryptoVerification.SpqrV1.Poly (
  encoderStateAt polyEncoderAt polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag polyEncoderSize polyEncoderVecsOff
  protoPolynomialEncoderAt protoPolynomialEncoderSize resultPolyEncoderFromPbAt
)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  bv_add_lit_add_lit bv_lit_add_lit
  decodePbPointsTotal decodePbPointsTotal_length decodePbPointsTotal_value_length_le
  decodePbPolysTotal decodePbPolysTotal_length
  encoderFromPbStack fromPbResult fromPbResult_eq_of_err
  fromPbResult_eq_of_polys fromPbResult_eq_of_pts
  length_vecHeadersBytesOf protoPolyEncoderRest protoPolyEncoder_close protoPolyEncoder_open
  savedCells sepWP_pure_left
  spqrRustAllocSym spqrRustDeallocSym spqrRustNoAllocShimSym
  stackAt_dropGluePoly16_split_bottom stack_split_for_polys stack_split_for_pts
  vecGF16HeapList vecGF16ListOf_entails_headers_heaps vecHeadersBytesOf zeroPolySlotsAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved fitsEvents_append
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (session2MemcpyAcpSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (
  EncoderFromPbAllocEnv EncoderFromPbEnv
  encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents encoderFromPbPtsLoopEvents
  encoderFromPbSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget (
  polys_init_zero_headers_placed
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlacedBudget (
  polys_outer_loop_placed
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlacedBudget (
  from_pb_header_err_placed from_pb_header_polys_placed from_pb_header_pts_placed
  from_pb_save_regs_placed sepWPp_of_exit_placed
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlacedBudget (
  pts_init_empty_headers_placed pts_outer_loop_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbExitClPlacedBudget (
  from_pb_err_header_cl_placed from_pb_err_polys_cl_placed from_pb_err_pts_cl_placed
  from_pb_ok_copy_out_cl_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

@[local arm64_norm, local wp_norm] private theorem bv384_toNat' : (384#64 : BitVec 64).toNat = 384 := rfl
@[local arm64_norm, local wp_norm] private theorem bv8_toNat' : (8#64 : BitVec 64).toNat = 8 := rfl

private theorem allocCallPreserved_refl (s0 : State) : AllocCallPreserved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1) (h2 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 := by
  rcases h1 with ⟨hfs1, htr1, hsig1, htp1, hbs1, hor1, hsym1⟩
  rcases h2 with ⟨hfs2, htr2, hsig2, htp2, hbs2, hor2, hsym2⟩
  exact ⟨hfs2.trans hfs1, htr2.trans htr1, hsig2.trans hsig1,
    htp2.trans htp1, hbs2.trans hbs1, hor2.trans hor1, hsym2.trans hsym1⟩

private theorem allocCallPreserved_step {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1)
    (hfs : s2.fs = s1.fs := by rfl)
    (htr : s2.trace = s1.trace := by rfl)
    (hsig : s2.sigActions = s1.sigActions := by rfl)
    (htp : s2.tpidrEl0 = s1.tpidrEl0 := by rfl)
    (hbs : s2.brkStart = s1.brkStart := by rfl)
    (hor : s2.oracle = s1.oracle := by rfl)
    (hsym : s2.symtab = s1.symtab := by rfl) :
    AllocCallPreserved s0 s2 :=
  allocCallPreserved_trans h1 ⟨hfs, htr, hsig, htp, hbs, hor, hsym⟩

private theorem allocCallPreserved_step_trans {s0 s1 s2 s3 : State}
    (h1 : AllocCallPreserved s0 s1) (h23 : AllocCallPreserved s2 s3)
    (hfs : s2.fs = s1.fs := by rfl)
    (htr : s2.trace = s1.trace := by rfl)
    (hsig : s2.sigActions = s1.sigActions := by rfl)
    (htp : s2.tpidrEl0 = s1.tpidrEl0 := by rfl)
    (hbs : s2.brkStart = s1.brkStart := by rfl)
    (hor : s2.oracle = s1.oracle := by rfl)
    (hsym : s2.symtab = s1.symtab := by rfl) :
    AllocCallPreserved s0 s3 :=
  allocCallPreserved_trans (allocCallPreserved_step h1 hfs htr hsig htp hbs hor hsym) h23

private theorem allocCallPreserved_writeLr_iff (s0 s : State) (v : BitVec 64) :
    AllocCallPreserved (s0.writeReg64 (Reg.gpr 30#5) v) s ↔ AllocCallPreserved s0 s := by
  unfold AllocCallPreserved
  simp [State.writeReg64]

private theorem hookSat_session2MemcpyAcpWithStack_of_allocMemcpyVm
    {H : String → Option (State → State)} {name : String} (hookStack : Nat)
    (h : HookSat H name allocMemcpyVmSpec) :
    HookSat H name (session2MemcpyAcpSpecWithStack hookStack) := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  dsimp only [session2MemcpyAcpSpecWithStack] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [allocMemcpyVmSpec, session2MemcpyAcpSpecWithStack] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

private theorem seq_lscl_st [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

private theorem sepWPp_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q_mid sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hvm, hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hvm hq))

private theorem sepWPp_bind_lscl_st [LibsignalPlacement] {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_mid : State → Prop}
    {Q Q_panic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P
      (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_mid sm)
      Q_panic)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm →
      SepWPp prog target_pc sm (P_mid sm) Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic := by
  intro R hsat hL
  obtain ⟨s', hsteps, hout⟩ := h1 R hsat hL
  rcases hout with ⟨htgt, hrun, P_mid', hsat', hPm, hQm⟩ | hpan | hoom
  · have hcl' : LibsignalCodeLoaded lsmpl s'.mem :=
      LibsignalCodeLoaded.of_keepsFrozen hcl hsteps.keepsFrozen
    have hsat_mid : s'.mem ⊨ P_mid s' ∗ R :=
      Satisfies.mono (sepConj_mono_left hPm) hsat'
    obtain ⟨s'', hsteps2, hout2⟩ :=
      h2 s' htgt hrun hcl' hQm R hsat_mid (hsteps.codeLoaded hL)
    exact ⟨s'', hsteps.trans hsteps2, hout2⟩
  · exact ⟨s', hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨s', hsteps, Or.inr (Or.inr hoom)⟩

private theorem sepWPp_bind_lscl_st_eq [LibsignalPlacement] {prog : Program}
    {mid' mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_mid : State → Prop}
    {Q Q_panic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hmid : mid' = mid)
    (h1 : SepWPp prog mid' s P
      (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_mid sm)
      Q_panic)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm →
      SepWPp prog target_pc sm (P_mid sm) Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic :=
  sepWPp_bind_lscl_st hcl (hmid ▸ h1) h2

/-- Budget-threaded placed `.polys` success exit (`+1548 -> s0.lr`) under `LibsignalCodeLoaded`. -/
theorem from_pb_ok_polys_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (polys : List Poly) (hpolys_len : polys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1548#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A.repAlloc (fsp + 480#64) (polys.map Poly.coefficients) ∗
        memRegion out polyEncoderSize ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        memRegion (fsp - 4128#64) 32 ∗
        stackAt fsp allocHookStack ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok { idx := pb.idx, s := .polys polys }) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hvecs_len : (polys.map Poly.coefficients).length = 16 := by simp [hpolys_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecGF16ListOf_entails_headers_heaps A.repAlloc
      (polys.map Poly.coefficients) (fsp + 480#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply sepWP_pure_left; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (polys.map Poly.coefficients)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  have hbs_lt : (vecHeadersBytesOf pins (polys.map Poly.coefficients)).length < 2 ^ 64 := by
    rw [hbs_len]; decide
  have hmemcpy' : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec :=
    spqr_hook_ok_of_mem hmemcpy_sat
  dsimp only [allocMemcpyVmSpec, BitVec.ofNat_eq_ofNat] at hmemcpy'
  refine seq_lscl_st hcl
    (mid := (blkPl_374).base + 1572#64)
    (P_mid := fun sm =>
      memRegion out polyEncoderSize ∗
      ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins (polys.map Poly.coefficients)) ∗
      vecGF16HeapList A.repAlloc pins (polys.map Poly.coefficients) ∗
      ((fsp + 56#64) ↦₆₄ out) ∗
      ((pbA + 48#64) ↦₃₂ pb.idx) ∗
      stackAt fsp allocHookStack ∗
      cells fsp 7 ∗
      ((fsp + 64#64) ↦₆₄ pbA) ∗
      cells (fsp + 456#64) 3 ∗
      memRegion (fsp + 480#64) 384 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 ∗
      memRegion (fsp - 4128#64) 32 ∗
      ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
      ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((pbA + 32#64) ↦₆₄ polysPtr) ∗
      ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0 ∗
      A.pool lim st sm)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = 1#64 ∧
      sm.readReg64 .x20 = pbA ∧
      sm.trace = s0.trace ∧
      AllocCallPreserved s0 sm ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · conv => arg 4; pattern (memRegion (fsp + 72#64) 384); rw [← hbs_len]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmemcpy' (fsp + 72#64, fsp + 480#64,
      vecHeadersBytesOf pins (polys.map Poly.coefficients))
    have hacp_mc : AllocCallPreserved s0 sf :=
      allocCallPreserved_step_trans hacp ‹AllocCallPreserved _ sf›
    have htr_mc : sf.trace = s0.trace := hacp_mc.2.1
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool ((blkPl_374).base + 1572#64)
    simp only [State.setMem_setMem]
    have hsrc : ((fsp + 480#64) ↦ₛ vecHeadersBytesOf pins (polys.map Poly.coefficients)) ⊢
        memRegion (fsp + 480#64) 384 := by
      rw [← hbs_len]; exact ProofLib.pointsToBytes_entails_memRegion (fsp + 480#64) _
    have hacp_end := allocCallPreserved_step hacp_mc
    exact SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      ⟨Entails.trans
        (Entails.of_eq (show _ =
          ((fsp + 480#64) ↦ₛ vecHeadersBytesOf pins (polys.map Poly.coefficients)) ∗
          (memRegion out polyEncoderSize ∗
           ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins (polys.map Poly.coefficients)) ∗
           vecGF16HeapList A.repAlloc pins (polys.map Poly.coefficients) ∗
           ((fsp + 56#64) ↦₆₄ out) ∗ ((pbA + 48#64) ↦₃₂ pb.idx) ∗ stackAt fsp allocHookStack ∗
           cells fsp 7 ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗ cells (fsp + 456#64) 3 ∗
           cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
           memRegion (fsp + 920#64) 8 ∗ memRegion (fsp - 4128#64) 32 ∗
           ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
           savedCells s0 ∗ A.pool lim st _) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hsrc) (Entails.of_eq (by sep_ac_rfl))),
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       hacp_end.2.1, hacp_end, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx8_1, hx20_1, htr1, hacp1, hvregs1⟩
    refine from_pb_ok_copy_out_cl_placed
      (hookSat_session2MemcpyAcpWithStack_of_allocMemcpyVm allocHookStack hmemcpy_sat)
      hdealloc_sat st s0 s1 hcl1 fsp out pbA pbA 1#64 (hfsp_fn trivial)
      ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .polys polys }
      pins (polys.map Poly.coefficients) hpins_len hvecs_len ?_
      hsp0_align hpc1 hrun1 hsp1 hx8_1 hx20_1 htr1 hacp1 hvregs1 hlr0
    dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPolysTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [polyListOf_eq_vecGF16ListOf]
    have hp : polys.length = NUM_POLYS := hpolys_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 1#64) ∗
         vecGF16ListOf A.repAlloc (out + 8#64) (polys.map Poly.coefficients)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (Entails.pure_right hp (Entails.refl _)))
      (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded placed `.points` success exit (`+1648 -> +1572 -> s0.lr`) under
    `LibsignalCodeLoaded`. -/
theorem from_pb_ok_pts_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (pts : List Point) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A.repAlloc (fsp + 480#64) (pts.map Point.value) ∗
        memRegion out polyEncoderSize ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        memRegion (fsp - 4128#64) 32 ∗
        stackAt fsp allocHookStack ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok { idx := pb.idx, s := .points pts }) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hvecs_len : (pts.map Point.value).length = 16 := by simp [hpts_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecGF16ListOf_entails_headers_heaps A.repAlloc
      (pts.map Point.value) (fsp + 480#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply sepWP_pure_left; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  have hbs_lt : (vecHeadersBytesOf pins (pts.map Point.value)).length < 2 ^ 64 := by
    rw [hbs_len]; decide
  have hmemcpy' : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec :=
    spqr_hook_ok_of_mem hmemcpy_sat
  dsimp only [allocMemcpyVmSpec, BitVec.ofNat_eq_ofNat] at hmemcpy'
  refine seq_lscl_st hcl
    (mid := (blkPl_374).base + 1572#64)
    (P_mid := fun sm =>
      memRegion out polyEncoderSize ∗
      ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
      vecGF16HeapList A.repAlloc pins (pts.map Point.value) ∗
      ((fsp + 56#64) ↦₆₄ out) ∗
      ((pbA + 48#64) ↦₃₂ pb.idx) ∗
      stackAt fsp allocHookStack ∗
      cells fsp 7 ∗
      ((fsp + 64#64) ↦₆₄ v64) ∗
      cells (fsp + 456#64) 3 ∗
      memRegion (fsp + 480#64) 384 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 ∗
      memRegion (fsp - 4128#64) 32 ∗
      ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
      ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((pbA + 32#64) ↦₆₄ polysPtr) ∗
      ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0 ∗
      A.pool lim st sm)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = 0#64 ∧
      sm.readReg64 .x20 = pbA ∧
      sm.trace = s0.trace ∧
      AllocCallPreserved s0 sm ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · conv => arg 4; pattern (memRegion (fsp + 72#64) 384); rw [← hbs_len]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmemcpy' (fsp + 72#64, fsp + 480#64,
      vecHeadersBytesOf pins (pts.map Point.value))
    have hacp_mc : AllocCallPreserved s0 sf :=
      allocCallPreserved_step_trans hacp ‹AllocCallPreserved _ sf›
    have htr_mc : sf.trace = s0.trace := hacp_mc.2.1
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool ((blkPl_374).base + 1572#64)
    simp only [State.setMem_setMem]
    have hsrc : ((fsp + 480#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ⊢
        memRegion (fsp + 480#64) 384 := by
      rw [← hbs_len]; exact ProofLib.pointsToBytes_entails_memRegion (fsp + 480#64) _
    have hacp_end := allocCallPreserved_step hacp_mc
    exact SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      ⟨Entails.trans
        (Entails.of_eq (show _ =
          ((fsp + 480#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
          (memRegion out polyEncoderSize ∗
           ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
           vecGF16HeapList A.repAlloc pins (pts.map Point.value) ∗
           ((fsp + 56#64) ↦₆₄ out) ∗ ((pbA + 48#64) ↦₃₂ pb.idx) ∗ stackAt fsp allocHookStack ∗
           cells fsp 7 ∗ ((fsp + 64#64) ↦₆₄ v64) ∗ cells (fsp + 456#64) 3 ∗
           cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
           memRegion (fsp + 920#64) 8 ∗ memRegion (fsp - 4128#64) 32 ∗
           ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
           savedCells s0 ∗ A.pool lim st _) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hsrc) (Entails.of_eq (by sep_ac_rfl))),
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       hacp_end.2.1, hacp_end, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx8_1, hx20_1, htr1, hacp1, hvregs1⟩
    refine from_pb_ok_copy_out_cl_placed
      (hookSat_session2MemcpyAcpWithStack_of_allocMemcpyVm allocHookStack hmemcpy_sat)
      hdealloc_sat st s0 s1 hcl1 fsp out pbA v64 0#64 (hfsp_fn trivial)
      ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .points pts }
      pins (pts.map Point.value) hpins_len hvecs_len ?_
      hsp0_align hpc1 hrun1 hsp1 hx8_1 hx20_1 htr1 hacp1 hvregs1 hlr0
    dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [pointListOf_eq_vecGF16ListOf]
    have hp : pts.length = NUM_POLYS := hpts_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 0#64) ∗
         vecGF16ListOf A.repAlloc (out + 8#64) (pts.map Point.value)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono_left (Entails.pure_right (And.intro hp hpts_bound) (Entails.refl _)))
      (Entails.of_eq (by sep_ac_rfl))

/-- `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
    satisfies `withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)` on `lsProg_374`. -/
theorem encoder_from_pb_cl_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_374 (Rust.withPanics ext)) (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) := by
  have hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem halloc_sat
  have hdealloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc_sat
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA, pb⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [encoderFromPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpts_max, hEnv, hlr0⟩, hmem⟩
  refine ⟨stackAt s0.sp encoderFromPbStack ∗
      (memRegion out polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        A.pool lim st s0),
    R, ?_, ?_⟩
  · exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  dsimp only [withLsCodeLoaded, encoderFromPbSpec]
  have hpro := from_pb_save_regs_placed (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A.repAlloc pbA pb ∗ A.pool lim st s0)
    hpc0 hrun0 hx0 hx1
  refine sepWPp_seq_vm_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx29_1, htr1, hacp1, hvregs1⟩
  rw [← A.pool_of_vmPreserved hvm1]
  let fsp := s0.sp - 1024#64
  have hfsp : fsp = s0.sp - 1024#64 := rfl
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (protoPolyEncoder_open A.repAlloc pbA pb))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro ptsCap
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.exists_elim; intro polysCap
  apply SepWPp.exists_elim; intro polysPtr
  refine SepWPp.weaken_pre
    (Entails.of_eq (show _ =
      ⌜pb.pts.length < 2 ^ 63 ∧ pb.polys.length < 2 ^ 63⌝ ∗
      (savedCells s0 ∗
       stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
       memRegion out polyEncoderSize ∗
       ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
       protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
  apply SepWPp.pure_left; rintro ⟨hnPts, hnPolys⟩
  by_cases hcase_pts : pb.pts.length = 16 ∧ pb.polys.length = 0
  · obtain ⟨hpts16, hpolys0⟩ := hcase_pts
    have hEnv_pts : EncoderFromPbAllocEnv pb (encoderFromPbPtsLoopEvents pb.pts) :=
      Or.inr (Or.inl ⟨hpts16, hpolys0, rfl⟩)
    have hFit_pts : FitsEvents M lim st (encoderFromPbPtsLoopEvents pb.pts) :=
      hEnv _ hEnv_pts
    rw [fromPbResult_eq_of_pts pb hpts16 hpolys0]
    have hdisp := from_pb_header_pts_placed (ext := ext) s1 fsp out pbA
      (savedCells s0 ∗
       stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
       memRegion out polyEncoderSize ∗
       ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
       protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
       A.pool lim st s1)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre
      (by rw [hpts16, hpolys0]; exact Entails.of_eq (by sep_ac_rfl))
      (sepWPp_seq_vm_lscl hcl1 hdisp ?_)
    intro s2 hpc2 hrun2 hcl2 hvm2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hacp12, hvregs2⟩
    have hacp2 := allocCallPreserved_trans hacp1 hacp12
    rw [← A.pool_of_vmPreserved hvm2, stack_split_for_pts s0.sp, ← hfsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v64
    apply SepWPp.exists_elim; intro v56
    have hinit := pts_init_empty_headers_placed (ext := ext) s2 fsp out pbA ptsPtr v56 hfsp_align
      (savedCells s0 ∗
       memRegion (fsp - 4128#64) 32 ∗
       stackAt fsp allocHookStack ∗
       cells fsp 7 ∗
       ((fsp + 64#64) ↦₆₄ v64) ∗
       memRegion (fsp + 72#64) 384 ∗
       cells (fsp + 456#64) 3 ∗
       cells (fsp + 864#64) 4 ∗
       cells (fsp + 896#64) 3 ∗
       memRegion (fsp + 920#64) 8 ∗
       memRegion out polyEncoderSize ∗
       ((pbA + 16#64) ↦₆₄ 16#64) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ 0#64) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
       protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
       A.pool lim st s2)
      hpc2 hrun2 hsp2 hx0_2 hx1_2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (sepWPp_seq_vm_lscl hcl2 hinit ?_)
    intro s3 hpc3 hrun3 hcl3 hvm3
      ⟨hsp3, hx1_3, hx21_3, hx23_3, hx24_3, hx25_3, _, _, _, _, _, _, hx29_3, htr3, hacp23, hvregs3⟩
    have hacp3 := allocCallPreserved_trans hacp2 hacp23
    rw [← A.pool_of_vmPreserved hvm3]
    have hpts_ne : pb.pts ≠ [] := by
      intro h; simp [h] at hpts16
    have hvec_nil : vecGF16ListOf A.repAlloc (fsp + 480#64) [] = emp := rfl
    let Frame_pts : SepProp :=
      memRegion out polyEncoderSize ∗
      cells fsp 7 ∗
      ((fsp + 56#64) ↦₆₄ out) ∗
      ((fsp + 64#64) ↦₆₄ v64) ∗
      memRegion (fsp + 72#64) 384 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 ∗
      memRegion (fsp - 4128#64) 32 ∗
      ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
      ((pbA + 16#64) ↦₆₄ 16#64) ∗
      ((pbA + 32#64) ↦₆₄ polysPtr) ∗
      ((pbA + 40#64) ↦₆₄ 0#64) ∗
      ((pbA + 48#64) ↦₃₂ pb.idx) ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0
    cases hdec : decodePbPointsTotal pb.pts with
    | ok tail =>
      dsimp only
      let s0_pts := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1648#64)
      have hr30_pts : s0_pts.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1648#64 := by
        simp [s0_pts, wp_norm, arm64_norm]
      refine SepWPp.weaken_pre
        (by
          dsimp only [Frame_pts, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
          rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpts16]
          exact Entails.of_eq (by sep_ac_rfl))
        (sepWPp_bind_lscl_st_eq hcl3 hr30_pts
          (pts_outer_loop_placed hshim halloc s0_pts fsp ptsPtr hfsp_align pb.pts 0 [] st s3 Frame_pts
            hFit_pts hpts_ne (by omega) rfl (fun bs hbs => by have := hpts_max bs hbs; omega)
            hpc3 hrun3 hsp3 hx21_3 hx23_3 hx24_3 hx25_3
            (by rw [htr3, htr2, htr1]; rfl)
            ((allocCallPreserved_writeLr_iff s0 s3 _).mpr hacp3)
            (by rw [hvregs3, hvregs2, hvregs1]; rfl)
            (Q := fun sm Pm =>
              (Pm ⊢ vecGF16ListOf A.repAlloc (fsp + 480#64) ([] ++ tail.map Point.value) ∗
                arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * 0)) pb.pts ∗
                cells (fsp + 456#64) 3 ∗
                A.pool lim (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) sm ∗
                stackAt fsp allocHookStack ∗ Frame_pts) ∧
              (sm.sp = fsp ∧ sm.readReg64 .x1 = s3.readReg64 .x1 ∧ sm.trace = s0.trace ∧
               AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
            (fun sm tail' hdec_ok hpcm hrunm hspm hx1m _ htrm hacpm hvregsm => by
              rw [hdec] at hdec_ok; injection hdec_ok with htail_eq; subst htail_eq
              exact SepWPp.done (hpcm.trans hr30_pts.symm) hrunm
                ⟨Entails.refl _, hspm, hx1m, htrm,
                 (allocCallPreserved_writeLr_iff s0 sm _).mp hacpm, hvregsm⟩)
            (fun sm errPts hdec_err _ _ _ _ _ _ _ _ _ => by
              rw [hdec] at hdec_err; cases hdec_err))
          ?_)
      intro sm hpcm hrunm hclm ⟨hspm, hx1m, htrm, hacpm, hvregsm⟩
      have htail_len : tail.length = 16 := by
        rw [decodePbPointsTotal_length pb.pts tail hdec, hpts16]
      have htail_bound : ∀ pt ∈ tail, pt.value.length ≤ 0x0555555555555555 :=
        decodePbPointsTotal_value_length_le pb.pts tail hdec hpts_max
      have hok := from_pb_ok_pts_cl_placed hmemcpy_sat hdealloc_sat
        (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) s0 sm hclm
        fsp out pbA v64 hfsp ptsCap ptsPtr polysCap polysPtr pb tail htail_len htail_bound
        hsp0_align hpcm hrunm hspm (hx1m.trans hx1_3) htrm hacpm hvregsm hlr0
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 sm st out pbA pb
          (.ok { idx := pb.idx, s := .points tail })
          (encoderFromPbPtsLoopEvents pb.pts) hEnv_pts _ R hok)
      dsimp only [Frame_pts, List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, hpts16, hpolys0]
      exact Entails.of_eq (by sep_ac_rfl)
    | error e =>
      dsimp only
      let s0_pts := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1612#64)
      have hr30_pts : s0_pts.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1612#64 := by
        simp [s0_pts, wp_norm, arm64_norm]
      refine SepWPp.weaken_pre
        (by
          dsimp only [Frame_pts, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
          rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpts16]
          exact Entails.of_eq (by sep_ac_rfl))
        (sepWPp_bind_lscl_st_eq hcl3 hr30_pts
          (pts_outer_loop_placed hshim halloc s0_pts fsp ptsPtr hfsp_align pb.pts 0 [] st s3 Frame_pts
            hFit_pts hpts_ne (by omega) rfl (fun bs hbs => by have := hpts_max bs hbs; omega)
            hpc3 hrun3 hsp3 hx21_3 hx23_3 hx24_3 hx25_3
            (by rw [htr3, htr2, htr1]; rfl)
            ((allocCallPreserved_writeLr_iff s0 s3 _).mpr hacp3)
            (by rw [hvregs3, hvregs2, hvregs1]; rfl)
            (Q := fun sm Pm =>
              (Pm ⊢ ∃∗ errPts : List (List GF16), ⌜errPts.length = 16 ∧ e = .serializationInvalid⌝ ∗
                (vecGF16ListOf A.repAlloc (fsp + 480#64) errPts ∗
                 arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * 0)) pb.pts ∗
                 cells (fsp + 456#64) 3 ∗
                 A.pool lim (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) sm ∗
                 stackAt fsp allocHookStack ∗ Frame_pts)) ∧
              (sm.sp = fsp ∧ sm.readReg64 .x1 = s3.readReg64 .x1 ∧ sm.trace = s0.trace ∧
               AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
            (fun sm tail' hdec_ok _ _ _ _ _ _ _ _ => by
              rw [hdec] at hdec_ok; cases hdec_ok)
            (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m _ htrm hacpm hvregsm => by
              rw [hdec] at hdec_err; injection hdec_err with he_eq
              exact SepWPp.done (hpcm.trans hr30_pts.symm) hrunm
                ⟨Entails.sepExists_right errPts (Entails.pure_right ⟨herr_len, he_eq⟩ (Entails.refl _)),
                 hspm, hx1m, htrm,
                 (allocCallPreserved_writeLr_iff s0 sm _).mp hacpm, hvregsm⟩))
          ?_)
      intro sm hpcm hrunm hclm ⟨hspm, hx1m, htrm, hacpm, hvregsm⟩
      apply SepWPp.exists_elim; intro errPts
      apply SepWPp.pure_left; rintro ⟨herr_len, rfl⟩
      have herr := from_pb_err_pts_cl_placed hdealloc_sat
        (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) s0 sm hclm
        fsp out pbA v64 hfsp pb errPts herr_len
        hsp0_align hpcm hrunm hspm (hx1m.trans hx1_3) htrm hacpm hvregsm hlr0
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 sm st out pbA pb (.error .serializationInvalid)
          (encoderFromPbPtsLoopEvents pb.pts) hEnv_pts _ R herr)
      dsimp only [Frame_pts, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, stackAt_dropGluePoly16_split_bottom fsp]
      have hpb := protoPolyEncoder_close A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb
      rw [hpts16, hpolys0] at hpb
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ 16#64) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ 0#64) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
          (memRegion out polyEncoderSize ∗
           vecGF16ListOf A.repAlloc (fsp + 480#64) errPts ∗
           cells fsp 7 ∗
           ((fsp + 56#64) ↦₆₄ out) ∗
           ((fsp + 64#64) ↦₆₄ v64) ∗
           memRegion (fsp + 72#64) 384 ∗
           cells (fsp + 456#64) 3 ∗
           cells (fsp + 864#64) 4 ∗
           cells (fsp + 896#64) 3 ∗
           memRegion (fsp + 920#64) 8 ∗
           (memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack) ∗
           savedCells s0 ∗
           A.pool lim (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) sm) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by sep_ac_rfl))
  · by_cases hcase_polys : pb.pts.length = 0 ∧ pb.polys.length = 16
    · obtain ⟨hpts0, hpolys16⟩ := hcase_polys
      have hEnv_polys :
          EncoderFromPbAllocEnv pb
            (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) :=
        Or.inr (Or.inr ⟨hpts0, hpolys16, rfl⟩)
      obtain ⟨hFit_init, hFit_loop⟩ :=
        (fitsEvents_append M lim encoderFromPbPolysInitEvents
          (encoderFromPbPolysLoopEvents pb.polys) st).mp (hEnv _ hEnv_polys)
      rw [fromPbResult_eq_of_polys pb hpts0 hpolys16]
      have hdisp := from_pb_header_polys_placed (ext := ext) s1 fsp out pbA
        (savedCells s0 ∗
         stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
         memRegion out polyEncoderSize ∗
         ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 32#64) ↦₆₄ polysPtr) ∗
         ((pbA + 48#64) ↦₃₂ pb.idx) ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
         protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
         A.pool lim st s1)
        hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
      refine SepWPp.weaken_pre
        (by rw [hpts0, hpolys16]; exact Entails.of_eq (by sep_ac_rfl))
        (sepWPp_seq_vm_lscl hcl1 hdisp ?_)
      intro s2 hpc2 hrun2 hcl2 hvm2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hacp12, hvregs2⟩
      have hacp2 := allocCallPreserved_trans hacp1 hacp12
      rw [← A.pool_of_vmPreserved hvm2, stack_split_for_polys s0.sp, ← hfsp]
      let Frame_init : SepProp :=
        savedCells s0 ∗
        memRegion (fsp - 4128#64) 32 ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        memRegion out polyEncoderSize ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ 0#64) ∗
        ((pbA + 40#64) ↦₆₄ 16#64) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb
      let s0_init := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1204#64)
      have hr30_init : s0_init.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1204#64 := by
        simp [s0_init, wp_norm, arm64_norm]
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [Frame_init]; sep_ac_rfl))
        (sepWPp_bind_lscl_st_eq hcl2 hr30_init
          (polys_init_zero_headers_placed hshim halloc st hFit_init s0_init s2 fsp out pbA polysPtr
            hfsp_align Frame_init hpc2 hrun2 hsp2 hx0_2 hx1_2 hx29_2
            (by rw [htr2, htr1]; rfl)
            ((allocCallPreserved_writeLr_iff s0 s2 _).mpr hacp2)
            (by rw [hvregs2, hvregs1]; rfl)
            (Q := fun sm Pm =>
              (Pm ⊢ cells fsp 7 ∗
                ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
                ((pbA + 32#64) ↦₆₄ polysPtr) ∗
                zeroPolySlotsAt A.repAlloc (fsp + 480#64) 16 ∗
                A.pool lim (M.stepEvents encoderFromPbPolysInitEvents st) sm ∗
                stackAt fsp allocHookStack ∗ Frame_init) ∧
              (sm.sp = fsp ∧ sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = fsp + 864#64 ∧
               sm.readReg64 .x24 = polysPtr ∧ sm.readReg64 .x28 = 0#64 ∧
               sm.readReg64 .x29 = fsp + 928#64 ∧ sm.trace = s0.trace ∧
               AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
            (fun sm hpcm hrunm hspm hx22m hx23m hx24m hx28m hx29m htrm hacpm hvregsm =>
              SepWPp.done (hpcm.trans hr30_init.symm) hrunm
                ⟨Entails.refl _, hspm, hx22m, hx23m, hx24m, hx28m, hx29m, htrm,
                 (allocCallPreserved_writeLr_iff s0 sm _).mp hacpm, hvregsm⟩))
          ?_)
      intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx22_3, hx23_3, hx24_3, hx28_3, hx29_3, htr3, hacp3, hvregs3⟩
      have hpolys_ne : pb.polys ≠ [] := by
        intro h; simp [h] at hpolys16
      have hvec_nil : vecGF16ListOf A.repAlloc (fsp + 480#64) [] = emp := rfl
      let Frame_polys : SepProp :=
        memRegion out polyEncoderSize ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        memRegion (fsp - 4128#64) 32 ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ 0#64) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ 16#64) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0
      cases hdec : decodePbPolysTotal pb.polys with
      | ok tail =>
        dsimp only
        let s0_polys := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1548#64)
        have hr30_polys : s0_polys.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1548#64 := by
          simp [s0_polys, wp_norm, arm64_norm]
        refine SepWPp.weaken_pre
          (by
            dsimp only [Frame_init, Frame_polys, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
            rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpolys16]
            exact Entails.of_eq (by sep_ac_rfl))
          (sepWPp_bind_lscl_st_eq hcl3 hr30_polys
            (polys_outer_loop_placed hshim halloc hdealloc s0_polys fsp polysPtr hfsp_align
              pb.polys 0 [] (M.stepEvents encoderFromPbPolysInitEvents st) s3 Frame_polys
              hFit_loop hpolys_ne (by omega) rfl
              hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3
              ((allocCallPreserved_writeLr_iff s0 s3 _).mpr hacp3) hvregs3
              (Q := fun sm Pm =>
                (Pm ⊢ vecGF16ListOf A.repAlloc (fsp + 480#64) ([] ++ tail.map Poly.coefficients) ∗
                  arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * 0)) pb.polys ∗
                  cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
                  A.pool lim
                    (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st) sm ∗
                  stackAt fsp allocHookStack ∗ Frame_polys) ∧
                (sm.sp = fsp ∧ sm.trace = s0.trace ∧
                 AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
              (fun sm tail' hdec_ok hpcm hrunm hspm _ htrm hacpm hvregsm => by
                rw [hdec] at hdec_ok; injection hdec_ok with htail_eq; subst htail_eq
                rw [← M.stepEvents_append]
                exact SepWPp.done (hpcm.trans hr30_polys.symm) hrunm
                  ⟨Entails.refl _, hspm, htrm,
                   (allocCallPreserved_writeLr_iff s0 sm _).mp hacpm, hvregsm⟩)
              (fun sm errPolys hdec_err _ _ _ _ _ _ _ _ _ => by
                rw [hdec] at hdec_err; cases hdec_err))
            ?_)
        intro sm hpcm hrunm hclm ⟨hspm, htrm, hacpm, hvregsm⟩
        have htail_len : tail.length = 16 := by
          rw [decodePbPolysTotal_length pb.polys tail hdec, hpolys16]
        have hok := from_pb_ok_polys_cl_placed hmemcpy_sat hdealloc_sat
          (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st)
          s0 sm hclm fsp out pbA hfsp ptsCap ptsPtr polysCap polysPtr pb tail htail_len
          hsp0_align hpcm hrunm hspm htrm hacpm hvregsm hlr0
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_exit_placed s0 sm st out pbA pb
            (.ok { idx := pb.idx, s := .polys tail })
            (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys)
            hEnv_polys _ R hok)
        dsimp only [Frame_polys, List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, hpts0, hpolys16]
        exact Entails.of_eq (by sep_ac_rfl)
      | error e =>
        dsimp only
        let s0_polys := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1496#64)
        have hr30_polys : s0_polys.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1496#64 := by
          simp [s0_polys, wp_norm, arm64_norm]
        refine SepWPp.weaken_pre
          (by
            dsimp only [Frame_init, Frame_polys, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
            rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpolys16]
            exact Entails.of_eq (by sep_ac_rfl))
          (sepWPp_bind_lscl_st_eq hcl3 hr30_polys
            (polys_outer_loop_placed hshim halloc hdealloc s0_polys fsp polysPtr hfsp_align
              pb.polys 0 [] (M.stepEvents encoderFromPbPolysInitEvents st) s3 Frame_polys
              hFit_loop hpolys_ne (by omega) rfl
              hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3
              ((allocCallPreserved_writeLr_iff s0 s3 _).mpr hacp3) hvregs3
              (Q := fun sm Pm =>
                (Pm ⊢ ∃∗ errPolys : List (List GF16), ⌜errPolys.length = 16 ∧ e = .serializationInvalid⌝ ∗
                  (vecGF16ListOf A.repAlloc (fsp + 480#64) errPolys ∗
                   arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * 0)) pb.polys ∗
                   cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
                   A.pool lim
                     (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st) sm ∗
                   stackAt fsp allocHookStack ∗ Frame_polys)) ∧
                (sm.sp = fsp ∧ sm.readReg64 .x19 = 2#64 ∧
                 sm.trace = s0.trace ∧ AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
              (fun sm tail' hdec_ok _ _ _ _ _ _ _ => by
                rw [hdec] at hdec_ok; cases hdec_ok)
              (fun sm errPolys hdec_err herr_len hpcm hrunm hspm hx19m _ htrm hacpm hvregsm => by
                rw [hdec] at hdec_err; injection hdec_err with he_eq
                rw [← M.stepEvents_append]
                exact SepWPp.done (hpcm.trans hr30_polys.symm) hrunm
                  ⟨Entails.sepExists_right errPolys (Entails.pure_right ⟨herr_len, he_eq⟩ (Entails.refl _)),
                   hspm, hx19m, htrm,
                   (allocCallPreserved_writeLr_iff s0 sm _).mp hacpm, hvregsm⟩))
            ?_)
        intro sm hpcm hrunm hclm ⟨hspm, hx19m, htrm, hacpm, hvregsm⟩
        apply SepWPp.exists_elim; intro errPolys
        apply SepWPp.pure_left; rintro ⟨herr_len, rfl⟩
        have herr := from_pb_err_polys_cl_placed hdealloc_sat
          (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st)
          s0 sm hclm fsp out pbA hfsp pb errPolys herr_len
          hsp0_align hpcm hrunm hspm hx19m htrm hacpm hvregsm hlr0
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_exit_placed s0 sm st out pbA pb (.error .serializationInvalid)
            (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys)
            hEnv_polys _ R herr)
        dsimp only [Frame_polys, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, stackAt_dropGluePoly16_split_bottom fsp]
        have hpb := protoPolyEncoder_close A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb
        rw [hpts0, hpolys16] at hpb
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
             ((pbA + 16#64) ↦₆₄ 0#64) ∗
             ((pbA + 32#64) ↦₆₄ polysPtr) ∗
             ((pbA + 40#64) ↦₆₄ 16#64) ∗
             ((pbA + 48#64) ↦₃₂ pb.idx) ∗
             arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
             arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
             protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
            (memRegion out polyEncoderSize ∗
             vecGF16ListOf A.repAlloc (fsp + 480#64) errPolys ∗
             cells fsp 7 ∗
             ((fsp + 56#64) ↦₆₄ out) ∗
             ((fsp + 64#64) ↦₆₄ pbA) ∗
             memRegion (fsp + 72#64) 384 ∗
             cells (fsp + 456#64) 3 ∗
             cells (fsp + 864#64) 4 ∗
             cells (fsp + 896#64) 3 ∗
             memRegion (fsp + 920#64) 8 ∗
             (memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack) ∗
             savedCells s0 ∗
             A.pool lim
               (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st) sm)
            by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by sep_ac_rfl))
    · have hEnv_nil : EncoderFromPbAllocEnv pb [] := Or.inl rfl
      rw [fromPbResult_eq_of_err pb hcase_pts hcase_polys]
      have hdisp := from_pb_header_err_placed (ext := ext) s1 fsp out pbA
        pb.pts.length pb.polys.length hnPts hnPolys hcase_pts hcase_polys
        (savedCells s0 ∗
         stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
         memRegion out polyEncoderSize ∗
         ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 32#64) ↦₆₄ polysPtr) ∗
         ((pbA + 48#64) ↦₃₂ pb.idx) ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
         protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
         A.pool lim st s1)
        hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (sepWPp_seq_vm_lscl hcl1 hdisp ?_)
      intro s2 hpc2 hrun2 hcl2 hvm2 ⟨hsp2, hx0_2, hx1_2, _, htr2, hacp12, hvregs2⟩
      have hacp2 := allocCallPreserved_trans hacp1 hacp12
      rw [← A.pool_of_vmPreserved hvm2]
      have herr := from_pb_err_header_cl_placed hdealloc_sat (M.stepEvents [] st) s0 s2 hcl2
        out pbA pb hsp0_align hpc2 hrun2 hsp2 hx0_2 hx1_2 (by rw [htr2, htr1])
        hacp2 (by rw [hvregs2, hvregs1]) hlr0
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 s2 st out pbA pb (.error .serializationInvalid)
          [] hEnv_nil _ R herr)
      have hpb := protoPolyEncoder_close A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
          (memRegion out polyEncoderSize ∗
           savedCells s0 ∗
           stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
           A.pool lim (M.stepEvents [] st) s2) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by sep_ac_rfl))

/-- `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
    satisfies `withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)` on
    `libsignalSessionLib.blockProgram lsmpl 374`. -/
theorem encoder_from_pb_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 374 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  ls_to_blockProgram
    (encoder_from_pb_cl_placed_ok_ext hshim_sat halloc_sat hdealloc_sat hmemcpy_sat)

/-- Retargetable `encoder_from_pb_cl_on` on any block `idx`'s program. -/
theorem encoder_from_pb_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  ls_subroutine_ok_of_block
    (encoder_from_pb_cl_placed_ok_ext hshim_sat halloc_sat hdealloc_sat hmemcpy_sat) hidx

/-- Retargetable `encoder_from_pb_mem_on` on any block `idx`'s program. -/
theorem encoder_from_pb_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 374)
      (withMemEq m (encoderFromPbSpec M A lim)) :=
  lscall_blk_cl
    (encoder_from_pb_cl_placed_ok_ext hshim_sat halloc_sat hdealloc_sat hmemcpy_sat) hcl hidx

/-- Placed `subroutine_ok` for `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
    retargeted onto Block `333` (`lsProg_333`). -/
theorem encoder_from_pb_on_333_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  encoder_from_pb_cl_on (callerProg := lsProg_333 (Rust.withPanics ext))
    hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlacedBudget
