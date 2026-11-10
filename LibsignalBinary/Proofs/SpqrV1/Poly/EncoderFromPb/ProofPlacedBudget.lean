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
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ExitPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlacedBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Top-Level Proof for `<PolyEncoder>::from_pb`

Proves `encoder_from_pb_placed_ok_ext` and `encoder_from_pb_placed_ok_x` on Block `374` under
`RustCliAllocBudget M` and `EncoderFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkLib_374 blkLib_eq_374 blkPC_374 blkPl_374 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (
  CHUNK_SIZE GF16 NUM_POLYS Point Poly PolyEncoder PolynomialError ProtoPolynomialEncoder
)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
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
  bv384_toNat' bv8_toNat' bv_add_lit_add_lit bv_lit_add_lit
  decodePbPointsTotal decodePbPointsTotal_length decodePbPointsTotal_value_length_le
  decodePbPolysTotal decodePbPolysTotal_length emptySlotsAt
  encoderFromPbStack fromPbResult fromPbResult_eq_of_err
  fromPbResult_eq_of_polys fromPbResult_eq_of_pts
  length_vecHeadersBytesOf ofNat_ne_16 ofNat_ne_zero_of_pos
  protoPolyEncoderRest protoPolyEncoder_close protoPolyEncoder_open
  savedCells sepWP_cells_succ sepWP_cells_zero sepWP_pure_left
  sp_sub_16_add_8' sp_sub_24_add_8' sp_sub_32_add_8' sp_sub_40_add_8'
  sp_sub_48_add_8' sp_sub_56_add_8' sp_sub_64_add_8' sp_sub_72_add_8'
  sp_sub_80_add_8' sp_sub_88_add_8' sp_sub_96_add_16' sp_sub_96_add_32'
  sp_sub_96_add_48' sp_sub_96_add_64' sp_sub_96_add_8' sp_sub_96_add_80'
  sp_sub_96_sub_928'
  spqrRustAllocSym spqrRustDeallocSym spqrRustNoAllocShimSym
  stackAt_dropGluePoly16_split_bottom stackAt_encoderFromPb_split_96
  stack_split_for_polys stack_split_for_pts
  vecGF16HeapList vecGF16ListOf_entails_headers_heaps vecHeadersBytesOf zeroPolySlotsAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved fitsEvents_append
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (
  EncoderFromPbAllocEnv EncoderFromPbEnv EncoderFromPbPlacedOkExt EncoderFromPbPlacedOkX
  encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents encoderFromPbPtsLoopEvents
  encoderFromPbSpec encoderFromPbSpecX_of_encoderFromPbSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ExitPlacedBudget (
  from_pb_err_header_placed from_pb_err_polys_placed from_pb_err_pts_placed
  from_pb_ok_copy_out_placed_of_subroutine
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget (
  polys_init_zero_headers_placed
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlacedBudget (
  polys_outer_loop_placed
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlacedBudget (
  pts_init_empty_headers_placed pts_outer_loop_placed
)

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  bv384_toNat' bv8_toNat'
  sp_sub_96_add_8' sp_sub_96_add_16' sp_sub_96_add_32' sp_sub_96_add_48'
  sp_sub_96_add_64' sp_sub_96_add_80' sp_sub_88_add_8' sp_sub_80_add_8'
  sp_sub_72_add_8' sp_sub_64_add_8' sp_sub_56_add_8' sp_sub_48_add_8'
  sp_sub_40_add_8' sp_sub_32_add_8' sp_sub_24_add_8' sp_sub_16_add_8'
  sp_sub_96_sub_928'
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

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

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s : State} {tp : BitVec 64}
    {P P_mid : SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P_mid (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.weaken_pre hent hwp

private theorem seq_vm_wpp {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid ret : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q_mid sm →
      SepWPp (P.rebase b Hk) ret sm P_mid Q Qp) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQm⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hQm))

/-! ## Placed Success Exits (`+1548` & `+1648`) and Prologue / Header Steppers -/

/-- Budget-threaded placed `.polys` success exit (`+1548 -> s0.lr`, subroutine hypothesis form). -/
theorem from_pb_ok_polys_placed_of_subroutine [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (s0 s : State) (st : M.σ) (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (polys : List Poly) (hpolys_len : polys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1548#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hacp : AllocCallPreserved s0 s)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A.repAlloc (fsp + 480#64) (polys.map Poly.coefficients) ∗
        memRegion out polyEncoderSize ∗ cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗ cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗ memRegion (fsp - 4128#64) 32 ∗
        stackAt fsp allocHookStack ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok { idx := pb.idx, s := .polys polys }) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧ AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
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
  have hmemcpy' := hmemcpy
  dsimp only [allocMemcpyVmSpec, BitVec.ofNat_eq_ofNat] at hmemcpy'
  conv => arg 4; pattern (memRegion (fsp + 72#64) 384); rw [← hbs_len]
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
  have hfsp_eq := hfsp_fn trivial
  refine SepWP.weaken_pre ?_
    (from_pb_ok_copy_out_placed_of_subroutine hmemcpy hdrop_pb s0 _ st fsp out pbA pbA 1#64
      hfsp_eq ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .polys polys }
      pins (polys.map Poly.coefficients) hpins_len hvecs_len ?_
      hsp0_align (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal)
      (allocCallPreserved_step hacp_mc) hlr0)
  · have hsrc : ((fsp + 480#64) ↦ₛ vecHeadersBytesOf pins (polys.map Poly.coefficients)) ⊢
        memRegion (fsp + 480#64) 384 := by
      rw [← hbs_len]; exact ProofLib.pointsToBytes_entails_memRegion (fsp + 480#64) _
    refine Entails.trans
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
         savedCells s0 ∗ A.pool lim st _) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hsrc) (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPolysTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [polyListOf_eq_vecGF16ListOf]
    have hp : polys.length = NUM_POLYS := hpolys_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 1#64) ∗ vecGF16ListOf A.repAlloc (out + 8#64) (polys.map Poly.coefficients)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (Entails.pure_right hp (Entails.refl _)))
      (Entails.of_eq (by sep_ac_rfl))

theorem from_pb_ok_polys_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (s0 s : State) (st : M.σ) (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (polys : List Poly) (hpolys_len : polys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1548#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hacp : AllocCallPreserved s0 s)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A.repAlloc (fsp + 480#64) (polys.map Poly.coefficients) ∗
        memRegion out polyEncoderSize ∗ cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗ cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗ memRegion (fsp - 4128#64) 32 ∗
        stackAt fsp allocHookStack ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok { idx := pb.idx, s := .polys polys }) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧ AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace) :=
  from_pb_ok_polys_placed_of_subroutine (spqr_hook_ok_of_mem hmemcpy_sat) hdrop_pb
    s0 s st fsp out pbA hfsp ptsCap ptsPtr polysCap polysPtr pb polys hpolys_len
    hsp0_align hpc hrun hsp htrace hvregs hacp hlr0

/-- Budget-threaded placed `.points` success exit (`+1648 -> +1572 -> s0.lr`, subroutine form). -/
theorem from_pb_ok_pts_placed_of_subroutine [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (s0 s : State) (st : M.σ) (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (pts : List Point) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1648#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hacp : AllocCallPreserved s0 s)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A.repAlloc (fsp + 480#64) (pts.map Point.value) ∗
        memRegion out polyEncoderSize ∗ cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗ cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗ memRegion (fsp - 4128#64) 32 ∗
        stackAt fsp allocHookStack ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok { idx := pb.idx, s := .points pts }) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧ AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
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
  have hmemcpy' := hmemcpy
  dsimp only [allocMemcpyVmSpec, BitVec.ofNat_eq_ofNat] at hmemcpy'
  conv => arg 4; pattern (memRegion (fsp + 72#64) 384); rw [← hbs_len]
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
  have hfsp_eq := hfsp_fn trivial
  refine SepWP.weaken_pre ?_
    (from_pb_ok_copy_out_placed_of_subroutine hmemcpy hdrop_pb s0 _ st fsp out pbA v64 0#64
      hfsp_eq ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .points pts }
      pins (pts.map Point.value) hpins_len hvecs_len ?_
      hsp0_align (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal)
      (allocCallPreserved_step hacp_mc) hlr0)
  · have hsrc : ((fsp + 480#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ⊢
        memRegion (fsp + 480#64) 384 := by
      rw [← hbs_len]; exact ProofLib.pointsToBytes_entails_memRegion (fsp + 480#64) _
    refine Entails.trans
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
         savedCells s0 ∗ A.pool lim st _) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hsrc) (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [pointListOf_eq_vecGF16ListOf]
    have hp : pts.length = NUM_POLYS := hpts_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 0#64) ∗ vecGF16ListOf A.repAlloc (out + 8#64) (pts.map Point.value)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono_left (Entails.pure_right (And.intro hp hpts_bound) (Entails.refl _)))
      (Entails.of_eq (by sep_ac_rfl))

theorem from_pb_ok_pts_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (s0 s : State) (st : M.σ) (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (pts : List Point) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1648#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hacp : AllocCallPreserved s0 s)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A.repAlloc (fsp + 480#64) (pts.map Point.value) ∗
        memRegion out polyEncoderSize ∗ cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗ cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗ memRegion (fsp - 4128#64) 32 ∗
        stackAt fsp allocHookStack ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok { idx := pb.idx, s := .points pts }) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧ AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace) :=
  from_pb_ok_pts_placed_of_subroutine (spqr_hook_ok_of_mem hmemcpy_sat) hdrop_pb
    s0 s st fsp out pbA v64 hfsp ptsCap ptsPtr polysCap polysPtr pb pts hpts_len hpts_bound
    hsp0_align hpc hrun hsp hx1 htrace hvregs hacp hlr0

/-- Placed prologue register save and stack allocation (`+0 -> +32`), preserving `VmPreserved`
    and `AllocCallPreserved`. -/
theorem from_pb_save_regs_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s0.pc = (blkPl_374).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = pbA) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 32#64) s0
      (stackAt s0.sp encoderFromPbStack ∗ Frame)
      (fun sm Pm =>
        VmPreserved s0 sm ∧
        (Pm ⊢ savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗ Frame) ∧
        sm.sp = s0.sp - 1024#64 ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = (s0.sp - 1024#64) + 928#64 ∧
        sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  rw [stackAt_encoderFromPb_split_96 s0.sp]
  rw [sepConj_comm (stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928)) (cells (s0.sp - 96#64) 12),
      sepConj_assoc]
  iterate 12 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [sp_sub_96_add_8', sp_sub_88_add_8', sp_sub_80_add_8', sp_sub_72_add_8',
    sp_sub_64_add_8', sp_sub_56_add_8', sp_sub_48_add_8', sp_sub_40_add_8', sp_sub_32_add_8',
    sp_sub_24_add_8', sp_sub_16_add_8', sepConj_assoc]
  by_vm_steps (
    wp_steps
    refine align_pre_vm ?_ ?_
    · unfold savedCells
      exact Entails.of_eq (by sep_ac_rfl)
    · dsimp only [AllocCallPreserved]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨rfl, Entails.refl _, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_,
        by wp_norm_goal, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by wp_norm_goal⟩
      wp_norm_goal
  )

/-- Placed header dispatch when `pb.pts.length = 16` and `pb.polys.length = 0` (`+32 -> +56`),
    preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem from_pb_header_pts_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 56#64) s
      (((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 40#64) ↦₆₄ 0#64) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 40#64) ↦₆₄ 0#64) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  by_vm_steps (
    wp_steps
    dsimp only [AllocCallPreserved]
    wp_done
  )

/-- Placed header dispatch when `pb.pts.length = 0` and `pb.polys.length = 16` (`+32 -> +556`),
    preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem from_pb_header_polys_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 556#64) s
      (((pbA + 16#64) ↦₆₄ 0#64) ∗
        ((pbA + 40#64) ↦₆₄ 16#64) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 0#64) ∗
          ((pbA + 40#64) ↦₆₄ 16#64) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  by_vm_steps (
    wp_steps
    dsimp only [AllocCallPreserved]
    wp_done
  )

/-- Placed header dispatch when `¬(nPts = 16 ∧ nPolys = 0)` and `¬(nPts = 0 ∧ nPolys = 16)`
    (`+32 -> +1448`), preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem from_pb_header_err_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64) (nPts nPolys : Nat)
    (hnPts : nPts < 2 ^ 63) (hnPolys : nPolys < 2 ^ 63)
    (hnot_pts : ¬(nPts = 16 ∧ nPolys = 0))
    (hnot_polys : ¬(nPts = 0 ∧ nPolys = 16))
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 1448#64) s
      (((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 nPolys) ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗
          ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 nPolys) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  by_cases hpts0 : nPts = 0
  · subst hpts0
    have hpolys16 : nPolys ≠ 16 := fun h => hnot_polys ⟨rfl, h⟩
    have hne16 : BitVec.ofNat 64 nPolys ≠ 16#64 := ofNat_ne_16 hpolys16 (by omega)
    have hbeq16 : (BitVec.ofNat 64 nPolys == 16#64) = false := beq_eq_false_iff_ne.mpr hne16
    have hbeq16' : (16#64 == BitVec.ofNat 64 nPolys) = false := beq_eq_false_iff_ne.mpr hne16.symm
    have hbne16 : (BitVec.ofNat 64 nPolys != 16#64) = true := bne_iff_ne.mpr hne16
    have hbne16' : (16#64 != BitVec.ofNat 64 nPolys) = true := bne_iff_ne.mpr hne16.symm
    by_vm_steps (
      wp_steps
      dsimp only [AllocCallPreserved]
      wp_done
    )
  · have hne0 : BitVec.ofNat 64 nPts ≠ 0#64 := ofNat_ne_zero_of_pos (by omega) (by omega)
    have hbeq0 : (BitVec.ofNat 64 nPts == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
    have hbne0 : (BitVec.ofNat 64 nPts != 0#64) = true := bne_iff_ne.mpr hne0
    by_cases hpolys0 : nPolys = 0
    · subst hpolys0
      have hpts16 : nPts ≠ 16 := fun h => hnot_pts ⟨h, rfl⟩
      have hne16 : BitVec.ofNat 64 nPts ≠ 16#64 := ofNat_ne_16 hpts16 (by omega)
      have hbeq16 : (BitVec.ofNat 64 nPts == 16#64) = false := beq_eq_false_iff_ne.mpr hne16
      have hbeq16' : (16#64 == BitVec.ofNat 64 nPts) = false := beq_eq_false_iff_ne.mpr hne16.symm
      have hbne16 : (BitVec.ofNat 64 nPts != 16#64) = true := bne_iff_ne.mpr hne16
      have hbne16' : (16#64 != BitVec.ofNat 64 nPts) = true := bne_iff_ne.mpr hne16.symm
      by_vm_steps (
        wp_steps
        dsimp only [AllocCallPreserved]
        wp_done
      )
    · have hne_p0 : BitVec.ofNat 64 nPolys ≠ 0#64 := ofNat_ne_zero_of_pos (by omega) (by omega)
      have hbeq_p0 : (BitVec.ofNat 64 nPolys == 0#64) = false := beq_eq_false_iff_ne.mpr hne_p0
      have hbeq_p0' : (0#64 == BitVec.ofNat 64 nPolys) = false := beq_eq_false_iff_ne.mpr hne_p0.symm
      have hbne_p0 : (BitVec.ofNat 64 nPolys != 0#64) = true := bne_iff_ne.mpr hne_p0
      have hbne_p0' : (0#64 != BitVec.ofNat 64 nPolys) = true := bne_iff_ne.mpr hne_p0.symm
      by_vm_steps (
        wp_steps
        dsimp only [AllocCallPreserved]
        wp_done
      )

/-! ## Exit Lift & Top-Level Placed Contracts -/

/-- Lift a budget-threaded exit `SepWP` producing `FreeOnlyEvs evs_free` on top of
    `M.stepEvents evs_alloc st` (where `EncoderFromPbAllocEnv pb evs_alloc`) into the `SepWPp`
    postcondition of `encoderFromPbSpec M A lim`. -/
theorem sepWPp_of_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (s0 s : State) (st : M.σ) (out pbA : BitVec 64) (pb : ProtoPolynomialEncoder)
    (res : Except PolynomialError PolyEncoder)
    (evs_alloc : List AllocEvent) (hEnv_alloc : EncoderFromPbAllocEnv pb evs_alloc)
    (P R : SepProp)
    (h : SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 Reg.lr) s P
      (fun sf Pf =>
        ∃ evs_free, FreeOnlyEvs evs_free ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out res ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs_free (M.stepEvents evs_alloc st)) sf ∗
            stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace)) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ∃∗ evs : List AllocEvent,
              ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ EncoderFromPbEnv pb evs⌝ ∗
              resultPolyEncoderFromPbAt A.repAlloc out res ∗
              memRegion pbA protoPolynomialEncoderSize ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp encoderFromPbStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine SepWPp.of_sepWP (SepWP.mono h
    fun sf Pf hpcf hrunf ⟨evs_free, hfo, hPf, hcs, hacpf, hspf, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  have h1 : sf.mem ⊨ (resultPolyEncoderFromPbAt A.repAlloc out res ∗
      memRegion pbA protoPolynomialEncoderSize ∗
      A.pool lim (M.stepEvents (evs_alloc ++ evs_free) st) sf ∗
      stackAt s0.sp encoderFromPbStack) ∗ R := by
    rw [M.stepEvents_append]
    exact Satisfies.mono (sepConj_mono_left hPf) hmem_f
  have hEnv : EncoderFromPbEnv pb (evs_alloc ++ evs_free) :=
    ⟨evs_alloc, evs_free, rfl, hEnv_alloc, hfo⟩
  refine Satisfies.mono ?_ h1
  exact Entails.sepExists_right (evs_alloc ++ evs_free)
    (Entails.pure_right ⟨htrf, hacpf, hEnv⟩ (Entails.of_eq (by sep_ac_rfl)))

/-- `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`) satisfies
    `encoderFromPbSpec M A lim` under `[LibsignalPlacement]` (`subroutine_ok` callee form). -/
theorem encoder_from_pb_placed_ok_ext_of_subroutine [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec)
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim)) :
    EncoderFromPbPlacedOkExt M A lim ext := by
  unfold EncoderFromPbPlacedOkExt
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA, pb⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [encoderFromPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpts_max, hEnv, hlr0⟩, hmem⟩
  refine ⟨stackAt s0.sp encoderFromPbStack ∗
      (memRegion out polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        A.pool lim st s0),
    R, ?_, ?_⟩
  · exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  dsimp only [encoderFromPbSpec]
  have hpro := from_pb_save_regs_placed (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A.repAlloc pbA pb ∗ A.pool lim st s0)
    hpc0 hrun0 hx0 hx1
  refine seq_vm_wpp hpro ?_
  intro s1 hpc1 hrun1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx29_1, htr1, hacp1, hvregs1⟩
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
      (seq_vm_wpp hdisp ?_)
    intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hacp12, hvregs2⟩
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
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_vm_wpp hinit ?_)
    intro s3 hpc3 hrun3 hvm3
      ⟨hsp3, hx1_3, hx21_3, hx23_3, hx24_3, hx25_3, _, _, _, _, _, _, hx29_3, htr3, hacp23, hvregs3⟩
    have hacp3 := allocCallPreserved_trans hacp2 hacp23
    rw [← A.pool_of_vmPreserved hvm3]
    have hpts_ne : pb.pts ≠ [] := by
      intro h; simp [h] at hpts16
    have hvec_nil : vecGF16ListOf A.repAlloc (fsp + 480#64) [] = emp := rfl
    refine SepWPp.weaken_pre
      (by
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpts16]
        exact Entails.of_eq (by sep_ac_rfl))
      (pts_outer_loop_placed hshim halloc s0 fsp ptsPtr hfsp_align pb.pts 0 [] st s3
        (memRegion out polyEncoderSize ∗
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
         savedCells s0)
        hFit_pts hpts_ne (by omega) rfl (fun bs hbs => by have := hpts_max bs hbs; omega)
        hpc3 hrun3 hsp3 hx21_3 hx23_3 hx24_3 hx25_3
        (by rw [htr3, htr2, htr1]) hacp3 (by rw [hvregs3, hvregs2, hvregs1])
        (fun sm tail hdec_ok hpcm hrunm hspm hx1m _ htrm hacpm hvregsm => ?_)
        (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m _ htrm hacpm hvregsm => ?_))
    · rw [hdec_ok]; dsimp only
      have htail_len : tail.length = 16 := by
        rw [decodePbPointsTotal_length pb.pts tail hdec_ok, hpts16]
      have htail_bound : ∀ pt ∈ tail, pt.value.length ≤ 0x0555555555555555 :=
        decodePbPointsTotal_value_length_le pb.pts tail hdec_ok hpts_max
      have hok := from_pb_ok_pts_placed_of_subroutine hmemcpy hdrop_pb s0 sm
        (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) fsp out pbA v64 hfsp
        ptsCap ptsPtr polysCap polysPtr pb tail htail_len htail_bound hsp0_align
        hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm hacpm hlr0
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 sm st out pbA pb
          (.ok { idx := pb.idx, s := .points tail })
          (encoderFromPbPtsLoopEvents pb.pts) hEnv_pts _ R hok)
      dsimp only [List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, hpts16, hpolys0]
      exact Entails.of_eq (by sep_ac_rfl)
    · rw [hdec_err]; dsimp only
      have herr := from_pb_err_pts_placed hdrop16 hdrop_pb s0 sm
        (M.stepEvents (encoderFromPbPtsLoopEvents pb.pts) st) fsp out pbA v64 hfsp
        pb errPts herr_len hsp0_align hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm hacpm hlr0
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 sm st out pbA pb (.error .serializationInvalid)
          (encoderFromPbPtsLoopEvents pb.pts) hEnv_pts _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
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
        (seq_vm_wpp hdisp ?_)
      intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hacp12, hvregs2⟩
      have hacp2 := allocCallPreserved_trans hacp1 hacp12
      rw [← A.pool_of_vmPreserved hvm2, stack_split_for_polys s0.sp, ← hfsp]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (polys_init_zero_headers_placed hshim halloc st hFit_init s0 s2 fsp out pbA polysPtr hfsp_align
          (savedCells s0 ∗
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
           protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb)
          hpc2 hrun2 hsp2 hx0_2 hx1_2 hx29_2 (by rw [htr2, htr1]) hacp2 (by rw [hvregs2, hvregs1]) ?_)
      intro s3 hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3 hacp3 hvregs3
      have hpolys_ne : pb.polys ≠ [] := by
        intro h; simp [h] at hpolys16
      have hvec_nil : vecGF16ListOf A.repAlloc (fsp + 480#64) [] = emp := rfl
      refine SepWPp.weaken_pre
        (by
          dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
          rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpolys16]
          exact Entails.of_eq (by sep_ac_rfl))
        (polys_outer_loop_placed hshim halloc hdealloc s0 fsp polysPtr hfsp_align
          pb.polys 0 [] (M.stepEvents encoderFromPbPolysInitEvents st) s3
          (memRegion out polyEncoderSize ∗
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
           savedCells s0)
          hFit_loop hpolys_ne (by omega) rfl
          hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3 hacp3 hvregs3
          (fun sm tail hdec_ok hpcm hrunm hspm _ htrm hacpm hvregsm => ?_)
          (fun sm errPolys hdec_err herr_len hpcm hrunm hspm hx19m _ htrm hacpm hvregsm => ?_))
      · rw [hdec_ok, ← M.stepEvents_append]; dsimp only
        have htail_len : tail.length = 16 := by
          rw [decodePbPolysTotal_length pb.polys tail hdec_ok, hpolys16]
        have hok := from_pb_ok_polys_placed_of_subroutine hmemcpy hdrop_pb s0 sm
          (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st)
          fsp out pbA hfsp ptsCap ptsPtr polysCap polysPtr pb tail htail_len hsp0_align
          hpcm hrunm hspm htrm hvregsm hacpm hlr0
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_exit_placed s0 sm st out pbA pb
            (.ok { idx := pb.idx, s := .polys tail })
            (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys)
            hEnv_polys _ R hok)
        dsimp only [List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, hpts0, hpolys16]
        exact Entails.of_eq (by sep_ac_rfl)
      · rw [hdec_err, ← M.stepEvents_append]; dsimp only
        have herr := from_pb_err_polys_placed hdrop16 hdrop_pb s0 sm
          (M.stepEvents (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys) st)
          fsp out pbA hfsp pb errPolys herr_len
          hsp0_align hpcm hrunm hspm hx19m htrm hvregsm hacpm hlr0
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_exit_placed s0 sm st out pbA pb (.error .serializationInvalid)
            (encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys)
            hEnv_polys _ R herr)
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
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
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_vm_wpp hdisp ?_)
      intro s2 hpc2 hrun2 hvm2 ⟨hsp2, hx0_2, hx1_2, _, htr2, hacp12, hvregs2⟩
      have hacp2 := allocCallPreserved_trans hacp1 hacp12
      rw [← A.pool_of_vmPreserved hvm2]
      have herr := from_pb_err_header_placed hdrop_pb s0 s2 (M.stepEvents [] st) out pbA pb hsp0_align
        hpc2 hrun2 hsp2 hx0_2 hx1_2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1]) hacp2 hlr0
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

theorem encoder_from_pb_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim)) :
    EncoderFromPbPlacedOkExt M A lim ext :=
  encoder_from_pb_placed_ok_ext_of_subroutine
    (spqr_hook_ok_of_mem hshim_sat)
    (spqr_hook_ok_of_mem halloc_sat)
    (spqr_hook_ok_of_mem hdealloc_sat)
    (spqr_hook_ok_of_mem hmemcpy_sat)
    hdrop16 hdrop_pb

theorem encoder_from_pb_placed_ok_x_of_subroutine [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec)
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim)) :
    EncoderFromPbPlacedOkX M A lim ext :=
  encoderFromPbSpecX_of_encoderFromPbSpec
    (encoder_from_pb_placed_ok_ext_of_subroutine hshim halloc hdealloc hmemcpy hdrop16 hdrop_pb)

theorem encoder_from_pb_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec M A lim))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim)) :
    EncoderFromPbPlacedOkX M A lim ext :=
  encoderFromPbSpecX_of_encoderFromPbSpec
    (encoder_from_pb_placed_ok_ext hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hdrop16 hdrop_pb)

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlacedBudget
