/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Exit
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbExitClPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Placed Top-Level Proof under `LibsignalCodeLoaded` (Block `374`)

Proves `from_pb_ok_polys_cl_placed`, `from_pb_ok_pts_cl_placed`,
`encoder_from_pb_cl_placed_ok_ext`, and `encoder_from_pb_on_333_placed_ok_ext`
for `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
under `[LibsignalPlacement]` with `LibsignalCodeLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L1
open CryptoVerification.SpqrV1.Layout.L22

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

@[local arm64_norm, local wp_norm] private theorem bv384_toNat' : (384#64 : BitVec 64).toNat = 384 := rfl
@[local arm64_norm, local wp_norm] private theorem bv8_toNat' : (8#64 : BitVec 64).toNat = 8 := rfl

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

private theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hq))

private theorem sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop}
    {Q Q_panic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P
      (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm)
      Q_panic)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm →
      SepWPp prog target_pc sm P_mid Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic := by
  intro R hsat hL
  obtain ⟨s', hsteps, hout⟩ := h1 R hsat hL
  rcases hout with ⟨htgt, hrun, P_mid', hsat', hPm, hQm⟩ | hpan | hoom
  · have hcl' : LibsignalCodeLoaded lsmpl s'.mem :=
      LibsignalCodeLoaded.of_keepsFrozen hcl hsteps.keepsFrozen
    have hsat_mid : s'.mem ⊨ P_mid ∗ R :=
      Satisfies.mono (sepConj_mono_left hPm) hsat'
    obtain ⟨s'', hsteps2, hout2⟩ :=
      h2 s' htgt hrun hcl' hQm R hsat_mid (hsteps.codeLoaded hL)
    exact ⟨s'', hsteps.trans hsteps2, hout2⟩
  · exact ⟨s', hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨s', hsteps, Or.inr (Or.inr hoom)⟩

/-- Placed `.polys` success exit (`+1548 -> s0.lr`) under `LibsignalCodeLoaded`. -/
theorem from_pb_ok_polys_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (polys : List LibsignalSpqrV1.Poly) (hpolys_len : polys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1548#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A (fsp + 480#64) (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
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
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.ok { idx := pb.idx, s := .polys polys }) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hvecs_len : (polys.map LibsignalSpqrV1.Poly.coefficients).length = 16 := by
    simp [hpolys_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecGF16ListOf_entails_headers_heaps A
      (polys.map LibsignalSpqrV1.Poly.coefficients) (fsp + 480#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply sepWP_pure_left; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  have hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  simp only [sessionMemcpySpec, BitVec.ofNat_eq_ofNat] at hmemcpy
  refine seq_clean_lscl hcl
    (mid := (blkPl_374).base + 1572#64)
    (P_mid :=
      memRegion out polyEncoderSize ∗
      ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
      vecGF16HeapList A pins (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
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
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0 ∗
      A.pool)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = 1#64 ∧
      sm.readReg64 .x20 = pbA ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    wp_call hmemcpy (fsp + 72#64, fsp + 480#64,
      vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients))
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hsrc : ((fsp + 480#64) ↦ₛ
          vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ⊢
          memRegion (fsp + 480#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion (fsp + 480#64) _
      rw [hsp]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((fsp + 480#64) ↦ₛ
            vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
          (memRegion out polyEncoderSize ∗
           ((fsp + 72#64) ↦ₛ
             vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
           vecGF16HeapList A pins (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
           ((fsp + 56#64) ↦₆₄ out) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           stackAt fsp allocHookStack ∗
           cells fsp 7 ∗
           ((fsp + 64#64) ↦₆₄ pbA) ∗
           cells (fsp + 456#64) 3 ∗
           cells (fsp + 864#64) 4 ∗
           cells (fsp + 896#64) 3 ∗
           memRegion (fsp + 920#64) 8 ∗
           memRegion (fsp - 4128#64) 32 ∗
           ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
           savedCells s0 ∗ A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hsrc) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx8_1, hx20_1, htr1, hvregs1⟩
    refine from_pb_ok_copy_out_cl_placed hmemcpy_sat hdealloc_sat s0 s1 hcl1 fsp out pbA pbA 1#64 (hfsp_fn trivial)
      ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .polys polys }
      pins (polys.map LibsignalSpqrV1.Poly.coefficients) hpins_len hvecs_len ?_
      hsp0_align hpc1 hrun1 hsp1 hx8_1 hx20_1 htr1 hvregs1
    dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPolysTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [EncoderFromPb.polyListOf_eq_vecGF16ListOf]
    have hp : polys.length = NUM_POLYS := hpolys_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 1#64) ∗
         vecGF16ListOf A (out + 8#64) (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (Entails.pure_right hp (Entails.refl _))) ?_
    exact Entails.of_eq (by ac_rfl)

/-- Placed `.points` success exit (`+1648 -> +1572 -> s0.lr`) under `LibsignalCodeLoaded`. -/
theorem from_pb_ok_pts_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (s0 s : State)
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
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16ListOf A (fsp + 480#64) (pts.map Point.value) ∗
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
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.ok { idx := pb.idx, s := .points pts }) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hvecs_len : (pts.map Point.value).length = 16 := by
    simp [hpts_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecGF16ListOf_entails_headers_heaps A
      (pts.map Point.value) (fsp + 480#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply sepWP_pure_left; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  have hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  simp only [sessionMemcpySpec, BitVec.ofNat_eq_ofNat] at hmemcpy
  refine seq_clean_lscl hcl
    (mid := (blkPl_374).base + 1572#64)
    (P_mid :=
      memRegion out polyEncoderSize ∗
      ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
      vecGF16HeapList A pins (pts.map Point.value) ∗
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
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0 ∗
      A.pool)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = 0#64 ∧
      sm.readReg64 .x20 = pbA ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    wp_call hmemcpy (fsp + 72#64, fsp + 480#64,
      vecHeadersBytesOf pins (pts.map Point.value))
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hsrc : ((fsp + 480#64) ↦ₛ
          vecHeadersBytesOf pins (pts.map Point.value)) ⊢
          memRegion (fsp + 480#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion (fsp + 480#64) _
      rw [hsp]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((fsp + 480#64) ↦ₛ
            vecHeadersBytesOf pins (pts.map Point.value)) ∗
          (memRegion out polyEncoderSize ∗
           ((fsp + 72#64) ↦ₛ
             vecHeadersBytesOf pins (pts.map Point.value)) ∗
           vecGF16HeapList A pins (pts.map Point.value) ∗
           ((fsp + 56#64) ↦₆₄ out) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           stackAt fsp allocHookStack ∗
           cells fsp 7 ∗
           ((fsp + 64#64) ↦₆₄ v64) ∗
           cells (fsp + 456#64) 3 ∗
           cells (fsp + 864#64) 4 ∗
           cells (fsp + 896#64) 3 ∗
           memRegion (fsp + 920#64) 8 ∗
           memRegion (fsp - 4128#64) 32 ∗
           ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
           savedCells s0 ∗ A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hsrc) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx8_1, hx20_1, htr1, hvregs1⟩
    refine from_pb_ok_copy_out_cl_placed hmemcpy_sat hdealloc_sat s0 s1 hcl1 fsp out pbA v64 0#64 (hfsp_fn trivial)
      ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .points pts }
      pins (pts.map Point.value) hpins_len hvecs_len ?_
      hsp0_align hpc1 hrun1 hsp1 hx8_1 hx20_1 htr1 hvregs1
    dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [EncoderFromPb.pointListOf_eq_vecGF16ListOf]
    have hp : pts.length = NUM_POLYS := hpts_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 0#64) ∗
         vecGF16ListOf A (out + 8#64) (pts.map Point.value)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (Entails.pure_right (And.intro hp hpts_bound) (Entails.refl _))) ?_
    exact Entails.of_eq (by ac_rfl)

/-- `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
    satisfies `withLsCodeLoaded lsmpl (encoderFromPbSpec A)` on `lsProg_374`. -/
theorem encoder_from_pb_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec) :
    subroutine_ok (lsProg_374 (Rust.withPanics ext)) (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [encoderFromPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpts_max⟩, hmem⟩
  refine ⟨stackAt s0.sp encoderFromPbStack ∗
      (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A pbA pb ∗ A.pool),
    R, ?_, ?_⟩
  · exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  dsimp only [withLsCodeLoaded, encoderFromPbSpec]
  have hpro := from_pb_save_regs_placed (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A pbA pb ∗ A.pool)
    hpc0 hrun0 hx0 hx1
  refine sepWPp_seq_clean_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx29_1, htr1, hvregs1⟩
  let fsp := s0.sp - 1024#64
  have hfsp : fsp = s0.sp - 1024#64 := rfl
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (protoPolyEncoder_open A pbA pb))))) ?_
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
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
       A.pool) by ac_rfl)) ?_
  apply SepWPp.pure_left; rintro ⟨hnPts, hnPolys⟩
  by_cases hcase_pts : pb.pts.length = 16 ∧ pb.polys.length = 0
  · obtain ⟨hpts16, hpolys0⟩ := hcase_pts
    rw [fromPbResult_eq_of_pts pb hpts16 hpolys0]
    have hdisp := from_pb_header_pts_placed (ext := ext) s1 fsp out pbA
      (savedCells s0 ∗
       stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
       memRegion out polyEncoderSize ∗
       ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
       A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre
      (by rw [hpts16, hpolys0]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean_lscl hcl1 hdisp ?_)
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hvregs2⟩
    rw [stack_split_for_pts s0.sp, ← hfsp]
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
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
       A.pool)
      hpc2 hrun2 hsp2 hx0_2 hx1_2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean_lscl hcl2 hinit ?_)
    intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx1_3, hx21_3, hx23_3, hx24_3, hx25_3, _, _, _, _, _, _, hx29_3, htr3, hvregs3⟩
    have hpts_ne : pb.pts ≠ [] := by
      intro h; simp [h] at hpts16
    have hvec_nil : vecGF16ListOf A (fsp + 480#64) [] = emp := rfl
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
      arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0
    cases hdec : decodePbPointsTotal pb.pts with
    | ok tail =>
      dsimp only
      let s0_pts := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1648#64)
      have hr30_pts : s0_pts.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1648#64 := by
        simp [s0_pts, wp_norm, arm64_norm]
      have hloop_raw :=
        pts_outer_loop_placed h_panic hshim_sat halloc_sat s0_pts fsp ptsPtr hfsp_align pb.pts 0 [] s3
          Frame_pts R hpts_ne (by omega) rfl (fun bs hbs => by have := hpts_max bs hbs; omega)
          hpc3 hrun3 hsp3 hx21_3 hx23_3 hx24_3 hx25_3
          (by rw [htr3, htr2, htr1]; rfl)
          (by rw [hvregs3, hvregs2, hvregs1]; rfl)
          (Q := fun sm Pm =>
            (Pm ⊢ vecGF16ListOf A (fsp + 480#64) ([] ++ tail.map Point.value) ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * 0)) pb.pts ∗
              cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame_pts) ∧
            (sm.sp = fsp ∧ sm.readReg64 .x1 = s3.readReg64 .x1 ∧ sm.trace = s0.trace ∧
             calleeSavedVRegs sm = calleeSavedVRegs s0))
          (fun sm tail' hdec_ok hpcm hrunm hspm hx1m _ htrm hvregsm => by
            rw [hdec] at hdec_ok; injection hdec_ok with htail_eq; subst htail_eq
            exact SepWPp.done (hpcm.trans hr30_pts.symm) hrunm
              ⟨Entails.refl _, hspm, hx1m, htrm, hvregsm⟩)
          (fun sm errPts hdec_err _ _ _ _ _ _ _ _ => by
            rw [hdec] at hdec_err; cases hdec_err)
      rw [hr30_pts] at hloop_raw
      refine SepWPp.weaken_pre
        (by
          dsimp only [Frame_pts, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
          rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpts16]
          exact Entails.of_eq (by ac_rfl))
        (sepWPp_bind_lscl hcl3 hloop_raw ?_)
      intro sm hpcm hrunm hclm ⟨hspm, hx1m, htrm, hvregsm⟩
      have htail_len : tail.length = 16 := by
        rw [decodePbPointsTotal_length pb.pts tail hdec, hpts16]
      have htail_bound : ∀ pt ∈ tail, pt.value.length ≤ 0x0555555555555555 :=
        decodePbPointsTotal_value_length_le pb.pts tail hdec hpts_max
      have hok := from_pb_ok_pts_cl_placed hmemcpy_sat hdealloc_sat s0 sm hclm fsp out pbA v64 hfsp
        ptsCap ptsPtr polysCap polysPtr pb tail htail_len htail_bound hsp0_align
        hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 sm out pbA (.ok { idx := pb.idx, s := .points tail }) _ R hok)
      dsimp only [Frame_pts, List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, hpts16, hpolys0]
      exact Entails.of_eq (by ac_rfl)
    | error e =>
      dsimp only
      let s0_pts := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1612#64)
      have hr30_pts : s0_pts.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1612#64 := by
        simp [s0_pts, wp_norm, arm64_norm]
      have hloop_raw :=
        pts_outer_loop_placed h_panic hshim_sat halloc_sat s0_pts fsp ptsPtr hfsp_align pb.pts 0 [] s3
          Frame_pts R hpts_ne (by omega) rfl (fun bs hbs => by have := hpts_max bs hbs; omega)
          hpc3 hrun3 hsp3 hx21_3 hx23_3 hx24_3 hx25_3
          (by rw [htr3, htr2, htr1]; rfl)
          (by rw [hvregs3, hvregs2, hvregs1]; rfl)
          (Q := fun sm Pm =>
            (Pm ⊢ ∃∗ errPts : List (List GF16), ⌜errPts.length = 16 ∧ e = .serializationInvalid⌝ ∗
              (vecGF16ListOf A (fsp + 480#64) errPts ∗
               arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * 0)) pb.pts ∗
               cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame_pts)) ∧
            (sm.sp = fsp ∧ sm.readReg64 .x1 = s3.readReg64 .x1 ∧ sm.trace = s0.trace ∧
             calleeSavedVRegs sm = calleeSavedVRegs s0))
          (fun sm tail' hdec_ok _ _ _ _ _ _ _ => by
            rw [hdec] at hdec_ok; cases hdec_ok)
          (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m _ htrm hvregsm => by
            rw [hdec] at hdec_err; injection hdec_err with he_eq
            exact SepWPp.done (hpcm.trans hr30_pts.symm) hrunm
              ⟨Entails.sepExists_right errPts (Entails.pure_right ⟨herr_len, he_eq⟩ (Entails.refl _)),
               hspm, hx1m, htrm, hvregsm⟩)
      rw [hr30_pts] at hloop_raw
      refine SepWPp.weaken_pre
        (by
          dsimp only [Frame_pts, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
          rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpts16]
          exact Entails.of_eq (by ac_rfl))
        (sepWPp_bind_lscl hcl3 hloop_raw ?_)
      intro sm hpcm hrunm hclm ⟨hspm, hx1m, htrm, hvregsm⟩
      apply SepWPp.exists_elim; intro errPts
      apply SepWPp.pure_left; rintro ⟨herr_len, rfl⟩
      have herr := from_pb_err_pts_cl_placed hdealloc_sat s0 sm hclm fsp out pbA v64 hfsp pb errPts herr_len
        hsp0_align hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 sm out pbA (.error .serializationInvalid) _ R herr)
      dsimp only [Frame_pts, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, stackAt_dropGluePoly16_split_bottom fsp]
      have hpb := protoPolyEncoder_close A pbA ptsCap ptsPtr polysCap polysPtr pb
      rw [hpts16, hpolys0] at hpb
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ 16#64) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ 0#64) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
          (memRegion out polyEncoderSize ∗
           vecGF16ListOf A (fsp + 480#64) errPts ∗
           cells fsp 7 ∗
           ((fsp + 56#64) ↦₆₄ out) ∗
           ((fsp + 64#64) ↦₆₄ v64) ∗
           memRegion (fsp + 72#64) 384 ∗
           cells (fsp + 456#64) 3 ∗
           cells (fsp + 864#64) 4 ∗
           cells (fsp + 896#64) 3 ∗
           memRegion (fsp + 920#64) 8 ∗
           (memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack) ∗
           savedCells s0 ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · by_cases hcase_polys : pb.pts.length = 0 ∧ pb.polys.length = 16
    · obtain ⟨hpts0, hpolys16⟩ := hcase_polys
      rw [fromPbResult_eq_of_polys pb hpts0 hpolys16]
      have hdisp := from_pb_header_polys_placed (ext := ext) s1 fsp out pbA
        (savedCells s0 ∗
         stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
         memRegion out polyEncoderSize ∗
         ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 32#64) ↦₆₄ polysPtr) ∗
         ((pbA + 48#64) ↦₃₂ pb.idx) ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
         protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
         A.pool)
        hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
      refine SepWPp.weaken_pre
        (by rw [hpts0, hpolys16]; exact Entails.of_eq (by ac_rfl))
        (sepWPp_seq_clean_lscl hcl1 hdisp ?_)
      intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hvregs2⟩
      rw [stack_split_for_polys s0.sp, ← hfsp]
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
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb
      let s0_init := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1204#64)
      have hr30_init : s0_init.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1204#64 := by
        simp [s0_init, wp_norm, arm64_norm]
      have hinit_raw :=
        polys_init_zero_headers_placed h_panic hshim_sat halloc_sat s0_init s2 fsp out pbA polysPtr hfsp_align
          Frame_init R hpc2 hrun2 hsp2 hx0_2 hx1_2 hx29_2
          (by rw [htr2, htr1]; rfl) (by rw [hvregs2, hvregs1]; rfl)
          (Q := fun sm Pm =>
            (Pm ⊢ cells fsp 7 ∗
              ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
              ((pbA + 32#64) ↦₆₄ polysPtr) ∗
              zeroPolySlotsAt A (fsp + 480#64) 16 ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame_init) ∧
            (sm.sp = fsp ∧ sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = fsp + 864#64 ∧
             sm.readReg64 .x24 = polysPtr ∧ sm.readReg64 .x28 = 0#64 ∧
             sm.readReg64 .x29 = fsp + 928#64 ∧ sm.trace = s0.trace ∧
             calleeSavedVRegs sm = calleeSavedVRegs s0))
          (fun sm hpcm hrunm hspm hx22m hx23m hx24m hx28m hx29m htrm hvregsm =>
            SepWPp.done (hpcm.trans hr30_init.symm) hrunm
              ⟨Entails.refl _, hspm, hx22m, hx23m, hx24m, hx28m, hx29m, htrm, hvregsm⟩)
      rw [hr30_init] at hinit_raw
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [Frame_init]; ac_rfl))
        (sepWPp_bind_lscl hcl2 hinit_raw ?_)
      intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx22_3, hx23_3, hx24_3, hx28_3, hx29_3, htr3, hvregs3⟩
      have hpolys_ne : pb.polys ≠ [] := by
        intro h; simp [h] at hpolys16
      have hvec_nil : vecGF16ListOf A (fsp + 480#64) [] = emp := rfl
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
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0
      cases hdec : decodePbPolysTotal pb.polys with
      | ok tail =>
        dsimp only
        let s0_polys := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1548#64)
        have hr30_polys : s0_polys.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1548#64 := by
          simp [s0_polys, wp_norm, arm64_norm]
        have hloop_raw :=
          polys_outer_loop_placed h_panic hshim_sat halloc_sat hdealloc_sat s0_polys fsp polysPtr hfsp_align
            pb.polys 0 [] s3 Frame_polys R hpolys_ne (by omega) rfl
            hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3 hvregs3
            (Q := fun sm Pm =>
              (Pm ⊢ vecGF16ListOf A (fsp + 480#64) ([] ++ tail.map LibsignalSpqrV1.Poly.coefficients) ∗
                arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * 0)) pb.polys ∗
                cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame_polys) ∧
              (sm.sp = fsp ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
            (fun sm tail' hdec_ok hpcm hrunm hspm _ htrm hvregsm => by
              rw [hdec] at hdec_ok; injection hdec_ok with htail_eq; subst htail_eq
              exact SepWPp.done (hpcm.trans hr30_polys.symm) hrunm
                ⟨Entails.refl _, hspm, htrm, hvregsm⟩)
            (fun sm errPolys hdec_err _ _ _ _ _ _ _ _ => by
              rw [hdec] at hdec_err; cases hdec_err)
        rw [hr30_polys] at hloop_raw
        refine SepWPp.weaken_pre
          (by
            dsimp only [Frame_init, Frame_polys, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
            rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpolys16]
            exact Entails.of_eq (by ac_rfl))
          (sepWPp_bind_lscl hcl3 hloop_raw ?_)
        intro sm hpcm hrunm hclm ⟨hspm, htrm, hvregsm⟩
        have htail_len : tail.length = 16 := by
          rw [decodePbPolysTotal_length pb.polys tail hdec, hpolys16]
        have hok := from_pb_ok_polys_cl_placed hmemcpy_sat hdealloc_sat s0 sm hclm fsp out pbA hfsp
          ptsCap ptsPtr polysCap polysPtr pb tail htail_len hsp0_align
          hpcm hrunm hspm htrm hvregsm
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_exit_placed s0 sm out pbA (.ok { idx := pb.idx, s := .polys tail }) _ R hok)
        dsimp only [Frame_polys, List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, hpts0, hpolys16]
        exact Entails.of_eq (by ac_rfl)
      | error e =>
        dsimp only
        let s0_polys := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_374).base + 1496#64)
        have hr30_polys : s0_polys.readReg64 (Reg.gpr 30#5) = (blkPl_374).base + 1496#64 := by
          simp [s0_polys, wp_norm, arm64_norm]
        have hloop_raw :=
          polys_outer_loop_placed h_panic hshim_sat halloc_sat hdealloc_sat s0_polys fsp polysPtr hfsp_align
            pb.polys 0 [] s3 Frame_polys R hpolys_ne (by omega) rfl
            hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3 hvregs3
            (Q := fun sm Pm =>
              (Pm ⊢ ∃∗ errPolys : List (List GF16), ⌜errPolys.length = 16 ∧ e = .serializationInvalid⌝ ∗
                (vecGF16ListOf A (fsp + 480#64) errPolys ∗
                 arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * 0)) pb.polys ∗
                 cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
                 A.pool ∗ stackAt fsp allocHookStack ∗ Frame_polys)) ∧
              (sm.sp = fsp ∧ sm.readReg64 .x19 = 2#64 ∧
               sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0))
            (fun sm tail' hdec_ok _ _ _ _ _ _ => by
              rw [hdec] at hdec_ok; cases hdec_ok)
            (fun sm errPolys hdec_err herr_len hpcm hrunm hspm hx19m _ htrm hvregsm => by
              rw [hdec] at hdec_err; injection hdec_err with he_eq
              exact SepWPp.done (hpcm.trans hr30_polys.symm) hrunm
                ⟨Entails.sepExists_right errPolys (Entails.pure_right ⟨herr_len, he_eq⟩ (Entails.refl _)),
                 hspm, hx19m, htrm, hvregsm⟩)
        rw [hr30_polys] at hloop_raw
        refine SepWPp.weaken_pre
          (by
            dsimp only [Frame_init, Frame_polys, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
            rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpolys16]
            exact Entails.of_eq (by ac_rfl))
          (sepWPp_bind_lscl hcl3 hloop_raw ?_)
        intro sm hpcm hrunm hclm ⟨hspm, hx19m, htrm, hvregsm⟩
        apply SepWPp.exists_elim; intro errPolys
        apply SepWPp.pure_left; rintro ⟨herr_len, rfl⟩
        have herr := from_pb_err_polys_cl_placed hdealloc_sat s0 sm hclm fsp out pbA hfsp pb errPolys herr_len
          hsp0_align hpcm hrunm hspm hx19m htrm hvregsm
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_exit_placed s0 sm out pbA (.error .serializationInvalid) _ R herr)
        dsimp only [Frame_polys, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, stackAt_dropGluePoly16_split_bottom fsp]
        have hpb := protoPolyEncoder_close A pbA ptsCap ptsPtr polysCap polysPtr pb
        rw [hpts0, hpolys16] at hpb
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
             ((pbA + 16#64) ↦₆₄ 0#64) ∗
             ((pbA + 32#64) ↦₆₄ polysPtr) ∗
             ((pbA + 40#64) ↦₆₄ 16#64) ∗
             ((pbA + 48#64) ↦₃₂ pb.idx) ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
             protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
            (memRegion out polyEncoderSize ∗
             vecGF16ListOf A (fsp + 480#64) errPolys ∗
             cells fsp 7 ∗
             ((fsp + 56#64) ↦₆₄ out) ∗
             ((fsp + 64#64) ↦₆₄ pbA) ∗
             memRegion (fsp + 72#64) 384 ∗
             cells (fsp + 456#64) 3 ∗
             cells (fsp + 864#64) 4 ∗
             cells (fsp + 896#64) 3 ∗
             memRegion (fsp + 920#64) 8 ∗
             (memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack) ∗
             savedCells s0 ∗ A.pool) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
    · rw [fromPbResult_eq_of_err pb hcase_pts hcase_polys]
      have hdisp := from_pb_header_err_placed (ext := ext) s1 fsp out pbA
        pb.pts.length pb.polys.length hnPts hnPolys hcase_pts hcase_polys
        (savedCells s0 ∗
         stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
         memRegion out polyEncoderSize ∗
         ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 32#64) ↦₆₄ polysPtr) ∗
         ((pbA + 48#64) ↦₃₂ pb.idx) ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
         protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
         A.pool)
        hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean_lscl hcl1 hdisp ?_)
      intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, _, htr2, hvregs2⟩
      have herr := from_pb_err_header_cl_placed hdealloc_sat s0 s2 hcl2 out pbA pb hsp0_align
        hpc2 hrun2 hsp2 hx0_2 hx1_2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1])
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_placed s0 s2 out pbA (.error .serializationInvalid) _ R herr)
      have hpb := protoPolyEncoder_close A pbA ptsCap ptsPtr polysCap polysPtr pb
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
          (memRegion out polyEncoderSize ∗
           savedCells s0 ∗
           stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
           A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))

/-- `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
    satisfies `withLsCodeLoaded lsmpl (encoderFromPbSpec A)` on `libsignalSessionLib.blockProgram lsmpl 374`. -/
theorem encoder_from_pb_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 374 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) :=
  ls_to_blockProgram (encoder_from_pb_cl_placed_ok_ext h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat)

/-- Retargetable `encoder_from_pb_cl_on` on any block `idx`'s program. -/
theorem encoder_from_pb_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) :=
  ls_subroutine_ok_of_block (encoder_from_pb_cl_placed_ok_ext h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat) hidx

/-- Retargetable `encoder_from_pb_mem_on` on any block `idx`'s program. -/
theorem encoder_from_pb_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 374)
      (withMemEq m (encoderFromPbSpec A)) :=
  lscall_blk_cl (encoder_from_pb_cl_placed_ok_ext h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat) hcl hidx

/-- Placed `subroutine_ok` for `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`)
    retargeted onto Block `333` (`lsProg_333`). -/
theorem encoder_from_pb_on_333_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) :=
  encoder_from_pb_cl_on (callerProg := lsProg_333 (Rust.withPanics ext))
    h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  from_pb_ok_polys_cl_placed
  from_pb_ok_pts_cl_placed
  encoder_from_pb_cl_placed_ok_ext
  encoder_from_pb_cl_blockProgram
  encoder_from_pb_cl_on
  encoder_from_pb_mem_on
  encoder_from_pb_on_333_placed_ok_ext
)
end CryptoVerification.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  from_pb_ok_polys_cl_placed
  from_pb_ok_pts_cl_placed
  encoder_from_pb_cl_placed_ok_ext
  encoder_from_pb_cl_blockProgram
  encoder_from_pb_cl_on
  encoder_from_pb_mem_on
  encoder_from_pb_on_333_placed_ok_ext
)
end CryptoVerification.SpqrV1.Poly.EncoderFromPb
