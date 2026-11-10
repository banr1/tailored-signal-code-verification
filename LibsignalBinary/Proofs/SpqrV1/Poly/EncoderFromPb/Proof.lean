/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Exit
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Top-Level Proof

**Checked by Lean.**

Composes prologue register save, header dispatch, `.points` and `.polys` loops, and exit blocks to
prove `encoder_from_pb_ok_ext` and `encoder_from_pb_ok_x` (`0x62188`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv384_toNat' bv8_toNat'
  sp_sub_96_add_8' sp_sub_96_add_16' sp_sub_96_add_32' sp_sub_96_add_48'
  sp_sub_96_add_64' sp_sub_96_add_80' sp_sub_88_add_8' sp_sub_80_add_8'
  sp_sub_72_add_8' sp_sub_64_add_8' sp_sub_56_add_8' sp_sub_48_add_8'
  sp_sub_40_add_8' sp_sub_32_add_8' sp_sub_24_add_8' sp_sub_16_add_8'
  sp_sub_96_sub_928'
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

/-! ## `.polys` and `.points` Success Exit Blocks (`+1548 -> s0.lr` and `+1648 -> s0.lr`) -/

/-- `.polys` success exit (`+1548 -> s0.lr`, `0x62794..0x627d0 -> +1460`):
    copies the 16 `Poly` headers from `fsp + 480` to `fsp + 72` and then to `out + 8`,
    stores `1#64` (`.polys` tag) at `out` and `pb.idx` at `out + 392`, and runs `from_pb_epilogue`. -/
theorem from_pb_ok_polys {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (polys : List LibsignalSpqrV1.Poly) (hpolys_len : polys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1548#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
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
  have hmemcpy := hA.session_memcpy_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec] at hmemcpy
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encoderFromPbName + 1572#64)
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
  · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1548 24
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_call hmemcpy (fsp + 72#64, fsp + 480#64,
      vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients))
    wp_steps
    refine align_pre ?_ ?_
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
  · intro s1 hpc1 hrun1 ⟨hsp1, hx8_1, hx20_1, htr1, hvregs1⟩
    refine from_pb_ok_copy_out hA s0 s1 fsp out pbA pbA 1#64 (hfsp_fn trivial)
      ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .polys polys }
      pins (polys.map LibsignalSpqrV1.Poly.coefficients) hpins_len hvecs_len ?_
      hsp0_align hpc1 hrun1 hsp1 hx8_1 hx20_1 htr1 hvregs1
    dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPolysTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [polyListOf_eq_vecGF16ListOf]
    have hp : polys.length = NUM_POLYS := hpolys_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 1#64) ∗
         vecGF16ListOf A (out + 8#64) (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (Entails.pure_right hp (Entails.refl _))) ?_
    exact Entails.of_eq (by ac_rfl)

/-- `.points` success exit (`+1648 -> +1572 -> s0.lr`, `0x627f8..0x62810 -> 0x627ac`):
    saves `x1` (`pbA`) in `x20`, copies the 16 `Point` headers from `fsp + 480` to `fsp + 72`
    and then to `out + 8`, stores `0#64` (`.points` tag) at `out` and `pb.idx` at `out + 392`,
    and runs `from_pb_epilogue`. -/
theorem from_pb_ok_pts {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder)
    (pts : List Point) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
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
  have hmemcpy := hA.session_memcpy_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec] at hmemcpy
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encoderFromPbName + 1572#64)
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
  · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1648 28
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_call hmemcpy (fsp + 72#64, fsp + 480#64,
      vecHeadersBytesOf pins (pts.map Point.value))
    wp_steps
    refine align_pre ?_ ?_
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
  · intro s1 hpc1 hrun1 ⟨hsp1, hx8_1, hx20_1, htr1, hvregs1⟩
    refine from_pb_ok_copy_out hA s0 s1 fsp out pbA v64 0#64 (hfsp_fn trivial)
      ptsCap ptsPtr polysCap polysPtr pb { idx := pb.idx, s := .points pts }
      pins (pts.map Point.value) hpins_len hvecs_len ?_
      hsp0_align hpc1 hrun1 hsp1 hx8_1 hx20_1 htr1 hvregs1
    dsimp only [resultPolyEncoderFromPbAt, polyEncoderAt, encoderStateAt,
      polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff, polyEncoderPadSize]
    rw [pointListOf_eq_vecGF16ListOf]
    have hp : pts.length = NUM_POLYS := hpts_len
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((out ↦₆₄ 0#64) ∗
         vecGF16ListOf A (out + 8#64) (pts.map Point.value)) ∗
        (((out + 392#64) ↦₃₂ pb.idx) ∗ memRegion (out + 396#64) 4) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (Entails.pure_right (And.intro hp hpts_bound) (Entails.refl _))) ?_
    exact Entails.of_eq (by ac_rfl)

/-! ## Prologue (`+0 -> +32`, `0x62188 -> 0x621a8`) -/

/-- Prologue register save and stack allocation (`+0 -> +32`, `0x62188..0x621a4`):
    stores `x19..x30` into `savedCells s0` and allocates the 1024-byte stack frame. -/
theorem from_pb_save_regs {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s0.pc = (contractProg b ext).fnAddr encoderFromPbName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = pbA) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 32#64) s0
      (stackAt s0.sp encoderFromPbStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗ Frame) ∧
        sm.sp = s0.sp - 1024#64 ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = (s0.sp - 1024#64) + 928#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  rw [stackAt_encoderFromPb_split_96 s0.sp]
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 0 32
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  rw [sepConj_comm (stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928)) (cells (s0.sp - 96#64) 12),
      sepConj_assoc]
  iterate 12 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [sp_sub_96_add_8', sp_sub_88_add_8', sp_sub_80_add_8', sp_sub_72_add_8',
    sp_sub_64_add_8', sp_sub_56_add_8', sp_sub_48_add_8', sp_sub_40_add_8', sp_sub_32_add_8',
    sp_sub_24_add_8', sp_sub_16_add_8', sepConj_assoc]
  wp_steps
  refine align_pre ?_ ?_
  · unfold savedCells
    exact Entails.of_eq (by ac_rfl)
  · apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨Entails.refl _, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_, by wp_norm_goal, by wp_norm_goal⟩
    wp_norm_goal

/-! ## Header Dispatch (`+32 -> +56 / +556 / +1448`) -/

/-- Header dispatch when `pb.pts.length = 16` and `pb.polys.length = 0` (`+32 -> +56`). -/
theorem from_pb_header_pts {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 56#64) s
      (((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 40#64) ↦₆₄ 0#64) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 40#64) ↦₆₄ 0#64) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 32 24
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Header dispatch when `pb.pts.length = 0` and `pb.polys.length = 16` (`+32 -> +548 -> +556`). -/
theorem from_pb_header_polys {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 556#64) s
      (((pbA + 16#64) ↦₆₄ 0#64) ∗
        ((pbA + 40#64) ↦₆₄ 16#64) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 0#64) ∗
          ((pbA + 40#64) ↦₆₄ 16#64) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 32 24
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 548 12
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Header dispatch when `¬(nPts = 16 ∧ nPolys = 0)` and `¬(nPts = 0 ∧ nPolys = 16)` (`+32 -> +1448`). -/
theorem from_pb_header_err {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64) (nPts nPolys : Nat)
    (hnPts : nPts < 2 ^ 63) (hnPolys : nPolys < 2 ^ 63)
    (hnot_pts : ¬(nPts = 16 ∧ nPolys = 0))
    (hnot_polys : ¬(nPts = 0 ∧ nPolys = 16))
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 1448#64) s
      (((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 nPolys) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗
          ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 nPolys) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 32 24
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 548 12
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  by_cases hpts0 : nPts = 0
  · subst hpts0
    have hpolys16 : nPolys ≠ 16 := fun h => hnot_polys ⟨rfl, h⟩
    have hne16 : BitVec.ofNat 64 nPolys ≠ 16#64 := ofNat_ne_16 hpolys16 (by omega)
    have hbeq16 : (BitVec.ofNat 64 nPolys == 16#64) = false := beq_eq_false_iff_ne.mpr hne16
    have hbeq16' : (16#64 == BitVec.ofNat 64 nPolys) = false := beq_eq_false_iff_ne.mpr hne16.symm
    have hbne16 : (BitVec.ofNat 64 nPolys != 16#64) = true := bne_iff_ne.mpr hne16
    have hbne16' : (16#64 != BitVec.ofNat 64 nPolys) = true := bne_iff_ne.mpr hne16.symm
    wp_steps
    wp_done
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
      wp_steps
      wp_done
    · have hne_p0 : BitVec.ofNat 64 nPolys ≠ 0#64 := ofNat_ne_zero_of_pos (by omega) (by omega)
      have hbeq_p0 : (BitVec.ofNat 64 nPolys == 0#64) = false := beq_eq_false_iff_ne.mpr hne_p0
      have hbeq_p0' : (0#64 == BitVec.ofNat 64 nPolys) = false := beq_eq_false_iff_ne.mpr hne_p0.symm
      have hbne_p0 : (BitVec.ofNat 64 nPolys != 0#64) = true := bne_iff_ne.mpr hne_p0
      have hbne_p0' : (0#64 != BitVec.ofNat 64 nPolys) = true := bne_iff_ne.mpr hne_p0.symm
      wp_steps
      wp_done

/-! ## Pure `fromPbResult` / Length Helpers and Top-Level Proof -/

theorem sepWPp_of_exit {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64)
    (res : Except PolynomialError PolyEncoder)
    (P R : SepProp)
    (h : SepWP (contractProg b ext) (s0.readReg64 Reg.lr) s P
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out res ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace)) :
    SepWPp (contractProg b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
            resultPolyEncoderFromPbAt A out res ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool ∗ stackAt s0.sp encoderFromPbStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  have h1 : sf.mem ⊨ (resultPolyEncoderFromPbAt A out res ∗
      memRegion pbA protoPolynomialEncoderSize ∗
      A.pool ∗ stackAt s0.sp encoderFromPbStack) ∗ R :=
    Satisfies.mono (sepConj_mono_left hPf) hmem_f
  exact Satisfies.mono (Entails.pure_right htrf (Entails.of_eq (by ac_rfl))) h1

theorem encoder_from_pb_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    EncoderFromPbOkExt b A ext := by
  unfold EncoderFromPbOkExt
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [encoderFromPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpts_max⟩, hmem⟩
  refine ⟨stackAt s0.sp encoderFromPbStack ∗
      (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A pbA pb ∗ A.pool),
    R, ?_, ?_⟩
  · exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  dsimp only [encoderFromPbSpec]
  have hpro := from_pb_save_regs (b := b) (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A pbA pb ∗ A.pool)
    hpc0 hrun0 hx0 hx1
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx29_1, htr1, hvregs1⟩
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
    have hdisp := from_pb_header_pts (b := b) (ext := ext) s1 fsp out pbA
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
      (sepWPp_seq_clean hdisp ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hvregs2⟩
    rw [stack_split_for_pts s0.sp, ← hfsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v64
    apply SepWPp.exists_elim; intro v56
    have hinit := pts_init_empty_headers (b := b) (ext := ext) s2 fsp out pbA ptsPtr v56 hfsp_align
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
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hinit ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx1_3, hx21_3, hx23_3, hx24_3, hx25_3, _, _, _, _, _, _, hx29_3, htr3, hvregs3⟩
    have hpts_ne : pb.pts ≠ [] := by
      intro h; simp [h] at hpts16
    have hvec_nil : vecGF16ListOf A (fsp + 480#64) [] = emp := rfl
    refine SepWPp.weaken_pre
      (by
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpts16]
        exact Entails.of_eq (by ac_rfl))
      (pts_outer_loop hA s0 fsp ptsPtr hfsp_align pb.pts 0 [] s3
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
         arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
         protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
         savedCells s0)
        R hpts_ne (by omega) rfl (fun bs hbs => by have := hpts_max bs hbs; omega)
        hpc3 hrun3 hsp3 hx21_3 hx23_3 hx24_3 hx25_3
        (by rw [htr3, htr2, htr1])
        (by rw [hvregs3, hvregs2, hvregs1])
        (fun sm tail hdec_ok hpcm hrunm hspm hx1m _ htrm hvregsm => ?_)
        (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m _ htrm hvregsm => ?_))
    · rw [hdec_ok]; dsimp only
      have htail_len : tail.length = 16 := by
        rw [decodePbPointsTotal_length pb.pts tail hdec_ok, hpts16]
      have htail_bound : ∀ pt ∈ tail, pt.value.length ≤ 0x0555555555555555 :=
        decodePbPointsTotal_value_length_le pb.pts tail hdec_ok hpts_max
      have hok := from_pb_ok_pts hA s0 sm fsp out pbA v64 hfsp
        ptsCap ptsPtr polysCap polysPtr pb tail htail_len htail_bound hsp0_align
        hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm
      refine SepWPp.weaken_pre ?_ (sepWPp_of_exit s0 sm out pbA (.ok { idx := pb.idx, s := .points tail }) _ R hok)
      dsimp only [List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, hpts16, hpolys0]
      exact Entails.of_eq (by ac_rfl)
    · rw [hdec_err]; dsimp only
      have herr := from_pb_err_pts hA s0 sm fsp out pbA v64 hfsp pb errPts herr_len
        hsp0_align hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm
      refine SepWPp.weaken_pre ?_ (sepWPp_of_exit s0 sm out pbA (.error .serializationInvalid) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
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
      have hdisp := from_pb_header_polys (b := b) (ext := ext) s1 fsp out pbA
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
        (sepWPp_seq_clean hdisp ?_)
      intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hvregs2⟩
      rw [stack_split_for_polys s0.sp, ← hfsp]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (polys_init_zero_headers hA s0 s2 fsp out pbA polysPtr hfsp_align
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
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb)
          R hpc2 hrun2 hsp2 hx0_2 hx1_2 hx29_2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1]) ?_)
      intro s3 hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3 hvregs3
      have hpolys_ne : pb.polys ≠ [] := by
        intro h; simp [h] at hpolys16
      have hvec_nil : vecGF16ListOf A (fsp + 480#64) [] = emp := rfl
      refine SepWPp.weaken_pre
        (by
          dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
          rw [hvec_nil, emp_sepConj, BitVec.add_zero, BitVec.add_zero, hpolys16]
          exact Entails.of_eq (by ac_rfl))
        (polys_outer_loop hA s0 fsp polysPtr hfsp_align pb.polys 0 [] s3
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
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
           savedCells s0)
          R hpolys_ne (by omega) rfl hpc3 hrun3 hsp3 hx22_3 hx23_3 hx24_3 hx28_3 hx29_3 htr3 hvregs3
          (fun sm tail hdec_ok hpcm hrunm hspm _ htrm hvregsm => ?_)
          (fun sm errPolys hdec_err herr_len hpcm hrunm hspm hx19m _ htrm hvregsm => ?_))
      · rw [hdec_ok]; dsimp only
        have htail_len : tail.length = 16 := by
          rw [decodePbPolysTotal_length pb.polys tail hdec_ok, hpolys16]
        have hok := from_pb_ok_polys hA s0 sm fsp out pbA hfsp
          ptsCap ptsPtr polysCap polysPtr pb tail htail_len hsp0_align
          hpcm hrunm hspm htrm hvregsm
        refine SepWPp.weaken_pre ?_ (sepWPp_of_exit s0 sm out pbA (.ok { idx := pb.idx, s := .polys tail }) _ R hok)
        dsimp only [List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, hpts0, hpolys16]
        exact Entails.of_eq (by ac_rfl)
      · rw [hdec_err]; dsimp only
        have herr := from_pb_err_polys hA s0 sm fsp out pbA hfsp pb errPolys herr_len
          hsp0_align hpcm hrunm hspm hx19m htrm hvregsm
        refine SepWPp.weaken_pre ?_ (sepWPp_of_exit s0 sm out pbA (.error .serializationInvalid) _ R herr)
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
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
      have hdisp := from_pb_header_err (b := b) (ext := ext) s1 fsp out pbA
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
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hdisp ?_)
      intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, _, htr2, hvregs2⟩
      have herr := from_pb_err_header hA s0 s2 out pbA pb hsp0_align
        hpc2 hrun2 hsp2 hx0_2 hx1_2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1])
      refine SepWPp.weaken_pre ?_ (sepWPp_of_exit s0 s2 out pbA (.error .serializationInvalid) _ R herr)
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

theorem encoder_from_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    EncoderFromPbOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (encoderFromPbSpecX_of_encoderFromPbSpec (encoder_from_pb_ok_ext hA))

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
