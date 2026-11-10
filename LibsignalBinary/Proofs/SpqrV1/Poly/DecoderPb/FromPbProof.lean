/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopy
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlaced
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Top-Level Proof

**Checked by Lean.**

Proves the prologue, `pb.pts.length = 16` check, empty-slot initialization (`+0..+204`), and
top-level contracts `fromPbDec_ok_ext`, `decoder_from_pb_ok_ext`, `fromPbDec_ok_x`, and their
`[LibsignalPlacement]` counterparts on Block `376`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustReallocSym spqrRustNoAllocShimSym
   spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section Legacy
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Prologue, Header Length Check, and Empty Slot Initialization (`+0 -> +204`) -/

attribute [local arm64_norm, local wp_norm]
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32
  fsp_448_add_40 fsp_448_add_48 fsp_448_add_56 fsp_448_add_64
  fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8
  fsp_488_add_8 fsp_496_add_8 fsp_504_add_8 fsp_512_add_8
  fsp_520_add_8 fsp_528_add_8

@[local simp, local arm64_norm, local wp_norm]
theorem bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sepWP_cells_succ {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target_pc s (cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest)) post) :
    SepWP prog target_pc s (cells a (k + 1) ∗ Rest) post := by
  have heq : cells a (k + 1) ∗ Rest = ∃∗ v : BitVec 64, cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest) := by
    rw [ProofLib.cells_succ, sepExists_sepConj_left]
    exact congrArg sepExists (funext fun v => by ac_rfl)
  rw [heq]
  exact ProofLib.SepWP.exists_left h

theorem sepWP_cells_zero {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s Rest post) :
    SepWP prog target_pc s (cells a 0 ∗ Rest) post := by
  rw [ProofLib.cells_zero, emp_sepConj]
  exact h

/-- Prologue (`+0 -> +32`, `0x62b1c..0x62b3c`):
    allocates the 544-byte frame (`sp := s0.sp - 544#64`), saves `x19..x30` into
    `savedRegsAt (s0.sp - 544#64) s0`, and sets `x29 := (s0.sp - 544#64) + 448#64`. -/
theorem fromPb_save_regs_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = pbA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 32#64) s0
      (stackAt s0.sp fromPbCoreStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ savedRegsAt (s0.sp - 544#64) s0 ∗
          memRegion (s0.sp - 544#64) 448 ∗
          stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗ Frame) ∧
        sm.sp = s0.sp - 544#64 ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = (s0.sp - 544#64) + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 544#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  have hfsp448_align : (((s0.sp - 544#64) + 448#64) &&& 15#64 == 0#64) = true := by
    revert hfsp_align; bv_bits
  rw [stackAt_fromPbCoreStack_split s0.sp,
      show (96 : Nat) = 8 * 12 by rfl,
      ProofLib.memRegion_cells ((s0.sp - 544#64) + 448#64) 12 (by decide)]
  from_pb_fetches_range b (Rust.withPanics ext) 0 32
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  have hpre_comm :
      (stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗
        memRegion (s0.sp - 544#64) 448 ∗
        cells ((s0.sp - 544#64) + 448#64) 12) ∗ Frame =
      cells ((s0.sp - 544#64) + 448#64) 12 ∗
        (stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗
          memRegion (s0.sp - 544#64) 448 ∗ Frame) := by ac_rfl
  rw [hpre_comm]
  iterate 12 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [fsp_448_add_8, fsp_456_add_8, fsp_464_add_8, fsp_472_add_8,
    fsp_480_add_8, fsp_488_add_8, fsp_496_add_8, fsp_504_add_8, fsp_512_add_8,
    fsp_520_add_8, fsp_528_add_8, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
  unfold savedRegsAt
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

theorem ofNat_ne_16_of_ne {n : Nat} (hne : n ≠ 16) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 16#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
  omega

/-- Header length check when `pb.pts.length = 16` (`+32 -> +48`, `0x62b3c..0x62b4c`). -/
theorem fromPb_header_ok_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 48#64) s
      (((pbA + 16#64) ↦₆₄ 16#64) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 16#64) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  from_pb_fetches_range b (Rust.withPanics ext) 32 16
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Header length check when `pb.pts.length ≠ 16` (`+32 -> +712`, `0x62b3c..0x62b4c -> 0x62de4`). -/
theorem fromPb_header_err_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64) (nPts : Nat)
    (hnPts : nPts < 2 ^ 64) (hne16 : nPts ≠ 16)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 712#64) s
      (((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 nPts ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  have hne : BitVec.ofNat 64 nPts ≠ 16#64 := ofNat_ne_16_of_ne hne16 hnPts
  have hbeq : (BitVec.ofNat 64 nPts == 16#64) = false := beq_eq_false_iff_ne.mpr hne
  have hbeq' : (16#64 == BitVec.ofNat 64 nPts) = false := beq_eq_false_iff_ne.mpr hne.symm
  have hbne : (BitVec.ofNat 64 nPts != 16#64) = true := bne_iff_ne.mpr hne
  have hbne' : (16#64 != BitVec.ofNat 64 nPts) = true := bne_iff_ne.mpr hne.symm
  from_pb_fetches_range b (Rust.withPanics ext) 32 16
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Empty `SortedSet<Pt>` slot initialization (`+48 -> +204`, `0x62b4c..0x62be8`):
    initializes 16 empty `SortedSet<Pt>` headers `(0, 2, 0)` at `fsp + 32 .. fsp + 416`,
    loads `ptsPtr` from `[pbA + 8]`, stores `out` at `[fsp + 8]`, `pbA` at `[fsp + 16]`,
    and `ptsPtr` at `[fsp + 24]`, and sets `x19 := 24`, `x21 := ptsPtr`, `x25 := 0`. -/
theorem fromPb_init_empty_headers_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ptsPtr v8 v16 v24 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 48#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = 16#64)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64) s
      (memRegion (fsp + 32#64) 384 ∗
        ((fsp + 8#64) ↦₆₄ v8) ∗
        ((fsp + 16#64) ↦₆₄ v16) ∗
        ((fsp + 24#64) ↦₆₄ v24) ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ emptySlotsAt (fsp + 32#64) 16 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗
          ((fsp + 16#64) ↦₆₄ pbA) ∗
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = 24#64 ∧
        sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  from_pb_fetches_range b (Rust.withPanics ext) 48 156
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_cells (fsp + 32#64) 48 (by decide)]
  iterate 24 (apply sepWP_cells_succ; intro)
  iterate 24 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
  simp only [emptySlotsAt, List.replicate_succ, List.replicate_zero, arrayAt_cons, arrayAt_nil,
    emptySlotAt, sepConj_emp, bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  exact Entails.of_eq (by ac_rfl)

/-! ## Top-Level Proofs (`fromPbDec_ok_ext` and `fromPbDec_ok_x`) -/

theorem decodePbPtsTotal_eq_ok_of_all_mod4 :
    ∀ (bss : List (List (BitVec 8))),
      (∀ bs ∈ bss, bs.length % 4 = 0) →
      decodePbPtsTotal bss = .ok (bss.map fun bs => pushChunks4Total bs { vec := [] }) := by
  intro bss hall
  induction bss with
  | nil => rfl
  | cons bs rest ih =>
    have hbs : bs.length % 4 = 0 := hall bs List.mem_cons_self
    have hrest : ∀ x ∈ rest, x.length % 4 = 0 := fun x hx => hall x (List.mem_cons_of_mem bs hx)
    have hne : (bs.length % 4 != 0) = false := by simp [hbs]
    simp only [decodePbPtsTotal, hne, Bool.false_eq_true, ↓reduceIte, ih hrest, List.map_cons,
      SortedSetPt.withCapacity]

theorem decodePbPtsTotal_eq_err_of_exists_mod4 :
    ∀ (bss : List (List (BitVec 8))),
      (∃ bs ∈ bss, bs.length % 4 ≠ 0) →
      decodePbPtsTotal bss = .error .serializationInvalid := by
  intro bss hex
  induction bss with
  | nil => rcases hex with ⟨_, hmem, _⟩; nomatch hmem
  | cons bs rest ih =>
    unfold decodePbPtsTotal
    by_cases hbs : bs.length % 4 = 0
    · have hne : (bs.length % 4 != 0) = false := by simp [hbs]
      rcases hex with ⟨x, hx, hmod⟩
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact False.elim (hmod hbs)
      · simp only [hne, Bool.false_eq_true, ↓reduceIte, ih ⟨x, hmem, hmod⟩]
    · have hne : (bs.length % 4 != 0) = true := by simp [hbs]
      simp only [hne, ↓reduceIte]

theorem fromPbDecResult_eq_ok_of_all_mod4 (pb : ProtoPolynomialDecoder)
    (hlen : pb.pts.length = 16) (hall : ∀ bs ∈ pb.pts, bs.length % 4 = 0) :
    fromPbDecResult pb = .ok {
      ptsNeeded := pb.ptsNeeded.toNat
      isComplete := pb.isComplete
      pts := pb.pts.map fun bs => pushChunks4Total bs { vec := [] }
    } := by
  unfold fromPbDecResult
  simp [hlen, decodePbPtsTotal_eq_ok_of_all_mod4 pb.pts hall]

theorem fromPbDecResult_eq_err_of_exists_mod4 (pb : ProtoPolynomialDecoder)
    (hlen : pb.pts.length = 16) (hex : ∃ bs ∈ pb.pts, bs.length % 4 ≠ 0) :
    fromPbDecResult pb = .error .serializationInvalid := by
  unfold fromPbDecResult
  simp [hlen, decodePbPtsTotal_eq_err_of_exists_mod4 pb.pts hex]

theorem fromPbDecResult_eq_err_of_len_ne_16 (pb : ProtoPolynomialDecoder)
    (hne : pb.pts.length ≠ 16) :
    fromPbDecResult pb = .error .serializationInvalid := by
  unfold fromPbDecResult
  have hbne : (pb.pts.length != 16) = true := bne_iff_ne.mpr hne
  simp [hbne]

theorem memRegion_448_split (fsp : BitVec 64) :
    memRegion fsp 448 =
      memRegion fsp 8 ∗
      (∃∗ v8 : BitVec 64, (fsp + 8#64) ↦₆₄ v8) ∗
      (∃∗ v16 : BitVec 64, (fsp + 16#64) ↦₆₄ v16) ∗
      (∃∗ v24 : BitVec 64, (fsp + 24#64) ↦₆₄ v24) ∗
      memRegion (fsp + 32#64) 384 ∗
      (∃∗ v416 : BitVec 64, (fsp + 416#64) ↦₆₄ v416) ∗
      (∃∗ v424 : BitVec 64, (fsp + 424#64) ↦₆₄ v424) ∗
      (∃∗ v432 : BitVec 64, (fsp + 432#64) ↦₆₄ v432) ∗
      memRegion (fsp + 440#64) 8 := by
  have ha16 : (fsp + 8#64) + 8#64 = fsp + 16#64 := by bv_omega
  have ha24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_omega
  have ha32 : (fsp + 24#64) + 8#64 = fsp + 32#64 := by bv_omega
  have ha416 : (fsp + 32#64) + 384#64 = fsp + 416#64 := by bv_omega
  have ha424 : (fsp + 416#64) + 8#64 = fsp + 424#64 := by bv_omega
  have ha432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_omega
  have ha440 : (fsp + 432#64) + 8#64 = fsp + 440#64 := by bv_omega
  rw [show (448 : Nat) = 8 + (8 + (8 + (8 + (384 + (8 + (8 + (8 + 8))))))) by rfl,
      ProofLib.memRegion_split fsp 8 440 (by decide),
      ProofLib.memRegion_split (fsp + 8#64) 8 432 (by decide), ha16,
      ProofLib.memRegion_split (fsp + 16#64) 8 424 (by decide), ha24,
      ProofLib.memRegion_split (fsp + 24#64) 8 416 (by decide), ha32,
      ProofLib.memRegion_split (fsp + 32#64) 384 32 (by decide), ha416,
      ProofLib.memRegion_split (fsp + 416#64) 8 24 (by decide), ha424,
      ProofLib.memRegion_split (fsp + 424#64) 8 16 (by decide), ha432,
      ProofLib.memRegion_split (fsp + 432#64) 8 8 (by decide), ha440,
      ProofLib.memRegion_eight (fsp + 8#64), ProofLib.memRegion_eight (fsp + 16#64),
      ProofLib.memRegion_eight (fsp + 24#64), ProofLib.memRegion_eight (fsp + 416#64),
      ProofLib.memRegion_eight (fsp + 424#64), ProofLib.memRegion_eight (fsp + 432#64)]

def fromPbDecSpecWithStack (A : RustAlloc) (stk : Nat) : Spec FromPbDecGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyDecoderFromPbAt A x.out (fromPbDecResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool ∗ stackAt s0.sp stk
  onPanic := fun _ s0 sf => fromPbOnPanic s0 sf

theorem sepWPp_of_exit_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64)
    (res : Except PolynomialError PolyDecoder)
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out res ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ emp) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            resultPolyDecoderFromPbAt A out res ∗
            memRegion pbA protoPolynomialDecoderSize ∗
            A.pool ∗ stackAt s0.sp fromPbCoreStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  rw [sepConj_emp] at hPf
  have h1 : sf.mem ⊨ (resultPolyDecoderFromPbAt A out res ∗
      memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack) ∗ R :=
    Satisfies.mono (sepConj_mono_left hPf) hmem_f
  exact Satisfies.mono (Entails.trans (Entails.pure_right htrf (Entails.of_eq rfl))
    (Entails.of_eq (by ac_rfl))) h1

theorem protoPolynomialDecoderAt_expose (A : RustAlloc) (pbA : BitVec 64)
    (pb : ProtoPolynomialDecoder) (Frame : SepProp) :
    protoPolynomialDecoderAt A pbA pb ∗ Frame ⊢
      ∃∗ cap_pts : BitVec 64, ∃∗ ptsPtr : BitVec 64,
        ⌜pb.pts.length ≤ cap_pts.toNat ∧ cap_pts.toNat * 24 < 2 ^ 63 ∧
          pb.pts.length * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        Frame := by
  unfold protoPolynomialDecoderAt
  dsimp only [protoPolynomialDecoderPtsNeededOff, protoPolynomialDecoderPolysOff,
    protoPolynomialDecoderIsCompleteOff, protoPolynomialDecoderPadOff,
    protoPolynomialDecoderPadSize, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left (vecVecU8At_expose A pbA pb.pts))) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap_pts
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right cap_pts (Entails.sepExists_right ptsPtr ?_)
  exact Entails.of_eq (by ac_rfl)

/-- Core correctness of `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`)
    with stack budget `fromPbCoreStack = 544 + dropGluePoly16Stack`. -/
theorem fromPbDec_ok_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
      (fromPbDecSpecWithStack A fromPbCoreStack) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [fromPbDecSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨stackAt s0.sp fromPbCoreStack ∗
      (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [fromPbDecSpecWithStack]
  have hpro := fromPb_save_regs_sepWP (b := b) (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool)
    hpc0 hrun0 hx0 hx1
  refine SepWPp.seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx29_1, hvregs1, htr1⟩
  let fsp := s0.sp - 544#64
  have hfsp : HiddenEq fsp (s0.sp - 544#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (protoPolynomialDecoderAt_expose A pbA pb
        (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
          memRegion out polyDecoderSize ∗ A.pool))) ?_
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.pure_elim; rintro ⟨hle, hcap_bound, hlen_bound, _⟩
  by_cases hlen16 : pb.pts.length = 16
  · have hhdr := fromPb_header_ok_sepWP (b := b) (ext := ext) s1 fsp out pbA
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (by rw [hlen16]; exact Entails.of_eq (by ac_rfl))
      (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, hx29_2, hvregs2, htr2⟩
    conv => arg 4; rw [memRegion_448_split fsp, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v432
    apply SepWPp.exists_elim; intro v424
    apply SepWPp.exists_elim; intro v416
    apply SepWPp.exists_elim; intro v24
    apply SepWPp.exists_elim; intro v16
    apply SepWPp.exists_elim; intro v8
    have hinit := fromPb_init_empty_headers_sepWP (b := b) (ext := ext)
      s2 fsp out pbA ptsPtr v8 v16 v24 hfsp_align
      (memRegion fsp 8 ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 hx29_2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hinit ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3, htr3⟩
    have hpts_ne : pb.pts ≠ [] := by intro h; simp [h] at hlen16
    refine SepWPp.weaken_pre
      (by
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, BitVec.add_zero, hlen16]
        exact Entails.of_eq (by ac_rfl))
      (fromPb_outer_loop_wpp hA s0 fsp ptsPtr hfsp_align pb.pts hpts_ne 0
        (by omega) v416 v424 v432 s3
        (((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          memRegion fsp 8 ∗ memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ memRegion out polyDecoderSize)
        hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
        (by rw [htr3, htr2, htr1]) (by rw [hvregs3, hvregs2, hvregs1])
        (fun sm w416 w424 w432 hall hpcm hrunm hspm hx21m _ _ htrm hvregsm => ?_)
        (fun sm sets_err w416 w424 w432 hex hsets_len hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm => ?_))
    · rw [fromPbDecResult_eq_ok_of_all_mod4 pb hlen16 hall]
      have hout_len : (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }).length = 16 := by
        simp [hlen16]
      have hok := fromPb_success_exit_876_sepWP hA s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align pb hlen16
        (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }) hout_len hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core s0 sm out pbA _ _ R hok)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      exact Entails.of_eq (by ac_rfl)
    · rw [fromPbDecResult_eq_err_of_exists_mod4 pb hlen16 hex]
      have hsets_len16 : sets_err.length = 16 := hsets_len.trans hlen16
      have herr := fromPb_error_exit_740_sepWP hA s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align sets_err hsets_len16 pb.pts hlen16 hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hx24m hx29m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core s0 sm out pbA (.error .serializationInvalid) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      exact replace_sub_entails hpb16
        (memRegion out 400 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          sortedSetPtListOf A (fsp + 32#64) sets_err ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack)
        (by ac_rfl) (by ac_rfl)
  · rw [fromPbDecResult_eq_err_of_len_ne_16 pb hlen16]
    have hnPts : pb.pts.length < 2 ^ 64 := by omega
    have hhdr := fromPb_header_err_sepWP (b := b) (ext := ext) s1 fsp out pbA
      pb.pts.length hnPts hlen16
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, _, hvregs2, htr2⟩
    have herr := fromPb_error_exit_712_sepWP hA s0 fsp out pbA cap_pts ptsPtr
      hfsp hsp0_align hfsp_align pb.pts hle hcap_bound hlen_bound
      s2 emp hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 (by rw [hvregs2, hvregs1]) (by rw [htr2, htr1])
    refine SepWPp.weaken_pre ?_
      (sepWPp_of_exit_core s0 s2 out pbA (.error .serializationInvalid) _ R herr)
    dsimp only [polyDecoderSize]
    have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
    exact replace_sub_entails hpb16
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack)
      (by ac_rfl) (by ac_rfl)

theorem fromPb_satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

theorem fromPbDecSpecWithStack_mono {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {stk1 stk2 : Nat} (hle : stk1 ≤ stk2) (hmax : stk1 + (stk2 - stk1) ≤ 2 ^ 64)
    (h : subroutine_ok P addr (fromPbDecSpecWithStack A stk1)) :
    subroutine_ok P addr (fromPbDecSpecWithStack A stk2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp stk2 =
      memRegion (s0.sp - BitVec.ofNat 64 stk2) (stk2 - stk1) ∗ stackAt s0.sp stk1 := by
    have h1 := stackAt_split_bottom s0.sp stk1 (stk2 - stk1) hmax
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk2) (stk2 - stk1) ∗ R
  have hpre' : s0.mem ⊨ (fromPbDecSpecWithStack A stk1).pre x s0 ∗ R' := by
    dsimp only [fromPbDecSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [fromPbDecSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, fromPb_satisfies_anyHeap_frame hpost⟩)
  · dsimp only [fromPbDecSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

theorem fromPbDec_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    FromPbDecOkExt b A ext :=
  fromPbDecSpecWithStack_mono (by decide) (by decide) (fromPbDec_ok_core hA)

theorem fromPbDec_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    FromPbDecOkExt b A ext :=
  fromPbDec_ok_ext hA

/-- `<spqr::encoding::polynomial::PolyDecoder>::from_pb` (`0x62b1c`, 325 instructions)
    at the `1056 + allocHookStack` stack budget (`States.FromPb.decoderFromPbStack`). -/
theorem fromPbDec_ok_stack1056 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName)
      (fromPbDecSpecWithStack A (1056 + allocHookStack)) :=
  fromPbDecSpecWithStack_mono (by decide) (by decide) (fromPbDec_ok_core hA)

theorem fromPbDecResult_eq_decoderFromPbResult (pb : ProtoPolynomialDecoder) :
    fromPbDecResult pb = States.FromPb.decoderFromPbResult pb :=
  Except.ok.inj ((fromPbDec_eq_ok pb).symm.trans (States.FromPb.decoderFromPb_eq_ok pb))

theorem decoderFromPbSpec_of_fromPbDecSpecWithStack {P : Program} {A : RustAlloc}
    (h : subroutine_ok P (P.fnAddr fromPbDecName) (fromPbDecSpecWithStack A (1056 + allocHookStack))) :
    subroutine_ok P (P.fnAddr States.FromPb.decoderFromPbName) (States.FromPb.decoderFromPbSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hal => ?_
  refine h.mono_outcome ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [States.FromPb.decoderFromPbSpec, fromPbDecSpecWithStack] at hpost ⊢
    rwa [← fromPbDecResult_eq_decoderFromPbResult pb]
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem decoder_from_pb_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    States.FromPb.DecoderFromPbOkExt b A ext :=
  decoderFromPbSpec_of_fromPbDecSpecWithStack (fromPbDec_ok_stack1056 hA)

theorem decoderFromPb_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    States.FromPb.DecoderFromPbOkExt b A ext :=
  decoder_from_pb_ok_ext hA

theorem fromPbDec_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    FromPbDecOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (fromPbDecSpecWithStack_mono (by decide) (by decide) (fromPbDec_ok_core hA))

theorem decoder_from_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    FromPbDecOkX img A ext :=
  fromPbDec_ok_x hA

end Legacy

/-! ## `[LibsignalPlacement]` Relocatable Proofs (Block `376`) -/

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_lit_add_lit
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32
  fsp_448_add_40 fsp_448_add_48 fsp_448_add_56 fsp_448_add_64
  fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8
  fsp_488_add_8 fsp_496_add_8 fsp_504_add_8 fsp_512_add_8
  fsp_520_add_8 fsp_528_add_8
attribute [local simp] bv_add_lit_add_lit

theorem fromPb_save_regs_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s0.pc = (blkPl_376).base)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = pbA) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 32#64) s0
      (stackAt s0.sp fromPbCoreStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ savedRegsAt (s0.sp - 544#64) s0 ∗
          memRegion (s0.sp - 544#64) 448 ∗
          stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗ Frame) ∧
        sm.sp = s0.sp - 544#64 ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = (s0.sp - 544#64) + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 544#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  have hfsp448_align : (((s0.sp - 544#64) + 448#64) &&& 15#64 == 0#64) = true := by
    revert hfsp_align; bv_bits
  rw [stackAt_fromPbCoreStack_split s0.sp,
      show (96 : Nat) = 8 * 12 by rfl,
      ProofLib.memRegion_cells ((s0.sp - 544#64) + 448#64) 12 (by decide)]
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hpre_comm :
      (stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗
        memRegion (s0.sp - 544#64) 448 ∗
        cells ((s0.sp - 544#64) + 448#64) 12) ∗ Frame =
      cells ((s0.sp - 544#64) + 448#64) 12 ∗
        (stackAt (s0.sp - 544#64) dropGluePoly16Stack ∗
          memRegion (s0.sp - 544#64) 448 ∗ Frame) := by ac_rfl
  rw [hpre_comm]
  iterate 12 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [fsp_448_add_8, fsp_456_add_8, fsp_464_add_8, fsp_472_add_8,
    fsp_480_add_8, fsp_488_add_8, fsp_496_add_8, fsp_504_add_8, fsp_512_add_8,
    fsp_520_add_8, fsp_528_add_8, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
  unfold savedRegsAt
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

theorem fromPb_header_ok_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 48#64) s
      (((pbA + 16#64) ↦₆₄ 16#64) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 16#64) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

theorem fromPb_header_err_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (fsp out pbA : BitVec 64) (nPts : Nat)
    (hnPts : nPts < 2 ^ 64) (hne16 : nPts ≠ 16)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 32#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 712#64) s
      (((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 nPts ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  have hne : BitVec.ofNat 64 nPts ≠ 16#64 := ofNat_ne_16_of_ne hne16 hnPts
  have hbeq : (BitVec.ofNat 64 nPts == 16#64) = false := beq_eq_false_iff_ne.mpr hne
  have hbeq' : (16#64 == BitVec.ofNat 64 nPts) = false := beq_eq_false_iff_ne.mpr hne.symm
  have hbne : (BitVec.ofNat 64 nPts != 16#64) = true := bne_iff_ne.mpr hne
  have hbne' : (16#64 != BitVec.ofNat 64 nPts) = true := bne_iff_ne.mpr hne.symm
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

theorem fromPb_init_empty_headers_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ptsPtr v8 v16 v24 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 48#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = 16#64)
    (hx29 : s.readReg64 .x29 = fsp + 448#64) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 204#64) s
      (memRegion (fsp + 32#64) 384 ∗
        ((fsp + 8#64) ↦₆₄ v8) ∗
        ((fsp + 16#64) ↦₆₄ v16) ∗
        ((fsp + 24#64) ↦₆₄ v24) ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ emptySlotsAt (fsp + 32#64) 16 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗
          ((fsp + 16#64) ↦₆₄ pbA) ∗
          ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = 24#64 ∧
        sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = 16#64 ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x29 = fsp + 448#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.trace = s.trace) := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [ProofLib.memRegion_cells (fsp + 32#64) 48 (by decide)]
  iterate 24 (apply sepWP_cells_succ; intro)
  iterate 24 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
  simp only [emptySlotsAt, List.replicate_succ, List.replicate_zero, arrayAt_cons, arrayAt_nil,
    emptySlotAt, sepConj_emp, bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  exact Entails.of_eq (by ac_rfl)

theorem sepWPp_of_exit_core_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64)
    (res : Except PolynomialError PolyDecoder)
    (P R : SepProp)
    (h : SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out res ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ emp) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            resultPolyDecoderFromPbAt A out res ∗
            memRegion pbA protoPolynomialDecoderSize ∗
            A.pool ∗ stackAt s0.sp fromPbCoreStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  rw [sepConj_emp] at hPf
  have h1 : sf.mem ⊨ (resultPolyDecoderFromPbAt A out res ∗
      memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack) ∗ R :=
    Satisfies.mono (sepConj_mono_left hPf) hmem_f
  exact Satisfies.mono (Entails.trans (Entails.pure_right htrf (Entails.of_eq rfl))
    (Entails.of_eq (by ac_rfl))) h1

theorem fromPbDec_placed_ok_core [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (fromPbDecSpecWithStack A fromPbCoreStack) := by
  have halloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  have hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc_sat
  have hmemcpy : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  have hmemmove : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrMemmoveSym) (sessionMemmoveSpec 0) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemmove_sat
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [fromPbDecSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨stackAt s0.sp fromPbCoreStack ∗
      (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [fromPbDecSpecWithStack]
  have hpro := fromPb_save_regs_placed_sepWP (ext := ext) s0 out pbA hsp0_align
    (memRegion out polyDecoderSize ∗ protoPolynomialDecoderAt A pbA pb ∗ A.pool)
    hpc0 hrun0 hx0 hx1
  refine SepWPp.seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx29_1, hvregs1, htr1⟩
  let fsp := s0.sp - 544#64
  have hfsp : HiddenEq fsp (s0.sp - 544#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 544#64 hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (protoPolynomialDecoderAt_expose A pbA pb
        (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
          memRegion out polyDecoderSize ∗ A.pool))) ?_
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptsPtr
  apply SepWPp.pure_elim; rintro ⟨hle, hcap_bound, hlen_bound, _⟩
  by_cases hlen16 : pb.pts.length = 16
  · have hhdr := fromPb_header_ok_placed_sepWP (ext := ext) s1 fsp out pbA
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (by rw [hlen16]; exact Entails.of_eq (by ac_rfl))
      (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, hx29_2, hvregs2, htr2⟩
    conv => arg 4; rw [memRegion_448_split fsp, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v432
    apply SepWPp.exists_elim; intro v424
    apply SepWPp.exists_elim; intro v416
    apply SepWPp.exists_elim; intro v24
    apply SepWPp.exists_elim; intro v16
    apply SepWPp.exists_elim; intro v8
    have hinit := fromPb_init_empty_headers_placed_sepWP (ext := ext)
      s2 fsp out pbA ptsPtr v8 v16 v24 hfsp_align
      (memRegion fsp 8 ∗
        ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 hx29_2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hinit ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx24_3, hx25_3, hx29_3, hvregs3, htr3⟩
    have hpts_ne : pb.pts ≠ [] := by intro h; simp [h] at hlen16
    refine SepWPp.weaken_pre
      (by
        dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, BitVec.add_zero, hlen16]
        exact Entails.of_eq (by ac_rfl))
      (fromPb_outer_loop_placed_wpp h_panic hshim_sat halloc_sat hmemmove_sat
        s0 fsp ptsPtr hfsp_align pb.pts hpts_ne 0
        (by omega) v416 v424 v432 s3
        (((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          memRegion fsp 8 ∗ memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ memRegion out polyDecoderSize)
        hpc3 hrun3 hsp3 hx19_3 hx21_3 hx24_3 hx25_3 hx29_3
        (by rw [htr3, htr2, htr1]) (by rw [hvregs3, hvregs2, hvregs1])
        (fun sm w416 w424 w432 hall hpcm hrunm hspm hx21m _ _ htrm hvregsm => ?_)
        (fun sm sets_err w416 w424 w432 hex hsets_len hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm => ?_))
    · rw [fromPbDecResult_eq_ok_of_all_mod4 pb hlen16 hall]
      have hout_len : (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }).length = 16 := by
        simp [hlen16]
      have hok := fromPb_success_exit_876_placed_sepWP hdealloc hmemcpy s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align pb hlen16
        (pb.pts.map fun bs => pushChunks4Total bs { vec := [] }) hout_len hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA _ _ R hok)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      exact Entails.of_eq (by ac_rfl)
    · rw [fromPbDecResult_eq_err_of_exists_mod4 pb hlen16 hex]
      have hsets_len16 : sets_err.length = 16 := hsets_len.trans hlen16
      have herr := fromPb_error_exit_740_placed_sepWP hdealloc hdrop s0 fsp out pbA cap_pts ptsPtr w416 w424 w432
        hfsp hsp0_align hfsp_align sets_err hsets_len16 pb.pts hlen16 hle hcap_bound
        sm emp hpcm hrunm hspm hx21m hx24m hx29m hvregsm htrm
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_exit_core_placed s0 sm out pbA (.error .serializationInvalid) _ R herr)
      dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, polyDecoderSize]
      rw [BitVec.add_zero, BitVec.add_zero]
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      exact replace_sub_entails hpb16
        (memRegion out 400 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          sortedSetPtListOf A (fsp + 32#64) sets_err ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack)
        (by ac_rfl) (by ac_rfl)
  · rw [fromPbDecResult_eq_err_of_len_ne_16 pb hlen16]
    have hnPts : pb.pts.length < 2 ^ 64 := by omega
    have hhdr := fromPb_header_err_placed_sepWP (ext := ext) s1 fsp out pbA
      pb.pts.length hnPts hlen16
      ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        memRegion out polyDecoderSize ∗ A.pool)
      hpc1 hrun1 hsp1 hx0_1 hx1_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hhdr ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx20_2, hx24_2, _, hvregs2, htr2⟩
    have herr := fromPb_error_exit_712_placed_sepWP hdealloc s0 fsp out pbA cap_pts ptsPtr
      hfsp hsp0_align hfsp_align pb.pts hle hcap_bound hlen_bound
      s2 emp hpc2 hrun2 hsp2 hx0_2 hx20_2 hx24_2 (by rw [hvregs2, hvregs1]) (by rw [htr2, htr1])
    refine SepWPp.weaken_pre ?_
      (sepWPp_of_exit_core_placed s0 s2 out pbA (.error .serializationInvalid) _ R herr)
    dsimp only [polyDecoderSize]
    have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
    exact replace_sub_entails hpb16
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack)
      (by ac_rfl) (by ac_rfl)

theorem fromPbDec_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    FromPbDecPlacedOkExt A ext :=
  fromPbDecSpecWithStack_mono (by decide) (by decide)
    (fromPbDec_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop h_panic)

theorem fromPbDec_placed_ok_stack1056 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (fromPbDecSpecWithStack A States.FromPb.decoderFromPbStack) :=
  fromPbDecSpecWithStack_mono (by decide) (by decide)
    (fromPbDec_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop h_panic)

theorem decoderFromPbSpec_of_fromPbDecSpecWithStack_at {A : RustAlloc} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      (fromPbDecSpecWithStack A States.FromPb.decoderFromPbStack)) :
    subroutine_ok P entry (States.FromPb.decoderFromPbSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hal => ?_
  refine h.mono_outcome ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [States.FromPb.decoderFromPbSpec, fromPbDecSpecWithStack] at hpost ⊢
    rwa [← fromPbDecResult_eq_decoderFromPbResult pb]
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem decoder_from_pb_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (blkPl_376).base
      (States.FromPb.decoderFromPbSpec A) :=
  decoderFromPbSpec_of_fromPbDecSpecWithStack_at
    (fromPbDec_placed_ok_stack1056 halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop h_panic)

theorem fromPbDec_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    FromPbDecPlacedOkX A ext :=
  fromPbDecSpecWithStack_mono (by decide) (by decide)
    (fromPbDec_placed_ok_core halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop h_panic)

theorem decoder_from_pb_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    FromPbDecPlacedOkX A ext :=
  fromPbDec_placed_ok_x halloc_sat hshim_sat hdealloc_sat hmemcpy_sat hmemmove_sat hdrop h_panic

end CryptoVerification.SpqrV1.Poly.DecoderPb
