/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Exit
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.ExitPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Relocatable Top-Level Proof

Relocatable `[LibsignalPlacement]` proof of `encoder_from_pb_placed_ok_ext` and
`encoder_from_pb_placed_ok_x` on Block `374`.
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
open CryptoVerification.SpqrV1.Layout.L1
open CryptoVerification.SpqrV1.Layout.L22

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

@[local arm64_norm, local wp_norm] theorem bv384_toNat' : (384#64 : BitVec 64).toNat = 384 := rfl
@[local arm64_norm, local wp_norm] theorem bv8_toNat' : (8#64 : BitVec 64).toNat = 8 := rfl

@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_8' (sp : BitVec 64) : (sp - 96#64) + 8#64 = sp - 88#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16' (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32' (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48' (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64' (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80' (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_88_add_8' (sp : BitVec 64) : (sp - 88#64) + 8#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8' (sp : BitVec 64) : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_72_add_8' (sp : BitVec 64) : (sp - 72#64) + 8#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_64_add_8' (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_56_add_8' (sp : BitVec 64) : (sp - 56#64) + 8#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_48_add_8' (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_40_add_8' (sp : BitVec 64) : (sp - 40#64) + 8#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_32_add_8' (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_24_add_8' (sp : BitVec 64) : (sp - 24#64) + 8#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_16_add_8' (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_928' (sp : BitVec 64) : (sp - 96#64) - 928#64 = sp - 1024#64 := by bv_omega

theorem sepWP_pure_left {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog target_pc s P post) :
    SepWP prog target_pc s (⌜φ⌝ ∗ P) post :=
  SepWP.pure_elim h

theorem ofNat_ne_16 {n : Nat} (hne : n ≠ 16) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 16#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
  omega

theorem decodePbPointsTotal_length :
    ∀ (bss : List (List (BitVec 8))) (pts : List Point),
      decodePbPointsTotal bss = .ok pts → pts.length = bss.length
  | [], pts, h => by
    simp [decodePbPointsTotal] at h
    subst h; rfl
  | bs :: rest, pts, h => by
    unfold decodePbPointsTotal at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i tail htail
        simp only [Except.ok.injEq] at h
        subst h
        simp [decodePbPointsTotal_length rest tail htail]

theorem decodePbPolysTotal_length :
    ∀ (bss : List (List (BitVec 8))) (polys : List LibsignalSpqrV1.Poly),
      decodePbPolysTotal bss = .ok polys → polys.length = bss.length
  | [], polys, h => by
    simp [decodePbPolysTotal] at h
    subst h; rfl
  | bs :: rest, polys, h => by
    unfold decodePbPolysTotal at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i p hp tail htail
        simp only [Except.ok.injEq] at h
        subst h
        simp [decodePbPolysTotal_length rest tail htail]

theorem fromPbResult_eq_of_pts (pb : ProtoPolynomialEncoder)
    (hpts : pb.pts.length = 16) (hpolys : pb.polys.length = 0) :
    fromPbResult pb =
      match decodePbPointsTotal pb.pts with
      | .error e => .error e
      | .ok out => .ok { idx := pb.idx, s := .points out } := by
  unfold fromPbResult
  have h1 : (!pb.pts.isEmpty) = true := by
    cases h : pb.pts with
    | nil => simp [h] at hpts
    | cons _ _ => rfl
  have h2 : (!pb.polys.isEmpty) = false := by
    cases h : pb.polys with
    | nil => rfl
    | cons _ _ => simp [h] at hpolys
  have h3 : (pb.pts.length != NUM_POLYS) = false := by
    simp [hpts, NUM_POLYS, CHUNK_SIZE]
  rw [h1, h2, h3]
  rfl

theorem fromPbResult_eq_of_polys (pb : ProtoPolynomialEncoder)
    (hpts : pb.pts.length = 0) (hpolys : pb.polys.length = 16) :
    fromPbResult pb =
      match decodePbPolysTotal pb.polys with
      | .error e => .error e
      | .ok out => .ok { idx := pb.idx, s := .polys out } := by
  unfold fromPbResult
  have h1 : (!pb.pts.isEmpty) = false := by
    cases h : pb.pts with
    | nil => rfl
    | cons _ _ => simp [h] at hpts
  have h2 : (pb.polys.length == NUM_POLYS) = true := by
    simp [hpolys, NUM_POLYS, CHUNK_SIZE]
  rw [h1, h2]
  rfl

theorem fromPbResult_eq_of_err (pb : ProtoPolynomialEncoder)
    (hnot_pts : ¬(pb.pts.length = 16 ∧ pb.polys.length = 0))
    (hnot_polys : ¬(pb.pts.length = 0 ∧ pb.polys.length = 16)) :
    fromPbResult pb = .error .serializationInvalid := by
  unfold fromPbResult
  cases hpts_list : pb.pts with
  | nil =>
    have hpts0 : pb.pts.length = 0 := by simp [hpts_list]
    have hpolys16 : (pb.polys.length == NUM_POLYS) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      apply hnot_polys
      refine ⟨hpts0, ?_⟩
      simpa [NUM_POLYS, CHUNK_SIZE] using h
    rw [hpolys16]
    rfl
  | cons phead ptail =>
    cases hpolys_list : pb.polys with
    | nil =>
      have hpolys0 : pb.polys.length = 0 := by simp [hpolys_list]
      have hpts16 : ((phead :: ptail).length != NUM_POLYS) = true := by
        rw [bne_iff_ne]
        intro h
        apply hnot_pts
        refine ⟨?_, hpolys0⟩
        rw [hpts_list]
        simpa [NUM_POLYS, CHUNK_SIZE] using h
      rw [hpts16]
      rfl
    | cons _ _ =>
      rfl

theorem stack_split_for_pts (sp : BitVec 64) :
    stackAt (sp - 96#64) (dropGluePoly16Stack + 928) =
      ∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64,
        memRegion ((sp - 1024#64) - 4128#64) 32 ∗
        stackAt (sp - 1024#64) allocHookStack ∗
        cells (sp - 1024#64) 7 ∗
        (((sp - 1024#64) + 56#64) ↦₆₄ v56) ∗
        (((sp - 1024#64) + 64#64) ↦₆₄ v64) ∗
        memRegion ((sp - 1024#64) + 72#64) 384 ∗
        cells ((sp - 1024#64) + 456#64) 3 ∗
        memRegion ((sp - 1024#64) + 480#64) 384 ∗
        cells ((sp - 1024#64) + 864#64) 4 ∗
        cells ((sp - 1024#64) + 896#64) 3 ∗
        memRegion ((sp - 1024#64) + 920#64) 8 := by
  rw [stackAt_96_split_928 sp, stackAt_dropGluePoly16_split_bottom (sp - 1024#64),
      memRegion_928_split (sp - 1024#64), cells9_split_7_1_1 (sp - 1024#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact congrArg sepExists (funext fun v64 => congrArg sepExists (funext fun v56 => by ac_rfl))

theorem stack_split_for_polys (sp : BitVec 64) :
    stackAt (sp - 96#64) (dropGluePoly16Stack + 928) =
      memRegion ((sp - 1024#64) - 4128#64) 32 ∗
      stackAt (sp - 1024#64) allocHookStack ∗
      cells (sp - 1024#64) 4 ∗
      cells ((sp - 1024#64) + 32#64) 5 ∗
      memRegion ((sp - 1024#64) + 72#64) 384 ∗
      cells ((sp - 1024#64) + 456#64) 3 ∗
      cells ((sp - 1024#64) + 480#64) 48 ∗
      cells ((sp - 1024#64) + 864#64) 4 ∗
      cells ((sp - 1024#64) + 896#64) 3 ∗
      memRegion ((sp - 1024#64) + 920#64) 8 := by
  rw [stackAt_96_split_928 sp, stackAt_dropGluePoly16_split_bottom (sp - 1024#64),
      memRegion_928_split (sp - 1024#64), cells9_split_4_5 (sp - 1024#64),
      ProofLib.memRegion_cells ((sp - 1024#64) + 480#64) 48 (by decide)]
  ac_rfl

private theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

/-- `encoderFromPbSpec A` entails `encoderFromPbSpecX A` by framing the unused bottom stack region. -/
theorem encoderFromPbSpecX_of_encoderFromPbSpec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (encoderFromPbSpec A)) :
    subroutine_ok P addr (encoderFromPbSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : encoderFromPbStack ≤ encoderFromPbStackX := by decide
  have hsplit : stackAt s0.sp encoderFromPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encoderFromPbStackX)
        (encoderFromPbStackX - encoderFromPbStack) ∗
        stackAt s0.sp encoderFromPbStack := by
    have h1 := stackAt_split_bottom s0.sp encoderFromPbStack
      (encoderFromPbStackX - encoderFromPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encoderFromPbStackX)
      (encoderFromPbStackX - encoderFromPbStack) ∗ R
  have hpre' : s0.mem ⊨ (encoderFromPbSpec A).pre x s0 ∗ R' := by
    dsimp only [encoderFromPbSpecX, encoderFromPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encoderFromPbSpecX, encoderFromPbSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [encoderFromPbSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Placed Proofs for Block `374` -/

theorem from_pb_ok_polys_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
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
  refine seq_clean
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
    refine from_pb_ok_copy_out_placed hmemcpy_sat hdrop_pb s0 s1 fsp out pbA pbA 1#64 (hfsp_fn trivial)
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

theorem from_pb_ok_pts_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
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
  refine seq_clean
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
    refine from_pb_ok_copy_out_placed hmemcpy_sat hdrop_pb s0 s1 fsp out pbA v64 0#64 (hfsp_fn trivial)
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
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 40#64) ↦₆₄ 0#64) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  wp_steps
  wp_done

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
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ 0#64) ∗
          ((pbA + 40#64) ↦₆₄ 16#64) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  wp_steps
  wp_done

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
        (Pm ⊢ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 nPts) ∗
          ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 nPolys) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
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

theorem sepWPp_of_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64)
    (res : Except PolynomialError PolyEncoder)
    (P R : SepProp)
    (h : SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out res ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace)) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
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

theorem encoder_from_pb_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec A))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A)) :
    EncoderFromPbPlacedOkExt A ext := by
  unfold EncoderFromPbPlacedOkExt
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [encoderFromPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpts_max⟩, hmem⟩
  refine ⟨stackAt s0.sp encoderFromPbStack ∗
      (memRegion out polyEncoderSize ∗ protoPolynomialEncoderAt A pbA pb ∗ A.pool),
    R, ?_, ?_⟩
  · exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  dsimp only [encoderFromPbSpec]
  have hpro := from_pb_save_regs_placed (ext := ext) s0 out pbA hsp0_align
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
      (sepWPp_seq_clean hdisp ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hvregs2⟩
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
      (pts_outer_loop_placed h_panic hshim_sat halloc_sat s0 fsp ptsPtr hfsp_align pb.pts 0 [] s3
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
      have hok := from_pb_ok_pts_placed hmemcpy_sat hdrop_pb s0 sm fsp out pbA v64 hfsp
        ptsCap ptsPtr polysCap polysPtr pb tail htail_len htail_bound hsp0_align
        hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm
      refine SepWPp.weaken_pre ?_ (sepWPp_of_exit_placed s0 sm out pbA (.ok { idx := pb.idx, s := .points tail }) _ R hok)
      dsimp only [List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      rw [BitVec.add_zero, hpts16, hpolys0]
      exact Entails.of_eq (by ac_rfl)
    · rw [hdec_err]; dsimp only
      have herr := from_pb_err_pts_placed hdrop16 hdrop_pb s0 sm fsp out pbA v64 hfsp pb errPts herr_len
        hsp0_align hpcm hrunm hspm (hx1m.trans hx1_3) htrm hvregsm
      refine SepWPp.weaken_pre ?_ (sepWPp_of_exit_placed s0 sm out pbA (.error .serializationInvalid) _ R herr)
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
        (sepWPp_seq_clean hdisp ?_)
      intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx29_2, htr2, hvregs2⟩
      rw [stack_split_for_polys s0.sp, ← hfsp]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (polys_init_zero_headers_placed h_panic hshim_sat halloc_sat s0 s2 fsp out pbA polysPtr hfsp_align
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
        (polys_outer_loop_placed h_panic hshim_sat halloc_sat hdealloc_sat s0 fsp polysPtr hfsp_align pb.polys 0 [] s3
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
        have hok := from_pb_ok_polys_placed hmemcpy_sat hdrop_pb s0 sm fsp out pbA hfsp
          ptsCap ptsPtr polysCap polysPtr pb tail htail_len hsp0_align
          hpcm hrunm hspm htrm hvregsm
        refine SepWPp.weaken_pre ?_ (sepWPp_of_exit_placed s0 sm out pbA (.ok { idx := pb.idx, s := .polys tail }) _ R hok)
        dsimp only [List.nil_append, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
        rw [BitVec.add_zero, hpts0, hpolys16]
        exact Entails.of_eq (by ac_rfl)
      · rw [hdec_err]; dsimp only
        have herr := from_pb_err_polys_placed hdrop16 hdrop_pb s0 sm fsp out pbA hfsp pb errPolys herr_len
          hsp0_align hpcm hrunm hspm hx19m htrm hvregsm
        refine SepWPp.weaken_pre ?_ (sepWPp_of_exit_placed s0 sm out pbA (.error .serializationInvalid) _ R herr)
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
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hdisp ?_)
      intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, _, htr2, hvregs2⟩
      have herr := from_pb_err_header_placed hdrop_pb s0 s2 out pbA pb hsp0_align
        hpc2 hrun2 hsp2 hx0_2 hx1_2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1])
      refine SepWPp.weaken_pre ?_ (sepWPp_of_exit_placed s0 s2 out pbA (.error .serializationInvalid) _ R herr)
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

theorem encoder_from_pb_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec A))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A)) :
    EncoderFromPbPlacedOkX A ext :=
  encoderFromPbSpecX_of_encoderFromPbSpec (encoder_from_pb_placed_ok_ext h_panic hshim_sat halloc_sat hdealloc_sat hmemcpy_sat hdrop16 hdrop_pb)

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
