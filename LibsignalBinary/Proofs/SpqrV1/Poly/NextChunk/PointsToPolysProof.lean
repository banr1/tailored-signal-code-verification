/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1
import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Conversion Loop

Verifies per-iteration slot cleanup (`0x6b328..0x6b38c`, `+4004 -> +976 / +4424`) and the
16-iteration `pointsToPolysLoop_sepWPp` (`0x6a754..0x6b38c`, `+976 -> +4424`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_p2p :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
theorem add_8_add_8_eq (a : BitVec 64) : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega

/-! ## 1. Pure Polynomial Conversion and Slicing Helpers -/

/-- Pure polynomial interpolated from a `Point` (`ys = pt.value`). -/
def pointToPolyPure (pt : Point) : Poly :=
  if pt.value.length = 0 then
    Poly.zero
  else
    let pts := PolyEncoder.enumeratePts 0 pt.value
    Poly.lagrangeSum pts (completePointsBasisPure pts)

theorem fromCompletePoints_enumeratePts_eq (pt : Point)
    (hbound : pt.value.length ≤ 0x0555555555555555) :
    Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 pt.value) =
      .ok (.ok (pointToPolyPure pt)) := by
  have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
    enumeratePts_length 0 pt.value
  by_cases hn0 : pt.value.length = 0
  · have hnil : pt.value = [] := List.eq_nil_of_length_eq_zero hn0
    unfold pointToPolyPure
    simp only [hn0, ↓reduceIte]
    rw [hnil]
    rfl
  · have hcomp : Poly.checkCompletePoints 0 (PolyEncoder.enumeratePts 0 pt.value) = true :=
      checkCompletePoints_enumeratePts 0 pt.value
    have hbound' : (PolyEncoder.enumeratePts 0 pt.value).length ≤ 0x0555555555555555 := by
      omega
    rw [fromCompletePoints_eq_ok (PolyEncoder.enumeratePts 0 pt.value) hcomp hbound']
    unfold pointToPolyPure
    simp [hn0]

theorem lagrangeSumFoldPoly_length {n : Nat} :
    ∀ (pts : List Pt) (polys : List Poly) (acc : Poly),
      acc.coefficients.length = n →
      (∀ p ∈ polys, p.coefficients.length = n) →
      (lagrangeSumFoldPoly acc pts polys).coefficients.length = n
  | [], _, acc, hacc, _ => hacc
  | _ :: _, [], acc, hacc, _ => hacc
  | pt :: ptsRest, poly :: polysRest, acc, hacc, hplen => by
    have hp : poly.coefficients.length = n := hplen poly (List.mem_cons_self ..)
    have hacc' : (acc.addAssign (poly.multAssign pt.y)).coefficients.length = n := by
      unfold Poly.addAssign
      rw [addAssignCoeffs_length_eq (by rw [hacc, multAssign_length, hp]), hacc]
    exact lagrangeSumFoldPoly_length ptsRest polysRest _ hacc'
      (fun p hp' => hplen p (List.mem_cons_of_mem poly hp'))

theorem lagrangeSum_coefficients_length (pts : List Pt) (polys : List Poly) (n : Nat)
    (hpts : pts ≠ []) (hpolys : polys ≠ [])
    (hplen : ∀ p ∈ polys, p.coefficients.length = n) :
    (Poly.lagrangeSum pts polys).coefficients.length = n := by
  cases pts with
  | nil => contradiction
  | cons pt0 ptsRest =>
    cases polys with
    | nil => contradiction
    | cons poly0 polysRest =>
      rw [lagrangeSum_eq_foldPoly, lagrangeSumFoldPoly_cons]
      have hp0 : poly0.coefficients.length = n := hplen poly0 (List.mem_cons_self ..)
      have hacc0 : (Poly.zero.addAssign (poly0.multAssign pt0.y)).coefficients.length = n := by
        unfold Poly.addAssign Poly.zero
        rw [addAssignCoeffs_nil_left, multAssign_length, hp0]
      exact lagrangeSumFoldPoly_length ptsRest polysRest _ hacc0
        (fun p hp' => hplen p (List.mem_cons_of_mem poly0 hp'))

theorem pointToPolyPure_coefficients_length (pt : Point) :
    (pointToPolyPure pt).coefficients.length = pt.value.length := by
  unfold pointToPolyPure
  split
  · rename_i hn0
    simp [Poly.zero, hn0]
  · rename_i hn0
    have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
      enumeratePts_length 0 pt.value
    have hpts_ne : PolyEncoder.enumeratePts 0 pt.value ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hbasis_len :
        (completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value)).length =
          (PolyEncoder.enumeratePts 0 pt.value).length :=
      completePointsBasisPure_length _
    have hbasis_ne : completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value) ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hplen : ∀ p ∈ completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value),
        p.coefficients.length = (PolyEncoder.enumeratePts 0 pt.value).length :=
      completePointsBasisPure_mem_length (PolyEncoder.enumeratePts 0 pt.value)
    rw [lagrangeSum_coefficients_length _ _ _ hpts_ne hbasis_ne hplen, hlen]

/-- Dynamic buffer ownership of the newly constructed polynomial before writing its header to `slot`. -/
def newPolyBufAt (A : RustAlloc) (ptr : BitVec 64) (pt : Point) : SepProp :=
  if pt.value.length = 0 then
    ⌜ptr = 2#64⌝
  else
    ⌜ptr ≠ 0#64⌝ ∗
    A.live ptr (2 * pt.value.length) 2 ∗
    gf16SliceAt ptr (pointToPolyPure pt).coefficients

theorem polyOf_of_newPolyBufAt (A : RustAlloc) (slot ptr : BitVec 64) (pt : Point)
    (hbound : pt.value.length ≤ 0x0555555555555555) :
    (slot ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
    ((slot + 8#64) ↦₆₄ ptr) ∗
    ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
    newPolyBufAt A ptr pt ⊢
    polyOf A slot (pointToPolyPure pt) := by
  have hplen : (pointToPolyPure pt).coefficients.length = pt.value.length :=
    pointToPolyPure_coefficients_length pt
  unfold newPolyBufAt
  by_cases hn0 : pt.value.length = 0
  · simp only [hn0, ↓reduceIte]
    have hpull :
        (slot ↦₆₄ 0#64) ∗ ((slot + 8#64) ↦₆₄ ptr) ∗ ((slot + 16#64) ↦₆₄ 0#64) ∗ ⌜ptr = 2#64⌝ =
        ⌜ptr = 2#64⌝ ∗ ((slot ↦₆₄ 0#64) ∗ ((slot + 8#64) ↦₆₄ ptr) ∗ ((slot + 16#64) ↦₆₄ 0#64)) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hptr
    subst hptr
    have hp0 : pointToPolyPure pt = Poly.zero := by
      unfold pointToPolyPure; simp [hn0]
    rw [hp0]
    unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align Poly.zero
    apply Entails.sepExists_right 0#64
    apply Entails.sepExists_right 2#64
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.zero_mul, ↓reduceIte, sepConj_emp]
    rw [sepConj_comm (slot ↦₆₄ 0#64 ∗ (slot + 8#64) ↦₆₄ 2#64 ∗ (slot + 16#64) ↦₆₄ 0#64)]
    exact Entails.pure_right ⟨Nat.le_refl 0, by decide, by decide⟩ (Entails.refl _)
  · simp only [hn0, ↓reduceIte]
    have hpull :
        (slot ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((slot + 8#64) ↦₆₄ ptr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        (⌜ptr ≠ 0#64⌝ ∗ A.live ptr (2 * pt.value.length) 2 ∗
          gf16SliceAt ptr (pointToPolyPure pt).coefficients) =
        ⌜ptr ≠ 0#64⌝ ∗
        ((slot ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((slot + 8#64) ↦₆₄ ptr) ∗
         ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         A.live ptr (2 * pt.value.length) 2 ∗
         gf16SliceAt ptr (pointToPolyPure pt).coefficients) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hptr_ne
    rw [gf16SliceAt_eq_pointsToBytes]
    exact polyOf_of_pointsToBytes A slot ptr (pointToPolyPure pt) pt.value.length
      (by omega) (by omega) hptr_ne hplen

theorem polyOf_empty_unfold (A : RustAlloc) (slot : BitVec 64) :
    polyOf A slot ⟨[]⟩ ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (slot ↦₆₄ cap) ∗ ((slot + 8#64) ↦₆₄ ptr) ∗ ((slot + 16#64) ↦₆₄ 0#64) ∗
        (if cap = 0#64 then emp else A.live ptr (cap.toNat * 2) 2 ∗ memRegion ptr (cap.toNat * 2)) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.sepExists_right cap
  apply Entails.sepExists_right ptr
  simp only [List.length_nil, Nat.zero_le, true_and, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Nat.sub_zero, arrayAt, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem ptVecBufAt_pos_entails (A : RustAlloc) (ptr : BitVec 64) (ys : List GF16)
    (hpos : 0 < ys.length) (hbound : ys.length ≤ 0x0555555555555555) :
    ptVecBufAt A ptr ys ⊢
      ⌜ptr ≠ 0#64⌝ ∗ A.live ptr (4 * ys.length) 2 ∗ memRegion ptr (4 * ys.length) := by
  have hne0 : ys.length ≠ 0 := by omega
  have hlen_enum : (PolyEncoder.enumeratePts 0 ys).length = ys.length :=
    enumeratePts_length 0 ys
  unfold ptVecBufAt
  simp only [hne0, ↓reduceIte]
  have hmem := ptSliceAt_entails_memRegion ptr (PolyEncoder.enumeratePts 0 ys) (by omega)
  rw [hlen_enum] at hmem
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hmem)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem pointsToPolysLoop_eq_map (pts : List Point)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555) :
    ∀ (rem i : Nat) (acc : List Poly),
      i + rem = pts.length →
      PolyEncoder.pointsToPolysLoop pts i rem acc =
        .ok (acc ++ (pts.drop i).map pointToPolyPure)
  | 0, i, acc, hlen => by
    have hi : i = pts.length := by omega
    subst hi
    simp [PolyEncoder.pointsToPolysLoop]
  | rem + 1, i, acc, hlen => by
    have hi : i < pts.length := by omega
    have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
    have hbound_i : (pts[i]'hi).value.length ≤ 0x0555555555555555 :=
      hbounds (pts[i]'hi) (List.getElem_mem hi)
    have hfc := fromCompletePoints_enumeratePts_eq (pts[i]'hi) hbound_i
    have ih := pointsToPolysLoop_eq_map pts hbounds rem (i + 1)
      (acc ++ [pointToPolyPure (pts[i]'hi)]) (by omega)
    have hdrop : pts.drop i = (pts[i]'hi) :: pts.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    unfold PolyEncoder.pointsToPolysLoop
    simp only [hpt, hfc, ih, hdrop, List.map_cons, List.append_assoc, List.singleton_append,
      Bind.bind, Except.bind]

/-! ## 2. Per-Iteration Cleanup (`0x6b328..0x6b38c`, `+4004 -> +976 / +4424`) -/

theorem cmn_one_ne_zero {n : Nat} (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n + 1#64 == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h1 : (BitVec.ofNat 64 n + 1#64).toNat = 0 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)] at h1
  omega

theorem shl1_oldCap_eq {cap : BitVec 64} (h : cap.toNat * 2 < 2 ^ 63) :
    cap <<< (1 : Nat) = BitVec.ofNat 64 (cap.toNat * 2) ∧
    (cap <<< 1#64) = BitVec.ofNat 64 (cap.toNat * 2) ∧
    (BitVec.ofNat 64 (cap.toNat * 2)).toNat = cap.toNat * 2 := by
  have hto : (cap <<< 1#64).toNat = cap.toNat * 2 :=
    CryptoVerification.SpqrV1.Drop.shiftLeft_one_toNat h
  have hmod : (BitVec.ofNat 64 (cap.toNat * 2)).toNat = cap.toNat * 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heq : cap <<< 1#64 = BitVec.ofNat 64 (cap.toNat * 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [hto, hmod]
  exact ⟨heq, heq, hmod⟩

theorem shl2_len_eq {n : Nat} (hn : n ≤ 0x0555555555555555) :
    BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) ∧
    BitVec.ofNat 64 n <<< 2#64 = BitVec.ofNat 64 (4 * n) ∧
    (BitVec.ofNat 64 (4 * n)).toNat = 4 * n := by
  have hmod : (BitVec.ofNat 64 (4 * n)).toNat = 4 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmod_n : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hto : (BitVec.ofNat 64 n <<< (2 : Nat)).toNat = 4 * n := by
    rw [BitVec.toNat_shiftLeft, hmod_n, Nat.shiftLeft_eq]
    have hs : n * 2 ^ 2 = 4 * n := by omega
    rw [hs, Nat.mod_eq_of_lt (by omega)]
  have h1 : BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [hto, hmod]
  exact ⟨h1, h1, hmod⟩

theorem ptVecBufAt_zero_drop (A : RustAlloc) (ptr : BitVec 64) (ys : List GF16)
    (hn0 : ys.length = 0) (Rest : SepProp) :
    ptVecBufAt A ptr ys ∗ Rest ⊢ Rest := by
  have hnil : ys = [] := List.eq_nil_of_length_eq_zero hn0
  subst hnil
  unfold ptVecBufAt PolyEncoder.enumeratePts ptSliceAt arrayAt
  simp only [List.length_nil, ↓reduceIte, emp_sepConj, sepConj_emp]
  apply Entails.pure_left; intro _
  exact Entails.refl _

/-- Sub-block 1 (`0x6b328..0x6b354`, `+4004 -> +4048`):
    checks `x19 + 1 != 0`, computes `slot = (fsp + 256) + 24 * j`, and deallocates the old
    `Poly` buffer in `slot` if `oldCap != 0`. -/
theorem deallocOldPolySlot_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j n : Nat) (hn : n ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4004#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 n)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1 oldCap oldPtr,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4048#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 n →
      s1.readReg64 .x20 = (fsp + 256#64) + BitVec.ofNat 64 (24 * j) →
      s1.readReg64 .x21 = ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
         (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
       polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  simp only [rustDeallocSpec] at hdealloc
  have hcmn := cmn_one_ne_zero hn
  have hmul24 : BitVec.ofNat 64 j * 24#64 = BitVec.ofNat 64 (24 * j) := by bv_omega
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (polyOf_empty_unfold A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro oldCap
  apply SepWP.exists_elim; intro oldPtr
  have hpull :
      A.pool ∗
      (⌜oldCap.toNat * 2 < 2 ^ 63 ∧ oldPtr ≠ 0#64⌝ ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       (if oldCap = 0#64 then emp else A.live oldPtr (oldCap.toNat * 2) 2 ∗ memRegion oldPtr (oldCap.toNat * 2))) ∗
      stackAt fsp allocHookStack ∗ Frame =
      ⌜oldCap.toNat * 2 < 2 ^ 63 ∧ oldPtr ≠ 0#64⌝ ∗
      (A.pool ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       (if oldCap = 0#64 then emp else A.live oldPtr (oldCap.toNat * 2) 2 ∗ memRegion oldPtr (oldCap.toNat * 2)) ∗
       stackAt fsp allocHookStack ∗ Frame) := by
    ac_rfl
  rw [hpull]
  apply SepWP.pure_elim; rintro ⟨holdCap_lt, holdPtr_ne⟩
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xfa4 44
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  by_cases hcap0 : oldCap = 0#64
  · subst hcap0
    simp only [↓reduceIte, sepConj_emp]
    wp_steps
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ 0#64 oldPtr
        (by subst hentry; simp only [arm64_norm, wp_norm, hx19, hcmn])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by simp only [arm64_norm, wp_norm, hsp, hx20, hx28, hmul24])
        (by simp only [arm64_norm, wp_norm, hsp, hx20, hx28, hmul24])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx28])
        (by simp only [arm64_norm, wp_norm]))
  · have hcap_beq : (oldCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hcap_bne : ¬(oldCap == 0#64) = true := by simp [hcap_beq]
    obtain ⟨hshl_nat, hshl_bv, hshl_toNat⟩ := shl1_oldCap_eq holdCap_lt
    simp only [hcap0, ↓reduceIte]
    rw [← hshl_toNat]
    wp_steps; wp_apply
    subst hentry
    have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = _›]; simp only [arm64_norm, wp_norm, hsp]
    rw [hsp]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont sf oldCap oldPtr hpc_sf hrun_sf hsp_sf
        (by rw [hpost])
        (by rw [hvregs])
        (by rw [h]; simp only [arm64_norm, wp_norm, hx19])
        (by rw [h_1])
        (by rw [h_2])
        (by rw [h_7])
        (by rw [h_8])
        (by rw [h_9]; simp only [arm64_norm, wp_norm, hx28])
        (by rw [hcs_sf]))

/-- Sub-block 2 (`0x6b354..0x6b37c`, `+4048 -> +4088`):
    writes the new `Poly` header `(n, newPtr, n)` into `slot = (fsp + 256) + 24 * j`,
    folds `polyOf A slot (pointToPolyPure pt)`, and deallocates `ptVecBufAt A ptVecPtr pt.value`. -/
theorem storeNewPolyAndFreePtVec_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s : State) (fsp oldCap oldPtr newPtr ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4048#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 pt.value.length)
    (hx20 : s.readReg64 .x20 = (fsp + 256#64) + BitVec.ofNat 64 (24 * j))
    (hx21 : s.readReg64 .x21 = ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4088#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       newPolyBufAt A newPtr pt ∗
       ptVecBufAt A ptVecPtr pt.value ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  simp only [rustDeallocSpec] at hdealloc
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xfd0 40
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  by_cases hn0 : pt.value.length = 0
  · have hpoly0 := polyOf_of_newPolyBufAt A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) newPtr pt hbound
    simp only [hn0, BitVec.ofNat_eq_ofNat] at hpoly0
    wp_steps
    apply SepWP.fold hpoly0 (by sep_focus)
    simp only [hn0, BitVec.ofNat_eq_ofNat] at hcont ⊢
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        ptVecBufAt A ptVecPtr pt.value ∗
        (A.pool ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 40#64) ↦₆₄ 0#64) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ 0#64) ∗
         stackAt fsp allocHookStack ∗ Frame) by ac_rfl))
        (ptVecBufAt_zero_drop A ptVecPtr pt.value hn0 _))
      (hcont _
        (by subst hentry; simp only [arm64_norm, wp_norm, hn0])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx28])
        (by simp only [arm64_norm, wp_norm]))
  · have hn_pos : 0 < pt.value.length := by omega
    obtain ⟨hn_beq, hn_bne⟩ := ofNat_pos_ne_zero hn_pos hbound
    obtain ⟨hshl2_nat, hshl2_bv, hshl2_toNat⟩ := shl2_len_eq hbound
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ptVecBufAt_pos_entails A ptVecPtr pt.value hn_pos hbound))))))) ?_
    have hpull :
        A.pool ∗
        (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
        ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
        ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
        newPolyBufAt A newPtr pt ∗
        (⌜ptVecPtr ≠ 0#64⌝ ∗ A.live ptVecPtr (4 * pt.value.length) 2 ∗ memRegion ptVecPtr (4 * pt.value.length)) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((fsp + 640#64) ↦₆₄ newPtr) ∗
        ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        stackAt fsp allocHookStack ∗ Frame =
        ⌜ptVecPtr ≠ 0#64⌝ ∗
        (A.pool ∗
         (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
         newPolyBufAt A newPtr pt ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗ memRegion ptVecPtr (4 * pt.value.length) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) := by
      ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hptVec_ne
    rw [← hshl2_toNat]
    wp_steps; wp_apply
    subst hentry
    have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = _›]; simp only [arm64_norm, wp_norm, hsp]
    rw [hsp]
    apply SepWP.fold (polyOf_of_newPolyBufAt A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) newPtr pt hbound)
      (by sep_focus)
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont sf hpc_sf hrun_sf hsp_sf
        (by rw [hpost])
        (by rw [hvregs])
        (by rw [h_8])
        (by rw [h_9]; simp only [arm64_norm, wp_norm, hx28])
        (by rw [hcs_sf]))

/-- Full per-iteration cleanup (`0x6b328..0x6b38c`, `+4004 -> +976 / +4424`):
    deallocates the dummy `Poly` buffer in `slot j`, writes the newly constructed `Poly` into `slot j`,
    deallocates `ptVecBufAt`, reloads `x20 = j + 1` and `x19 = ptsBase`, and branches to
    `+976` (`j < 15`) or `+4424` (`j = 15`). -/
theorem cleanupIter_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s : State) (fsp ptsBase newPtr ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4004#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 pt.value.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1,
      s1.pc = (if j == 15 then
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64
      else
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = ptsBase →
      s1.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
       polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       newPolyBufAt A newPtr pt ∗
       ptVecBufAt A ptVecPtr pt.value ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (deallocOldPolySlot_sepWP hA s fsp hfsp_align j pt.value.length hbound
      (newPolyBufAt A newPtr pt ∗
       ptVecBufAt A ptVecPtr pt.value ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗ Frame)
      hpc hrun hsp hx19 hx20 hx28 ?_)
  intro s1 oldCap oldPtr hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx26_1 hx27_1 hx28_1 hx29_1
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (storeNewPolyAndFreePtVec_sepWP hA s1 fsp oldCap oldPtr newPtr ptVecPtr hfsp_align j pt hbound
      (((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ Frame)
      hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 (hx26_1.trans hx26) hx28_1 ?_)
  intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx28_2 hx29_2
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xff8 20
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc2 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  by_cases hj15 : j = 15
  · subst hj15
    wp_steps
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _
        (by subst hentry; simp only [arm64_norm, wp_norm])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp2])
        (by simp only [arm64_norm, wp_norm, htr2, htr1])
        (by simp only [arm64_norm, wp_norm, hvregs2, hvregs1])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx27_2, hx27_1])
        (by simp only [arm64_norm, wp_norm, hx28_2])
        (by simp only [arm64_norm, wp_norm, hx29_2, hx29_1]))
  · have hj15_beq : (j == 15) = false := beq_eq_false_iff_ne.mpr hj15
    have hcmp_sub : (BitVec.ofNat 64 (j + 1) - 16#64 == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr; bv_omega
    have hcmp_eq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := by
      apply beq_eq_false_iff_ne.mpr; bv_omega
    have hcmp_bne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := by
      simp [bne, hcmp_eq]
    wp_steps
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _
        (by subst hentry; simp only [arm64_norm, wp_norm, hj15_beq, hcmp_sub, hcmp_eq, hcmp_bne]; rfl)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp2])
        (by simp only [arm64_norm, wp_norm, htr2, htr1])
        (by simp only [arm64_norm, wp_norm, hvregs2, hvregs1])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx27_2, hx27_1])
        (by simp only [arm64_norm, wp_norm, hx28_2])
        (by simp only [arm64_norm, wp_norm, hx29_2, hx29_1]))

/-! ## 3. Full Per-Iteration & 16-Iteration `points_to_polys` Loop (`0x6a754..0x6b38c`, `+976 -> +4424`) -/

theorem stackAt_lagrangePrepare_fold_alloc (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack) (lagrangePrepareStack - allocHookStack) ⊢
    stackAt fsp lagrangePrepareStack := by
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  exact Entails.refl _

theorem memRegion_112_split_216 (fsp : BitVec 64) :
    memRegion (fsp + 112#64) 120 ⊢
      ∃∗ u216 : BitVec 64, ∃∗ u224 : BitVec 64,
        memRegion (fsp + 112#64) 104 ∗
        ((fsp + 216#64) ↦₆₄ u216) ∗
        ((fsp + 224#64) ↦₆₄ u224) := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 104) (k := 16) (b' := fsp + 216#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u224
  apply Entails.sepExists_elim; intro u216
  exact Entails.sepExists_right u216 (Entails.sepExists_right u224 (Entails.of_eq (by ac_rfl)))

theorem memRegion_112_fold_216 (fsp u216 u224 : BitVec 64) :
    memRegion (fsp + 112#64) 104 ∗
    ((fsp + 216#64) ↦₆₄ u216) ∗
    ((fsp + 224#64) ↦₆₄ u224) ⊢
    memRegion (fsp + 112#64) 120 := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 104) (k := 16) (b' := fsp + 216#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u224
  apply Entails.sepExists_right u216
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_656_fold (fsp u656 u664 u672 : BitVec 64) :
    ((fsp + 656#64) ↦₆₄ u656) ∗
    ((fsp + 664#64) ↦₆₄ u664) ∗
    ((fsp + 672#64) ↦₆₄ u672) ⊢
    memRegion (fsp + 656#64) 24 := by
  rw [memRegion24_off_eq_polyHeader fsp]
  exact Entails.sepExists_right u672
    (Entails.sepExists_right u664
      (Entails.sepExists_right u656 (Entails.of_eq (by ac_rfl))))

theorem newPolyBufAt_n0_intro (A : RustAlloc) (pt : Point) (hn0 : pt.value.length = 0)
    (Rest : SepProp) :
    Rest ⊢ newPolyBufAt A 2#64 pt ∗ Rest := by
  unfold newPolyBufAt
  simp only [hn0, ↓reduceIte, pure_true, emp_sepConj]
  exact Entails.refl _

theorem newPolyBufAt_pos_intro (A : RustAlloc) (accPtr : BitVec 64) (pt : Point)
    (hn0 : pt.value.length ≠ 0) (hacc_ne : accPtr ≠ 0#64) (Rest : SepProp) :
    A.live accPtr (2 * (PolyEncoder.enumeratePts 0 pt.value).length) 2 ∗
    gf16SliceAt accPtr
      (Poly.lagrangeSum (PolyEncoder.enumeratePts 0 pt.value)
        (completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value))).coefficients ∗
    Rest ⊢
    newPolyBufAt A accPtr pt ∗ Rest := by
  have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
    enumeratePts_length 0 pt.value
  have hp : pointToPolyPure pt =
      Poly.lagrangeSum (PolyEncoder.enumeratePts 0 pt.value)
        (completePointsBasisPure (PolyEncoder.enumeratePts 0 pt.value)) := by
    unfold pointToPolyPure
    simp [hn0]
  unfold newPolyBufAt
  simp only [hn0, ↓reduceIte, hlen, ← hp]
  rw [sepConj_assoc]
  refine Entails.pure_right hacc_ne ?_
  exact Entails.of_eq (by ac_rfl)

theorem ptVecBufAt_pos_fold (A : RustAlloc) (ptVecPtr : BitVec 64) (pt : Point)
    (hn0 : pt.value.length ≠ 0) (hpt_ne : ptVecPtr ≠ 0#64) (Rest : SepProp) :
    ptSliceAt ptVecPtr (PolyEncoder.enumeratePts 0 pt.value) ∗
    A.live ptVecPtr (4 * pt.value.length) 2 ∗
    Rest ⊢
    ptVecBufAt A ptVecPtr pt.value ∗ Rest := by
  unfold ptVecBufAt
  simp only [hn0, ↓reduceIte]
  rw [sepConj_assoc]
  refine Entails.pure_right hpt_ne ?_
  exact Entails.of_eq (by ac_rfl)

/-- One full iteration (`j < 16`, `0x6a754..0x6b38c`, `+976 -> +976 / +4424`) of the
    `points_to_polys` conversion loop: converts `pts[j]` into `pointToPolyPure pts[j]` and
    stores it into slot `j` of `[fsp + 256 .. fsp + 640)`. -/
theorem pointsToPolysStep_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (s0 s : State) (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      s_out.pc = (if j == 15 then
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64
      else
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64) →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool ∗
         pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
       polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (setupPtVec_sepWPp hA s0 s fsp ptsBase hfsp_align j hj pt hbound u32 u40
      (polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
       memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗ Frame) R
      hpc hrun hsp htrace hx19 hx20 hx28 ?_)
  intro s1 ptVecPtr hptVec_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  by_cases hn0 : pt.value.length = 0
  · rw [memRegion24_off_eq_polyHeader fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro u672
    apply SepWPp.exists_elim; intro u664
    apply SepWPp.exists_elim; intro u656
    have hx25_0 : s1.readReg64 .x25 = 0#64 := by rw [hx25_1, hn0]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (basis_n0_sepWPp s0 s1 fsp hfsp_align u24 u96 u640 u648 u664 u672
        (A.pool ∗
         pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ptVecBufAt A ptVecPtr pt.value ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         stackAt fsp allocHookStack ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 656#64) ↦₆₄ u656) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗ Frame) R
        hpc1 hrun1 hsp1 htr1 hx25_0 ?_)
    intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
    have hx19_2' : s2.readReg64 .x19 = BitVec.ofNat 64 pt.value.length := by
      rw [hx19_2, hn0]
    have h648_eq : ((fsp + 648#64) ↦₆₄ 0#64) = ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) := by
      rw [hn0]
    rw [h648_eq]
    apply SepWPp.of_sepWP (mid := if j == 15 then
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64
    else
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64)
    refine SepWP.weaken_pre (newPolyBufAt_n0_intro A pt hn0 _) ?_
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (cleanupIter_sepWP hA s2 fsp ptsBase 2#64 ptVecPtr hfsp_align j hj pt hbound
        (pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ 0#64) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 96#64) ↦₆₄ 0#64) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 656#64) ↦₆₄ u656) ∗ ((fsp + 664#64) ↦₆₄ 2#64) ∗ ((fsp + 672#64) ↦₆₄ 0#64) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗ Frame)
        hpc2 hrun2 hsp2 hx19_2' (hx20_2.trans hx20_1) (hx26_2.trans hx26_1) (hx28_2.trans hx28_1) ?_)
    intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx27_3 hx28_3 hx29_3
    apply SepWP.done hpc3 hrun3
    apply SepWPp.fold (memRegion_656_fold fsp u656 2#64 0#64) (by sep_focus)
    apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc fsp) (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont s3 u16 0#64 (BitVec.ofNat 64 (j + 1)) (BitVec.ofNat 64 pt.value.length)
        u64 u72 u80 0#64 2#64 (BitVec.ofNat 64 pt.value.length) u1040 u1048 u1056
        hpc3 hrun3 hsp3 (htr3.trans htr2) (hvregs3.trans (hvregs2.trans hvregs1)) hx19_3 hx20_3
        (hx27_3.trans (hx27_2.trans hx27_1)) hx28_3
        (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))))
  · have hpts_len : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
      enumeratePts_length 0 pt.value
    have hpts_ne : PolyEncoder.enumeratePts 0 pt.value ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hpts_bound : (PolyEncoder.enumeratePts 0 pt.value).length ≤ 0x0555555555555555 := by
      omega
    unfold ptVecBufAt
    simp only [hn0, ↓reduceIte]
    apply SepWPp.fold (memRegion_112_split_216 fsp) (by sep_focus)
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
    apply SepWPp.exists_elim; intro u216
    apply SepWPp.exists_elim; intro u224
    apply SepWPp.pure_left; intro _
    apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc fsp) (by sep_focus)
    have hx24_1' : s1.readReg64 .x24 = BitVec.ofNat 64 (4 * (PolyEncoder.enumeratePts 0 pt.value).length) := by
      rw [hpts_len, hx24_1]
    have hx25_1' : s1.readReg64 .x25 = BitVec.ofNat 64 (PolyEncoder.enumeratePts 0 pt.value).length := by
      rw [hpts_len, hx25_1]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (basis_pos_sepWPp hA hb (PolyEncoder.enumeratePts 0 pt.value) hpts_ne hpts_bound
        s0 s1 fsp ptVecPtr hfsp_align u24 u72 u80 u96 u216 u224 u1040 u1048 u1056
        (pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         memRegion (fsp + 112#64) 104 ∗
         ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗ Frame) R
        hpc1 hrun1 hsp1 htr1 hx24_1' hx25_1' hx26_1 (hx29_1.trans hx29) ?_)
    intro s2 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
      hbasis_ne hacc_ne hpc2 hrun2 hsp2 htr2 hvregs2 hx0_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
    apply SepWPp.fold (memRegion_112_fold_216 fsp u216' u224') (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (lagrangeSumAndFree_sepWPp hA hb (PolyEncoder.enumeratePts 0 pt.value) hpts_ne hpts_bound
        s0 s2 fsp accPtr basisPtr ptVecPtr (BitVec.ofNat 64 j) (s.readReg64 .x27)
        hfsp_align u16 u64 u72' u80' u640 u648
        (pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysAt b ∗ Frame) R
        hpc2 hrun2 hsp2 htr2 hx0_2 (hx20_2.trans hx20_1) hx24_2 hx25_2 hx26_2
        (hx27_2.trans hx27_1) (hx28_2.trans hx28_1) hx29_2 ?_)
    intro s3 u656' u664' u672' hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx26_3 hx27_3 hx28_3 hx29_3
    have hx19_3' : s3.readReg64 .x19 = BitVec.ofNat 64 pt.value.length := by
      rw [← hpts_len, hx19_3]
    apply SepWPp.fold (newPolyBufAt_pos_intro A accPtr pt hn0 hacc_ne emp) (by sep_focus)
    apply SepWPp.fold (ptVecBufAt_pos_fold A ptVecPtr pt hn0 hptVec_ne emp) (by sep_focus)
    apply SepWPp.fold (memRegion_656_fold fsp u656' u664' u672') (by sep_focus)
    rw [hpts_len, stackAt_lagrangePrepare_split_alloc fsp]
    apply SepWPp.of_sepWP (mid := if j == 15 then
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64
    else
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64)
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (cleanupIter_sepWP hA s3 fsp ptsBase accPtr ptVecPtr hfsp_align j hj pt hbound
        (pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ s.readReg64 .x27) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         memRegion (fsp + 112#64) 120 ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗ Frame)
        hpc3 hrun3 hsp3 hx19_3' hx20_3 hx26_3 hx28_3 ?_)
    intro s4 hpc4 hrun4 hsp4 htr4 hvregs4 hx19_4 hx20_4 hx27_4 hx28_4 hx29_4
    apply SepWP.done hpc4 hrun4
    apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc fsp) (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont s4 (BitVec.ofNat 64 j) (BitVec.ofNat 64 pt.value.length)
        (BitVec.ofNat 64 (j + 1)) (BitVec.ofNat 64 pt.value.length)
        (s.readReg64 .x27) basisPtr ptVecPtr (BitVec.ofNat 64 pt.value.length)
        accPtr (BitVec.ofNat 64 pt.value.length) u1040' u1048' u1056'
        hpc4 hrun4 hsp4 (htr4.trans htr3)
        (hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1))) hx19_4 hx20_4
        (hx27_4.trans hx27_3) hx28_4 (hx29_4.trans hx29_3))

theorem pointListOf_cons_mul24_off (A : RustAlloc) (base : BitVec 64) (j : Nat)
    (pt : Point) (pts : List Point) :
    pointListOf A (base + BitVec.ofNat 64 (24 * j)) (pt :: pts) =
      pointOf A (base + BitVec.ofNat 64 (24 * j)) pt ∗
      pointListOf A (base + BitVec.ofNat 64 (24 * (j + 1))) pts := by
  dsimp only [pointListOf, arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * j)) + 24#64 = base + BitVec.ofNat 64 (24 * (j + 1)) := by
    bv_omega
  rw [haddr]

theorem polyListOf_cons_mul24_off (A : RustAlloc) (base : BitVec 64) (j : Nat)
    (p : Poly) (ps : List Poly) :
    polyListOf A (base + BitVec.ofNat 64 (24 * j)) (p :: ps) =
      polyOf A (base + BitVec.ofNat 64 (24 * j)) p ∗
      polyListOf A (base + BitVec.ofNat 64 (24 * (j + 1))) ps := by
  dsimp only [polyListOf, arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * j)) + 24#64 = base + BitVec.ofNat 64 (24 * (j + 1)) := by
    bv_omega
  rw [haddr]

/-- Tail induction for `points_to_polys` (`0x6a754..0x6b38c`, `+976 -> +4424`) over the remaining
    `rem + 1` points starting at index `j` (`j + (rem + 1) = 16`). -/
theorem pointsToPolysLoop_tail_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (s0 : State) (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (R : SepProp) :
    ∀ (rem j : Nat) (pts : List Point)
      (_hlen : pts.length = rem + 1) (_hsum : j + (rem + 1) = 16)
      (_hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
      (s : State)
      (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
      (Frame : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64 →
      s.status = .Running → s.sp = fsp → s.trace = s0.trace →
      s.readReg64 .x19 = ptsBase →
      s.readReg64 .x20 = BitVec.ofNat 64 j →
      s.readReg64 .x28 = 24#64 →
      s.readReg64 .x29 = fsp + 1104#64 →
      (∀ s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
        s_out.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64 →
        s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
        calleeSavedVRegs s_out = calleeSavedVRegs s →
        s_out.readReg64 .x19 = ptsBase →
        s_out.readReg64 .x20 = 16#64 →
        s_out.readReg64 .x27 = s.readReg64 .x27 →
        s_out.readReg64 .x28 = 24#64 →
        s_out.readReg64 .x29 = fsp + 1104#64 →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s_out
          (A.pool ∗
           pointListOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pts ∗
           polyListOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pts.map pointToPolyPure) ∗
           ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
           ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
           ((fsp + 48#64) ↦₆₄ 2#64) ∗
           ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
           ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
           memRegion (fsp + 112#64) 120 ∗
           ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
           memRegion (fsp + 656#64) 24 ∗
           ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
           completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
           stackAt fsp lagrangePrepareStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
        (A.pool ∗
         pointListOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pts ∗
         polyListOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (List.replicate (rem + 1) ⟨[]⟩) ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
         ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | 0, j, pts, hlen, hsum, hbounds, s,
    u16, u24, u32, u40, u64, u72, u80, u96, u640, u648, u1040, u1048, u1056, Frame,
    hpc, hrun, hsp, htrace, hx19, hx20, hx28, hx29, hcont => by
    cases pts with
    | nil => contradiction
    | cons pt pts_rest =>
      have hnil : pts_rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hnil
      have hj15 : j = 15 := by omega
      subst hj15
      have hbound : pt.value.length ≤ 0x0555555555555555 :=
        hbounds pt List.mem_cons_self
      dsimp only [List.replicate, List.map, pointListOf, polyListOf, arrayAt] at hcont ⊢
      simp only [sepConj_emp] at hcont ⊢
      exact pointsToPolysStep_sepWPp hA hb s0 s fsp ptsBase hfsp_align 15 (by decide) pt hbound
        u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
        hpc hrun hsp htrace hx19 hx20 hx28 hx29
        (fun s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
          hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out =>
          hcont s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
            hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out)
  | rem' + 1, j, pts, hlen, hsum, hbounds, s,
    u16, u24, u32, u40, u64, u72, u80, u96, u640, u648, u1040, u1048, u1056, Frame,
    hpc, hrun, hsp, htrace, hx19, hx20, hx28, hx29, hcont => by
    cases pts with
    | nil => contradiction
    | cons pt pts_rest =>
      have hlen_rest : pts_rest.length = rem' + 1 := by simpa using hlen
      have hj16 : j < 16 := by omega
      have hj_ne15 : (j == 15) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hbound : pt.value.length ≤ 0x0555555555555555 :=
        hbounds pt List.mem_cons_self
      have hbounds_rest : ∀ pt' ∈ pts_rest, pt'.value.length ≤ 0x0555555555555555 :=
        fun pt' hmem => hbounds pt' (List.mem_cons_of_mem pt hmem)
      rw [List.replicate_succ,
          pointListOf_cons_mul24_off A ptsBase j pt pts_rest,
          polyListOf_cons_mul24_off A (fsp + 256#64) j ⟨[]⟩ (List.replicate (rem' + 1) ⟨[]⟩)]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (pointsToPolysStep_sepWPp hA hb s0 s fsp ptsBase hfsp_align j hj16 pt hbound
          u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
          (pointListOf A (ptsBase + BitVec.ofNat 64 (24 * (j + 1))) pts_rest ∗
           polyListOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * (j + 1))) (List.replicate (rem' + 1) ⟨[]⟩) ∗
           Frame) R
          hpc hrun hsp htrace hx19 hx20 hx28 hx29 ?_)
      intro s_mid u16_m u24_m u32_m u40_m u64_m u72_m u80_m u96_m u640_m u648_m u1040_m u1048_m u1056_m
        hpc_m hrun_m hsp_m htr_m hvregs_m hx19_m hx20_m hx27_m hx28_m hx29_m
      rw [hj_ne15] at hpc_m
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (pointsToPolysLoop_tail_sepWPp hA hb s0 fsp ptsBase hfsp_align R rem' (j + 1) pts_rest
          hlen_rest (by omega) hbounds_rest s_mid
          u16_m u24_m u32_m u40_m u64_m u72_m u80_m u96_m u640_m u648_m u1040_m u1048_m u1056_m
          (pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
           polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
           Frame)
          hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx28_m hx29_m ?_)
      intro s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
        hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out
      have hfold :
          A.pool ∗
          pointListOf A (ptsBase + BitVec.ofNat 64 (24 * (j + 1))) pts_rest ∗
          polyListOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * (j + 1))) (pts_rest.map pointToPolyPure) ∗
          ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
          ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
          ((fsp + 48#64) ↦₆₄ 2#64) ∗
          ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
          ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
          memRegion (fsp + 112#64) 120 ∗
          ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
          memRegion (fsp + 656#64) 24 ∗
          ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
          completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
          stackAt fsp lagrangePrepareStack ∗
          (pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
           polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗ Frame) =
          A.pool ∗
          pointListOf A (ptsBase + BitVec.ofNat 64 (24 * j)) (pt :: pts_rest) ∗
          polyListOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ((pt :: pts_rest).map pointToPolyPure) ∗
          ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
          ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
          ((fsp + 48#64) ↦₆₄ 2#64) ∗
          ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
          ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
          memRegion (fsp + 112#64) 120 ∗
          ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
          memRegion (fsp + 656#64) 24 ∗
          ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
          completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
          stackAt fsp lagrangePrepareStack ∗ Frame := by
        rw [List.map_cons,
            pointListOf_cons_mul24_off A ptsBase j pt pts_rest,
            polyListOf_cons_mul24_off A (fsp + 256#64) j (pointToPolyPure pt) (pts_rest.map pointToPolyPure)]
        ac_rfl
      refine SepWPp.weaken_pre (Entails.of_eq hfold)
        (hcont s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
          hpc_out hrun_out hsp_out htr_out (hvregs_out.trans hvregs_m) hx19_out hx20_out (hx27_out.trans hx27_m) hx28_out hx29_out)

/-- Full 16-iteration `points_to_polys` loop (`0x6a754..0x6b38c`, `+976 -> +4424`):
    converts `pointListOf A ptsBase pts` (`pts.length = 16`) and `zeroPolySlotsAt A (fsp + 256#64) 16`
    into `polyListOf A (fsp + 256#64) (pts.map pointToPolyPure)`. -/
theorem pointsToPolysLoop_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (s0 s : State) (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (hlen : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      s_out.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool ∗
         pointListOf A ptsBase pts ∗
         polyListOf A (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       pointListOf A ptsBase pts ∗
       zeroPolySlotsAt A (fsp + 256#64) 16 ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  apply SepWPp.fold (zeroPolySlotsAt_entails_polyListOf A 16 (fsp + 256#64)) (by sep_focus)
  have h0_pts : ptsBase = ptsBase + BitVec.ofNat 64 (24 * 0) := by simp
  have h0_fsp : fsp + 256#64 = (fsp + 256#64) + BitVec.ofNat 64 (24 * 0) := by simp
  refine SepWPp.weaken_pre (Entails.of_eq (by rw [← h0_pts, ← h0_fsp]; ac_rfl))
    (pointsToPolysLoop_tail_sepWPp hA hb s0 fsp ptsBase hfsp_align R 15 0 pts
      hlen rfl hbounds s u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame
      hpc hrun hsp htrace hx19 hx20 hx28 hx29 ?_)
  intro s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out
  rw [← h0_pts, ← h0_fsp]
  exact hcont s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out

end CryptoVerification.SpqrV1.Poly.NextChunk

