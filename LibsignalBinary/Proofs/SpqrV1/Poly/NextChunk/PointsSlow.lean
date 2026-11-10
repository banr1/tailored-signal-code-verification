/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFast
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProof
public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `Points` Slow-Path Prefix and Block C

**Checked by Lean.**

Verifies the `Points` fast-path prefix (`0..i0`), slow-path trigger (`+288 -> +436`), and Block C
(`+4424 -> +296`, dropping old `[Point; 16]` and installing `EncoderState::Polys`) surrounding
`points_to_polys`.
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
open CryptoVerification.SpqrV1.Drop
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

theorem cmp_len_idx_le {len : Nat} {idx16 : BitVec 16}
    (hle : len ≤ idx16.toNat) :
    BitVec.ule (BitVec.ofNat 64 len) (idx16.setWidth 64) = true ∧
    (BitVec.ult (BitVec.ofNat 64 len) (idx16.setWidth 64) ||
      (BitVec.ofNat 64 len == idx16.setWidth 64)) = true ∧
    (BitVec.ult (BitVec.ofNat 64 len) (idx16.setWidth 64) ||
      (BitVec.ofNat 64 len - idx16.setWidth 64 == 0#64)) = true := by
  have hidx64 : idx16.toNat < 2 ^ 64 := Nat.lt_trans idx16.isLt (by decide : 2 ^ 16 < 2 ^ 64)
  have hlen64 : len < 2 ^ 64 := Nat.lt_of_le_of_lt hle hidx64
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen64
  have hidx_mod : (idx16.setWidth 64).toNat = idx16.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hidx64
  have hule : BitVec.ule (BitVec.ofNat 64 len) (idx16.setWidth 64) = true := by
    simp [BitVec.ule, hlen_mod, hidx_mod, hle]
  refine ⟨hule, ?_, ?_⟩
  · by_cases hlt : len < idx16.toNat
    · have hult : BitVec.ult (BitVec.ofNat 64 len) (idx16.setWidth 64) = true := by
        simp [BitVec.ult, hlen_mod, hidx_mod, hlt]
      simp [hult]
    · have heq : BitVec.ofNat 64 len = idx16.setWidth 64 := by
        apply BitVec.eq_of_toNat_eq; omega
      simp [heq]
  · by_cases hlt : len < idx16.toNat
    · have hult : BitVec.ult (BitVec.ofNat 64 len) (idx16.setWidth 64) = true := by
        simp [BitVec.ult, hlen_mod, hidx_mod, hlt]
      simp [hult]
    · have heq : BitVec.ofNat 64 len = idx16.setWidth 64 := by
        apply BitVec.eq_of_toNat_eq; omega
      simp [heq]

/-- Slow-path trigger (`0x6a4a4..0x6a4a8 -> 0x6a508..0x6a514`, `+288 -> +436`, 6 insns):
    when `(pts[i0]).value.length ≤ (x.enc.idx.setWidth 16).toNat`, stores `i0` to `[fsp + 104]`
    and branches to Block A (`+436`). -/
theorem pointsSlowTrigger_sepWP
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (i0 : Nat) (hi0 : i0 < 16)
    (hidx_le : (pts[i0]'(by omega)).value.length ≤ (x.enc.idx.setWidth 16).toNat)
    (fsp u104 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (s : State)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i0)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 436#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
        (pointListOf A (x.encA + 8#64) pts ∗
         ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
         Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (pointListOf A (x.encA + 8#64) pts ∗
       ((fsp + 104#64) ↦₆₄ u104) ∗
       Frame) post := by
  have hi0_len : i0 < pts.length := by omega
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x120 8
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x184 16
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  rw [pointListOf_split_idx A (x.encA + 8#64) pts i0 hi0_len]
  apply SepWP.fold (pointOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) (pts[i0]'hi0_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  have hpure_pull : ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
      (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest = ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWP.pure_elim; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [pointBufBody_eq_slice_rest A cap ptr (pts[i0]'hi0_len) hlen_cap]
  rcases cmp_len_idx_le hidx_le with ⟨hule_len, hcond_eq, hcond_sub⟩
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk" = entry
  examples_hide_fetches
  wp_steps 6
  have hfold_point :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (pts[i0]'hi0_len).value.length) ∗
        gf16SliceAt ptr (pts[i0]'hi0_len).value ∗
        pointBufRest A cap ptr (pts[i0]'hi0_len) ⊢
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) (pts[i0]'hi0_len) :=
    pointOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) cap ptr (pts[i0]'hi0_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_point (by sep_focus)
  have hfold_list :
      pointListOf A (x.encA + 8#64) (pts.take i0) ∗
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) (pts[i0]'hi0_len) ∗
        pointListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i0 + 1))) (pts.drop (i0 + 1)) ⊢
        pointListOf A (x.encA + 8#64) pts := by
    rw [← pointListOf_split_idx A (x.encA + 8#64) pts i0 hi0_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _
      (by subst hentry; simp only [arm64_norm, wp_norm, hule_len, hcond_eq, hcond_sub, ↓reduceIte])
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp)
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm])
      (by simpa [arm64_norm, wp_norm] using hx24)
      (by simpa [arm64_norm, wp_norm] using hx27)
      (by simp only [arm64_norm, wp_norm]))

/-! ## 2. `vecGF16ListOf` Header/Heap Splitting & Block C (`0x6b4cc..0x6b504`, `+4424 -> +296`) -/

@[local arm64_norm, local wp_norm] theorem bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl

theorem sepWP_pure_left {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog target_pc s P post) :
    SepWP prog target_pc s (⌜φ⌝ ∗ P) post :=
  SepWP.pure_elim h

/-- 24-byte serialized `Vec` header `(cap, ptr, len)`. -/
def vecHeaderBytesOf (pin : VecPin) (len : Nat) : List (BitVec 8) :=
  unpack64 pin.cap ++ unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)

@[simp] theorem length_vecHeaderBytesOf (pin : VecPin) (len : Nat) :
    (vecHeaderBytesOf pin len).length = 24 := rfl

/-- Concatenated 24-byte `Vec` headers for `pins` and `vecs`. -/
def vecHeadersBytesOf : List VecPin → List (List GF16) → List (BitVec 8)
  | [], _ => []
  | _, [] => []
  | pin :: pins, cs :: vecs => vecHeaderBytesOf pin cs.length ++ vecHeadersBytesOf pins vecs

theorem length_vecHeadersBytesOf :
    ∀ (pins : List VecPin) (vecs : List (List GF16)),
      pins.length = vecs.length →
      (vecHeadersBytesOf pins vecs).length = vecs.length * 24
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | pin :: pins, cs :: vecs, h => by
    simp only [List.length_cons] at h
    have ih := length_vecHeadersBytesOf pins vecs (Nat.succ.inj h)
    simp only [vecHeadersBytesOf, List.length_append, length_vecHeaderBytesOf, ih, List.length_cons]
    omega

/-- Separating conjunction of `vecBuf A gf16Stride gf16Align gf16At` across `pins` and `vecs`. -/
def vecGF16HeapList (A : RustAlloc) : List VecPin → List (List GF16) → SepProp
  | [], _ => emp
  | _, [] => emp
  | pin :: pins, cs :: vecs =>
    vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ∗ vecGF16HeapList A pins vecs

theorem vecHeader_eq_pointsToBytes (a : BitVec 64) (pin : VecPin) (len : Nat) :
    vecHeader a pin.cap pin.ptr (BitVec.ofNat 64 len) =
      (a ↦ₛ vecHeaderBytesOf pin len) := by
  unfold vecHeader vecHeaderBytesOf
  rw [List.append_assoc,
      ProofLib.pointsToBytes_append a (unpack64 pin.cap)
        (unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)),
      unpack64_length,
      ProofLib.pointsToBytes_append (a + 8#64) (unpack64 pin.ptr) (unpack64 (BitVec.ofNat 64 len)),
      unpack64_length]
  have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [h16, ← pointsTo64_eq_pointsToBytes a pin.cap,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) pin.ptr,
      ← pointsTo64_eq_pointsToBytes (a + 16#64) (BitVec.ofNat 64 len)]

theorem vecGF16Of_entails_pin (A : RustAlloc) (a : BitVec 64) (cs : List GF16) :
    vecGF16Of A a cs ⊢
      ∃∗ pin : VecPin,
        (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
          vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs := by
  unfold vecGF16Of vecOf vecAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ cs.length]
  exact Entails.refl _

theorem pin_entails_vecGF16Of (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (cs : List GF16) :
    (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
      vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ⊢
      vecGF16Of A a cs := by
  rw [← vecHeader_eq_pointsToBytes a pin cs.length]
  unfold vecGF16Of vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem vecGF16ListOf_entails_headers_heaps (A : RustAlloc) :
    ∀ (vecs : List (List GF16)) (a : BitVec 64),
      vecGF16ListOf A a vecs ⊢
        ∃∗ pins : List VecPin,
          ⌜pins.length = vecs.length⌝ ∗
            (a ↦ₛ vecHeadersBytesOf pins vecs) ∗
            vecGF16HeapList A pins vecs
  | [], a => by
    simp only [vecGF16ListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    simp [vecHeadersBytesOf, vecGF16HeapList, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | cs :: vecs, a => by
    simp only [vecGF16ListOf, arrayAt, vecHeaderBytes]
    refine Entails.trans (sepConj_mono (vecGF16Of_entails_pin A a cs)
      (vecGF16ListOf_entails_headers_heaps A vecs (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pins
    apply Entails.sepExists_elim; intro pin
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs) ∗
        (⌜pins.length = vecs.length⌝ ∗
          ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs) =
      ⌜pins.length = vecs.length⌝ ∗
        (((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
          (vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ∗ vecGF16HeapList A pins vecs)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (cs :: vecs).length := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    simp only [vecHeadersBytesOf, vecGF16HeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
        length_vecHeaderBytesOf]
    exact Entails.refl _

theorem headers_heaps_entails_vecGF16ListOf (A : RustAlloc) :
    ∀ (pins : List VecPin) (vecs : List (List GF16)) (a : BitVec 64),
      pins.length = vecs.length →
      (a ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs ⊢
        vecGF16ListOf A a vecs
  | [], [], a, _ => by
    simp [vecHeadersBytesOf, vecGF16HeapList, vecGF16ListOf, arrayAt, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | pin :: pins, cs :: vecs, a, h => by
    simp only [List.length_cons] at h
    simp only [vecHeadersBytesOf, vecGF16HeapList, vecGF16ListOf, arrayAt, vecHeaderBytes]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
        length_vecHeaderBytesOf]
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
        (vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ∗ vecGF16HeapList A pins vecs) =
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs) ∗
        (((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs) by ac_rfl)) ?_
    exact sepConj_mono (pin_entails_vecGF16Of A a pin cs)
      (headers_heaps_entails_vecGF16ListOf A pins vecs (a + 24#64) (Nat.succ.inj h))

theorem pointListOf_eq_vecGF16ListOf (A : RustAlloc) :
    ∀ (pts : List Point) (a : BitVec 64),
      pointListOf A a pts = vecGF16ListOf A a (pts.map Point.value)
  | [], _ => rfl
  | pt :: pts, a => by
    have ih := pointListOf_eq_vecGF16ListOf A pts (a + 24#64)
    dsimp only [pointListOf, vecGF16ListOf, vecHeaderBytes] at ih ⊢
    simp only [arrayAt, List.map_cons]
    rw [ih]
    rfl

theorem polyListOf_eq_vecGF16ListOf (A : RustAlloc) :
    ∀ (polys : List LibsignalSpqrV1.Poly) (a : BitVec 64),
      polyListOf A a polys = vecGF16ListOf A a (polys.map LibsignalSpqrV1.Poly.coefficients)
  | [], _ => rfl
  | p :: polys, a => by
    have ih := polyListOf_eq_vecGF16ListOf A polys (a + 24#64)
    dsimp only [polyListOf, vecGF16ListOf, vecHeaderBytes] at ih ⊢
    simp only [arrayAt, List.map_cons]
    rw [ih]
    rfl

theorem stackAt_dropGluePoly16_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropGluePoly16Stack =
      memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 32 (by decide)

theorem drop_glue_poly16_ok_at_nextChunk {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName +
        bv% (2 ^ 64 + ls_off% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" -
          ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
      (dropGluePoly16Spec A) := by
  have h := drop_glue_poly16_ok_ext hA.dealloc
  have haddr : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName +
      bv% (2 ^ 64 + ls_off% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" -
        ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk") =
      (dropProgAtExt b ext).fnAddr dropPoly16Name := by
    simp only [dropProgAtExt, Program.fnAddr_rebase,
      polyNextChunkName, dropPoly16Name,
      (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>")]
    bv_omega
  rw [haddr]
  exact h

/-- Block C (`0x6b4cc..0x6b504`, `+4424 -> +296`, 15 instructions):
    copies the 16 new `Poly` headers from `fsp + 256` to `fsp + 656`, drops the old
    `[Point; 16]` at `x.encA + 8` via `drop_glue::<[Poly; 16]>`, writes tag `1#64`
    (`EncoderState::Polys`) to `x.encA`, copies the 16 `Poly` headers from `fsp + 656`
    to `x.encA + 8`, reloads `x9 = i0` from `[fsp + 104]`, and jumps to `+296`. -/
theorem blockC_sepWP
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost)
    (pts : List Point) (hlen_pts : pts.length = 16)
    (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (i0 : Nat)
    (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (s : State)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 296#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x9 = BitVec.ofNat 64 i0 →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
        (polyListOf A (x.encA + 8#64) polys ∗
         (x.encA ↦₆₄ 1#64) ∗
         memRegion (fsp + 256#64) 384 ∗
         memRegion (fsp + 656#64) 384 ∗
         ((fsp + 8#64) ↦₆₄ x.encA) ∗
         ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
         memRegion (fsp - 4128#64) 32 ∗
         stackAt fsp allocHookStack ∗
         A.pool ∗
         Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (polyListOf A (fsp + 256#64) polys ∗
       memRegion (fsp + 656#64) 384 ∗
       pointListOf A (x.encA + 8#64) pts ∗
       (x.encA ↦₆₄ 0#64) ∗
       ((fsp + 8#64) ↦₆₄ x.encA) ∗
       ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
       memRegion (fsp - 4128#64) 32 ∗
       stackAt fsp allocHookStack ∗
       A.pool ∗
       Frame) post := by
  have hvecs_polys : (polys.map LibsignalSpqrV1.Poly.coefficients).length = 16 := by
    simp [hlen_polys]
  have hvecs_pts : (pts.map Point.value).length = NUM_POLYS := by
    simp [NUM_POLYS, CHUNK_SIZE, hlen_pts]
  rw [polyListOf_eq_vecGF16ListOf, pointListOf_eq_vecGF16ListOf]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecGF16ListOf_entails_headers_heaps A
      (polys.map LibsignalSpqrV1.Poly.coefficients) (fsp + 256#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply sepWP_pure_left; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_polys]
  have hmemcpy := hA.session_memcpy_ok_at polyNextChunkName
    (num% (ls_off% "memcpy" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
  simp only [sessionMemcpySpec] at hmemcpy
  have hdrop16 := drop_glue_poly16_ok_at_nextChunk hA
  simp only [dropGluePoly16Spec] at hdrop16
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1148 60
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, polyArrayBytes, NUM_POLYS, CHUNK_SIZE,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hdrop16 hnext ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk" = entry
  examples_hide_fetches
  wp_steps 4
  wp_call hmemcpy (fsp + 656#64, fsp + 256#64,
    vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients))
  have hsrc256 : ((fsp + 256#64) ↦ₛ
      vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ⊢
      memRegion (fsp + 256#64) 384 := by
    rw [← hbs_len]
    exact ProofLib.pointsToBytes_entails_memRegion (fsp + 256#64) _
  apply SepWP.fold hsrc256 (by sep_focus)
  have hjoin_drop_stack :
      memRegion (fsp - 4128#64) 32 ∗ stackAt s.sp 4096 ⊢
        stackAt fsp dropGluePoly16Stack := by
    rw [hsp, stackAt_dropGluePoly16_split_bottom fsp]
    exact Entails.refl _
  apply SepWP.fold hjoin_drop_stack (by sep_focus)
  wp_steps 2
  wp_call hdrop16 (⟨x.encA + 8#64, pts.map Point.value⟩ : DropGluePoly16Ghost)
  have hsplit_drop_stack :
      stackAt sf.sp dropGluePoly16Stack ⊢
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp 4096 := by
    rw [hsp_sf, hsp, stackAt_dropGluePoly16_split_bottom fsp]
    exact Entails.refl _
  apply SepWP.fold hsplit_drop_stack (by sep_focus)
  wp_steps 7
  wp_call hmemcpy (x.encA + 8#64, fsp + 656#64,
    vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients))
  have hsrc656 : ((fsp + 656#64) ↦ₛ
      vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ⊢
      memRegion (fsp + 656#64) 384 := by
    rw [← hbs_len]
    exact ProofLib.pointsToBytes_entails_memRegion (fsp + 656#64) _
  apply SepWP.fold hsrc656 (by sep_focus)
  have hfold_polys :
      ((x.encA + 8#64) ↦ₛ vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
        vecGF16HeapList A pins (polys.map LibsignalSpqrV1.Poly.coefficients) ⊢
        polyListOf A (x.encA + 8#64) polys := by
    rw [polyListOf_eq_vecGF16ListOf]
    exact headers_heaps_entails_vecGF16ListOf A pins _ (x.encA + 8#64) hpins_len
  apply SepWP.fold hfold_polys (by sep_focus)
  wp_steps 2
  have hsp_sf1 : stackAt sf_1.sp 4096 ⊢ stackAt fsp allocHookStack := by
    rw [hsp_sf_1, hsp_sf, hsp]
    exact Entails.refl _
  apply SepWP.fold hsp_sf1 (by sep_focus)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _
      (by subst hentry; simp only [arm64_norm, wp_norm])
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, Reg.x19, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]))

/-! ## 3. Prefix `0..i0` of the `Points` Fast-Path Loop (`+288 -> +288`) -/

attribute [local simp, local arm64_norm, local wp_norm]
  madd_24_eq madd_24_eq' zext16_shl1_bv_eq zext16_shl1_nat_eq
  ofNat_add_one_eq ofNat_two_mul_add_one ofNat_two_mul_add_two
  lsr8_zext16_eq trunc8_zext16_eq

set_option maxHeartbeats 1200000 in
/-- Single iteration `i < 15` of the `Points` fast-path loop (`+288 -> +288`, 30 insns)
    with a generic `Frame : SepProp` and preserving `x29`. -/
theorem pointsFastPrefix_step_sepWP
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr fsp u104 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i : Nat) (hi15 : i < 15)
    (hidx_lt : (x.enc.idx.setWidth 16).toNat < (pts[i]'(by omega)).value.length)
    (Frame : SepProp) (s : State)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (2 * i))
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = 0#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
          pointListOf A (x.encA + 8#64) pts ∗
          ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
          ((fsp + 232#64) ↦₆₄ 32#64) ∗
          ((fsp + 240#64) ↦₆₄ out_ptr) ∗
          ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
        pointListOf A (x.encA + 8#64) pts ∗
        ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        ((fsp + 104#64) ↦₆₄ u104) ∗
        ((fsp + 232#64) ↦₆₄ 32#64) ∗
        ((fsp + 240#64) ↦₆₄ out_ptr) ∗
        ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        Frame) post := by
  have hi16 : i < 16 := by omega
  have hi_len : i < pts.length := by omega
  have hi15_ne : (i == 15) = false := beq_eq_false_iff_ne.mpr (by omega)
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xfc 68
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x15c 92
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  rw [pointListOf_split_idx A (x.encA + 8#64) pts i hi_len]
  apply SepWP.fold (pointOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  have hpure_pull : ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
      (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest = ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWP.pure_elim; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [pointBufBody_eq_slice_rest A cap ptr (pts[i]'hi_len) hlen_cap,
      gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
  have hlen_lt : (pts[i]'hi_len).value.length < 2 ^ 63 :=
    pointValue_len_lt_two_pow_63 hlen_cap hcap_bound
  rcases cmp_len_idx_gt (idx16 := x.enc.idx.setWidth 16) hidx_lt hlen_lt with
    ⟨hult_len, hule_len, hbeq_len, hsub_len⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_add_one_beq_16 hi16 with ⟨hcmp16_eq, hcmp16_sub⟩
  rw [hi15_ne] at hcmp16_eq hcmp16_sub
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk" = entry
  examples_hide_fetches
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 30
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 (((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ⊢
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) := by
    rw [chunkPointsBytes_zero_succ (x.enc.idx.setWidth 16) pts i hi_len hidx_lt]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) i
      (chunkPointsBytes_length (x.enc.idx.setWidth 16) pts 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_slice :
      gf16SliceAt ptr ((pts[i]'hi_len).value.take (x.enc.idx.setWidth 16).toNat) ∗
        ((ptr + BitVec.ofNat 64 (2 * (x.enc.idx.setWidth 16).toNat)) ↦₁₆
          ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ∗
        gf16SliceAt (ptr + BitVec.ofNat 64 (2 * ((x.enc.idx.setWidth 16).toNat + 1)))
          ((pts[i]'hi_len).value.drop ((x.enc.idx.setWidth 16).toNat + 1)) ⊢
        gf16SliceAt ptr (pts[i]'hi_len).value := by
    rw [← gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
    exact Entails.refl _
  apply SepWP.fold hfold_slice (by sep_focus)
  have hfold_point :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (pts[i]'hi_len).value.length) ∗
        gf16SliceAt ptr (pts[i]'hi_len).value ∗
        pointBufRest A cap ptr (pts[i]'hi_len) ⊢
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) :=
    pointOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (pts[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_point (by sep_focus)
  have hfold_list :
      pointListOf A (x.encA + 8#64) (pts.take i) ∗
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) ∗
        pointListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (pts.drop (i + 1)) ⊢
        pointListOf A (x.encA + 8#64) pts := by
    rw [← pointListOf_split_idx A (x.encA + 8#64) pts i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _
      (by subst hentry; simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hcmp16_eq, hcmp16_sub])
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp)
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx24])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx27])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx28])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub]))

/-- Prefix `i..i+k` (`i + k < 16`) of the `Points` fast-path loop (`+288 -> +288`),
    producing `chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + k)`. -/
theorem pointsFastPrefix_sepWP
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) :
    ∀ (k i : Nat) (u104 : BitVec 64) (s : State),
      (hik : i + k < 16) →
      (∀ (j : Nat) (hj : i ≤ j ∧ j < i + k),
        (x.enc.idx.setWidth 16).toNat < (pts[j]'(by omega)).value.length) →
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = x.encA + 8#64 →
      s.readReg64 .x20 = BitVec.ofNat 64 (2 * i) →
      s.readReg64 .x21 = 0#64 →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s.readReg64 .x28 = 24#64 →
      (∀ sf : State, ∀ u104' : BitVec 64,
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64 →
        sf.status = .Running →
        sf.sp = fsp →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        sf.readReg64 .x9 = BitVec.ofNat 64 (i + k) →
        sf.readReg64 .x19 = x.encA + 8#64 →
        sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + k)) →
        sf.readReg64 .x21 = 0#64 →
        sf.readReg64 .x24 = x.encA →
        sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
        sf.readReg64 .x28 = 24#64 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
          ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + k)) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + k))) (32 - 2 * (i + k)) ∗
            pointListOf A (x.encA + 8#64) pts ∗
            ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
            ((fsp + 104#64) ↦₆₄ u104') ∗
            ((fsp + 232#64) ↦₆₄ 32#64) ∗
            ((fsp + 240#64) ↦₆₄ out_ptr) ∗
            ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + k))) ∗
            Frame) post) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
          pointListOf A (x.encA + 8#64) pts ∗
          ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          ((fsp + 104#64) ↦₆₄ u104) ∗
          ((fsp + 232#64) ↦₆₄ 32#64) ∗
          ((fsp + 240#64) ↦₆₄ out_ptr) ∗
          ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          Frame) post
  | 0, i, u104, s, _hik, _hfast, hpc, hrun, hsp, hx9, hx19, hx20, hx21, hx24, hx27, hx28, hnext => by
    simp only [Nat.add_zero] at hnext
    exact hnext s u104 hpc hrun hsp rfl rfl hx9 hx19 hx20 hx21 hx24 hx27 hx28 rfl
  | k + 1, i, u104, s, hik, hfast, hpc, hrun, hsp, hx9, hx19, hx20, hx21, hx24, hx27, hx28, hnext => by
    have hi15 : i < 15 := by omega
    refine pointsFastPrefix_step_sepWP A b ext x pts hlen_pts out_ptr fsp u104 hfsp_align
      i hi15 (hfast i ⟨by omega, by omega⟩) Frame s
      hpc hrun hsp hx9 hx19 hx20 hx21 hx24 hx27 hx28 ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1 hx27_1 hx28_1 hx29_1
    have hik' : (i + 1) + k < 16 := by omega
    have hadd_assoc : (i + 1) + k = i + (k + 1) := by omega
    refine pointsFastPrefix_sepWP A b ext x pts hlen_pts out_ptr fsp hfsp_align Frame
      k (i + 1) (BitVec.ofNat 64 i) s1 hik'
      (fun j hj => hfast j ⟨by omega, by omega⟩)
      hpc1 hrun1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1 hx27_1 hx28_1 ?_
    intro sf u104' hpcf hrunf hspf htrf hvregsf hx9f hx19f hx20f hx21f hx24f hx27f hx28f hx29f
    rw [hadd_assoc] at hx9f hx20f ⊢
    exact hnext sf u104' hpcf hrunf hspf (htrf.trans htr1) (hvregsf.trans hvregs1) hx9f hx19f hx20f hx21f hx24f hx27f hx28f
      (hx29f.trans hx29_1)

theorem sepWPp_drop_frame {prog : Program} {ret : BitVec 64}
    {A : RustAlloc} {b : BitVec 64} {x : PolyNextChunkGhost} {s0 s : State}
    {F P R : SepProp}
    (h : SepWPp prog ret s P
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ (F ∗ R)) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitAt b ∗
             reduceTableAt b ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ (F ∗ R))) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F ∗ R)) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ (F ∗ R)))) :
    SepWPp prog ret s (F ∗ P)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitAt b ∗
             reduceTableAt b ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  intro R0 hm hL
  have hm' : s.mem ⊨ P ∗ (F ∗ R0) := by
    rwa [show P ∗ (F ∗ R0) = (F ∗ P) ∗ R0 by ac_rfl]
  obtain ⟨sf, hsteps, hout⟩ := h (F ∗ R0) hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcc⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hmf⟩
  · refine Or.inl ⟨hpc, hrun, F ∗ P_f, ?_, ⟨fun hFR => ?_, hsp, hcc⟩⟩
    · rwa [show (F ∗ P_f) ∗ R0 = P_f ∗ (F ∗ R0) by ac_rfl]
    · have hFR' : sf.mem ⊨ P_f ∗ (F ∗ R) := by
        rwa [show P_f ∗ (F ∗ R) = (F ∗ P_f) ∗ R by ac_rfl]
      have h1 := hpost hFR'
      rw [show (⌜sf.trace = s0.trace⌝ ∗
            chunkAt x.outA x.chunk ∗
            polyEncoderAt A x.encA x.enc' ∗
            tokenInitAt b ∗
            reduceTableAt b ∗
            A.pool ∗
            stackAt s0.sp polyNextChunkStack ∗ (F ∗ R)) =
          F ∗ (⌜sf.trace = s0.trace⌝ ∗
            chunkAt x.outA x.chunk ∗
            polyEncoderAt A x.encA x.enc' ∗
            tokenInitAt b ∗
            reduceTableAt b ∗
            A.pool ∗
            stackAt s0.sp polyNextChunkStack ∗ R) by ac_rfl] at h1
      exact Satisfies.of_sep_right h1
  · refine Or.inr (Or.inl ⟨hpan, F ∗ P_f, ?_, fun hFR => ?_⟩)
    · rwa [show (F ∗ P_f) ∗ R0 = P_f ∗ (F ∗ R0) by ac_rfl]
    · have hFR' : sf.mem ⊨ P_f ∗ (F ∗ R) := by
        rwa [show P_f ∗ (F ∗ R) = (F ∗ P_f) ∗ R by ac_rfl]
      have h1 : sf.mem ⊨ F ∗ (nextChunkOnPanic s0 sf ∗ R) := by
        have := hqp hFR'
        rwa [show F ∗ (nextChunkOnPanic s0 sf ∗ R) = nextChunkOnPanic s0 sf ∗ (F ∗ R) by ac_rfl]
      exact Satisfies.of_sep_right h1
  · exact False.elim (not_satisfies_false_sepConj hmf)

/-- Find the first index `i ∈ [16 - rem, 16)` where `¬ (idx < (pts[i]?.getD ⟨[]⟩).value.length)`, or `16` if all satisfy `idx < len`. -/
def firstSlowIdxAux (idx : Nat) (pts : List Point) : Nat → Nat → Nat
  | 0, _ => 16
  | rem + 1, i =>
    if idx < (pts[i]?.getD ⟨[]⟩).value.length then
      firstSlowIdxAux idx pts rem (i + 1)
    else i

theorem firstSlowIdxAux_ge (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → i ≤ firstSlowIdxAux idx pts rem i
  | 0, i, h => by simp [firstSlowIdxAux]; omega
  | rem + 1, i, h => by
    unfold firstSlowIdxAux
    split_ifs with hlt
    · have ih := firstSlowIdxAux_ge idx pts rem (i + 1) (by omega)
      omega
    · exact Nat.le_refl i

theorem firstSlowIdxAux_le_16 (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → firstSlowIdxAux idx pts rem i ≤ 16
  | 0, i, h => by simp [firstSlowIdxAux]
  | rem + 1, i, h => by
    unfold firstSlowIdxAux
    split_ifs with hlt
    · exact firstSlowIdxAux_le_16 idx pts rem (i + 1) (by omega)
    · omega

theorem firstSlowIdxAux_fast (idx : Nat) (pts : List Point) :
    ∀ (rem i j : Nat), i + rem = 16 → i ≤ j → j < firstSlowIdxAux idx pts rem i →
      idx < (pts[j]?.getD ⟨[]⟩).value.length
  | 0, i, j, h, hij, hj => by simp [firstSlowIdxAux] at hj; omega
  | rem + 1, i, j, h, hij, hj => by
    unfold firstSlowIdxAux at hj
    split_ifs at hj with hlt
    · rcases Nat.eq_or_lt_of_le hij with rfl | hgt
      · exact hlt
      · exact firstSlowIdxAux_fast idx pts rem (i + 1) j (by omega) hgt hj
    · omega

theorem firstSlowIdxAux_slow (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → firstSlowIdxAux idx pts rem i < 16 →
      (pts[firstSlowIdxAux idx pts rem i]?.getD ⟨[]⟩).value.length ≤ idx
  | 0, i, h, hlt16 => by simp [firstSlowIdxAux] at hlt16
  | rem + 1, i, h, hlt16 => by
    unfold firstSlowIdxAux at hlt16 ⊢
    split_ifs at hlt16 ⊢ with hlt
    · exact firstSlowIdxAux_slow idx pts rem (i + 1) (by omega) hlt16
    · omega

theorem chunkPointsPolysBytes_length (idx : BitVec 16) (pts : List Point)
    (polys : List LibsignalSpqrV1.Poly) (i k rem total : Nat)
    (htot : total = k + rem) :
    (chunkPointsBytes idx pts i k ++ chunkPolysBytes idx polys (i + k) rem).length = 2 * total := by
  rw [List.length_append, chunkPointsBytes_length, chunkPolysBytes_length, htot, Nat.mul_add]

theorem chunkAtLoop_points_prefix_ge_eq (idx : BitVec 32) (pts : List Point)
    (polys : List LibsignalSpqrV1.Poly)
    (hlen_pts : pts.length = 16)
    (hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok polys) :
    ∀ (total k i rem : Nat)
      (_hle : (i + k) + (rem + 1) ≤ 16)
      (htot : total = k + (rem + 1)),
      (∀ j (hj : j < pts.length), i ≤ j → j < i + k →
        (idx.setWidth 16).toNat < (pts[j]'hj).value.length) →
      (pts[i + k]'(by omega)).value.length ≤ (idx.setWidth 16).toNat →
      PolyEncoder.chunkAtLoop (idx.setWidth 16) i total { idx := idx, s := .points pts } =
        .ok ({ idx := idx, s := .polys polys },
          ⟨chunkPointsBytes (idx.setWidth 16) pts i k ++
            chunkPolysBytes (idx.setWidth 16) polys (i + k) (rem + 1),
            chunkPointsPolysBytes_length (idx.setWidth 16) pts polys i k (rem + 1) total htot⟩)
  | 0, k, i, rem, _, htot, _, _ => by omega
  | t + 1, 0, i, rem, hle, htot, _hfast, hslow => by
    have ht : t = rem := by omega
    subst ht
    simp only [Nat.add_zero, chunkPointsBytes, List.nil_append] at hle hslow ⊢
    exact chunkAtLoop_points_ge_eq idx pts polys t i hle hlen_pts hslow hloop
  | t + 1, k + 1, i, rem, hle, htot, hfast, hslow => by
    have hi16 : i < 16 := by omega
    have hi_len : i < pts.length := by omega
    have hlt_i : (idx.setWidth 16).toNat < (pts[i]'hi_len).value.length :=
      hfast i hi_len (Nat.le_refl i) (by omega)
    have hpt_opt : pts[i]? = some (pts[i]'hi_len) := List.getElem?_eq_getElem hi_len
    have hval_opt : (pts[i]'hi_len).value[(idx.setWidth 16).toNat]? =
        some ((pts[i]'hi_len).value[(idx.setWidth 16).toNat]'hlt_i) :=
      List.getElem?_eq_getElem hlt_i
    have hmod : ((idx.setWidth 16).toNat * 16 + i) % 16 = i := totalIdx_mod_16 (idx.setWidth 16) hi16
    have hdiv : ((idx.setWidth 16).toNat * 16 + i) / 16 = (idx.setWidth 16).toNat :=
      totalIdx_div_16 (idx.setWidth 16) hi16
    have hpt := pointAt_points_lt_eq (idx := idx) hi_len hlt_i
    have hadd_assoc : (i + 1) + k = i + (k + 1) := by omega
    have ih := chunkAtLoop_points_prefix_ge_eq idx pts polys hlen_pts hloop t k (i + 1) rem
      (by omega) (by omega)
      (fun j hj hij hjk => hfast j hj (by omega) (by omega))
      (by simpa [hadd_assoc] using hslow)
    unfold PolyEncoder.chunkAtLoop chunkPointsBytes
    simp only [hmod, hdiv, hpt, ih, hpt_opt, hval_opt, Option.getD_some,
      hadd_assoc, List.cons_append, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

theorem nextChunk_points_slow_eq {idx : BitVec 32} {pts : List Point}
    (hlen_pts : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (i0 : Nat) (hi0 : i0 < 16)
    (hfast : ∀ j (hj : j < pts.length), j < i0 →
      (idx.setWidth 16).toNat < (pts[j]'hj).value.length)
    (hslow : (pts[i0]'(by omega)).value.length ≤ (idx.setWidth 16).toNat) :
    PolyEncoder.nextChunk { idx := idx, s := .points pts } =
      .ok ({ idx := idx + 1#32, s := .polys (pts.map pointToPolyPure) },
        { index := idx.setWidth 16,
          data := ⟨chunkPointsBytes (idx.setWidth 16) pts 0 i0 ++
            chunkPolysBytes (idx.setWidth 16) (pts.map pointToPolyPure) i0 (15 - i0 + 1),
            by simpa using chunkPointsPolysBytes_length (idx.setWidth 16) pts
                 (pts.map pointToPolyPure) 0 i0 (15 - i0 + 1) 16 (by omega)⟩ }) := by
  have hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok (pts.map pointToPolyPure) := by
    have h := pointsToPolysLoop_eq_map pts hbounds 16 0 [] (by omega)
    simp only [List.nil_append, List.drop_zero] at h
    exact h
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt
  have hchunk := chunkAtLoop_points_prefix_ge_eq idx pts (pts.map pointToPolyPure) hlen_pts hloop
    16 i0 0 (15 - i0) (by omega) (by omega)
    (fun j hj _ hjlt => hfast j hj (by omega)) (by simpa using hslow)
  simp only [Nat.zero_add] at hchunk
  rw [hchunk]
  rfl

theorem stackAt_nextChunkCallee_split_lagrangePrepare (fsp : BitVec 64) :
    stackAt fsp nextChunkCalleeStack =
      memRegion (fsp - 17232#64) 12928 ∗ stackAt fsp lagrangePrepareStack := by
  simpa [nextChunkCalleeStack, lagrangePrepareStack, allocHookStack, extHookStack] using
    stackAt_split_bottom fsp lagrangePrepareStack 12928 (by decide)

theorem stackAt_nextChunkCallee_split_blockC (fsp : BitVec 64) :
    stackAt fsp nextChunkCalleeStack =
      memRegion (fsp - 17232#64) 13104 ∗
      memRegion (fsp - 4128#64) 32 ∗
      stackAt fsp allocHookStack := by
  rw [stackAt_nextChunkCallee_split_allocHook fsp,
      ProofLib.memRegion_split' (b := fsp - 17232#64) (n := 13104) (k := 32)
        (b' := fsp - 4128#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem localFramePointsRest_unfold_slow (fsp : BitVec 64) :
    localFramePointsRest fsp ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u64 : BitVec 64,
      ∃∗ u72 : BitVec 64, ∃∗ u80 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u640 : BitVec 64, ∃∗ u648 : BitVec 64, ∃∗ u1040 : BitVec 64,
      ∃∗ u1048 : BitVec 64, ∃∗ u1056 : BitVec 64,
        memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ u8) ∗
        ((fsp + 16#64) ↦₆₄ u16) ∗
        ((fsp + 24#64) ↦₆₄ u24) ∗
        ((fsp + 32#64) ↦₆₄ u32) ∗
        ((fsp + 40#64) ↦₆₄ u40) ∗
        ((fsp + 64#64) ↦₆₄ u64) ∗
        ((fsp + 72#64) ↦₆₄ u72) ∗
        ((fsp + 80#64) ↦₆₄ u80) ∗
        ((fsp + 96#64) ↦₆₄ u96) ∗
        memRegion (fsp + 112#64) 120 ∗
        memRegion (fsp + 256#64) 384 ∗
        ((fsp + 640#64) ↦₆₄ u640) ∗
        ((fsp + 648#64) ↦₆₄ u648) ∗
        memRegion (fsp + 656#64) 24 ∗
        memRegion (fsp + 680#64) 360 ∗
        ((fsp + 1040#64) ↦₆₄ u1040) ∗
        ((fsp + 1048#64) ↦₆₄ u1048) ∗
        ((fsp + 1056#64) ↦₆₄ u1056) ∗
        memRegion (fsp + 1064#64) 40 := by
  unfold localFramePointsRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 40) (b' := fsp + 8#64)
        rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 32) (b' := fsp + 16#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 8#64),
      ProofLib.memRegion_split' (b := fsp + 16#64) (n := 8) (k := 24) (b' := fsp + 24#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 16#64),
      ProofLib.memRegion_split' (b := fsp + 24#64) (n := 8) (k := 16) (b' := fsp + 32#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 24#64),
      ProofLib.memRegion_split' (b := fsp + 32#64) (n := 8) (k := 8) (b' := fsp + 40#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 32#64),
      ProofLib.memRegion_eight (fsp + 40#64),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 8) (k := 16) (b' := fsp + 72#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 64#64),
      ProofLib.memRegion_split' (b := fsp + 72#64) (n := 8) (k := 8) (b' := fsp + 80#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 72#64),
      ProofLib.memRegion_eight (fsp + 80#64),
      ProofLib.memRegion_eight (fsp + 96#64),
      ProofLib.memRegion_split' (b := fsp + 256#64) (n := 384) (k := 464) (b' := fsp + 640#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 640#64) (n := 8) (k := 456) (b' := fsp + 648#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 640#64),
      ProofLib.memRegion_split' (b := fsp + 648#64) (n := 8) (k := 448) (b' := fsp + 656#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 648#64),
      ProofLib.memRegion_split' (b := fsp + 656#64) (n := 24) (k := 424) (b' := fsp + 680#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 680#64) (n := 360) (k := 64) (b' := fsp + 1040#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1040#64) (n := 8) (k := 56) (b' := fsp + 1048#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1040#64),
      ProofLib.memRegion_split' (b := fsp + 1048#64) (n := 8) (k := 48) (b' := fsp + 1056#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1048#64),
      ProofLib.memRegion_split' (b := fsp + 1056#64) (n := 8) (k := 40) (b' := fsp + 1064#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1056#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply Entails.sepExists_elim; intro _)
  rename_i u1056 u1048 u1040 u648 u640 u96 u80 u72 u64 u40 u32 u24 u16 u8
  exact Entails.sepExists_right u8 (Entails.sepExists_right u16 (Entails.sepExists_right u24
    (Entails.sepExists_right u32 (Entails.sepExists_right u40 (Entails.sepExists_right u64
      (Entails.sepExists_right u72 (Entails.sepExists_right u80 (Entails.sepExists_right u96
        (Entails.sepExists_right u640 (Entails.sepExists_right u648
          (Entails.sepExists_right u1040 (Entails.sepExists_right u1048
            (Entails.sepExists_right u1056 (Entails.of_eq (by ac_rfl)))))))))))))))

theorem localFramePointsRest_fold_slow
    (fsp u8 u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64) :
    memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ u8) ∗
      ((fsp + 16#64) ↦₆₄ u16) ∗
      ((fsp + 24#64) ↦₆₄ u24) ∗
      ((fsp + 32#64) ↦₆₄ u32) ∗
      ((fsp + 40#64) ↦₆₄ u40) ∗
      ((fsp + 64#64) ↦₆₄ u64) ∗
      ((fsp + 72#64) ↦₆₄ u72) ∗
      ((fsp + 80#64) ↦₆₄ u80) ∗
      ((fsp + 96#64) ↦₆₄ u96) ∗
      memRegion (fsp + 112#64) 120 ∗
      memRegion (fsp + 256#64) 384 ∗
      ((fsp + 640#64) ↦₆₄ u640) ∗
      ((fsp + 648#64) ↦₆₄ u648) ∗
      memRegion (fsp + 656#64) 384 ∗
      ((fsp + 1040#64) ↦₆₄ u1040) ∗
      ((fsp + 1048#64) ↦₆₄ u1048) ∗
      ((fsp + 1056#64) ↦₆₄ u1056) ∗
      memRegion (fsp + 1064#64) 40 ⊢
      localFramePointsRest fsp := by
  unfold localFramePointsRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 40) (b' := fsp + 8#64)
        rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 32) (b' := fsp + 16#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 8#64),
      ProofLib.memRegion_split' (b := fsp + 16#64) (n := 8) (k := 24) (b' := fsp + 24#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 16#64),
      ProofLib.memRegion_split' (b := fsp + 24#64) (n := 8) (k := 16) (b' := fsp + 32#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 24#64),
      ProofLib.memRegion_split' (b := fsp + 32#64) (n := 8) (k := 8) (b' := fsp + 40#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 32#64),
      ProofLib.memRegion_eight (fsp + 40#64),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 8) (k := 16) (b' := fsp + 72#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 64#64),
      ProofLib.memRegion_split' (b := fsp + 72#64) (n := 8) (k := 8) (b' := fsp + 80#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 72#64),
      ProofLib.memRegion_eight (fsp + 80#64),
      ProofLib.memRegion_eight (fsp + 96#64),
      ProofLib.memRegion_split' (b := fsp + 256#64) (n := 384) (k := 464) (b' := fsp + 640#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 640#64) (n := 8) (k := 456) (b' := fsp + 648#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 640#64),
      ProofLib.memRegion_split' (b := fsp + 648#64) (n := 8) (k := 448) (b' := fsp + 656#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 648#64),
      ProofLib.memRegion_split' (b := fsp + 656#64) (n := 384) (k := 64) (b' := fsp + 1040#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1040#64) (n := 8) (k := 56) (b' := fsp + 1048#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1040#64),
      ProofLib.memRegion_split' (b := fsp + 1048#64) (n := 8) (k := 48) (b' := fsp + 1056#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1048#64),
      ProofLib.memRegion_split' (b := fsp + 1056#64) (n := 8) (k := 40) (b' := fsp + 1064#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1056#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u1056
  apply Entails.sepExists_right u1048
  apply Entails.sepExists_right u1040
  apply Entails.sepExists_right u648
  apply Entails.sepExists_right u640
  apply Entails.sepExists_right u96
  apply Entails.sepExists_right u80
  apply Entails.sepExists_right u72
  apply Entails.sepExists_right u64
  apply Entails.sepExists_right u40
  apply Entails.sepExists_right u32
  apply Entails.sepExists_right u24
  apply Entails.sepExists_right u16
  apply Entails.sepExists_right u8
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_656_join_680 (fsp : BitVec 64) :
    memRegion (fsp + 656#64) 24 ∗ memRegion (fsp + 680#64) 360 ⊢
      memRegion (fsp + 656#64) 384 := by
  rw [ProofLib.memRegion_split' (b := fsp + 656#64) (n := 24) (k := 360) (b' := fsp + 680#64)
        rfl (by bv_omega) (by decide)]
  exact Entails.refl _


end CryptoVerification.SpqrV1.Poly.NextChunk
