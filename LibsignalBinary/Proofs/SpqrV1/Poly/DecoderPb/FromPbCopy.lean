/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Success Copy and Deallocation

**Checked by Lean.**

Proves the 16-slot `SortedSet<Pt>` header `memcpy` relocation, unrolled 16-slot `Vec<u8>`
deallocation (`+904..+1236`), and success exit (`+876 → s0.lr`) of `<PolyDecoder>::from_pb`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `Vec<Pt>` Array Header Relocation (`memcpy` of 16 `Vec<Pt>` Slots, 384 Bytes) -/

/-- 24-byte serialized `Vec` header `(cap, ptr, len)`. -/
def vecHeaderBytesOf (pin : VecPin) (len : Nat) : List (BitVec 8) :=
  unpack64 pin.cap ++ unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)

@[simp] theorem length_vecHeaderBytesOf (pin : VecPin) (len : Nat) :
    (vecHeaderBytesOf pin len).length = 24 := rfl

/-- Concatenated 24-byte `Vec` headers for `pins` and `vecs`. -/
def vecHeadersBytesOf : List VecPin → List (List Pt) → List (BitVec 8)
  | [], _ => []
  | _, [] => []
  | pin :: pins, cs :: vecs => vecHeaderBytesOf pin cs.length ++ vecHeadersBytesOf pins vecs

theorem length_vecHeadersBytesOf (pins : List VecPin) (vecs : List (List Pt))
    (h : pins.length = vecs.length) :
    (vecHeadersBytesOf pins vecs).length = vecs.length * 24 := by
  induction pins generalizing vecs with
  | nil =>
    cases vecs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons pin pins ih =>
    cases vecs with
    | nil => simp at h
    | cons cs vecs =>
      simp only [List.length_cons] at h
      have hih := ih vecs (Nat.succ.inj h)
      simp only [vecHeadersBytesOf, List.length_append, length_vecHeaderBytesOf, hih, List.length_cons]
      omega

/-- Separating conjunction of `vecBuf A ptStride ptAlign ptAt` across `pins` and `vecs`. -/
def vecPtHeapList (A : RustAlloc) : List VecPin → List (List Pt) → SepProp
  | [], _ => emp
  | _, [] => emp
  | pin :: pins, cs :: vecs =>
    vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ∗ vecPtHeapList A pins vecs

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

theorem vecPtOf_entails_pin (A : RustAlloc) (a : BitVec 64) (cs : List Pt) :
    vecPtOf A a cs ⊢
      ∃∗ pin : VecPin,
        (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
          vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs := by
  unfold vecPtOf vecOf vecAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ cs.length]
  exact Entails.refl _

theorem pin_entails_vecPtOf (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (cs : List Pt) :
    (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
      vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ⊢
      vecPtOf A a cs := by
  rw [← vecHeader_eq_pointsToBytes a pin cs.length]
  unfold vecPtOf vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem vecPtListOf_entails_headers_heaps (A : RustAlloc)
    (vecs : List (List Pt)) (a : BitVec 64) :
    vecPtListOf A a vecs ⊢
      ∃∗ pins : List VecPin,
        ⌜pins.length = vecs.length⌝ ∗
          (a ↦ₛ vecHeadersBytesOf pins vecs) ∗
          vecPtHeapList A pins vecs := by
  induction vecs generalizing a with
  | nil =>
    simp only [vecPtListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    simp [vecHeadersBytesOf, vecPtHeapList, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | cons cs vecs ih =>
    simp only [vecPtListOf, arrayAt, vecHeaderBytes]
    refine Entails.trans (sepConj_mono (vecPtOf_entails_pin A a cs) (ih (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pins
    apply Entails.sepExists_elim; intro pin
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs) ∗
        (⌜pins.length = vecs.length⌝ ∗
          ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecPtHeapList A pins vecs) =
      ⌜pins.length = vecs.length⌝ ∗
        (((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
          (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ∗ vecPtHeapList A pins vecs)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (cs :: vecs).length := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    simp only [vecHeadersBytesOf, vecPtHeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
        length_vecHeaderBytesOf]
    exact Entails.refl _

theorem headers_heaps_entails_vecPtListOf (A : RustAlloc)
    (pins : List VecPin) (vecs : List (List Pt)) (a : BitVec 64)
    (h : pins.length = vecs.length) :
    (a ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecPtHeapList A pins vecs ⊢
      vecPtListOf A a vecs := by
  induction pins generalizing vecs a with
  | nil =>
    cases vecs with
    | nil =>
      simp [vecHeadersBytesOf, vecPtHeapList, vecPtListOf, arrayAt, ProofLib.pointsToBytes_nil]
      exact Entails.refl _
    | cons _ _ => simp at h
  | cons pin pins ih =>
    cases vecs with
    | nil => simp at h
    | cons cs vecs =>
      simp only [List.length_cons] at h
      simp only [vecHeadersBytesOf, vecPtHeapList, vecPtListOf, arrayAt, vecHeaderBytes]
      rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
          length_vecHeaderBytesOf]
      refine Entails.trans (Entails.of_eq (show
        ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
          (vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs ∗ vecPtHeapList A pins vecs) =
        ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A ptStride ptAlign ptAt pin.cap pin.ptr cs) ∗
          (((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecPtHeapList A pins vecs) by ac_rfl)) ?_
      exact sepConj_mono (pin_entails_vecPtOf A a pin cs)
        (ih vecs (a + 24#64) (Nat.succ.inj h))

/-! ## Unrolled 16-Slot `Vec<u8>` Deallocation (`+904 -> +1236`) and Success Exit (`+876 -> s0.lr`) -/

/-- `arrayAt (fun bs addr => vecU8 A addr bs) 24` step helper for slot 0 (`ptsPtr + 0`). -/
theorem vecU8_frame_entails (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) :
    vecU8 A a bs ∗ Rest ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
          vecCapPtrDealloc A cap ptr) ∗ Rest := by
  refine Entails.trans (sepConj_mono_left (vecU8_entails_capPtr_dealloc A a bs)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem vecU8_step_entails (A : RustAlloc) (arrA off off8 off16 : BitVec 64)
    (hoff8 : (arrA + off) + 8#64 = arrA + off8)
    (hoff16 : (arrA + off) + 16#64 = arrA + off16)
    (bs : List (BitVec 8)) (Rest : SepProp) :
    vecU8 A (arrA + off) bs ∗ Rest ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8 ∗
          vecCapPtrDealloc A cap ptr) ∗ Rest := by
  have h := vecU8_frame_entails A (arrA + off) bs Rest
  rwa [hoff8, hoff16] at h

theorem SepWP.dealloc_u8_list_cons_step {A : RustAlloc} {prog : Program} {target_pc : BitVec 64} {s : State}
    (arrA off off8 off16 offNext : BitVec 64) (n m : Nat)
    (hoff : arrA + BitVec.ofNat 64 n = arrA + off)
    (hoff8 : (arrA + off) + 8#64 = arrA + off8)
    (hoff16 : (arrA + off) + 16#64 = arrA + off16)
    (hoffNext : (arrA + off) + 24#64 = arrA + offNext)
    (hm : n + 24 = m) (hbound : m ≤ 2 ^ 64)
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8))) (Tail : SepProp) {Q : State → Prop}
    (h : ∀ cap ptr : BitVec 64,
      SepWP prog target_pc s
        ((((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8 ∗
          vecCapPtrDealloc A cap ptr) ∗
          (memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail)))
        (fun sm Pm =>
          (Pm ⊢ (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗
            memRegion (arrA + off16) 8) ∗
            memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail)) ∧
          Q sm)) :
    SepWP prog target_pc s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + off) (bs :: rest) ∗ (memRegion arrA n ∗ Tail))
      (fun sm Pm =>
        (Pm ⊢ arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ (memRegion arrA m ∗ Tail)) ∧
        Q sm) := by
  have hpre : arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + off) (bs :: rest) ∗ (memRegion arrA n ∗ Tail) =
      vecU8 A (arrA + off) bs ∗ (memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail)) := by
    show (vecU8 A (arrA + off) bs ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ((arrA + off) + 24#64) rest) ∗ (memRegion arrA n ∗ Tail) = _
    rw [hoffNext]
    ac_rfl
  rw [hpre]
  refine SepWP.weaken_pre (vecU8_step_entails A arrA off off8 off16 hoff8 hoff16 bs _) ?_
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  have hpost :
      (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗
        memRegion (arrA + off16) 8) ∗
        memRegion arrA n ∗ (arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ Tail) ⊢
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (arrA + offNext) rest ∗ (memRegion arrA m ∗ Tail) := by
    refine Entails.trans (slot_join_memRegion_at arrA off off8 off16 cap ptr n m hoff hoff8 hoff16 hm hbound _) ?_
    exact Entails.of_eq (by ac_rfl)
  exact SepWP.strengthen_entails_const hpost (h cap ptr)

@[local simp, local arm64_norm, local wp_norm]
theorem truncate8_truncate32_zeroExtend64 (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.truncate 32 (b.zeroExtend 64)) = b := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem fromPb_bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl

local macro "dealloc_u8_slot_step " ptsPtr:term:max off0:term:max off8:term:max off16:term:max off24:term:max k:term:max k24:term:max c:term:max hsp:ident : tactic =>
  `(tactic| (
    refine SepWP.dealloc_u8_list_cons_step $ptsPtr $off0 $off8 $off16 $off24 $k $k24
      rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) $c _ _ ?_
    intro cap ptr; dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [$hsp:ident]; ac_rfl) ?_; wp_done))

/-- Deallocates slots `0..7` of `ptsPtr` (`+904..+1076`), writing `ptsNeeded` at `[out + 384]` and `isComplete` at `[out + 392]`. -/
theorem fromPb_success_dealloc_first8 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (fsp out pbA ptsPtr d384 ptsNeeded64 : BitVec 64)
    (b392 isComplete8 : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List (BitVec 8)) (rest : List (List (BitVec 8)))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = ptsNeeded64)
    (hx20 : s.readReg64 .x20 = isComplete8.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx22 : s.readReg64 .x22 = out)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1076#64)
      s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr
        (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        (Pm ⊢ arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 192#64) rest ∗
          (memRegion ptsPtr 192 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc := hA.dealloc_ok_at fromPbDecName
    (num% (ls_off% "__rustc::__rust_dealloc" - 0x5d724))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  from_pb_fetches_range b (Rust.withPanics ext) 904 172
  dsimp only [tripleRatchetProgAtExt, fromPbDecName,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx20 hx21 hx22 ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  refine DropGlueFacts.seq_clean (mid := entry + 932#64) (P_mid :=
    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
      (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
      (memRegion ptsPtr 24 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
        ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · have hpre0 :
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr
          (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
            ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
        vecU8 A ptsPtr c0 ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      show (vecU8 A ptsPtr c0 ∗ _) ∗ _ = _
      ac_rfl
    rw [hpre0]
    refine SepWP.weaken_pre (vecU8_frame_entails A ptsPtr c0 _) ?_
    apply ProofLib.SepWP.exists_left; intro cap
    apply ProofLib.SepWP.exists_left; intro ptr
    dsimp only [vecCapPtrDealloc]
    have hpost0 :
        ((ptsPtr ↦₆₄ cap) ∗ ((ptsPtr + 8#64) ↦₆₄ ptr) ∗ memRegion (ptsPtr + 16#64) 8) ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
            (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (((out + 384#64) ↦₆₄ ptsNeeded64) ∗ ((out + 392#64) ↦₈ isComplete8) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ⊢
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 24#64)
          (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 24 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      refine Entails.trans (slot0_entails_memRegion_24 ptsPtr cap ptr _) ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.strengthen_entails_const hpost0 ?_
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp_1, hx21_1, hvregs_1, htrace_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 952#64) (P_mid :=
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 48#64)
        (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion ptsPtr 48 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
          ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step ptsPtr 24#64 32#64 40#64 48#64 24 48 c1 hsp_1
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx21_2, hvregs_2, htrace_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + 976#64) (P_mid :=
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 72#64)
          (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion ptsPtr 72 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
            ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step ptsPtr 48#64 56#64 64#64 72#64 48 72 c2 hsp_2
      · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine DropGlueFacts.seq_clean (mid := entry + 996#64) (P_mid :=
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 96#64)
            (c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion ptsPtr 96 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
              ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step ptsPtr 72#64 80#64 88#64 96#64 72 96 c3 hsp_3
        · intro s4 hpc4 hrun4 ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine DropGlueFacts.seq_clean (mid := entry + 1016#64) (P_mid :=
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 120#64)
              (c5 :: c6 :: c7 :: rest) ∗
              (memRegion ptsPtr 120 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step ptsPtr 96#64 104#64 112#64 120#64 96 120 c4 hsp_4
          · intro s5 hpc5 hrun5 ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine DropGlueFacts.seq_clean (mid := entry + 1036#64) (P_mid :=
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 144#64)
                (c6 :: c7 :: rest) ∗
                (memRegion ptsPtr 144 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                  ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step ptsPtr 120#64 128#64 136#64 144#64 120 144 c5 hsp_5
            · intro s6 hpc6 hrun6 ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine DropGlueFacts.seq_clean (mid := entry + 1056#64) (P_mid :=
                arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 168#64)
                  (c7 :: rest) ∗
                  (memRegion ptsPtr 168 ∗ (((out + 384#64) ↦₆₄ ptsNeeded64) ∗
                    ((out + 392#64) ↦₈ isComplete8) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗
                    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                  sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
              · dealloc_u8_slot_step ptsPtr 144#64 152#64 160#64 168#64 144 168 c6 hsp_6
              · intro s7 hpc7 hrun7 ⟨hsp_7, hx19_7, hx21_7, hvregs_7, htrace_7⟩
                dealloc_u8_slot_step ptsPtr 168#64 176#64 184#64 192#64 168 192 c7 hsp_7

/-- Deallocates slots `8..15` of `ptsPtr` (`+1076..+1236`), merging into `memRegion ptsPtr 384`. -/
theorem fromPb_success_dealloc_last8 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 c15 : List (BitVec 8))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1236#64)
      s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 192#64)
        (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc := hA.dealloc_ok_at fromPbDecName
    (num% (ls_off% "__rustc::__rust_dealloc" - 0x5d724))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  from_pb_fetches_range b (Rust.withPanics ext) 1076 160
  dsimp only [tripleRatchetProgAtExt, fromPbDecName,
    Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx21 ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  refine DropGlueFacts.seq_clean (mid := entry + 1096#64) (P_mid :=
    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 216#64)
      (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
      (memRegion ptsPtr 216 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
      sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dealloc_u8_slot_step ptsPtr 192#64 200#64 208#64 216#64 192 216 c8 hsp
  · intro s1 hpc1 hrun1 ⟨hsp_1, hx19_1, hx21_1, hvregs_1, htrace_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 1116#64) (P_mid :=
      arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 240#64)
        (c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
        (memRegion ptsPtr 240 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
        sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dealloc_u8_slot_step ptsPtr 216#64 224#64 232#64 240#64 216 240 c9 hsp_1
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx19_2, hx21_2, hvregs_2, htrace_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + 1136#64) (P_mid :=
        arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 264#64)
          (c11 :: c12 :: c13 :: c14 :: c15 :: []) ∗
          (memRegion ptsPtr 264 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
          sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
      · dealloc_u8_slot_step ptsPtr 240#64 248#64 256#64 264#64 240 264 c10 hsp_2
      · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hvregs_3, htrace_3⟩
        refine DropGlueFacts.seq_clean (mid := entry + 1156#64) (P_mid :=
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 288#64)
            (c12 :: c13 :: c14 :: c15 :: []) ∗
            (memRegion ptsPtr 288 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
            sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
        · dealloc_u8_slot_step ptsPtr 264#64 272#64 280#64 288#64 264 288 c11 hsp_3
        · intro s4 hpc4 hrun4 ⟨hsp_4, hx19_4, hx21_4, hvregs_4, htrace_4⟩
          refine DropGlueFacts.seq_clean (mid := entry + 1176#64) (P_mid :=
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 312#64)
              (c13 :: c14 :: c15 :: []) ∗
              (memRegion ptsPtr 312 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
              sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
          · dealloc_u8_slot_step ptsPtr 288#64 296#64 304#64 312#64 288 312 c12 hsp_4
          · intro s5 hpc5 hrun5 ⟨hsp_5, hx19_5, hx21_5, hvregs_5, htrace_5⟩
            refine DropGlueFacts.seq_clean (mid := entry + 1196#64) (P_mid :=
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 336#64)
                (c14 :: c15 :: []) ∗
                (memRegion ptsPtr 336 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
            · dealloc_u8_slot_step ptsPtr 312#64 320#64 328#64 336#64 312 336 c13 hsp_5
            · intro s6 hpc6 hrun6 ⟨hsp_6, hx19_6, hx21_6, hvregs_6, htrace_6⟩
              refine DropGlueFacts.seq_clean (mid := entry + 1216#64) (P_mid :=
                arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 360#64)
                   (c15 :: []) ∗
                  (memRegion ptsPtr 360 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 (Reg.gpr 19#5) = pbA ∧
                  sm.readReg64 (Reg.gpr 21#5) = ptsPtr ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
              · dealloc_u8_slot_step ptsPtr 336#64 344#64 352#64 360#64 336 360 c14 hsp_6
              · intro s7 hpc7 hrun7 ⟨hsp_7, hx19_7, hx21_7, hvregs_7, htrace_7⟩
                have hpost_nil :
                    arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + 384#64) [] ∗
                      (memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) ⊢
                    memRegion ptsPtr 384 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
                  simp only [arrayAt_nil, emp_sepConj]; exact Entails.refl _
                refine SepWP.strengthen_entails_const hpost_nil ?_
                dealloc_u8_slot_step ptsPtr 360#64 368#64 376#64 384#64 360 384 c15 hsp_7

theorem list_length_16_elim {α : Type} {xs : List α} (h : xs.length = 16) :
    ∃ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15,
      xs = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] := by
  match xs, h with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15], _ =>
    exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, rfl⟩

theorem memRegion_400_split_ok (out : BitVec 64) :
    memRegion out 400 =
      memRegion out 384 ∗
      (∃∗ d384 : BitVec 64, (out + 384#64) ↦₆₄ d384) ∗
      (∃∗ b392 : BitVec 8, (out + 392#64) ↦₈ b392) ∗
      memRegion (out + 393#64) 7 := by
  have h392 : (out + 384#64) + 8#64 = out + 392#64 := by bv_omega
  have h393 : (out + 392#64) + 1#64 = out + 393#64 := by bv_omega
  rw [show (400 : Nat) = 384 + (8 + (1 + 7)) by rfl,
      ProofLib.memRegion_split out 384 16 (by decide),
      ProofLib.memRegion_split (out + 384#64) 8 8 (by decide), h392,
      ProofLib.memRegion_split (out + 392#64) 1 7 (by decide), h393,
      ProofLib.memRegion_eight, ProofLib.memRegion_one]

theorem u32_zeroExtend64_eq_ofNat_toNat (v : BitVec 32) :
    v.zeroExtend 64 = BitVec.ofNat 64 v.toNat := by
  bv_omega

/-- Success exit (`+876 -> s0.lr`):
    copies the 16 `SortedSet<Pt>` headers (`384` bytes) from `fsp + 32` to `out`,
    writes `pb.ptsNeeded` at `out + 384` and `pb.isComplete` at `out + 392`,
    deallocates the 16 `Vec<u8>` elements of `pb.pts` via `fromPb_success_dealloc_first8`
    and `fromPb_success_dealloc_last8`, and runs `fromPb_tail_1236_sepWP`. -/
theorem fromPb_success_exit_876_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pb : ProtoPolynomialDecoder) (hbss_len : pb.pts.length = 16)
    (outPts : List SortedSetPt) (hout_len : outPts.length = 16)
    (hle : pb.pts.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (sortedSetPtListOf A (fsp + 32#64) outPts ∗
        memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
        ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hmemcpy := hA.session_memcpy_ok_at fromPbDecName
    (num% (ls_off% "memcpy" - 0x5d724))
    (hk := by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [sessionMemcpySpec] at hmemcpy
  rw [sortedSetPtListOf_eq_vecPtListOf]
  have hvecs_len : (outPts.map SortedSetPt.vec).length = 16 := by simp [hout_len]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecPtListOf_entails_headers_heaps A (outPts.map SortedSetPt.vec) (fsp + 32#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply SepWP.pure_elim; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_len]
  conv => arg 4; rw [memRegion_400_split_ok out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b392
  apply ProofLib.SepWP.exists_left; intro d384
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hpts_eq⟩ :=
    list_length_16_elim hbss_len
  refine DropGlueFacts.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 904#64)
    (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
      (((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
        ((fsp + 16#64) ↦₆₄ pbA) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (sortedSetPtListOf A out outPts ∗
          memRegion (out + 393#64) 7 ∗
          memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ Frame)))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = BitVec.ofNat 64 pb.ptsNeeded.toNat ∧
      sm.readReg64 .x20 = (boolByte pb.isComplete).zeroExtend 64 ∧
      sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x22 = out ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · from_pb_fetches_range b (Rust.withPanics ext) 876 28
    dsimp only [tripleRatchetProgAtExt, fromPbDecName,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, BitVec.ofNat_eq_ofNat] at hmemcpy hpc hx21 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    rw [← hbs_len]
    wp_call hmemcpy (out, fsp + 32#64, vecHeadersBytesOf pins (outPts.map SortedSetPt.vec))
    apply SepWP.done hpc_sf hrun_sf
    have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp])
    refine ⟨?_, ?_⟩
    · rw [← hsp_sf, hsp_sf', hbs_len, sortedSetPtListOf_eq_vecPtListOf]
      have hdst : (out ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ∗
          vecPtHeapList A pins (outPts.map SortedSetPt.vec) ⊢
          vecPtListOf A out (outPts.map SortedSetPt.vec) :=
        headers_heaps_entails_vecPtListOf A pins (outPts.map SortedSetPt.vec) out hpins_len
      have hsrc : ((fsp + 32#64) ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ⊢
          memRegion (fsp + 32#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion (fsp + 32#64) _
      have hpb16 := pbA_tail_entails_memRegion_16 pbA pb.ptsNeeded pb.polys (boolByte pb.isComplete)
      refine Entails.trans (replace_sub_entails hdst
        (((fsp + 32#64) ↦ₛ vecHeadersBytesOf pins (outPts.map SortedSetPt.vec)) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (by ac_rfl) (by ac_rfl)) ?_
      refine Entails.trans (replace_sub_entails hsrc
        (vecPtListOf A out (outPts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          ((pbA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ pb.polys) ∗
          ((pbA + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (pbA + 33#64) 7 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (by ac_rfl) (by ac_rfl)) ?_
      exact replace_sub_entails hpb16
        (vecPtListOf A out (outPts.map SortedSetPt.vec) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
          ((out + 384#64) ↦₆₄ d384) ∗ ((out + 392#64) ↦₈ b392) ∗
          memRegion (out + 393#64) 7 ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (by ac_rfl) (by ac_rfl)
    · rw [← u32_zeroExtend64_eq_ofNat_toNat pb.ptsNeeded]
      simp [wp_norm, arm64_norm, *]
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hvregs1, htr1⟩
    have harr_eq : arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts =
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr
          [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] := by
      rw [hpts_eq]
    conv => arg 4; rw [harr_eq]
    refine DropGlueFacts.seq_clean
      (fromPb_success_dealloc_first8 hA s0 fsp out pbA ptsPtr d384
        (BitVec.ofNat 64 pb.ptsNeeded.toNat) b392 (boolByte pb.isComplete) hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] s1 _
        hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hvregs1 htr1) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hvregs2, htr2⟩
    refine align_pre_wp
      (DropGlueFacts.seq_clean
        (fromPb_success_dealloc_last8 hA s0 fsp pbA ptsPtr hfsp_align
          c8 c9 c10 c11 c12 c13 c14 c15 s2
          (((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
            ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
            ((fsp + 16#64) ↦₆₄ pbA) ∗
            (sortedSetPtListOf A out outPts ∗
              memRegion (out + 393#64) 7 ∗
              memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
              memRegion (fsp + 32#64) 384 ∗
              ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
              memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame))
          hpc2 hrun2 hsp2 hx19_2 hx21_2 hvregs2 htr2) ?_)
      (by ac_rfl)
    intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hvregs3, htr3⟩
    have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
    have hrejoin_buf := DropGlueFacts.memRegion_rejoin_vecBuf A 24 8 cap_pts ptsPtr pb.pts.length hle hcap_bound
    have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
    have hok_out :
        sortedSetPtListOf A out outPts ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (out + 393#64) 7 ⊢
        resultPolyDecoderFromPbAt A out
          (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) := by
      unfold resultPolyDecoderFromPbAt polyDecoderAt
      dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff, polyDecoderPadSize]
      have hpure : outPts.length = NUM_POLYS ∧ pb.ptsNeeded.toNat < 2 ^ 64 :=
        ⟨by simp [hout_len, NUM_POLYS, CHUNK_SIZE], by omega⟩
      exact Entails.pure_right hpure (Entails.of_eq (by ac_rfl))
    have hpre_1236 :
        memRegion ptsPtr 384 ∗
          (A.pool ∗ stackAt fsp allocHookStack ∗
            (((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
              ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
              ((fsp + 16#64) ↦₆₄ pbA) ∗
              (sortedSetPtListOf A out outPts ∗
                memRegion (out + 393#64) 7 ∗
                memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
                memRegion (fsp + 32#64) 384 ∗
                ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
                memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
                (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
                memRegion (pbA + 24#64) 16 ∗
                (if cap_pts = 0 then emp
                  else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                    memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24)) ((cap_pts.toNat - pb.pts.length) * 24)) ∗
                memRegion (fsp - 4128#64) 32 ∗ Frame))) ⊢
        (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
          (resultPolyDecoderFromPbAt A out
              (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) := by
      have h384 : memRegion ptsPtr 384 = memRegion ptsPtr (pb.pts.length * 24) := by rw [hbss_len]
      rw [h384, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
      unfold vecVecU8BufDealloc
      refine Entails.trans (replace_sub_entails hrejoin_buf
        (A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32 ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          sortedSetPtListOf A out outPts ∗
          memRegion (out + 393#64) 7 ∗
          memRegion fsp 8 ∗ ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          memRegion (fsp + 32#64) 384 ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)) ?_
      refine Entails.trans (replace_sub_entails hfsp448
        ((if (cap_pts == 0#64) = true then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32 ∗
          ((out + 384#64) ↦₆₄ BitVec.ofNat 64 pb.ptsNeeded.toNat) ∗
          ((out + 392#64) ↦₈ boolByte pb.isComplete) ∗
          sortedSetPtListOf A out outPts ∗
          memRegion (out + 393#64) 7 ∗
          savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)) ?_
      exact replace_sub_entails hok_out
        ((pbA ↦₆₄ cap_pts) ∗
          (if (cap_pts == 0#64) = true then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24)) ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)
    have hpost_final :
        (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
          (resultPolyDecoderFromPbAt A out
              (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
        resultPolyDecoderFromPbAt A out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
      replace_sub_entails hrejoin_pb
        (resultPolyDecoderFromPbAt A out
            (.ok { ptsNeeded := pb.ptsNeeded.toNat, isComplete := pb.isComplete, pts := outPts }) ∗
          A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
    exact SepWP.weaken_pre hpre_1236
      (SepWP.strengthen_entails_const hpost_final
        (fromPb_tail_1236_sepWP hA s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          s3 _ hpc3 hrun3 hsp3 hx19_3 hx21_3 hvregs3 htr3))

end CryptoVerification.SpqrV1.Poly.DecoderPb
