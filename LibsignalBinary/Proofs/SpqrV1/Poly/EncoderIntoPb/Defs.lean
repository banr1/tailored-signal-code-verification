/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- shake: keep

/-!
# `<PolyEncoder>::into_pb`: Definitions and Specifications

**Checked by Lean.**

AArch64 separation-logic specifications for `<spqr::encoding::polynomial::PolyEncoder>::into_pb`
(`0x6285c`), which consumes a 400-byte `PolyEncoder` at `x1` and writes its 56-byte
`ProtoPolynomialEncoder` (`enc.intoPb`) at `x0` (sret), or panics on OOM.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderIntoPb

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop (dropGluePoly16Stack dropPoly16Name vecGF16Of vecGF16ListOf
  pointListOf_eq_vecGF16ListOf polyListOf_eq_vecGF16ListOf)
export CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqrRustNoAllocShimSym spqrRustAllocSym)
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts

set_option linter.unusedSimpArgs false

/-! ## Symbol Names and Stack Budgets -/

abbrev dropGluePoly16Name : String := Drop.dropPoly16Name

abbrev encoderIntoPbName : String :=
  "<spqr::encoding::polynomial::PolyEncoder>::into_pb"

/-- Stack budget of `<PolyEncoder>::into_pb` (`0xe0 = 224` B own frame + `dropGluePoly16Stack` = `256 + allocHookStack`). -/
abbrev encoderIntoPbStack : Nat := 224 + dropGluePoly16Stack

abbrev encoderIntoPbStackX : Nat := 224 + extHookStack

/-! ## Specification -/

/-- Ghost arguments of `<PolyEncoder>::into_pb` (`0x6285c`). -/
structure EncoderIntoPbGhost where
  /-- Sret pointer (`x0`, 56-byte `ProtoPolynomialEncoder` output). -/
  out : BitVec 64
  /-- Pointer to the 400-byte `PolyEncoder` moved by value (`x1`). -/
  encA : BitVec 64
  /-- Logical `PolyEncoder` value at `encA`. -/
  enc : PolyEncoder

/-- Spec of `<spqr::encoding::polynomial::PolyEncoder>::into_pb`
    (`src/encoding/polynomial.rs:563–596`, image offset `0x6285c`, 176 instructions):
    * Registers: `x0 = out` (56-byte `ProtoPolynomialEncoder` sret), `x1 = encA` (400-byte `PolyEncoder`).
    * Consumes `polyEncoderAt A encA enc` (deallocating its 16 `Vec<GF16>` buffers and leaving
      `memRegion encA 400`) and writes `protoPolynomialEncoderAt A out enc.intoPb`, or panics on OOM. -/
def encoderIntoPbSpec (A : RustAlloc) : Spec EncoderIntoPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.encA⌝ ∗
      memRegion x.out protoPolynomialEncoderSize ∗
      polyEncoderAt A x.encA x.enc ∗
      A.pool ∗ stackAt s.sp encoderIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialEncoderAt A x.out x.enc.intoPb ∗
      memRegion x.encA polyEncoderSize ∗
      A.pool ∗ stackAt s0.sp encoderIntoPbStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Extended-stack variant of `encoderIntoPbSpec` (`encoderIntoPbStackX = 224 + extHookStack`). -/
def encoderIntoPbSpecX (A : RustAlloc) : Spec EncoderIntoPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.encA⌝ ∗
      memRegion x.out protoPolynomialEncoderSize ∗
      polyEncoderAt A x.encA x.enc ∗
      A.pool ∗ stackAt s.sp encoderIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialEncoderAt A x.out x.enc.intoPb ∗
      memRegion x.encA polyEncoderSize ∗
      A.pool ∗ stackAt s0.sp encoderIntoPbStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<PolyEncoder>::into_pb` meets `encoderIntoPbSpec A` on `tripleRatchetProgAtExt b ext`. -/
def EncoderIntoPbOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName)
    (encoderIntoPbSpec A)

/-- `<PolyEncoder>::into_pb` meets `(encoderIntoPbSpecX A).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def EncoderIntoPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encoderIntoPbName)
    ((encoderIntoPbSpecX A).inImage img)

/-- `<PolyEncoder>::into_pb` (Block `375`) meets `encoderIntoPbSpec A` on
    `(blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)` under `[LibsignalPlacement]`. -/
def EncoderIntoPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
    (blkPl_375).base
    (encoderIntoPbSpec A)

/-- `<PolyEncoder>::into_pb` (Block `375`) meets `encoderIntoPbSpecX A` on
    `(blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)` under `[LibsignalPlacement]`. -/
def EncoderIntoPbPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
    (blkPl_375).base
    (encoderIntoPbSpecX A)

/-! ## Shared Memory, Stack, and Representation Lemmas -/

/-- Serialize a list of `GF16` elements into big-endian byte pairs. -/
def serializeGF16List (cs : List GF16) : List (BitVec 8) :=
  cs.flatMap (fun g => u16ToBeBytes g.value)

@[simp] theorem serializeGF16List_nil :
    serializeGF16List [] = [] := rfl

@[simp] theorem serializeGF16List_cons (g : GF16) (cs : List GF16) :
    serializeGF16List (g :: cs) = u16ToBeBytes g.value ++ serializeGF16List cs := rfl

@[simp] theorem length_u16ToBeBytes (v : BitVec 16) :
    (u16ToBeBytes v).length = 2 := rfl

@[simp] theorem length_serializeGF16List :
    ∀ cs : List GF16, (serializeGF16List cs).length = 2 * cs.length
  | [] => rfl
  | g :: cs => by
    rw [serializeGF16List_cons, List.length_append, length_u16ToBeBytes,
        length_serializeGF16List cs, List.length_cons]
    omega

theorem intoPb_points_pts (pts : List Point) :
    pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value)) =
      (pts.map Point.value).map serializeGF16List := by
  rw [List.map_map]; rfl

theorem intoPb_polys_polys (polys : List LibsignalSpqrV1.Poly) :
    polys.map LibsignalSpqrV1.Poly.serialize =
      (polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List := by
  rw [List.map_map]; rfl

theorem pointsTo16_rev16_eq_u16ToBeBytes (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ ((rev16_64 (v.zeroExtend 64)).setWidth 32).setWidth 16) =
      (a ↦ₛ u16ToBeBytes v) := by
  rw [pointsTo16_eq_pointsToBytes]
  congr 1
  simp only [unpack16, u16ToBeBytes, rev16_64, List.cons.injEq, and_true]
  exact ⟨by bv_slice, by bv_slice⟩

theorem memRegion_two_cons (dstPtr : BitVec 64) (done n : Nat)
    (hbound : 2 * (n + 1) < 2 ^ 63) :
    memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * (n + 1)) =
      (∃∗ v : BitVec 16, (dstPtr + BitVec.ofNat 64 (2 * done)) ↦₁₆ v) ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * n) := by
  have hmul : 2 * (n + 1) = 2 + 2 * n := by omega
  have hadd : dstPtr + BitVec.ofNat 64 (2 * done) + 2#64 =
      dstPtr + BitVec.ofNat 64 (2 * (done + 1)) := by
    rw [BitVec.add_assoc]
    congr 1
    simp [Nat.mul_add, BitVec.ofNat_add]
  rw [hmul, ProofLib.memRegion_split (dstPtr + BitVec.ofNat 64 (2 * done)) 2 (2 * n) (by omega),
      ProofLib.memRegion_two, hadd]

theorem off_add_two (done : Nat) :
    BitVec.ofNat 64 (2 * done) + 2#64 = BitVec.ofNat 64 (2 * (done + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]; bv_omega

theorem rem_bytes_not_ule_one {done remLen total : Nat}
    (htot : done + (remLen + 1) = total) (hmax : 2 * total < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false := by
  have hsub : BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done) =
      BitVec.ofNat 64 (2 * (remLen + 1)) := by
    have h1 : 2 * total = 2 * done + 2 * (remLen + 1) := by omega
    rw [h1, BitVec.ofNat_add]
    bv_omega
  rw [hsub]
  have hlt : 2 * (remLen + 1) < 2 ^ 64 := by omega
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, decide_eq_false_iff_not]
  change ¬ (2 * (remLen + 1) ≤ 1)
  omega

theorem bne_one_of_pos {n : Nat} (hpos : 0 < n) (hlt : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1) != 1#64) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n + 1 = 1 at ht
  omega

@[arm64_norm, wp_norm]
theorem fp_sub_48 (fsp : BitVec 64) :
    (fsp + 128#64) + 18446744073709551568#64 = fsp + 80#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_sub_32 (fsp : BitVec 64) :
    (fsp + 128#64) + 18446744073709551584#64 = fsp + 96#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_sub_24 (fsp : BitVec 64) :
    (fsp + 128#64) + 18446744073709551592#64 = fsp + 104#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_sub_16 (fsp : BitVec 64) :
    (fsp + 128#64) + 18446744073709551600#64 = fsp + 112#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_sub_8 (fsp : BitVec 64) :
    (fsp + 128#64) + 18446744073709551608#64 = fsp + 120#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_sub_48_int (fsp : BitVec 64) :
    (fsp + 128#64) + (-48 : Int64).toBitVec = fsp + 80#64 := fp_sub_48 fsp

@[arm64_norm, wp_norm]
theorem fp_sub_32_int (fsp : BitVec 64) :
    (fsp + 128#64) + (-32 : Int64).toBitVec = fsp + 96#64 := fp_sub_32 fsp

@[arm64_norm, wp_norm]
theorem fp_sub_24_int (fsp : BitVec 64) :
    (fsp + 128#64) + (-24 : Int64).toBitVec = fsp + 104#64 := fp_sub_24 fsp

@[arm64_norm, wp_norm]
theorem fp_sub_16_int (fsp : BitVec 64) :
    (fsp + 128#64) + (-16 : Int64).toBitVec = fsp + 112#64 := fp_sub_16 fsp

@[arm64_norm, wp_norm]
theorem fp_sub_8_int (fsp : BitVec 64) :
    (fsp + 128#64) + (-8 : Int64).toBitVec = fsp + 120#64 := fp_sub_8 fsp

@[arm64_norm, wp_norm]
theorem fp_sub_40 (fsp : BitVec 64) :
    (fsp + 128#64) + 18446744073709551576#64 = fsp + 88#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_sub_40_int (fsp : BitVec 64) :
    (fsp + 128#64) + (-40 : Int64).toBitVec = fsp + 88#64 := fp_sub_40 fsp

@[arm64_norm, wp_norm]
theorem sp_add_56_add_8 (fsp : BitVec 64) :
    (fsp + 56#64) + 8#64 = fsp + 64#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem sp_add_80_add_8 (fsp : BitVec 64) :
    (fsp + 80#64) + 8#64 = fsp + 88#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem sp_add_104_add_8 (fsp : BitVec 64) :
    (fsp + 104#64) + 8#64 = fsp + 112#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
theorem ofNat_add_one (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add]

@[arm64_norm, wp_norm]
theorem madd_24_eq (base : BitVec 64) (j : Nat) :
    base + BitVec.ofNat 64 j * 24#64 = base + BitVec.ofNat 64 (24 * j) := by
  congr 1
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem off_24_succ (base : BitVec 64) (j : Nat) :
    (base + BitVec.ofNat 64 (24 * j)) + 24#64 = base + BitVec.ofNat 64 (24 * (j + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ofNat_ne_16 {j : Nat} (hj : j < 16) :
    (BitVec.ofNat 64 j != 16#64) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change j = 16 at ht
  omega

theorem ofNat_beq_16_false {j : Nat} (hj : j < 16) :
    (BitVec.ofNat 64 j == 16#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change j = 16 at ht
  omega

theorem memRegion_24_cons (base : BitVec 64) (j n : Nat) (h : j + (n + 1) ≤ 16) :
    memRegion (base + BitVec.ofNat 64 (24 * j)) (24 * (n + 1)) =
      (∃∗ v0 : BitVec 64, (base + BitVec.ofNat 64 (24 * j)) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, ((base + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, ((base + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ v2) ∗
      memRegion (base + BitVec.ofNat 64 (24 * (j + 1))) (24 * n) := by
  have hmul : 24 * (n + 1) = 24 + 24 * n := by omega
  let el := base + BitVec.ofNat 64 (24 * j)
  have h24 : memRegion el 24 =
      (∃∗ v0 : BitVec 64, el ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (el + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (el + 16#64) ↦₆₄ v2) := by
    have h88 : (el + 8#64) + 8#64 = el + 16#64 := by bv_omega
    rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
        ProofLib.memRegion_split el 8 (8 + 8) (by decide),
        ProofLib.memRegion_split (el + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        h88]
  rw [hmul, ProofLib.memRegion_split el 24 (24 * n) (by omega), h24, off_24_succ,
      sepConj_assoc, sepConj_assoc]

theorem vecU8_slot_intro (A : RustAlloc) (el cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (el ↦₆₄ cap) ∗ ((el + 8#64) ↦₆₄ ptr) ∗
      ((el + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢
    vecU8 A el bs := by
  have heq :
      (el ↦₆₄ cap) ∗ ((el + 8#64) ↦₆₄ ptr) ∗
        ((el + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs =
      vecU8At A el cap ptr bs := by
    rw [vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl
  rw [heq]
  exact vecU8At_entails_vecU8 A el cap ptr bs

/-- Remaining buffer and allocator block of a `Vec<GF16>` after splitting out `arrayAt gf16At 2 ptr cs`. -/
def vecGF16Tail (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ len * 2 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 2) 2 ∗
       memRegion (ptr + BitVec.ofNat 64 (len * 2)) ((cap.toNat - len) * 2))

theorem vecGF16Of_expose (A : RustAlloc) (v : BitVec 64) (cs : List GF16) :
    vecGF16Of A v cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜2 * cs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          arrayAt gf16At 2 ptr cs ∗
          vecGF16Tail A cap ptr cs.length := by
  unfold vecGF16Of vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (DropGlueFacts.vecAt_expose_loop A 2 2 gf16At v cap ptr cs) ?_
  unfold vecGF16Tail
  apply Entails.pure_left; rintro ⟨hle, hcap, hxs, hptr⟩
  have hlen : 2 * cs.length < 2 ^ 63 := by omega
  have heq :
      (⌜2 * cs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        arrayAt gf16At 2 ptr cs ∗
        (⌜cs.length ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ cs.length * 2 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 2) 2 ∗
             memRegion (ptr + BitVec.ofNat 64 (cs.length * 2)) ((cap.toNat - cs.length) * 2)))) =
      (⌜2 * cs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ cs.length * 2 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          arrayAt gf16At 2 ptr cs ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 2) 2 ∗
             memRegion (ptr + BitVec.ofNat 64 (cs.length * 2)) ((cap.toNat - cs.length) * 2)))) := by
    ac_rfl
  rw [heq]
  exact Entails.pure_right ⟨hlen, hptr⟩ (Entails.pure_right ⟨hle, hcap, hxs, hptr⟩ (Entails.refl _))

theorem vecGF16Of_intro (A : RustAlloc) (v cap ptr : BitVec 64) (cs : List GF16) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      arrayAt gf16At 2 ptr cs ∗
      vecGF16Tail A cap ptr cs.length) ⊢
    vecGF16Of A v cs := by
  unfold vecGF16Of vecOf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecAt vecHeader vecBuf vecGF16Tail gf16Stride gf16Align
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      arrayAt gf16At 2 ptr cs ∗
      (⌜cs.length ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ cs.length * 2 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 2) 2 ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 2)) ((cap.toNat - cs.length) * 2))) =
    ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ cs.length * 2 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length)) ∗
        (arrayAt gf16At 2 ptr cs ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 2) 2 ∗
             memRegion (ptr + BitVec.ofNat 64 (cs.length * 2)) ((cap.toNat - cs.length) * 2)))) by
    ac_rfl]
  apply Entails.pure_left; rintro ⟨hle, hcap, _, hptr⟩
  apply sepConj_mono_right
  apply Entails.pure_right ⟨hle, hcap, hptr⟩
  by_cases hc : cap = 0
  · subst hc
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp [arrayAt_nil]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8Buf_nil_intro (A : RustAlloc) (Rest : SepProp) :
    Rest ⊢ vecU8Buf A 0#64 1#64 [] ∗ Rest := by
  unfold vecU8Buf
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  exact Entails.pure_right hp (Entails.refl _)

theorem vecU8Buf_of_exact_alloc (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen_pos : 0 < bs.length) (hlen_bound : bs.length < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((ptr ↦ₛ bs) ∗ A.live ptr bs.length 1) ⊢
      vecU8Buf A (BitVec.ofNat 64 bs.length) ptr bs := by
  unfold vecU8Buf
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [htoNat] at ht
    change bs.length = 0 at ht
    omega
  have hp : bs.length ≤ (BitVec.ofNat 64 bs.length).toNat ∧
      (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    refine ⟨by omega, by omega, hptr⟩
  have hite :
      (if BitVec.ofNat 64 bs.length = 0 then emp
       else A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) ((BitVec.ofNat 64 bs.length).toNat - bs.length)) =
      (A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [hite]
  exact Entails.pure_right hp (Entails.of_eq (by ac_rfl))

theorem shiftLeft_one_eq_mul_two {n : Nat} (h : 2 * n < 2 ^ 63) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

@[arm64_norm, wp_norm] theorem off_8_add_8 (base : BitVec 64) : (base + 8#64) + 8#64 = base + 16#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_16_add_8 (base : BitVec 64) : (base + 16#64) + 8#64 = base + 24#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_24_add_8 (base : BitVec 64) : (base + 24#64) + 8#64 = base + 32#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_32_add_8 (base : BitVec 64) : (base + 32#64) + 8#64 = base + 40#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_40_add_8 (base : BitVec 64) : (base + 40#64) + 8#64 = base + 48#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_48_add_8 (base : BitVec 64) : (base + 48#64) + 8#64 = base + 56#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_56_add_8 (base : BitVec 64) : (base + 56#64) + 8#64 = base + 64#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_64_add_8 (base : BitVec 64) : (base + 64#64) + 8#64 = base + 72#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_72_add_8 (base : BitVec 64) : (base + 72#64) + 8#64 = base + 80#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_80_add_8 (base : BitVec 64) : (base + 80#64) + 8#64 = base + 88#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_88_add_8 (base : BitVec 64) : (base + 88#64) + 8#64 = base + 96#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_96_add_8 (base : BitVec 64) : (base + 96#64) + 8#64 = base + 104#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_104_add_8 (base : BitVec 64) : (base + 104#64) + 8#64 = base + 112#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_112_add_8 (base : BitVec 64) : (base + 112#64) + 8#64 = base + 120#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_120_add_8 (base : BitVec 64) : (base + 120#64) + 8#64 = base + 128#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_128_add_8 (base : BitVec 64) : (base + 128#64) + 8#64 = base + 136#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_136_add_8 (base : BitVec 64) : (base + 136#64) + 8#64 = base + 144#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_144_add_8 (base : BitVec 64) : (base + 144#64) + 8#64 = base + 152#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_152_add_8 (base : BitVec 64) : (base + 152#64) + 8#64 = base + 160#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_160_add_8 (base : BitVec 64) : (base + 160#64) + 8#64 = base + 168#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_168_add_8 (base : BitVec 64) : (base + 168#64) + 8#64 = base + 176#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_176_add_8 (base : BitVec 64) : (base + 176#64) + 8#64 = base + 184#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_184_add_8 (base : BitVec 64) : (base + 184#64) + 8#64 = base + 192#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_192_add_8 (base : BitVec 64) : (base + 192#64) + 8#64 = base + 200#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_200_add_8 (base : BitVec 64) : (base + 200#64) + 8#64 = base + 208#64 := by bv_omega
@[arm64_norm, wp_norm] theorem off_208_add_8 (base : BitVec 64) : (base + 208#64) + 8#64 = base + 216#64 := by bv_omega
@[arm64_norm, wp_norm] theorem sub_224_add_224 (sp : BitVec 64) : (sp - 224#64) + 224#64 = sp := by bv_omega

theorem pointsTo64_split32 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) := by
  apply IsBlock.eq (IsBlock.pointsTo64 a v)
    ((IsBlock.pointsTo32 a _).sepConj (IsBlock.pointsTo32 (a + 4#64) _) rfl (by decide))
  intro m
  rw [Memory.read32_eq_truncate_read64, Memory.read32_add4_eq_extract_read64]
  generalize m.read64 a = w
  constructor <;> intro h <;> bv_kernel

theorem pointsTo32_merge64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32]
  have h1 : (hi ++ lo).truncate 32 = lo := by bv_kernel
  have h2 : (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel
  rw [h1, h2]

theorem pointsTo64_off48_split32 (base : BitVec 64) (v : BitVec 64) :
    ((base + 48#64) ↦₆₄ v) =
      ((base + 48#64) ↦₃₂ v.truncate 32) ∗ ((base + 52#64) ↦₃₂ v.extractLsb' 32 32) := by
  have h52 : (base + 48#64) + 4#64 = base + 52#64 := by bv_omega
  rw [pointsTo64_split32, h52]

theorem pointsTo32_off48_merge64 (base : BitVec 64) (lo hi : BitVec 32) :
    (((base + 48#64) ↦₃₂ lo) ∗ ((base + 52#64) ↦₃₂ hi)) = ((base + 48#64) ↦₆₄ (hi ++ lo)) := by
  have h52 : (base + 48#64) + 4#64 = base + 52#64 := by bv_omega
  rw [← h52, pointsTo32_merge64]

theorem pointsTo64_off48_entails_idx_pad (out : BitVec 64) (idx hi : BitVec 32) :
    ((out + 48#64) ↦₆₄ (hi ++ idx)) ⊢
      ((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4 := by
  rw [← pointsTo32_off48_merge64 out idx hi]
  exact sepConj_mono_right (pointsTo32_entails_memRegion (out + 52#64) hi)

theorem memRegion_56_split (out : BitVec 64) :
    memRegion out 56 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (out + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (out + 48#64) ↦₆₄ d6) := by
  rw [show (56 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + 8))))) by rfl,
      ProofLib.memRegion_split out 8 48 (by decide),
      ProofLib.memRegion_split (out + 8#64) 8 40 (by decide), off_8_add_8,
      ProofLib.memRegion_split (out + 16#64) 8 32 (by decide), off_16_add_8,
      ProofLib.memRegion_split (out + 24#64) 8 24 (by decide), off_24_add_8,
      ProofLib.memRegion_split (out + 32#64) 8 16 (by decide), off_32_add_8,
      ProofLib.memRegion_split (out + 40#64) 8 8 (by decide), off_40_add_8,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight]

theorem encA_rejoin_400 (encA : BitVec 64) :
    memRegion encA 8 ∗ memRegion (encA + 8#64) 384 ∗ memRegion (encA + 392#64) 8 =
      memRegion encA 400 := by
  have h8_384 : (encA + 8#64) + 384#64 = encA + 392#64 := by bv_omega
  rw [show (400 : Nat) = 8 + (384 + 8) by rfl,
      ProofLib.memRegion_split encA 8 (384 + 8) (by decide),
      ProofLib.memRegion_split (encA + 8#64) 384 8 (by decide), h8_384]

theorem encA_tail_rejoin_8 (encA : BitVec 64) (idx : BitVec 32) :
    ((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4 ⊢
      memRegion (encA + 392#64) 8 := by
  have h396 : (encA + 392#64) + 4#64 = encA + 396#64 := by bv_omega
  rw [show (8 : Nat) = 4 + 4 by rfl,
      ProofLib.memRegion_split (encA + 392#64) 4 4 (by decide), h396]
  exact sepConj_mono_left (pointsTo32_entails_memRegion (encA + 392#64) idx)

theorem stackAt_encoderIntoPb_split (sp : BitVec 64) :
    stackAt sp encoderIntoPbStack =
      stackAt (sp - 224#64) dropGluePoly16Stack ∗ cells (sp - 224#64) 28 :=
  LibsignalTripleRatchet.stackAt_split_cells sp dropGluePoly16Stack 28 (by decide)

theorem stackAt_dropGluePoly16_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropGluePoly16Stack =
      memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 32 (by decide)

theorem cells28_fsp_eq (fsp : BitVec 64) :
    cells fsp 28 =
      (∃∗ v0 : BitVec 64, fsp ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (fsp + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (fsp + 16#64) ↦₆₄ v2) ∗ (∃∗ v3 : BitVec 64, (fsp + 24#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (fsp + 32#64) ↦₆₄ v4) ∗ (∃∗ v5 : BitVec 64, (fsp + 40#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (fsp + 48#64) ↦₆₄ v6) ∗ (∃∗ v7 : BitVec 64, (fsp + 56#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (fsp + 64#64) ↦₆₄ v8) ∗ (∃∗ v9 : BitVec 64, (fsp + 72#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (fsp + 80#64) ↦₆₄ v10) ∗ (∃∗ v11 : BitVec 64, (fsp + 88#64) ↦₆₄ v11) ∗
      (∃∗ v12 : BitVec 64, (fsp + 96#64) ↦₆₄ v12) ∗ (∃∗ v13 : BitVec 64, (fsp + 104#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (fsp + 112#64) ↦₆₄ v14) ∗ (∃∗ v15 : BitVec 64, (fsp + 120#64) ↦₆₄ v15) ∗
      (∃∗ v16 : BitVec 64, (fsp + 128#64) ↦₆₄ v16) ∗ (∃∗ v17 : BitVec 64, (fsp + 136#64) ↦₆₄ v17) ∗
      (∃∗ v18 : BitVec 64, (fsp + 144#64) ↦₆₄ v18) ∗ (∃∗ v19 : BitVec 64, (fsp + 152#64) ↦₆₄ v19) ∗
      (∃∗ v20 : BitVec 64, (fsp + 160#64) ↦₆₄ v20) ∗ (∃∗ v21 : BitVec 64, (fsp + 168#64) ↦₆₄ v21) ∗
      (∃∗ v22 : BitVec 64, (fsp + 176#64) ↦₆₄ v22) ∗ (∃∗ v23 : BitVec 64, (fsp + 184#64) ↦₆₄ v23) ∗
      (∃∗ v24 : BitVec 64, (fsp + 192#64) ↦₆₄ v24) ∗ (∃∗ v25 : BitVec 64, (fsp + 200#64) ↦₆₄ v25) ∗
      (∃∗ v26 : BitVec 64, (fsp + 208#64) ↦₆₄ v26) ∗ (∃∗ v27 : BitVec 64, (fsp + 216#64) ↦₆₄ v27) := by
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    off_8_add_8, off_16_add_8, off_24_add_8, off_32_add_8, off_40_add_8,
    off_48_add_8, off_56_add_8, off_64_add_8, off_72_add_8, off_80_add_8,
    off_88_add_8, off_96_add_8, off_104_add_8, off_112_add_8, off_120_add_8,
    off_128_add_8, off_136_add_8, off_144_add_8, off_152_add_8, off_160_add_8,
    off_168_add_8, off_176_add_8, off_184_add_8, off_192_add_8, off_200_add_8,
    off_208_add_8, ← sepExists_sepConj_left]

theorem cells28_fsp_entails (fsp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
     v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
    ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
    ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗ ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
    ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
    ((fsp + 128#64) ↦₆₄ v16) ∗ ((fsp + 136#64) ↦₆₄ v17) ∗ ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ∗
    ((fsp + 160#64) ↦₆₄ v20) ∗ ((fsp + 168#64) ↦₆₄ v21) ∗ ((fsp + 176#64) ↦₆₄ v22) ∗ ((fsp + 184#64) ↦₆₄ v23) ∗
    ((fsp + 192#64) ↦₆₄ v24) ∗ ((fsp + 200#64) ↦₆₄ v25) ∗ ((fsp + 208#64) ↦₆₄ v26) ∗ ((fsp + 216#64) ↦₆₄ v27) ⊢
    cells fsp 28 := by
  rw [cells28_fsp_eq fsp]
  exact sepConj_mono (Entails.sepExists_right v0 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v1 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v2 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v3 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v4 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v5 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v6 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v7 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v8 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v9 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v10 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v11 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v12 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v13 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v14 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v15 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v16 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v17 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v18 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v19 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v20 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v21 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v22 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v23 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v24 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v25 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v26 (Entails.refl _)) (Entails.sepExists_right v27 (Entails.refl _))))))))))))))))))))))))))))

theorem vecVecU8At_empty_cap16 (A : RustAlloc) (v ptr : BitVec 64) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ 16#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr 384 8 ∗ memRegion ptr 384) ⊢
    vecVecU8At A v [] := by
  unfold vecVecU8At vecOf
  refine Entails.sepExists_right 16#64 (Entails.sepExists_right ptr ?_)
  unfold vecAt vecHeader vecBuf vecHeaderBytes
  have h16_ne : (16#64 : BitVec 64) ≠ 0#64 := by decide
  have h16_toNat : (16#64 : BitVec 64).toNat = 16 := rfl
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, arrayAt_nil, sepConj_emp, emp_sepConj,
    h16_ne, ↓reduceIte, h16_toNat, Nat.zero_mul, Nat.sub_zero, Nat.reduceMul]
  have hz : ptr + 0#64 = ptr := by simp
  rw [hz]
  have hp : 0 ≤ 16 ∧ 384 < 2 ^ 63 ∧ ptr ≠ 0#64 := ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (Entails.pure_right hp (Entails.refl _)))

theorem vecVecU8At_full_cap16 (A : RustAlloc) (v ptr : BitVec 64)
    (bss : List (List (BitVec 8))) (hlen : bss.length = 16) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ 16#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 16#64) ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗ A.live ptr 384 8) ⊢
    vecVecU8At A v bss := by
  unfold vecVecU8At vecOf
  refine Entails.sepExists_right 16#64 (Entails.sepExists_right ptr ?_)
  unfold vecAt vecHeader vecBuf vecHeaderBytes
  have h16_ne : (16#64 : BitVec 64) ≠ 0#64 := by decide
  have h16_toNat : (16#64 : BitVec 64).toNat = 16 := rfl
  simp only [hlen, BitVec.ofNat_eq_ofNat, h16_ne, ↓reduceIte, h16_toNat,
    Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp, emp_sepConj, Nat.reduceMul]
  have hp : 16 ≤ 16 ∧ 384 < 2 ^ 63 ∧ ptr ≠ 0#64 := ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (Entails.pure_right hp (Entails.refl _)))

theorem into_pb_epilogue_post_entails (A : RustAlloc) (sp0 fsp out encA : BitVec 64)
    (hfsp : fsp = sp0 - 224#64)
    (idx hi48 : BitVec 32)
    (w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64)
    (r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (Frame : SepProp) :
    (fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
      ((fsp + 24#64) ↦₆₄ w3) ∗ ((fsp + 32#64) ↦₆₄ w4) ∗ ((fsp + 40#64) ↦₆₄ w5) ∗
      ((fsp + 48#64) ↦₆₄ (hi48 ++ idx)) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
      ((fsp + 64#64) ↦₆₄ w8) ∗ ((fsp + 72#64) ↦₆₄ w9) ∗ ((fsp + 80#64) ↦₆₄ w10) ∗
      ((fsp + 88#64) ↦₆₄ w11) ∗ ((fsp + 96#64) ↦₆₄ w12) ∗ ((fsp + 104#64) ↦₆₄ w13) ∗
      ((fsp + 112#64) ↦₆₄ w14) ∗ ((fsp + 120#64) ↦₆₄ w15) ∗
      ((fsp + 128#64) ↦₆₄ r29) ∗ ((fsp + 136#64) ↦₆₄ r30) ∗ ((fsp + 144#64) ↦₆₄ r28) ∗
      ((fsp + 152#64) ↦₆₄ r27) ∗ ((fsp + 160#64) ↦₆₄ r26) ∗ ((fsp + 168#64) ↦₆₄ r25) ∗
      ((fsp + 176#64) ↦₆₄ r24) ∗ ((fsp + 184#64) ↦₆₄ r23) ∗ ((fsp + 192#64) ↦₆₄ r22) ∗
      ((fsp + 200#64) ↦₆₄ r21) ∗ ((fsp + 208#64) ↦₆₄ r20) ∗ ((fsp + 216#64) ↦₆₄ r19) ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
      ((out + 48#64) ↦₆₄ (hi48 ++ idx)) ∗
      memRegion encA 8 ∗ memRegion (encA + 8#64) polyArrayBytes ∗ memRegion (encA + 392#64) 8 ∗
      A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame ⊢
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
      ((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4 ∗
      memRegion encA 400 ∗
      A.pool ∗ stackAt sp0 encoderIntoPbStack ∗ Frame := by
  have hcells := cells28_fsp_entails fsp
    w0 w1 w2 w3 w4 w5 (hi48 ++ idx) w7 w8 w9 w10 w11 w12 w13 w14 w15
    r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19
  have hidx := pointsTo64_off48_entails_idx_pad out idx hi48
  have hstk : stackAt sp0 encoderIntoPbStack = stackAt fsp dropGluePoly16Stack ∗ cells fsp 28 := by
    rw [hfsp, stackAt_encoderIntoPb_split sp0]
  dsimp only [polyArrayBytes]
  rw [hstk, ← encA_rejoin_400 encA]
  refine Entails.trans (Q :=
    ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
      ((fsp + 24#64) ↦₆₄ w3) ∗ ((fsp + 32#64) ↦₆₄ w4) ∗ ((fsp + 40#64) ↦₆₄ w5) ∗
      ((fsp + 48#64) ↦₆₄ (hi48 ++ idx)) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
      ((fsp + 64#64) ↦₆₄ w8) ∗ ((fsp + 72#64) ↦₆₄ w9) ∗ ((fsp + 80#64) ↦₆₄ w10) ∗
      ((fsp + 88#64) ↦₆₄ w11) ∗ ((fsp + 96#64) ↦₆₄ w12) ∗ ((fsp + 104#64) ↦₆₄ w13) ∗
      ((fsp + 112#64) ↦₆₄ w14) ∗ ((fsp + 120#64) ↦₆₄ w15) ∗
      ((fsp + 128#64) ↦₆₄ r29) ∗ ((fsp + 136#64) ↦₆₄ r30) ∗ ((fsp + 144#64) ↦₆₄ r28) ∗
      ((fsp + 152#64) ↦₆₄ r27) ∗ ((fsp + 160#64) ↦₆₄ r26) ∗ ((fsp + 168#64) ↦₆₄ r25) ∗
      ((fsp + 176#64) ↦₆₄ r24) ∗ ((fsp + 184#64) ↦₆₄ r23) ∗ ((fsp + 192#64) ↦₆₄ r22) ∗
      ((fsp + 200#64) ↦₆₄ r21) ∗ ((fsp + 208#64) ↦₆₄ r20) ∗ ((fsp + 216#64) ↦₆₄ r19)) ∗
    ((out + 48#64) ↦₆₄ (hi48 ++ idx)) ∗
    ((out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
      memRegion encA 8 ∗ memRegion (encA + 8#64) 384 ∗ memRegion (encA + 392#64) 8 ∗
      A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hcells (sepConj_mono hidx (Entails.refl _))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem pointsTo32_tag_entails_memRegion8 (a : BitVec 64) (lo hi : BitVec 32) :
    (a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi) ⊢ memRegion a 8 := by
  rw [pointsTo32_merge64 a lo hi]
  exact pointsTo64_entails_memRegion a (hi ++ lo)

theorem pointsTo64_split32_tag (a : BitVec 64) (tag : BitVec 64) (Rest : SepProp) :
    (a ↦₃₂ tag.truncate 32) ∗ ((a + 4#64) ↦₃₂ tag.extractLsb' 32 32) ∗ Rest ⊢
      memRegion a 8 ∗ Rest := by
  rw [← sepConj_assoc]
  exact sepConj_mono_left
    (pointsTo32_tag_entails_memRegion8 a (tag.truncate 32) (tag.extractLsb' 32 32))

theorem protoPolynomialEncoderAt_points_entails (A : RustAlloc) (out ptr_points ptr_polys : BitVec 64)
    (idx : BitVec 32) (points : List Point) (hlen : points.length = NUM_POLYS)
    (hptr_pts : ptr_points ≠ 0) (hptr_polys : ptr_polys ≠ 0) :
    ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_points) ∗ ((out + 16#64) ↦₆₄ 16#64) ∗
      ((out + 24#64) ↦₆₄ 16#64) ∗ ((out + 32#64) ↦₆₄ ptr_polys) ∗ ((out + 40#64) ↦₆₄ 0#64) ∗
      ((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4 ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
        ((points.map Point.value).map serializeGF16List) ∗
      A.live ptr_points 384 8 ∗
      A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384) ⊢
    protoPolynomialEncoderAt A out ({ idx := idx, s := .points points } : PolyEncoder).intoPb := by
  unfold protoPolynomialEncoderAt PolyEncoder.intoPb
  dsimp only [protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
    protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize, BitVec.ofNat_eq_ofNat]
  rw [intoPb_points_pts]
  have hlen' : ((points.map Point.value).map serializeGF16List).length = 16 := by
    simp [hlen, NUM_POLYS, CHUNK_SIZE]
  have hpts := vecVecU8At_full_cap16 A out ptr_points
    ((points.map Point.value).map serializeGF16List) hlen' hptr_pts
  have hpolys := vecVecU8At_empty_cap16 A (out + 24#64) ptr_polys hptr_polys
  have h32 : (out + 24#64) + 8#64 = out + 32#64 := by bv_omega
  have h40 : (out + 24#64) + 16#64 = out + 40#64 := by bv_omega
  rw [h32, h40] at hpolys
  refine Entails.trans (Q :=
    ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_points) ∗ ((out + 16#64) ↦₆₄ 16#64) ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
        ((points.map Point.value).map serializeGF16List) ∗
      A.live ptr_points 384 8) ∗
    (((out + 24#64) ↦₆₄ 16#64) ∗ ((out + 32#64) ↦₆₄ ptr_polys) ∗ ((out + 40#64) ↦₆₄ 0#64) ∗
      A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384) ∗
    (((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4))
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono hpts (sepConj_mono hpolys (Entails.refl _))

theorem protoPolynomialEncoderAt_polys_entails (A : RustAlloc) (out ptr_points ptr_polys : BitVec 64)
    (idx : BitVec 32) (polys : List LibsignalSpqrV1.Poly) (hlen : polys.length = NUM_POLYS)
    (hptr_pts : ptr_points ≠ 0) (hptr_polys : ptr_polys ≠ 0) :
    ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_points) ∗ ((out + 16#64) ↦₆₄ 0#64) ∗
      ((out + 24#64) ↦₆₄ 16#64) ∗ ((out + 32#64) ↦₆₄ ptr_polys) ∗ ((out + 40#64) ↦₆₄ 16#64) ∗
      ((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4 ∗
      A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
        ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
      A.live ptr_polys 384 8) ⊢
    protoPolynomialEncoderAt A out ({ idx := idx, s := .polys polys } : PolyEncoder).intoPb := by
  unfold protoPolynomialEncoderAt PolyEncoder.intoPb
  dsimp only [protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
    protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize, BitVec.ofNat_eq_ofNat]
  rw [intoPb_polys_polys]
  have hlen' : ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List).length = 16 := by
    simp [hlen, NUM_POLYS, CHUNK_SIZE]
  have hpts := vecVecU8At_empty_cap16 A out ptr_points hptr_pts
  have hpolys := vecVecU8At_full_cap16 A (out + 24#64) ptr_polys
    ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) hlen' hptr_polys
  have h32 : (out + 24#64) + 8#64 = out + 32#64 := by bv_omega
  have h40 : (out + 24#64) + 16#64 = out + 40#64 := by bv_omega
  rw [h32, h40] at hpolys
  refine Entails.trans (Q :=
    ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_points) ∗ ((out + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr_points 384 8 ∗ memRegion ptr_points 384) ∗
    (((out + 24#64) ↦₆₄ 16#64) ∗ ((out + 32#64) ↦₆₄ ptr_polys) ∗ ((out + 40#64) ↦₆₄ 16#64) ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
        ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
      A.live ptr_polys 384 8) ∗
    (((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4))
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono hpts (sepConj_mono hpolys (Entails.refl _))

@[arm64_norm, wp_norm] theorem bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl
@[arm64_norm, wp_norm] theorem bv8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl

@[arm64_norm, wp_norm]
theorem truncate_32_zeroExtend_64 (x : BitVec 32) :
    (x.zeroExtend 64).truncate 32 = x := by bv_omega

@[arm64_norm, wp_norm]
theorem setWidth_32_setWidth_64 (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by bv_omega

def withSaved19_20 (s0 : State) (encA out : BitVec 64) : State :=
  (s0.writeReg64 .x19 encA).writeReg64 .x20 out

@[simp] theorem withSaved19_20_lr (s0 : State) (encA out : BitVec 64) :
    (withSaved19_20 s0 encA out).readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_x19 (s0 : State) (encA out : BitVec 64) :
    (withSaved19_20 s0 encA out).readReg64 .x19 = encA := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_x20 (s0 : State) (encA out : BitVec 64) :
    (withSaved19_20 s0 encA out).readReg64 .x20 = out := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_trace (s0 : State) (encA out : BitVec 64) :
    (withSaved19_20 s0 encA out).trace = s0.trace := rfl

@[simp] theorem withSaved19_20_vregs (s0 : State) (encA out : BitVec 64) :
    calleeSavedVRegs (withSaved19_20 s0 encA out) = calleeSavedVRegs s0 := rfl

theorem sepWPp_elim_pure {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ Rest) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

/-- `encoderIntoPbSpec A` entails `encoderIntoPbSpecX A` by framing the unused bottom stack region. -/
theorem encoderIntoPbSpecX_of_encoderIntoPbSpec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (encoderIntoPbSpec A)) :
    subroutine_ok P addr (encoderIntoPbSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : encoderIntoPbStack ≤ encoderIntoPbStackX := by decide
  have hsplit : stackAt s0.sp encoderIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encoderIntoPbStackX)
        (encoderIntoPbStackX - encoderIntoPbStack) ∗
        stackAt s0.sp encoderIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp encoderIntoPbStack
      (encoderIntoPbStackX - encoderIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encoderIntoPbStackX)
      (encoderIntoPbStackX - encoderIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (encoderIntoPbSpec A).pre x s0 ∗ R' := by
    dsimp only [encoderIntoPbSpecX, encoderIntoPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encoderIntoPbSpecX, encoderIntoPbSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [encoderIntoPbSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SpqrV1.Poly.EncoderIntoPb
