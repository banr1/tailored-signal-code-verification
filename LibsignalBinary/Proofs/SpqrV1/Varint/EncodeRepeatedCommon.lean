/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Base
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import ProofLib.SepLogic.WPp

/-!
# Shared Definitions and Helpers for `prost::encoding::bytes::encode_repeated`

Shared instruction decodes, `&[Vec<u8>]` slice layout predicates, `encodeRepeatedSpec`,
and call-step helpers for `encode_repeated [local#1, 2]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction Decode Lemmas -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x36064 → 0x36150, 0x47c48 → 0x47d44]

abbrev encodeRepeated1Name : String :=
  "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#1]"

abbrev encodeRepeated2Name : String :=
  "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"

/-- Stack budget for `encode_repeated [local#1, 2]` parameterized by `resStack`:
`80 + (0x30 + resStack)` bytes (`80` B own frame + `0x30 + resStack` B for `encode_varint`). -/
abbrev encodeRepeatedStackOf (resStack : Nat) : Nat := 80 + (0x30 + resStack)

/-- Stack budget for `encode_repeated [local#1, 2]` (`0x35f80`, `0x4d040`):
`encodeVarintStack` (`4256` B) + own frame `0x50` (`80` B) = `4336` B. -/
abbrev encodeRepeatedStack : Nat := encodeRepeatedStackOf doReserveStack

abbrev encodeRepeatedStackX : Nat := encodeRepeatedStackOf doReserveStackX

/-! ## Pure Model of `prost::encoding::bytes::encode_repeated` -/

/-- `prost::encoding::bytes::encode_repeated(tag, values, buf)` (`prost-0.14.4/src/encoding.rs:733–737`):
for each element `v` in `values`, appends `encodeBytesField tag (some v)`
(`= encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 v.length) ++ v`). -/
def encodeRepeatedBytes (tag : ℕ) : List (List (BitVec 8)) → List (BitVec 8)
  | [] => []
  | v :: vs => encodeBytesField tag (some v) ++ encodeRepeatedBytes tag vs

@[simp]
theorem encodeRepeatedBytes_nil (tag : ℕ) :
    encodeRepeatedBytes tag [] = [] := rfl

@[simp]
theorem encodeRepeatedBytes_cons (tag : ℕ) (v : List (BitVec 8)) (vs : List (List (BitVec 8))) :
    encodeRepeatedBytes tag (v :: vs) =
      encodeBytesField tag (some v) ++ encodeRepeatedBytes tag vs := rfl

theorem encodeRepeatedBytes_append (tag : ℕ) (xs ys : List (List (BitVec 8))) :
    encodeRepeatedBytes tag (xs ++ ys) =
      encodeRepeatedBytes tag xs ++ encodeRepeatedBytes tag ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

theorem encodeBytesField_some_eq (tag : ℕ) (v : List (BitVec 8)) :
    encodeBytesField tag (some v) =
      encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 v.length) ++ v := rfl

theorem encodeKey_lengthDelimited_eq (tag : ℕ) :
    encodeKey tag .lengthDelimited = encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) := rfl

theorem encodeBytesField_some_length (tag : ℕ) (v : List (BitVec 8)) :
    (encodeBytesField tag (some v)).length =
      (encodeKey tag .lengthDelimited).length +
        (encodeVarint (BitVec.ofNat 64 v.length)).length + v.length := by
  simp only [encodeBytesField_some_eq, List.length_append]

/-! ## Memory Representation of `&[Vec<u8>]` Slices -/

/-- Read-only view of a single 24-byte `Vec<u8>` element at `a` as read by `encode_repeated`:
loads `ptr` from `a + 8` and `bs.length` from `a + 16` (`ldp x22, x21, [x25, #-8]`),
and reads `ptr ↦ₛ bs` (which is `emp` when `bs = []`). -/
def repeatedBytesElemAt (a ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((a + 8#64) ↦₆₄ ptr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (ptr ↦ₛ bs)

/-- Read-only slice of 24-byte `Vec<u8>` headers at `base, base + 24, ...`. -/
def repeatedBytesSliceAt (base : BitVec 64) : List (BitVec 64 × List (BitVec 8)) → SepProp
  | [] => emp
  | (ptr, bs) :: rest =>
    repeatedBytesElemAt base ptr bs ∗ repeatedBytesSliceAt (base + 24#64) rest

@[simp]
theorem repeatedBytesSliceAt_nil (base : BitVec 64) :
    repeatedBytesSliceAt base [] = emp := rfl

@[simp]
theorem repeatedBytesSliceAt_cons (base ptr : BitVec 64) (bs : List (BitVec 8))
    (rest : List (BitVec 64 × List (BitVec 8))) :
    repeatedBytesSliceAt base ((ptr, bs) :: rest) =
      repeatedBytesElemAt base ptr bs ∗ repeatedBytesSliceAt (base + 24#64) rest := rfl

/-- Full array of `vecU8At A` elements at `base, base + 24, ...`. -/
def vecU8ArrayAt (A : RustAlloc) (base : BitVec 64) :
    List (BitVec 64 × BitVec 64 × List (BitVec 8)) → SepProp
  | [] => emp
  | (cap, ptr, bs) :: rest =>
    vecU8At A base cap ptr bs ∗ vecU8ArrayAt A (base + 24#64) rest

/-- Frame remainder of a single `vecU8At A a cap ptr bs` after extracting `repeatedBytesElemAt a ptr bs`. -/
def vecU8ElemRestAt (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ cap) ∗
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if cap = 0 then emp
    else
      A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

/-- Frame remainder of `vecU8ArrayAt A base elems` after extracting `repeatedBytesSliceAt`. -/
def vecU8ArrayRestAt (A : RustAlloc) (base : BitVec 64) :
    List (BitVec 64 × BitVec 64 × List (BitVec 8)) → SepProp
  | [] => emp
  | (cap, ptr, bs) :: rest =>
    vecU8ElemRestAt A base cap ptr bs ∗ vecU8ArrayRestAt A (base + 24#64) rest

theorem vecU8At_eq_repeatedBytesElemAt (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (h : cap = 0 → bs = []) :
    vecU8At A a cap ptr bs =
      repeatedBytesElemAt a ptr bs ∗ vecU8ElemRestAt A a cap ptr bs := by
  unfold vecU8At vecHeader repeatedBytesElemAt vecU8ElemRestAt
  by_cases hcap : cap = 0
  · have hbs := h hcap
    subst hcap hbs
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
    ac_rfl
  · simp only [hcap, ↓reduceIte]
    ac_rfl

/-! ## Specifications of `encode_repeated [local#1, 2]` -/

/-- Ghost state for `prost::encoding::bytes::encode_repeated::<Vec<u8>, Vec<u8>>`:
field number `tag` (`w0`, `1 ≤ tag < 2 ^ 29`), slice `(base, elems)` (`x1, x2`),
and output `Vec<u8>` `(v, cap, ptr, bs)` (`x3`). -/
structure EncodeRepeatedGhost where
  /-- Protobuf field number (`1 ≤ tag < 2 ^ 29`, passed in `w0`). -/
  tag : Nat
  /-- Base address of the `&[Vec<u8>]` slice (`x1`). -/
  base : BitVec 64
  /-- Slice elements `(ptr_i, bs_i)` (`x2 = BitVec.ofNat 64 elems.length`). -/
  elems : List (BitVec 64 × List (BitVec 8))
  /-- Address of `buf: &mut Vec<u8>` (`x3`, 24-byte `Vec<u8>` header). -/
  v : BitVec 64
  /-- Initial capacity word of `buf` (`[v + 0]`). -/
  cap : BitVec 64
  /-- Initial buffer pointer of `buf` (`[v + 8]`). -/
  ptr : BitVec 64
  /-- Initial contents of `buf` (`[v + 16] = bs.length`). -/
  bs : List (BitVec 8)

/-- Specification of `prost::encoding::bytes::encode_repeated::<Vec<u8>, Vec<u8>>` (`[local#1, 2]`)
at reserve stack budget `resStack`: appends `encodeRepeatedBytes x.tag (x.elems.map Prod.snd)`
to `buf` (`x3`), preserving `repeatedBytesSliceAt x.base x.elems` and avoiding reallocation
whenever initial capacity `x.cap` covers the encoded output. -/
def encodeRepeatedSpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeRepeatedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 58 ∧
      (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length + 10 < 2 ^ 62)⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeRepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeRepeatedBytes x.tag (x.elems.map Prod.snd))) ∗
      A.pool ∗ stackAt s0.sp (encodeRepeatedStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def encodeRepeatedSpec (A : RustAlloc) : Spec EncodeRepeatedGhost :=
  encodeRepeatedSpecOf doReserveStack A

def encodeRepeatedSpecX (A : RustAlloc) : Spec EncodeRepeatedGhost :=
  encodeRepeatedSpecOf doReserveStackX A

/-! ## Arithmetic, Separation-Logic, and Call Helpers -/

theorem len_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

theorem setup_x24_eq {n : Nat} (hlt : n < 2 ^ 58) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 =
      BitVec.ofNat 64 (24 * n) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2n : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3n : (BitVec.ofNat 64 (3 * n)).toNat = 3 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h24n : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, hn, h2n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 (3 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hn, h2n, h3n, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, h3n, h24n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

theorem setup_x20_eq {tag : Nat} (htag : tag < 2 ^ 29) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32 (2#64 ||| BitVec.zeroExtend 64 (BitVec.ofNat 32 tag <<< 3))) =
      BitVec.ofNat 64 (tag * 8 + 2) := by
  have ht32 : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ht8_32 : (BitVec.ofNat 32 (tag * 8)).toNat = tag * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkey32 : (BitVec.ofNat 32 (tag * 8 + 2)).toNat = tag * 8 + 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkey64 : (BitVec.ofNat 64 (tag * 8 + 2)).toNat = tag * 8 + 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh : BitVec.ofNat 32 tag <<< 3 = BitVec.ofNat 32 (tag * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, ht32, ht8_32, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have htr : BitVec.truncate 32 (2#64 ||| BitVec.zeroExtend 64 (BitVec.ofNat 32 tag <<< 3)) =
      2#32 ||| (BitVec.ofNat 32 tag <<< 3) := by
    bv_bits
  have hor : (2#32 ||| (BitVec.ofNat 32 tag <<< 3)) = BitVec.ofNat 32 (tag * 8 + 2) := by
    have hadd : (BitVec.ofNat 32 tag <<< 3) + 2#32 = (2#32 ||| (BitVec.ofNat 32 tag <<< 3)) := by
      bv_bits
    rw [← hadd, hsh]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, ht8_32, hkey32]
    change (tag * 8 + 2) % 2 ^ 32 = tag * 8 + 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [htr, hor]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, hkey32, hkey64, Nat.mod_eq_of_lt (by omega)]

theorem latch_sub24_eq (k : Nat) (hk : k + 1 < 2 ^ 58) :
    BitVec.ofNat 64 (24 * (k + 1)) - 24#64 = BitVec.ofNat 64 (24 * k) := by
  have hk_toNat : (BitVec.ofNat 64 (24 * (k + 1))).toNat = 24 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk0_toNat : (BitVec.ofNat 64 (24 * k)).toNat = 24 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hle : (24#64 : BitVec 64) ≤ BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [BitVec.le_def, hk_toNat]
    change 24 ≤ 24 * (k + 1)
    omega
  rw [BitVec.toNat_sub_of_le hle, hk_toNat, hk0_toNat]
  change 24 * (k + 1) - 24 = 24 * k
  omega

theorem latch_beq_zero_true :
    (BitVec.ofNat 64 (24 * 1) + 18446744073709551592#64 == 0#64) = true := by
  rfl

theorem latch_beq_zero_false {k : Nat} (hpos : 0 < k) (hlt : k + 1 < 2 ^ 58) :
    (BitVec.ofNat 64 (24 * (k + 1)) + 18446744073709551592#64 == 0#64) = false := by
  have hsub : BitVec.ofNat 64 (24 * (k + 1)) + 18446744073709551592#64 =
      BitVec.ofNat 64 (24 * (k + 1)) - 24#64 := by bv_omega
  rw [hsub, latch_sub24_eq k hlt, beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change 24 * k = 0 at ht
  omega

theorem base_add16_sub8 (curBase : BitVec 64) :
    curBase + 16#64 - 8#64 = curBase + 8#64 := by bv_omega

theorem base_add16_sub8_add8 (curBase : BitVec 64) :
    curBase + 16#64 - 8#64 + 8#64 = curBase + 16#64 := by bv_omega

theorem base_add16_add24 (curBase : BitVec 64) :
    curBase + 16#64 + 24#64 = (curBase + 24#64) + 16#64 := by bv_omega

theorem elem_len_ult_spare_iff {cap : BitVec 64} {bsLen elemLen : Nat}
    (hle : bsLen ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (helem : elemLen < 2 ^ 63) :
    ((cap - BitVec.ofNat 64 bsLen).ult (BitVec.ofNat 64 elemLen) = true) ↔
      cap.toNat < bsLen + elemLen := by
  have hle_bv : BitVec.ofNat 64 bsLen ≤ cap := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hle
  rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le hle_bv,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem elem_len_after_reserve_not_ult {cap : BitVec 64} {bsLen elemLen : Nat}
    (hfit : bsLen + elemLen < 2 ^ 62) (hlt : cap.toNat < bsLen + elemLen) :
    let newCap := reserveCap cap.toNat bsLen elemLen
    ((BitVec.ofNat 64 elemLen).ule (BitVec.ofNat 64 newCap - BitVec.ofNat 64 bsLen) = true) ∧
      bsLen + elemLen ≤ (BitVec.ofNat 64 newCap).toNat ∧
      cap.toNat ≤ (BitVec.ofNat 64 newCap).toNat ∧
      newCap + 1 ≤ 2 ^ 63 := by
  intro newCap
  have hnew_ge : bsLen + elemLen ≤ newCap := by
    dsimp [newCap, reserveCap]; omega
  have hnew_cap : cap.toNat ≤ newCap := by
    dsimp [newCap, reserveCap]; omega
  have hnew_bound : newCap + 1 ≤ 2 ^ 63 := by
    dsimp [newCap, reserveCap]; omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, by omega, by omega, hnew_bound⟩
  have hle_bv : BitVec.ofNat 64 bsLen ≤ BitVec.ofNat 64 newCap := by
    rw [BitVec.le_def, hnew_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le hle_bv,
    hnew_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem vecU8At_expose_header (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          if cap = 0 then emp
          else
            A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, sepConj_assoc]

private theorem cap_ne_zero_of_pos {cap : BitVec 64} (h : 0 < cap.toNat) : cap ≠ 0 := by
  intro heq; subst heq; simp at h

theorem vecU8At_expose_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hle : bs.length + n ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) (hn_pos : 0 < n) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
          (cap.toNat - bs.length - n)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  have hcap_ne : cap ≠ 0 := cap_ne_zero_of_pos (by omega)
  rw [vecU8At_expose_header A v cap ptr bs, hpure, pure_true, emp_sepConj]
  simp only [hcap_ne, ↓reduceIte]
  rw [memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
        (n := n) (k := cap.toNat - bs.length - n)
        (by omega) rfl (by omega)]

theorem vecU8At_pack_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (hne : payload ≠ []) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
        (cap.toNat - bs.length - payload.length)) =
    vecU8At A v cap ptr (bs ++ payload) := by
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  have hcap_ne : cap ≠ 0 := cap_ne_zero_of_pos (by omega)
  rw [vecU8At_expose_header A v cap ptr (bs ++ payload)]
  simp only [hcap_ne, ↓reduceIte]
  have hlen : (bs ++ payload).length = bs.length + payload.length := List.length_append
  have hbv : BitVec.ofNat 64 (bs.length + payload.length) =
      BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length) =
      ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by bv_omega
  have hsub : cap.toNat - (bs.length + payload.length) =
      cap.toNat - bs.length - payload.length := by omega
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨hle, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, pointsToBytes_append, hpure, pure_true, emp_sepConj]
  ac_rfl

theorem stackAt_encodeRepeated {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (encodeRepeatedStackOf resStack) =
      stackAt (sp - 80#64) (0x30 + resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
          ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
          ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
          ((sp - 8#64) ↦₆₄ v9)) := by
  have h1 := ProofLib.stackAt_split_cells sp (0x30 + resStack) 10 (by omega)
  have heq : 0x30 + resStack + 8 * 10 = encodeRepeatedStackOf resStack := by
    dsimp [encodeRepeatedStackOf]; omega
  rw [heq] at h1
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [h1, hc10]

theorem stackAt_encodeVarint_eq_doReserve {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (0x30 + resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ stackAt sp1 resStack := by
  have h := ProofLib.stackAt_split_bottom sp1 resStack 48 (by omega)
  have heq : resStack + 48 = 0x30 + resStack := by omega
  simpa only [heq] using h

def vecU8RestAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0 then emp
  else
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8At_eq_header_rest (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8RestAt A cap ptr bs := by
  rw [vecU8At_expose_header A v cap ptr bs, vecU8RestAt]
  ac_rfl

theorem vecU8At_of_header_rest (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8RestAt A cap ptr bs) =
    vecU8At A v cap ptr bs := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨hle, hcap, hptr⟩
  rw [vecU8At_eq_header_rest A v cap ptr bs, hpure, pure_true, emp_sepConj]

theorem sp_sub_80_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 80#64) &&& 15#64 = 0#64 := by
  bv_bits

/-- Callee-saved registers `x26..x28` untouched by `encode_repeated` (`x19..x25, fp` are saved on stack),
together with `StepInv s0 s` for `inImage img` invariant propagation. -/
def EncRepeatedCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem EncRepeatedCalleeSaved.refl (s0 : State) : EncRepeatedCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, StepInv.refl s0⟩

theorem EncRepeatedCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : EncRepeatedCalleeSaved s0 s1) (h12 : EncRepeatedCalleeSaved s1 s2) :
    EncRepeatedCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h01.2.2.2.2.trans h12.2.2.2.2⟩

theorem EncRepeatedCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : EncRepeatedCalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem EncRepeatedCalleeSaved.step {s0 s1 s2 : State}
    (h01 : EncRepeatedCalleeSaved s0 s1)
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    EncRepeatedCalleeSaved s0 s2 :=
  h01.trans ⟨hx26, hx27, hx28, hvregs, hinv⟩

/-- Wrap a `Spec α` with `⌜EncRepeatedCalleeSaved s0 s⌝` in the precondition so a single
generalized proof works for both `spec` and `spec.inImage img`. -/
def withEncRepeatedCS {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜EncRepeatedCalleeSaved s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withEncRepeatedCS {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withEncRepeatedCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withEncRepeatedCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withEncRepeatedCS_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withEncRepeatedCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withEncRepeatedCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2.2.2 img hinv0, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

theorem step_memcpy_call_gen {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

theorem step_memcpy_call (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc sessionMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) :=
  step_memcpy_call_gen A hmemcpy dst src sp ret_pc bs hpc hrun hsp halign htr hlr hx0 hx1 hx2 hcs hP hnext

theorem step_encode_varint_call_gen {resStack : Nat} {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  refine SepWPp.call_cs (x := EncodeVarintGhost.mk val v curCap curPtr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withEncRepeatedCS, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withEncRepeatedCS, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      encodeRepeatedSpec, encodeRepeatedSpecOf, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    exact Entails.of_eq (by ac_rfl)

theorem step_encode_varint_call {resStack : Nat} (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) :=
  step_encode_varint_call_gen A henc val v curCap curPtr sp ret_pc curBs hlen_lt hpc hrun hsp halign htr hlr hx0 hx1 hcs hP hnext

theorem step_do_reserve2_call_gen {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 80#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)] at hm
    simp only [withEncRepeatedCS, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withEncRepeatedCS, doReserve2SpecOf, doReserveSpec, encodeRepeatedSpec,
      encodeRepeatedSpecOf, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, doReserve2SpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_do_reserve2_call {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withEncRepeatedCS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) :=
  step_do_reserve2_call_gen hres A hdoReserve v curCap curPtr sp ret_pc curBs additional hbound
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hcs hP hnext

theorem step_do_reserve7_call_gen {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withEncRepeatedCS s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_80_aligned halign
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 80#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)] at hm
    simp only [withEncRepeatedCS, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withEncRepeatedCS, doReserveSpecOf, doReserveSpec, encodeRepeatedSpec,
      encodeRepeatedSpecOf, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withEncRepeatedCS, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (EncRepeatedCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve hres (sp - 80#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_do_reserve7_call {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withEncRepeatedCS s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) :=
  step_do_reserve7_call_gen hres A hdoReserve v curCap curPtr sp ret_pc curBs additional hbound
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs hP hnext

end CryptoVerification.SpqrV1.Varint
