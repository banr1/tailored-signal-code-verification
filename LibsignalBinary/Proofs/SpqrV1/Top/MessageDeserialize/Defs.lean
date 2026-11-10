/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import ProofLib.SepLogic.WPp

/-!
# Specifications & Layout Helpers for `<Message>::deserialize`

Unaligned `q0`/`q1` byte-word swap lemmas, 48-byte `Result<Message, Error>` memory layout, stack
frame decomposition, and `messageDeserializeSpecX` for
`<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`, 212 instructions) against
`Message.deserialize`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.MessageDeserialize

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5a03c → 0x5a388]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Overlapping Unaligned `q0`/`q1` Swap Helpers and 32-Byte Chunk Decomposition -/

/-- Pack `b : BitVec 8` followed by the low 7 bytes of `w : BitVec 64` into a 64-bit word. -/
def shiftWord (b : BitVec 8) (w : BitVec 64) : BitVec 64 :=
  (w <<< 8) ||| b.zeroExtend 64

def hiByte (w : BitVec 64) : BitVec 8 :=
  w.extractLsb' 56 8

def loByte (u : BitVec 64) : BitVec 8 :=
  u.extractLsb' 0 8

/-- Pack the high 7 bytes of `u : BitVec 64` followed by `b : BitVec 8` into a 64-bit word. -/
def unshiftWord (u : BitVec 64) (b : BitVec 8) : BitVec 64 :=
  (u >>> 8) ||| (b.zeroExtend 64 <<< 56)

@[simp]
theorem loByte_shiftWord (b : BitVec 8) (w : BitVec 64) :
    loByte (shiftWord b w) = b := by
  unfold loByte shiftWord
  bv_kernel

theorem unpack64_shiftWord_append_hiByte (b : BitVec 8) (w : BitVec 64) :
    unpack64 (shiftWord b w) ++ [hiByte w] = b :: unpack64 w := by
  simp only [unpack64, shiftWord, hiByte, List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem loByte_cons_unpack64_unshiftWord (u : BitVec 64) (b : BitVec 8) :
    loByte u :: unpack64 (unshiftWord u b) = unpack64 u ++ [b] := by
  simp only [unpack64, loByte, unshiftWord, List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨trivial, by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem byte_word64_swap (a : BitVec 64) (b : BitVec 8) (w : BitVec 64) :
  ((a ↦₈ b) ∗ ((a + 1#64) ↦₆₄ w)) =
      ((a ↦₆₄ shiftWord b w) ∗ ((a + 8#64) ↦₈ hiByte w)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
    ← pointsToBytes_cons, ← unpack64_shiftWord_append_hiByte b w,
    pointsToBytes_append, unpack64_length]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem word64_byte_swap (a : BitVec 64) (u : BitVec 64) (b : BitVec 8) :
    ((a ↦₆₄ u) ∗ ((a + 8#64) ↦₈ b)) =
      ((a ↦₈ loByte u) ∗ ((a + 1#64) ↦₆₄ unshiftWord u b)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
    ← pointsToBytes_cons, loByte_cons_unpack64_unshiftWord u b,
    pointsToBytes_append, unpack64_length]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem shiftWord_byte_swap (a : BitVec 64) (c4 : BitVec 8) (c5 : BitVec 64) (b : BitVec 8) :
    ((a ↦₆₄ shiftWord c4 c5) ∗ ((a + 8#64) ↦₈ b)) =
      ((a ↦₈ c4) ∗ ((a + 1#64) ↦₆₄ unshiftWord (shiftWord c4 c5) b)) := by
  rw [word64_byte_swap, loByte_shiftWord]

/-- Assemble the 32-byte list corresponding to `(c0, c1, c2, c3, c4, c5, c6)`. -/
def chunk32Bytes (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) : List (BitVec 8) :=
  unpack32 c0 ++ unpack16 c1 ++ [c2] ++ unpack64 c3 ++ [c4] ++ unpack64 c5 ++ unpack64 c6

@[simp]
theorem chunk32Bytes_length (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) :
    (chunk32Bytes c0 c1 c2 c3 c4 c5 c6).length = 32 := by
  simp [chunk32Bytes]

/-- 7-atom decomposition of 32 bytes at `p` (`4 + 2 + 1 + 8 + 1 + 8 + 8 = 32` bytes), aligned
    with the loads/stores in `<Message>::deserialize` (`0x5f65c..0x5f6b0`). -/
def chunk32AtomsAt (p : BitVec 64) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) : SepProp :=
  (p ↦₃₂ c0) ∗ ((p + 4#64) ↦₁₆ c1) ∗ ((p + 6#64) ↦₈ c2) ∗
    ((p + 7#64) ↦₆₄ c3) ∗ ((p + 15#64) ↦₈ c4) ∗
    ((p + 16#64) ↦₆₄ c5) ∗ ((p + 24#64) ↦₆₄ c6)

theorem pointsToBytes_chunk32Bytes_eq (p : BitVec 64) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) :
    (p ↦ₛ chunk32Bytes c0 c1 c2 c3 c4 c5 c6) =
      chunk32AtomsAt p c0 c1 c2 c3 c4 c5 c6 := by
  unfold chunk32Bytes chunk32AtomsAt
  simp only [List.append_assoc]
  rw [pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes,
    pointsToBytes_append, unpack16_length, ← pointsTo16_eq_pointsToBytes,
    pointsToBytes_append, List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    pointsToBytes_append, List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem chunk32AtomsAt_entails_memRegion32 (p : BitVec 64) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) :
    chunk32AtomsAt p c0 c1 c2 c3 c4 c5 c6 ⊢ memRegion p 32 := by
  rw [← pointsToBytes_chunk32Bytes_eq]
  have h := pointsToBytes_entails_memRegion p (chunk32Bytes c0 c1 c2 c3 c4 c5 c6)
  rwa [chunk32Bytes_length] at h

theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ v : BitVec 32, bs = unpack32 v := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0, (unpack32_pack32 b0 b1 b2 b3).symm⟩

theorem exists_unpack16_of_length_2 {bs : List (BitVec 8)} (h : bs.length = 2) :
    ∃ v : BitVec 16, bs = unpack16 v := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try (simp at h)
  refine ⟨b1 ++ b0, ?_⟩
  simp only [unpack16, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits⟩

theorem exists_chunk32Bytes_of_length_32 {d : List (BitVec 8)} (hd : d.length = 32) :
    ∃ (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
      (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64),
      d = chunk32Bytes c0 c1 c2 c3 c4 c5 c6 := by
  have hd4 : (d.take 4).length = 4 := by simp [hd]
  obtain ⟨c0, hc0⟩ := exists_unpack32_of_length_4 hd4
  have hd2 : ((d.drop 4).take 2).length = 2 := by simp [hd]
  obtain ⟨c1, hc1⟩ := exists_unpack16_of_length_2 hd2
  have hd26 : (d.drop 6).length = 26 := by simp [hd]
  rcases hdrop6 : d.drop 6 with _ | ⟨c2, r7⟩
  · rw [hdrop6] at hd26; simp at hd26
  have hr7 : r7.length = 25 := by rw [hdrop6, List.length_cons] at hd26; omega
  have hr7_8 : (r7.take 8).length = 8 := by simp [hr7]
  obtain ⟨c3, hc3⟩ := exists_unpack64_of_length_8 hr7_8
  have hr7_17 : (r7.drop 8).length = 17 := by simp [hr7]
  rcases hdrop8 : r7.drop 8 with _ | ⟨c4, r16⟩
  · rw [hdrop8] at hr7_17; simp at hr7_17
  have hr16 : r16.length = 16 := by rw [hdrop8, List.length_cons] at hr7_17; omega
  obtain ⟨c5, c6, hc56, _⟩ := exists_unpack64_of_length_16 hr16
  refine ⟨c0, c1, c2, c3, c4, c5, c6, ?_⟩
  have h1 : d = d.take 4 ++ d.drop 4 := (List.take_append_drop 4 d).symm
  have h2 : d.drop 4 = (d.drop 4).take 2 ++ (d.drop 4).drop 2 := (List.take_append_drop 2 (d.drop 4)).symm
  have hdrop42 : (d.drop 4).drop 2 = d.drop 6 := by rw [List.drop_drop]
  have h3 : r7 = r7.take 8 ++ r7.drop 8 := (List.take_append_drop 8 r7).symm
  rw [h1, h2, hdrop42, hdrop6, h3, hdrop8, hc0, hc1, hc3, hc56]
  simp [chunk32Bytes, List.append_assoc]

/-! ## 2. `Result<Message, Error>` (`48` bytes) Representation and Specification -/

abbrev messageDeserializeName : String :=
  "<spqr::v1::chunked::states::Message>::deserialize"

/-- Stack budget for `<Message>::deserialize` (`0x5f434`): own frame `0x90 = 144` bytes
    (`+0x004: sub sp, sp, #0x90`) plus `extHookStack` (`16384` bytes) for
    `alloc::fmt::format::format_inner` on the unknown-tag error branch (`+0x2ec`). -/
abbrev messageDeserializeStackX : Nat := 0x90 + extHookStack

/-- Error variant of `Result<Message, spqr::Error>` at `out` (`48` bytes):
    - `+0x00..+0x08` (`8B`): `memRegion out 8`
    - `+0x08..+0x09` (`1B`): niche tag `0xff#8` (`255#8` in `MessagePayload` discriminant byte)
    - `+0x09..+0x10` (`7B`): `memRegion (out + 0x09#64) 7`
    - `+0x10..+0x20` (`16B`): `q0 : BitVec 128` whose low byte `BitVec.truncate 8 q0` is `spqrErrorTag err`
    - `+0x20..+0x28` (`8B`): `w2 : BitVec 64`
    - `+0x28..+0x30` (`8B`): `memRegion (out + 0x28#64) 8` -/
def messageErrorAt (out : BitVec 64) (err : Error) : SepProp :=
  ∃∗ q0 : BitVec 128, ∃∗ w2 : BitVec 64,
    ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗
    memRegion out 8 ∗
    ((out + 0x08#64) ↦₈ 0xff#8) ∗
    memRegion (out + 0x09#64) 7 ∗
    ((out + 0x10#64) ↦₁₂₈ q0) ∗
    ((out + 0x20#64) ↦₆₄ w2) ∗
    memRegion (out + 0x28#64) 8

/-- Representation of `Except Error (Message P)` (`Result<Message, spqr::Error>`, `48` bytes) at
    `out`. -/
def messageResultAt (P : PolyApi) (out : BitVec 64) : Except Error (Message P) → SepProp
  | .ok m => messageAt P out m
  | .error err => messageErrorAt out err

/-- Ghost arguments of `<Message>::deserialize` (`0x5f434`):
    - `out`: 48-byte `Result<Message, Error>` return pointer in `x0`
    - `epoch`: `Epoch` (`BitVec 64`) in `x1`
    - `fromPtr`: `from.as_ptr()` in `x2`
    - `fromBytes`: byte slice `from` (`from.len()` in `x3`) -/
structure MessageDeserializeCall where
  out : BitVec 64
  epoch : Epoch
  fromPtr : BitVec 64
  fromBytes : Bytes

/-- Contract of `<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`, 212
    instructions) at `messageDeserializeStackX`, related to `Message.deserialize P x.epoch
    x.fromBytes`. -/
def messageDeserializeSpecX (P : PolyApi) (A : RustAlloc) : Spec MessageDeserializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg64 .x1 = x.epoch ∧
      s.readReg64 .x2 = x.fromPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.fromBytes.length ∧
      x.fromBytes.length < 2 ^ 63⌝ ∗
    memRegion x.out 48 ∗
    (x.fromPtr ↦ₛ x.fromBytes) ∗
    A.pool ∗
    stackAt s.sp messageDeserializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    messageResultAt P x.out (Message.deserialize P x.epoch x.fromBytes) ∗
    (x.fromPtr ↦ₛ x.fromBytes) ∗
    A.pool ∗
    stackAt s0.sp messageDeserializeStackX
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Callee-contract predicate for `<spqr::v1::chunked::states::Message>::deserialize`
    (`0x5f434`). -/
def MessageDeserializeOkX (P : PolyApi) (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr messageDeserializeName)
    ((messageDeserializeSpecX P A).inImage img)

/-! ## 3. Output Buffer, Stack Frame, and Error/Success Folding Helpers -/

theorem msgDeserialize_fnOff :
    libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5a03c

theorem memRegion_48_err_split (out : BitVec 64) :
    memRegion out 48 =
      memRegion out 8 ∗
      (∃∗ b8 : BitVec 8, (out + 0x08#64) ↦₈ b8) ∗
      memRegion (out + 0x09#64) 7 ∗
      (∃∗ b10 : BitVec 8, (out + 0x10#64) ↦₈ b10) ∗
      (∃∗ bs7 : List (BitVec 8), ⌜bs7.length = 7⌝ ∗ ((out + 0x11#64) ↦ₛ bs7)) ∗
      (∃∗ w1 : BitVec 64, (out + 0x18#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (out + 0x20#64) ↦₆₄ w2) ∗
      memRegion (out + 0x28#64) 8 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40)
      (b' := out + 0x08#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x08#64) (n := 1) (k := 39)
      (b' := out + 0x09#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x09#64) (n := 7) (k := 32)
      (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x10#64) (n := 1) (k := 31)
      (b' := out + 0x11#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x11#64) (n := 7) (k := 24)
      (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16)
      (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
      (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_one (out + 0x08#64),
    ProofLib.memRegion_one (out + 0x10#64),
    ProofLib.memRegion_eq_exists_bytes (out + 0x11#64) 7 (by decide),
    ProofLib.memRegion_eight (out + 0x18#64),
    ProofLib.memRegion_eight (out + 0x20#64)]

theorem fold_messageErrorAt (out : BitVec 64) {bs7 : List (BitVec 8)} (hbs7 : bs7.length = 7)
    (w1 w2 : BitVec 64) :
    memRegion out 8 ∗ ((out + 0x08#64) ↦₈ 0xff#8) ∗ memRegion (out + 0x09#64) 7 ∗
      ((out + 0x10#64) ↦₈ 2#8) ∗ ((out + 0x11#64) ↦ₛ bs7) ∗
      ((out + 0x18#64) ↦₆₄ w1) ∗ ((out + 0x20#64) ↦₆₄ w2) ∗ memRegion (out + 0x28#64) 8 ⊢
      messageErrorAt out .msgDecode := by
  have h1 := ChainFromVNNorm.byte_bs7_word_to_pointsTo128 (out + 0x10#64) (spqrErrorTag .msgDecode) hbs7 w1
  simp only [spqrErrorTag, BitVec.add_assoc, BitVec.reduceAdd] at h1
  have hassoc :
      memRegion out 8 ∗ ((out + 0x08#64) ↦₈ 0xff#8) ∗ memRegion (out + 0x09#64) 7 ∗
        ((out + 0x10#64) ↦₈ 2#8) ∗ ((out + 0x11#64) ↦ₛ bs7) ∗
        ((out + 0x18#64) ↦₆₄ w1) ∗ ((out + 0x20#64) ↦₆₄ w2) ∗ memRegion (out + 0x28#64) 8 =
      memRegion out 8 ∗ ((out + 0x08#64) ↦₈ 0xff#8) ∗ memRegion (out + 0x09#64) 7 ∗
        (((out + 0x10#64) ↦₈ 2#8) ∗ ((out + 0x11#64) ↦ₛ bs7) ∗ ((out + 0x18#64) ↦₆₄ w1)) ∗
        ((out + 0x20#64) ↦₆₄ w2) ∗ memRegion (out + 0x28#64) 8 := by ac_rfl
  rw [hassoc]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1)))) ?_
  simp only [messageErrorAt, spqrErrorTag, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro q0
  refine Entails.sepExists_right q0 (Entails.sepExists_right w2 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem fold_messageErrorAt_region (out : BitVec 64) :
    memRegion out 8 ∗ ((out + 0x08#64) ↦₈ 0xff#8) ∗ memRegion (out + 0x09#64) 7 ∗
      ((out + 0x10#64) ↦₈ 2#8) ∗ memRegion (out + 0x11#64) 31 ⊢
      messageErrorAt out .msgDecode := by
  have hm31 : memRegion (out + 0x11#64) 31 =
      (∃∗ bs7 : List (BitVec 8), ⌜bs7.length = 7⌝ ∗ ((out + 0x11#64) ↦ₛ bs7)) ∗
      (∃∗ w1 : BitVec 64, (out + 0x18#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (out + 0x20#64) ↦₆₄ w2) ∗
      memRegion (out + 0x28#64) 8 := by
    rw [ProofLib.memRegion_split' (b := out + 0x11#64) (n := 7) (k := 24)
        (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16)
        (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
        (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eq_exists_bytes (out + 0x11#64) 7 (by decide),
      ProofLib.memRegion_eight (out + 0x18#64),
      ProofLib.memRegion_eight (out + 0x20#64)]
  rw [hm31]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro bs7
  refine Entails.pure_left fun hbs7 => ?_
  exact fold_messageErrorAt out hbs7 w1 w2

theorem memRegion_48_ok_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (out + 0x08#64) ↦₈ b8) ∗
      (∃∗ b9 : BitVec 8, (out + 0x09#64) ↦₈ b9) ∗
      (∃∗ c0 : BitVec 32, (out + 0x0a#64) ↦₃₂ c0) ∗
      (∃∗ c1 : BitVec 16, (out + 0x0e#64) ↦₁₆ c1) ∗
      (∃∗ c2 : BitVec 8, (out + 0x10#64) ↦₈ c2) ∗
      (∃∗ c3 : BitVec 64, (out + 0x11#64) ↦₆₄ c3) ∗
      (∃∗ c4 : BitVec 8, (out + 0x19#64) ↦₈ c4) ∗
      (∃∗ c5 : BitVec 64, (out + 0x1a#64) ↦₆₄ c5) ∗
      (∃∗ c6 : BitVec 64, (out + 0x22#64) ↦₆₄ c6) ∗
      (∃∗ idx16 : BitVec 16, (out + 0x2a#64) ↦₁₆ idx16) ∗
      memRegion (out + 0x2c#64) 4 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40)
      (b' := out + 0x08#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x08#64) (n := 1) (k := 39)
      (b' := out + 0x09#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x09#64) (n := 1) (k := 38)
      (b' := out + 0x0a#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x0a#64) (n := 4) (k := 34)
      (b' := out + 0x0e#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x0e#64) (n := 2) (k := 32)
      (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x10#64) (n := 1) (k := 31)
      (b' := out + 0x11#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x11#64) (n := 8) (k := 23)
      (b' := out + 0x19#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x19#64) (n := 1) (k := 22)
      (b' := out + 0x1a#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x1a#64) (n := 8) (k := 14)
      (b' := out + 0x22#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x22#64) (n := 8) (k := 6)
      (b' := out + 0x2a#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 0x2a#64) (n := 2) (k := 4)
      (b' := out + 0x2c#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 0x08#64),
    ProofLib.memRegion_one (out + 0x09#64),
    ProofLib.memRegion_four (out + 0x0a#64),
    ProofLib.memRegion_two (out + 0x0e#64),
    ProofLib.memRegion_one (out + 0x10#64),
    ProofLib.memRegion_eight (out + 0x11#64),
    ProofLib.memRegion_one (out + 0x19#64),
    ProofLib.memRegion_eight (out + 0x1a#64),
    ProofLib.memRegion_eight (out + 0x22#64),
    ProofLib.memRegion_two (out + 0x2a#64)]

/-- Raw 48-byte layout produced by the shared `Ok` epilogue (`0x5f680..0x5f6c8`). -/
def rawOkOutAt (out epoch : BitVec 64) (tag : BitVec 8)
    (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) (idx16 : BitVec 16) : SepProp :=
  (out ↦₆₄ epoch) ∗
    ((out + 0x08#64) ↦₈ tag) ∗
    ((out + 0x09#64) ↦₈ 1#8) ∗
    chunk32AtomsAt (out + 0x0a#64) c0 c1 c2 c3 c4 c5 c6 ∗
    ((out + 0x2a#64) ↦₁₆ idx16) ∗
    memRegion (out + 0x2c#64) 4

theorem rawOkOutAt_entails_ct1Ack (P : PolyApi) (out epoch : BitVec 64)
    (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) (idx16 : BitVec 16) :
    rawOkOutAt out epoch 4#8 c0 c1 c2 c3 c4 c5 c6 idx16 ⊢
      messageAt P out { epoch := epoch, payload := .ct1Ack true } := by
  unfold rawOkOutAt messageAt messagePayloadAt
  dsimp only [↓reduceIte]
  have hm32 := chunk32AtomsAt_entails_memRegion32 (out + 0x0a#64) c0 c1 c2 c3 c4 c5 c6
  have hm2 : ((out + 0x2a#64) ↦₁₆ idx16) ⊢ memRegion (out + 0x2a#64) 2 := by
    rw [ProofLib.memRegion_two]; exact Entails.sepExists_right idx16 (Entails.refl _)
  have hm38 : memRegion (out + 0x0a#64) 32 ∗ memRegion (out + 0x2a#64) 2 ∗ memRegion (out + 0x2c#64) 4 =
      memRegion (out + 0x0a#64) 38 := by
    rw [← ProofLib.memRegion_split' (b := out + 0x2a#64) (n := 2) (k := 4)
        (b' := out + 0x2c#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x0a#64) (n := 32) (k := 6)
        (b' := out + 0x2a#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  rw [← hm38]
  exact sepConj_mono hm32 (sepConj_mono_left hm2)

theorem rawOkOutAt_entails_none (P : PolyApi) (out epoch : BitVec 64)
    (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) (idx16 : BitVec 16) :
    rawOkOutAt out epoch 0#8 c0 c1 c2 c3 c4 c5 c6 idx16 ⊢
      messageAt P out { epoch := epoch, payload := .none } := by
  unfold rawOkOutAt messageAt messagePayloadAt
  dsimp only []
  have hm1 : ((out + 0x09#64) ↦₈ 1#8) ⊢ memRegion (out + 0x09#64) 1 := by
    rw [ProofLib.memRegion_one]; exact Entails.sepExists_right 1#8 (Entails.refl _)
  have hm32 := chunk32AtomsAt_entails_memRegion32 (out + 0x0a#64) c0 c1 c2 c3 c4 c5 c6
  have hm2 : ((out + 0x2a#64) ↦₁₆ idx16) ⊢ memRegion (out + 0x2a#64) 2 := by
    rw [ProofLib.memRegion_two]; exact Entails.sepExists_right idx16 (Entails.refl _)
  have hm39 : memRegion (out + 0x09#64) 1 ∗ memRegion (out + 0x0a#64) 32 ∗
      memRegion (out + 0x2a#64) 2 ∗ memRegion (out + 0x2c#64) 4 =
      memRegion (out + 0x09#64) 39 := by
    rw [← ProofLib.memRegion_split' (b := out + 0x2a#64) (n := 2) (k := 4)
        (b' := out + 0x2c#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x0a#64) (n := 32) (k := 6)
        (b' := out + 0x2a#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x09#64) (n := 1) (k := 38)
        (b' := out + 0x0a#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [← hm39]
  exact sepConj_mono hm1 (sepConj_mono hm32 (sepConj_mono_left hm2))

theorem rawOkOutAt_entails_chunk (P : PolyApi) (out epoch : BitVec 64) (tag : BitVec 8)
    (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) (idx16 : BitVec 16)
    (c : P.Chunk)
    (hIdx : P.chunkIndex c = idx16)
    (hData : (P.chunkData c).toList = chunk32Bytes c0 c1 c2 c3 c4 c5 c6) :
    rawOkOutAt out epoch tag c0 c1 c2 c3 c4 c5 c6 idx16 ⊢
      (out ↦₆₄ epoch) ∗ ((out + 0x08#64) ↦₈ tag) ∗ memRegion (out + 0x09#64) 1 ∗
        chunkAt (out + 0x0a#64) { index := P.chunkIndex c, data := P.chunkData c } ∗
        memRegion (out + 0x2c#64) 4 := by
  unfold rawOkOutAt chunkAt chunkIndexOff
  simp only [hIdx, hData, pointsToBytes_chunk32Bytes_eq, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hm1 : ((out + 0x09#64) ↦₈ 1#8) ⊢ memRegion (out + 0x09#64) 1 := by
    rw [ProofLib.memRegion_one]; exact Entails.sepExists_right 1#8 (Entails.refl _)
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm1))

/-- Untouched stack regions in `<Message>::deserialize`'s `144`-byte frame plus `extHookStack`. -/
def msgDeserFramePad (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 144#64) 8 ∗
    memRegion (sp0 - 127#64) 7 ∗
    memRegion (sp0 - 87#64) 11 ∗
    memRegion (sp0 - 70#64) 2 ∗
    memRegion (sp0 - 67#64) 3 ∗
    stackAt (sp0 - 144#64) extHookStack

/-- Scratch cells in `<Message>::deserialize`'s `144`-byte frame. -/
def msgDeserScratchAt (sp0 : BitVec 64) (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8)
    (st5 st6 : BitVec 64) (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8)
    (f50 f58 : BitVec 64) : SepProp :=
  ((sp0 - 136#64) ↦₆₄ f08) ∗
    ((sp0 - 128#64) ↦₈ f10) ∗
    ((sp0 - 120#64) ↦₆₄ f18) ∗
    ((sp0 - 112#64) ↦₆₄ st3) ∗ ((sp0 - 104#64) ↦₈ st4) ∗
    ((sp0 - 103#64) ↦₆₄ st5) ∗ ((sp0 - 95#64) ↦₆₄ st6) ∗
    ((sp0 - 76#64) ↦₃₂ st0) ∗ ((sp0 - 72#64) ↦₁₆ st1) ∗
    ((sp0 - 68#64) ↦₈ fb0) ∗
    ((sp0 - 64#64) ↦₆₄ f50) ∗ ((sp0 - 56#64) ↦₆₄ f58)

/-- Callee-saved register save slots `[sp0 - 48, sp0)`. -/
def msgDeserSavedAt (sp0 s29 s30 s22 s21 s20 s19 : BitVec 64) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s29) ∗ ((sp0 - 40#64) ↦₆₄ s30) ∗
    ((sp0 - 32#64) ↦₆₄ s22) ∗ ((sp0 - 24#64) ↦₆₄ s21) ∗
    ((sp0 - 16#64) ↦₆₄ s20) ∗ ((sp0 - 8#64) ↦₆₄ s19)

theorem stackAt_msgDeser_split (sp0 : BitVec 64) :
    stackAt sp0 messageDeserializeStackX =
      msgDeserFramePad sp0 ∗
      (∃∗ s19 : BitVec 64, ∃∗ s20 : BitVec 64, ∃∗ s21 : BitVec 64,
       ∃∗ s22 : BitVec 64, ∃∗ s30 : BitVec 64, ∃∗ s29 : BitVec 64,
       ∃∗ f58 : BitVec 64, ∃∗ f50 : BitVec 64, ∃∗ fb0 : BitVec 8,
       ∃∗ st1 : BitVec 16, ∃∗ st0 : BitVec 32, ∃∗ st6 : BitVec 64,
       ∃∗ st5 : BitVec 64, ∃∗ st4 : BitVec 8, ∃∗ st3 : BitVec 64,
       ∃∗ f18 : BitVec 64, ∃∗ f10 : BitVec 8, ∃∗ f08 : BitVec 64,
        msgDeserScratchAt sp0 f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
        msgDeserSavedAt sp0 s29 s30 s22 s21 s20 s19) := by
  have h1 : stackAt sp0 messageDeserializeStackX =
      stackAt (sp0 - 144#64) extHookStack ∗ memRegion (sp0 - 144#64) 144 := by
    unfold stackAt messageDeserializeStackX
    have hbase : sp0 - 144#64 = sp0 - BitVec.ofNat 64 (0x90 + extHookStack) + BitVec.ofNat 64 extHookStack := by
      change sp0 - 144#64 = sp0 - 16528#64 + 16384#64; bv_omega
    have hsub : sp0 - 144#64 - BitVec.ofNat 64 extHookStack = sp0 - BitVec.ofNat 64 (0x90 + extHookStack) := by
      change sp0 - 144#64 - 16384#64 = sp0 - 16528#64; bv_omega
    rw [hsub]
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 (0x90 + extHookStack))
      (n := extHookStack) (k := 144) (b' := sp0 - 144#64) rfl hbase (by decide)
  rw [h1]
  rw [ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 8) (k := 136)
      (b' := sp0 - 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 136#64) (n := 8) (k := 128)
      (b' := sp0 - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 128#64) (n := 1) (k := 127)
      (b' := sp0 - 127#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 127#64) (n := 7) (k := 120)
      (b' := sp0 - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 120#64) (n := 8) (k := 112)
      (b' := sp0 - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 112#64) (n := 8) (k := 104)
      (b' := sp0 - 104#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 104#64) (n := 1) (k := 103)
      (b' := sp0 - 103#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 103#64) (n := 8) (k := 95)
      (b' := sp0 - 95#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 95#64) (n := 8) (k := 87)
      (b' := sp0 - 87#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 87#64) (n := 11) (k := 76)
      (b' := sp0 - 76#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 76#64) (n := 4) (k := 72)
      (b' := sp0 - 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 72#64) (n := 2) (k := 70)
      (b' := sp0 - 70#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 70#64) (n := 2) (k := 68)
      (b' := sp0 - 68#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 68#64) (n := 1) (k := 67)
      (b' := sp0 - 67#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 67#64) (n := 3) (k := 64)
      (b' := sp0 - 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 64#64) (n := 8) (k := 56)
      (b' := sp0 - 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 56#64) (n := 8) (k := 48)
      (b' := sp0 - 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 48#64) (n := 8) (k := 40)
      (b' := sp0 - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 40#64) (n := 8) (k := 32)
      (b' := sp0 - 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 32#64) (n := 8) (k := 24)
      (b' := sp0 - 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 24#64) (n := 8) (k := 16)
      (b' := sp0 - 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 16#64) (n := 8) (k := 8)
      (b' := sp0 - 8#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight (sp0 - 136#64),
    ProofLib.memRegion_one (sp0 - 128#64),
    ProofLib.memRegion_eight (sp0 - 120#64),
    ProofLib.memRegion_eight (sp0 - 112#64),
    ProofLib.memRegion_one (sp0 - 104#64),
    ProofLib.memRegion_eight (sp0 - 103#64),
    ProofLib.memRegion_eight (sp0 - 95#64),
    ProofLib.memRegion_four (sp0 - 76#64),
    ProofLib.memRegion_two (sp0 - 72#64),
    ProofLib.memRegion_one (sp0 - 68#64),
    ProofLib.memRegion_eight (sp0 - 64#64),
    ProofLib.memRegion_eight (sp0 - 56#64),
    ProofLib.memRegion_eight (sp0 - 48#64),
    ProofLib.memRegion_eight (sp0 - 40#64),
    ProofLib.memRegion_eight (sp0 - 32#64),
    ProofLib.memRegion_eight (sp0 - 24#64),
    ProofLib.memRegion_eight (sp0 - 16#64),
    ProofLib.memRegion_eight (sp0 - 8#64)]
  unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt stackAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  ac_rfl

theorem msgDeser_stack_restore (sp0 : BitVec 64) (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8)
    (st5 st6 : BitVec 64) (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8)
    (f50 f58 s29 s30 s22 s21 s20 s19 : BitVec 64) :
    msgDeserFramePad sp0 ∗
      msgDeserScratchAt sp0 f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt sp0 s29 s30 s22 s21 s20 s19 ⊢
      stackAt sp0 messageDeserializeStackX := by
  rw [stackAt_msgDeser_split sp0]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right s19 (Entails.sepExists_right s20 (Entails.sepExists_right s21
    (Entails.sepExists_right s22 (Entails.sepExists_right s30 (Entails.sepExists_right s29
    (Entails.sepExists_right f58 (Entails.sepExists_right f50 (Entails.sepExists_right fb0
    (Entails.sepExists_right st1 (Entails.sepExists_right st0 (Entails.sepExists_right st6
    (Entails.sepExists_right st5 (Entails.sepExists_right st4 (Entails.sepExists_right st3
    (Entails.sepExists_right f18 (Entails.sepExists_right f10
    (Entails.sepExists_right f08 (Entails.refl _))))))))))))))))))

theorem msgDeser_fmt_slot_fold (sp0 : BitVec 64) (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64) :
    ((sp0 - 136#64) ↦₆₄ f08) ∗ ((sp0 - 128#64) ↦₈ f10) ∗
      memRegion (sp0 - 127#64) 7 ∗ ((sp0 - 120#64) ↦₆₄ f18) ⊢
      memRegion (sp0 - 136#64) 24 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 136#64) (n := 8) (k := 16)
      (b' := sp0 - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 128#64) (n := 1) (k := 15)
      (b' := sp0 - 127#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 127#64) (n := 7) (k := 8)
      (b' := sp0 - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp0 - 136#64),
    ProofLib.memRegion_one (sp0 - 128#64),
    ProofLib.memRegion_eight (sp0 - 120#64)]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    ((sp0 - 136#64) ↦₆₄ f08) ∗ ((sp0 - 128#64) ↦₈ f10) ∗
      memRegion (sp0 - 127#64) 7 ∗ ((sp0 - 120#64) ↦₆₄ f18) =
    ((sp0 - 136#64) ↦₆₄ f08) ∗ ((sp0 - 128#64) ↦₈ f10) ∗
      memRegion (sp0 - 127#64) 7 ∗ ((sp0 - 120#64) ↦₆₄ f18))) ?_
  exact sepConj_mono (Entails.sepExists_right f08 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right f10 (Entails.refl _))
      (sepConj_mono_right (Entails.sepExists_right f18 (Entails.refl _))))

theorem pointsTo64_entails_byte_memRegion7 (sp0 : BitVec 64) (w : BitVec 64) :
    ((sp0 - 128#64) ↦₆₄ w) ⊢ ((sp0 - 128#64) ↦₈ w.extractLsb' 0 8) ∗ memRegion (sp0 - 127#64) 7 := by
  have hlen : ((unpack64 w).drop 1).length = 7 := by simp [unpack64]
  have hadd : sp0 - 128#64 + 1#64 = sp0 - 127#64 := by bv_omega
  rw [pointsTo64_eq_pointsToBytes,
    show unpack64 w = w.extractLsb' 0 8 :: (unpack64 w).drop 1 by rfl,
    pointsToBytes_cons, hadd]
  exact sepConj_mono_right (by rw [← hlen]; exact pointsToBytes_entails_memRegion _ _)

/-! ## 4. Pure `deserAfterVarint` Helpers -/

open CryptoVerification.LibsignalSpqr

/-- Construct the chunked `Message P` for `tag ∈ {1#8, 2#8, 3#8, 5#8, 6#8}`. -/
def mkChunkMsg (P : PolyApi) (epoch : Epoch) (tag : BitVec 8) (c : P.Chunk) : Message P :=
  if tag = 1#8 then { epoch := epoch, payload := .hdr c }
  else if tag = 2#8 then { epoch := epoch, payload := .ek c }
  else if tag = 3#8 then { epoch := epoch, payload := .ekCt1Ack c }
  else if tag = 5#8 then { epoch := epoch, payload := .ct1 c }
  else { epoch := epoch, payload := .ct2 c }

/-- Law that `P.chunkIndex` and `P.chunkData` are projections of `P.mkChunk` (satisfied
    definitionally by `spqrPolyApi`). -/
def PolyApiChunkLaw (P : PolyApi) : Prop :=
  ∀ (idx : BitVec 16) (d : List.Vector (BitVec 8) 32),
    P.chunkIndex (P.mkChunk idx d) = idx ∧ P.chunkData (P.mkChunk idx d) = d

/-- Continuation of `Message.deserialize` after decoding the `index` varint for a chunk message
    tag. -/
def deserAfterVarint (P : PolyApi) (epoch : Epoch) (tag : BitVec 8)
    (res : Option (BitVec 64 × List (BitVec 8))) : Except Error (Message P) :=
  match res with
  | none => .error .msgDecode
  | some (index, rest2) =>
    if h1 : rest2.length < 32 then .error .msgDecode
    else if index.toNat > 65535 then .error .msgDecode
    else
      have hlen : (rest2.take 32).length = 32 := by
        rw [List.length_take]; omega
      .ok (mkChunkMsg P epoch tag (P.mkChunk (index.truncate 16) ⟨rest2.take 32, hlen⟩))

theorem deserialize_eq_deserAfterVarint (P : PolyApi) (epoch : Epoch) (tag : BitVec 8)
    (rest : List (BitVec 8))
    (htag : tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8) :
    Message.deserialize P epoch (tag :: rest) =
      deserAfterVarint P epoch tag (spqrDecodeVarint rest) := by
  have hw := decode_varint_eq_spqrDecodeVarint rest
  rcases htag with rfl | rfl | rfl | rfl | rfl <;> {
    unfold Message.deserialize MessageType.tryFromU8 decode_chunk deserAfterVarint mkChunkMsg
    dsimp only [↓reduceIte, beq_self_eq_true, Bool.true_or, Bool.false_or]
    rw [hw]
    cases spqrDecodeVarint rest with
    | none => rfl
    | some p =>
      rcases p with ⟨index, rest2⟩
      dsimp only [Bind.bind, Except.bind]
      by_cases h1 : rest2.length < 32
      · simp [h1]
      · simp only [h1, decide_false, Bool.false_or, ↓reduceDIte]
        by_cases h2 : index.toNat > 65535
        · simp [h2]
        · have hlen : (rest2.take 32).length = 32 := by rw [List.length_take]; omega
          simp only [h2, decide_false, ↓reduceIte]
          change (match (if h : (rest2.take 32).length = 32 then some ⟨rest2.take 32, h⟩ else none) with
            | some dataVec => Except.ok (P.mkChunk (BitVec.setWidth 16 index) dataVec, List.drop 32 rest2)
            | none => Except.error Error.msgDecode) >>= _ = _
          simp only [hlen, ↓reduceDIte]
          rfl
  }

theorem rawOkOutAt_entails_mkChunkMsg (P : PolyApi) (hP : PolyApiChunkLaw P)
    (out : BitVec 64) (epoch : Epoch)
    (tag : BitVec 8) (idx16 : BitVec 16)
    (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64)
    (d : List.Vector (BitVec 8) 32)
    (hd : d.toList = chunk32Bytes c0 c1 c2 c3 c4 c5 c6)
    (htag : tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8) :
    rawOkOutAt out epoch tag c0 c1 c2 c3 c4 c5 c6 idx16 ⊢
      messageResultAt P out (.ok (mkChunkMsg P epoch tag (P.mkChunk idx16 d))) := by
  obtain ⟨hIdx, hData⟩ := hP idx16 d
  have hData' : (P.chunkData (P.mkChunk idx16 d)).toList = chunk32Bytes c0 c1 c2 c3 c4 c5 c6 := by
    rw [hData, hd]
  rcases htag with rfl | rfl | rfl | rfl | rfl <;> {
    dsimp only [messageResultAt, messageAt, messagePayloadAt, mkChunkMsg, ↓reduceIte]
    exact rawOkOutAt_entails_chunk P out epoch _ c0 c1 c2 c3 c4 c5 c6 idx16
      (P.mkChunk idx16 d) hIdx hData'
  }

/-- Remainder of `fromPtr ↦ₛ fromBytes` when `b` at `fromPtr + pre.length` is focused. -/
def fromByteFrame (fromPtr : BitVec 64) (pre post : List (BitVec 8)) : SepProp :=
  (fromPtr ↦ₛ pre) ∗ ((fromPtr + BitVec.ofNat 64 pre.length + 1#64) ↦ₛ post)

theorem fromBytes_expose_byte (fromPtr : BitVec 64) (fromBytes pre post : List (BitVec 8))
    (b : BitVec 8) (addr : BitVec 64)
    (hsplit : fromBytes = pre ++ b :: post)
    (haddr : addr = fromPtr + BitVec.ofNat 64 pre.length) :
    (fromPtr ↦ₛ fromBytes) ⊢ (addr ↦₈ b) ∗ fromByteFrame fromPtr pre post := by
  unfold fromByteFrame
  rw [hsplit, pointsToBytes_append, pointsToBytes_cons, ← haddr]
  exact Entails.of_eq (by ac_rfl)

theorem fromBytes_unexpose_byte (fromPtr : BitVec 64) (fromBytes pre post : List (BitVec 8))
    (b : BitVec 8) (addr : BitVec 64)
    (hsplit : fromBytes = pre ++ b :: post)
    (haddr : addr = fromPtr + BitVec.ofNat 64 pre.length) :
    ((addr ↦₈ b) ∗ fromByteFrame fromPtr pre post) ⊢ (fromPtr ↦ₛ fromBytes) := by
  unfold fromByteFrame
  rw [hsplit, pointsToBytes_append, pointsToBytes_cons, ← haddr]
  exact Entails.of_eq (by ac_rfl)

/-- Remainder of `fromPtr ↦ₛ fromBytes` when the 32-byte chunk payload is focused. -/
def fromChunk32Frame (fromPtr : BitVec 64) (tag : BitVec 8) (pre₁ rest2 : List (BitVec 8)) : SepProp :=
  (fromPtr ↦ₛ (tag :: pre₁)) ∗
    ((fromPtr + BitVec.ofNat 64 (tag :: pre₁).length + 32#64) ↦ₛ rest2.drop 32)

/-- 7-atom decomposition of 32 bytes at `x10 + 2#64`, written with offsets directly from `x10`
    (`+2, +6, +8, +9, +17, +18, +26`) matching `0x5f65c..0x5f66c`. -/
def chunk32AtX10 (x10 : BitVec 64) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) : SepProp :=
  ((x10 + 2#64) ↦₃₂ c0) ∗ ((x10 + 6#64) ↦₁₆ c1) ∗ ((x10 + 8#64) ↦₈ c2) ∗
    ((x10 + 9#64) ↦₆₄ c3) ∗ ((x10 + 17#64) ↦₈ c4) ∗
    ((x10 + 18#64) ↦₆₄ c5) ∗ ((x10 + 26#64) ↦₆₄ c6)

theorem chunk32AtomsAt_eq_chunk32AtX10 (x10 : BitVec 64) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64) :
    chunk32AtomsAt (x10 + 2#64) c0 c1 c2 c3 c4 c5 c6 =
      chunk32AtX10 x10 c0 c1 c2 c3 c4 c5 c6 := by
  unfold chunk32AtomsAt chunk32AtX10
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem fromBytes_expose_chunk32 (fromPtr : BitVec 64) (fromBytes pre₁ rest2 : List (BitVec 8))
    (tag : BitVec 8) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64)
    (hsplit : fromBytes = (tag :: pre₁) ++ rest2)
    (htake : rest2.take 32 = chunk32Bytes c0 c1 c2 c3 c4 c5 c6) :
    (fromPtr ↦ₛ fromBytes) ⊢
      chunk32AtX10 (fromPtr + (BitVec.ofNat 64 pre₁.length - 1#64)) c0 c1 c2 c3 c4 c5 c6 ∗
      fromChunk32Frame fromPtr tag pre₁ rest2 := by
  unfold fromChunk32Frame
  have hrest2 : rest2 = chunk32Bytes c0 c1 c2 c3 c4 c5 c6 ++ rest2.drop 32 := by
    rw [← htake, List.take_append_drop]
  have haddr : fromPtr + BitVec.ofNat 64 (tag :: pre₁).length =
      fromPtr + (BitVec.ofNat 64 pre₁.length - 1#64) + 2#64 := by
    simp only [List.length_cons]; bv_omega
  rw [hsplit, pointsToBytes_append, hrest2, pointsToBytes_append, chunk32Bytes_length,
    pointsToBytes_chunk32Bytes_eq, haddr, chunk32AtomsAt_eq_chunk32AtX10, ← haddr]
  exact Entails.of_eq (by ac_rfl)

theorem fromBytes_unexpose_chunk32 (fromPtr : BitVec 64) (fromBytes pre₁ rest2 : List (BitVec 8))
    (tag : BitVec 8) (c0 : BitVec 32) (c1 : BitVec 16) (c2 : BitVec 8)
    (c3 : BitVec 64) (c4 : BitVec 8) (c5 c6 : BitVec 64)
    (hsplit : fromBytes = (tag :: pre₁) ++ rest2)
    (htake : rest2.take 32 = chunk32Bytes c0 c1 c2 c3 c4 c5 c6) :
    (chunk32AtX10 (fromPtr + (BitVec.ofNat 64 pre₁.length - 1#64)) c0 c1 c2 c3 c4 c5 c6 ∗
      fromChunk32Frame fromPtr tag pre₁ rest2) ⊢
      (fromPtr ↦ₛ fromBytes) := by
  unfold fromChunk32Frame
  have hrest2 : rest2 = chunk32Bytes c0 c1 c2 c3 c4 c5 c6 ++ rest2.drop 32 := by
    rw [← htake, List.take_append_drop]
  have haddr : fromPtr + BitVec.ofNat 64 (tag :: pre₁).length =
      fromPtr + (BitVec.ofNat 64 pre₁.length - 1#64) + 2#64 := by
    simp only [List.length_cons]; bv_omega
  rw [hsplit, pointsToBytes_append, hrest2, pointsToBytes_append, chunk32Bytes_length,
    pointsToBytes_chunk32Bytes_eq, haddr, chunk32AtomsAt_eq_chunk32AtX10, ← haddr]
  exact Entails.of_eq (by ac_rfl)

def rawOutBufAt (out : BitVec 64) (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64)
    (o2a : BitVec 16) : SepProp :=
  (out ↦₆₄ o0) ∗
    ((out + 0x08#64) ↦₈ o8) ∗
    ((out + 0x09#64) ↦₈ o9) ∗
    chunk32AtomsAt (out + 0x0a#64) oc0 oc1 oc2 oc3 oc4 oc5 oc6 ∗
    ((out + 0x2a#64) ↦₁₆ o2a) ∗
    memRegion (out + 0x2c#64) 4

theorem rawOutBufAt_entails_err_split (out : BitVec 64) (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64)
    (o2a : BitVec 16) :
    rawOutBufAt out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ⊢
      memRegion out 8 ∗
      ((out + 0x08#64) ↦₈ o8) ∗
      memRegion (out + 0x09#64) 7 ∗
      ((out + 0x10#64) ↦₈ oc2) ∗
      memRegion (out + 0x11#64) 31 := by
  have hm0 : (out ↦₆₄ o0) ⊢ memRegion out 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right o0 (Entails.refl _)
  have hm9 : ((out + 0x09#64) ↦₈ o9) ∗ ((out + 0x0a#64) ↦₃₂ oc0) ∗ ((out + 0x0e#64) ↦₁₆ oc1) ⊢
      memRegion (out + 0x09#64) 7 := by
    rw [ProofLib.memRegion_split' (b := out + 0x09#64) (n := 1) (k := 6)
        (b' := out + 0x0a#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x0a#64) (n := 4) (k := 2)
        (b' := out + 0x0e#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (out + 0x09#64),
      ProofLib.memRegion_four (out + 0x0a#64),
      ProofLib.memRegion_two (out + 0x0e#64)]
    exact sepConj_mono (Entails.sepExists_right o9 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right oc0 (Entails.refl _))
        (Entails.sepExists_right oc1 (Entails.refl _)))
  have hm11 : ((out + 0x11#64) ↦₆₄ oc3) ∗ ((out + 0x19#64) ↦₈ oc4) ∗
      ((out + 0x1a#64) ↦₆₄ oc5) ∗ ((out + 0x22#64) ↦₆₄ oc6) ∗
      ((out + 0x2a#64) ↦₁₆ o2a) ∗ memRegion (out + 0x2c#64) 4 ⊢
      memRegion (out + 0x11#64) 31 := by
    rw [ProofLib.memRegion_split' (b := out + 0x11#64) (n := 8) (k := 23)
        (b' := out + 0x19#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x19#64) (n := 1) (k := 22)
        (b' := out + 0x1a#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x1a#64) (n := 8) (k := 14)
        (b' := out + 0x22#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x22#64) (n := 8) (k := 6)
        (b' := out + 0x2a#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x2a#64) (n := 2) (k := 4)
        (b' := out + 0x2c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 0x11#64),
      ProofLib.memRegion_one (out + 0x19#64),
      ProofLib.memRegion_eight (out + 0x1a#64),
      ProofLib.memRegion_eight (out + 0x22#64),
      ProofLib.memRegion_two (out + 0x2a#64)]
    exact sepConj_mono (Entails.sepExists_right oc3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right oc4 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right oc5 (Entails.refl _))
          (sepConj_mono (Entails.sepExists_right oc6 (Entails.refl _))
            (sepConj_mono_left (Entails.sepExists_right o2a (Entails.refl _))))))
  unfold rawOutBufAt chunk32AtomsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₈ o8) ∗ ((out + 9#64) ↦₈ o9) ∗
      (((out + 10#64) ↦₃₂ oc0) ∗ ((out + 14#64) ↦₁₆ oc1) ∗ ((out + 16#64) ↦₈ oc2) ∗
        ((out + 17#64) ↦₆₄ oc3) ∗ ((out + 25#64) ↦₈ oc4) ∗
        ((out + 26#64) ↦₆₄ oc5) ∗ ((out + 34#64) ↦₆₄ oc6)) ∗
      ((out + 42#64) ↦₁₆ o2a) ∗ memRegion (out + 44#64) 4 =
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₈ o8) ∗
      (((out + 9#64) ↦₈ o9) ∗ ((out + 10#64) ↦₃₂ oc0) ∗ ((out + 14#64) ↦₁₆ oc1)) ∗
      ((out + 16#64) ↦₈ oc2) ∗
      (((out + 17#64) ↦₆₄ oc3) ∗ ((out + 25#64) ↦₈ oc4) ∗
        ((out + 26#64) ↦₆₄ oc5) ∗ ((out + 34#64) ↦₆₄ oc6) ∗
        ((out + 42#64) ↦₁₆ o2a) ∗ memRegion (out + 44#64) 4))) ?_
  exact sepConj_mono hm0 (sepConj_mono_right (sepConj_mono hm9 (sepConj_mono_right hm11)))

end CryptoVerification.SpqrV1.Top.MessageDeserialize
