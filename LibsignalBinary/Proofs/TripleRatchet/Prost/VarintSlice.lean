/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::varint::decode_varint_slice`

Proves that `prost::encoding::varint::decode_varint_slice` (`0x23008`) satisfies
`decodeVarintSliceSpec` and `decodeVarintSliceSpecX`, both in-image and under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Call-site lemma for the in-image `<DecodeError as From<DecodeErrorKind>>::from` -/

theorem decodeErrorFrom_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hFrom : AllocHooks A abs)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = libsignalSessionCode.fnOff decodeErrorFromName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (decodeErrorFromSpec A) := by
  have h := LibsignalTripleRatchet.decodeErrorFrom_ok b C A ctl abs hFrom
  rwa [← Program.fnAddr_rel rfl rfl (hfn ▸ hk)]

theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

/-! ## Memory and stack layout lemmas -/

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r2) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r0) := by
  have s1 := memRegion_split a 8 16 (by decide)
  change memRegion a 24 = memRegion a 8 ∗ memRegion (a + 8#64) 16 at s1
  have s2 := memRegion_split (a + 8#64) 8 8 (by decide)
  change memRegion (a + 8#64) 16 = memRegion (a + 8#64) 8 ∗ memRegion (a + 8#64 + 8#64) 8 at s2
  rw [BitVec.add_assoc, show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl] at s2
  rw [s1, s2, memRegion_eight a, memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_48_split (a : BitVec 64) :
    memRegion a 48 = (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ memRegion (a + 8#64) 40 := by
  rw [← memRegion_eight, ← memRegion_split a 8 40 (by decide)]

theorem stackAt_decodeVarintSliceGen {errStack : Nat} (herr : 0x50 + errStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (0x50 + errStack) =
      stackAt (sp - 80#64) errStack ∗
        memRegion (sp - 80#64) 8 ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 72#64) ↦₆₄ v9) ∗ ((sp - 64#64) ↦₆₄ v8) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp errStack 10 (by omega)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 10)) 10 (by decide)] at h0
  rw [show 0x50 + errStack = errStack + 8 * 10 by omega, h0]
  change stackAt (sp - 80#64) errStack ∗ memRegion (sp - 80#64) 80 = _
  have s1 := memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s1
  have s2 := memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s2
  have s3 := memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s3
  have s4 := memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s4
  have s5 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s5
  rw [s1, s2, s3, s4, s5,
    memRegion_eight (sp - 72#64), memRegion_eight (sp - 64#64),
    memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem stackAt_decodeVarintSlice (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStack =
      stackAt (sp - 80#64) decodeErrorHookStack ∗
        memRegion (sp - 80#64) 8 ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 72#64) ↦₆₄ v9) ∗ ((sp - 64#64) ↦₆₄ v8) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) :=
  stackAt_decodeVarintSliceGen (by decide) sp

/-! ## Precondition and list helpers -/

theorem eq_ofNat_of_toNat_eq {w : BitVec 64} {n : Nat} (h : w.toNat = n) :
    w = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem toNat_le_0x7f_iff (b : BitVec 8) : b.toNat ≤ 0x7F ↔ b ≤ 0x7f#8 := Iff.rfl

theorem two_le_toNat_iff (b : BitVec 8) : 2 ≤ b.toNat ↔ 2#8 ≤ b := Iff.rfl

theorem ne_nil_of_all_gt {pre rest : List (BitVec 8)}
    (hpre : VarintSlicePre (pre ++ rest))
    (hlen : pre.length ≤ 9)
    (hall : ∀ b ∈ pre, ¬ b ≤ 0x7f#8) :
    rest ≠ [] := by
  rintro rfl
  rw [List.append_nil] at hpre
  rcases hpre with h11 | ⟨hne, hlast⟩
  · omega
  · exact hall (pre.getLast hne) (List.getLast_mem hne) hlast

theorem exists_cons_of_all_gt {pre rest : List (BitVec 8)}
    (hpre : VarintSlicePre (pre ++ rest))
    (hlen : pre.length ≤ 9)
    (hall : ∀ b ∈ pre, ¬ b ≤ 0x7f#8) :
    ∃ b rest', rest = b :: rest' :=
  List.exists_cons_of_ne_nil (ne_nil_of_all_gt hpre hlen hall)

theorem pointsToBytes_split_last (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hsmall : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.dropLast) ∗
      ((ptr + BitVec.ofNat 64 bs.length - 1#64) ↦₈ bs.getLast hne) :=
  let _ := hsmall; ProofLib.pointsToBytes_split_last ptr bs hne

theorem ule_11_of_ge {n : Nat} (h11 : 11 ≤ n) (hlt : n < 2 ^ 63) :
    (11#64).ule (BitVec.ofNat 64 n) = true := by
  rw [BitVec.ule_iff_le, BitVec.le_def, BitVec.toNat_ofNat]
  change 11 ≤ n % 2 ^ 64
  omega

theorem ule_11_of_lt {n : Nat} (h11 : ¬ 11 ≤ n) (_hlt : n < 2 ^ 63) :
    (11#64).ule (BitVec.ofNat 64 n) = false := by
  rw [Bool.eq_false_iff, ne_eq, BitVec.ule_iff_le, BitVec.le_def, BitVec.toNat_ofNat]
  change ¬ 11 ≤ n % 2 ^ 64
  omega

theorem signExtend64_getLsbD_63_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.signExtend 64).getLsbD 63 = false := by bv_bits

theorem signExtend64_getLsbD_63_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.signExtend 64).getLsbD 63 = true := by bv_bits

theorem getLsbD_7_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    b.getLsbD 7 = false := by bv_bits

theorem getLsbD_7_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    b.getLsbD 7 = true := by bv_bits

/-! ## Checked-arithmetic no-overflow lemmas -/

abbrev part0_2 (b0 b1 : BitVec 8) : BitVec 32 :=
  BitVec.truncate 32 (BitVec.zeroExtend 64 b1 <<< 7) +
    BitVec.zeroExtend 32 (BitVec.truncate 8 (BitVec.signExtend 64 b0)) - 128#32

abbrev part0_3 (b0 b1 b2 : BitVec 8) : BitVec 32 :=
  part0_2 b0 b1 + BitVec.zeroExtend 32 b2 <<< 14 - 16384#32

abbrev part0_4 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  part0_3 b0 b1 b2 + BitVec.zeroExtend 32 b3 <<< 21 - 2097152#32

abbrev part1_2 (b4 b5 : BitVec 8) : BitVec 32 :=
  BitVec.zeroExtend 32 b4 + BitVec.zeroExtend 32 b5 <<< 7 - 128#32

abbrev part1_3 (b4 b5 b6 : BitVec 8) : BitVec 32 :=
  part1_2 b4 b5 + BitVec.zeroExtend 32 b6 <<< 14 - 16384#32

abbrev part1_4 (b4 b5 b6 b7 : BitVec 8) : BitVec 32 :=
  part1_3 b4 b5 b6 + BitVec.zeroExtend 32 b7 <<< 21 - 2097152#32

theorem ovf_byte2 {b0 b1 : BitVec 8} (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) :
    (part0_2 b0 b1).ult 16384#32 = false := by
  dsimp [part0_2]; bv_bits

theorem ovf_byte3 {b0 b1 b2 : BitVec 8} (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8)
    (hb2 : ¬ b2 ≤ 0x7f#8) :
    (part0_3 b0 b1 b2).ult 2097152#32 = false := by
  dsimp [part0_3, part0_2]; bv_bits

theorem ovf_byte4 {b0 b1 b2 b3 : BitVec 8} (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8)
    (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 >>> 28)) == 0#32) = false ∧
    (part0_4 b0 b1 b2 b3 >>> 28 == 0#32) = false := by
  dsimp [part0_4, part0_3, part0_2]; refine ⟨by bv_bits, by bv_bits⟩

theorem ovf_byte6 {b4 b5 : BitVec 8} (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) :
    (part1_2 b4 b5).ult 16384#32 = false := by
  dsimp [part1_2]; bv_bits

theorem ovf_byte7 {b4 b5 b6 : BitVec 8} (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) :
    (part1_3 b4 b5 b6).ult 2097152#32 = false := by
  dsimp [part1_3, part1_2]; bv_bits

theorem ovf_byte8 {b4 b5 b6 b7 : BitVec 8} (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 >>> 28)) == 0#32) = false ∧
    (part1_4 b4 b5 b6 b7 >>> 28 == 0#32) = false := by
  dsimp [part1_4, part1_3, part1_2]; refine ⟨by bv_bits, by bv_bits⟩

namespace VarintSliceBits

theorem signExtend64_getLsbD_63_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    ((b.signExtend 64).getLsbD 63 == true) = false := by
  rw [signExtend64_getLsbD_63_of_le h]; rfl

theorem signExtend64_getLsbD_63_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    ((b.signExtend 64).getLsbD 63 == true) = true := by
  rw [signExtend64_getLsbD_63_of_gt h]; rfl

theorem getLsbD_7_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.getLsbD 7 == true) = false := by
  rw [getLsbD_7_of_le h]; rfl

theorem getLsbD_7_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.getLsbD 7 == true) = true := by
  rw [getLsbD_7_of_gt h]; rfl

theorem ovf_byte4_zext {b0 b1 b2 b3 : BitVec 8} (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8)
    (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3) >>> 28)) == 0#64) = false := by
  dsimp [part0_4, part0_3, part0_2]; bv_bits

theorem ovf_byte8_zext {b4 b5 b6 b7 : BitVec 8} (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7) >>> 28)) == 0#64) = false := by
  dsimp [part1_4, part1_3, part1_2]; bv_bits

end VarintSliceBits

theorem byte9_ule_of_ge {b9 : BitVec 8} (hb9 : 2#8 ≤ b9) :
    (2#64).ule (b9.zeroExtend 64) = true := by bv_bits

theorem byte9_ule_of_lt {b9 : BitVec 8} (hb9 : ¬ 2#8 ≤ b9) :
    (2#64).ule (b9.zeroExtend 64) = false := by bv_bits

private theorem or_eq_add_of_toNat_lt_dvd {x z : BitVec 64} (k : Nat)
    (hx : x.toNat < 2 ^ k) (hz : z.toNat % 2 ^ k = 0) :
    x ||| z = x + z := by
  apply BitVec.eq_of_toNat_eq
  have hor : (x ||| z).toNat = x.toNat + z.toNat := by
    rw [BitVec.toNat_or]
    exact ProofLib.BV.Bits.NatLemmas.or_eq_add_of_lt_dvd hx hz
  have hlt : x.toNat + z.toNat < 2 ^ 64 := hor ▸ (x ||| z).isLt
  rw [hor, BitVec.toNat_add, Nat.mod_eq_of_lt hlt]

private theorem part01_lt_2_56 {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8)
    (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8)
    (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
      BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 <
      0x0100000000000000#64 := by
  have h0 : BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) < 0x10000000#64 := by
    dsimp [part0_4, part0_3, part0_2]; bv_bits
  have h1 : BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 ≤ 0x00fffffff0000000#64 := by
    dsimp [part1_4, part1_3, part1_2]; bv_bits
  generalize BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) = x0 at h0 ⊢
  generalize BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 = x1 at h1 ⊢
  clear hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  bv_bits

private theorem ovf_byte10_aux {x : BitVec 64} {b8 b9 : BitVec 8}
    (hx : x < 0x0100000000000000#64) :
    (x + (BitVec.zeroExtend 64 b8 &&& 127#64) <<< 56 ||| BitVec.zeroExtend 64 b9 <<< 63).ult x = false := by
  have hor : (x + (BitVec.zeroExtend 64 b8 &&& 127#64) <<< 56 ||| BitVec.zeroExtend 64 b9 <<< 63) =
      (x + (BitVec.zeroExtend 64 b8 &&& 127#64) <<< 56) + (BitVec.zeroExtend 64 b9 <<< 63) := by
    refine or_eq_add_of_toNat_lt_dvd 63 ?_ (by bv_bits)
    bv_bits
  rw [hor]
  bv_bits

theorem ovf_byte10 {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8}
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (_hb8 : ¬ b8 ≤ 0x7f#8)
    (_hb9 : ¬ 2#8 ≤ b9) :
    (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
      BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 +
      (BitVec.zeroExtend 64 b8 &&& 127#64) <<< 56 ||| BitVec.zeroExtend 64 b9 <<< 63).ult
    (BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
      BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28) = false :=
  ovf_byte10_aux (part01_lt_2_56 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)

theorem decodeVarint_eq_none_of_pre {bs : List (BitVec 8)}
    (hpre : VarintSlicePre bs) (hnone : decodeVarint bs = none) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 rest,
      bs = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest ∧
      ¬ b0 ≤ 0x7f#8 ∧ ¬ b1 ≤ 0x7f#8 ∧ ¬ b2 ≤ 0x7f#8 ∧ ¬ b3 ≤ 0x7f#8 ∧
      ¬ b4 ≤ 0x7f#8 ∧ ¬ b5 ≤ 0x7f#8 ∧ ¬ b6 ≤ 0x7f#8 ∧ ¬ b7 ≤ 0x7f#8 ∧
      ¬ b8 ≤ 0x7f#8 ∧ 2#8 ≤ b9 := by
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) hpre (by simp) (by rintro _ ⟨⟩)
  have hb0 : ¬ b0 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint, decodeVarintAux] at hnone; simp [toNat_le_0x7f_iff, h] at hnone
  obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
  have hb1 : ¬ b1 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint, decodeVarintAux, decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, h] at hnone
  obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, not_false_eq_true, and_self])
  have hb2 : ¬ b2 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 3 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, h] at hnone
  obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, hb2, not_false_eq_true, and_self])
  have hb3 : ¬ b3 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 4 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, h] at hnone
  obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
  have hb4 : ¬ b4 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 5 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, h] at hnone
  obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
  have hb5 : ¬ b5 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 6 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, h] at hnone
  obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true, and_self])
  have hb6 : ¬ b6 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 7 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, h] at hnone
  obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5, b6]) hpre
    (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
  have hb7 : ¬ b7 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 8 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, h] at hnone
  obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) hpre
    (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true, and_self])
  have hb8 : ¬ b8 ≤ 0x7f#8 := by
    intro h; rw [decodeVarint] at hnone; iterate 9 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, h] at hnone
  obtain ⟨b9, rest, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8])
    hpre (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true, and_self])
  have hb9 : 2#8 ≤ b9 := by
    by_contra h
    have hle : b9 ≤ 0x7f#8 := by revert h; bv_bits
    rw [decodeVarint] at hnone; iterate 10 rw [decodeVarintAux] at hnone
    simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8,
      hle, h] at hnone
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, rest, rfl,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩

/-! ## `decodeVarint` accumulator and `varintSliceResultAt` unfolding lemmas -/

def vAcc1 (b0 : BitVec 8) : BitVec 64 :=
  0#64 ||| ((b0 &&& 0x7F#8).zeroExtend 64 <<< 0)
def vAcc2 (b0 b1 : BitVec 8) : BitVec 64 :=
  vAcc1 b0 ||| ((b1 &&& 0x7F#8).zeroExtend 64 <<< 7)
def vAcc3 (b0 b1 b2 : BitVec 8) : BitVec 64 :=
  vAcc2 b0 b1 ||| ((b2 &&& 0x7F#8).zeroExtend 64 <<< 14)
def vAcc4 (b0 b1 b2 b3 : BitVec 8) : BitVec 64 :=
  vAcc3 b0 b1 b2 ||| ((b3 &&& 0x7F#8).zeroExtend 64 <<< 21)
def vAcc5 (b0 b1 b2 b3 b4 : BitVec 8) : BitVec 64 :=
  vAcc4 b0 b1 b2 b3 ||| ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28)
def vAcc6 (b0 b1 b2 b3 b4 b5 : BitVec 8) : BitVec 64 :=
  vAcc5 b0 b1 b2 b3 b4 ||| ((b5 &&& 0x7F#8).zeroExtend 64 <<< 35)
def vAcc7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : BitVec 64 :=
  vAcc6 b0 b1 b2 b3 b4 b5 ||| ((b6 &&& 0x7F#8).zeroExtend 64 <<< 42)
def vAcc8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  vAcc7 b0 b1 b2 b3 b4 b5 b6 ||| ((b7 &&& 0x7F#8).zeroExtend 64 <<< 49)
def vAcc9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) : BitVec 64 :=
  vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 ||| ((b8 &&& 0x7F#8).zeroExtend 64 <<< 56)
def vAcc10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) : BitVec 64 :=
  vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8 ||| ((b9 &&& 0x7F#8).zeroExtend 64 <<< 63)

theorem varintSliceResultAt_1 (A : RustAlloc) (ret : BitVec 64)
    (b0 : BitVec 8) (rest : List (BitVec 8)) (hb0 : b0 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: rest) (decodeVarint (b0 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc1 b0) ∗ ((ret + 16#64) ↦₆₄ 1#64) := by
  have hdec : decodeVarint (b0 :: rest) = some (vAcc1 b0, rest) := by
    rw [decodeVarint, decodeVarintAux]; simp [toNat_le_0x7f_iff, hb0, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons, Nat.add_sub_cancel_left]

theorem varintSliceResultAt_2 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 : BitVec 8) (rest : List (BitVec 8)) (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : b1 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: rest) (decodeVarint (b0 :: b1 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc2 b0 b1) ∗ ((ret + 16#64) ↦₆₄ 2#64) := by
  have hdec : decodeVarint (b0 :: b1 :: rest) = some (vAcc2 b0 b1, rest) := by
    rw [decodeVarint]; iterate 2 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 - rest.length = 2 by omega]

theorem varintSliceResultAt_3 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : b2 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: rest) (decodeVarint (b0 :: b1 :: b2 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc3 b0 b1 b2) ∗ ((ret + 16#64) ↦₆₄ 3#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: rest) = some (vAcc3 b0 b1 b2, rest) := by
    rw [decodeVarint]; iterate 3 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 - rest.length = 3 by omega]

theorem varintSliceResultAt_4 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : b3 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc4 b0 b1 b2 b3) ∗ ((ret + 16#64) ↦₆₄ 4#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: rest) = some (vAcc4 b0 b1 b2 b3, rest) := by
    rw [decodeVarint]; iterate 4 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 - rest.length = 4 by omega]

theorem varintSliceResultAt_5 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 b4 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : b4 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: b4 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc5 b0 b1 b2 b3 b4) ∗ ((ret + 16#64) ↦₆₄ 5#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      some (vAcc5 b0 b1 b2 b3 b4, rest) := by
    rw [decodeVarint]; iterate 5 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 + 1 - rest.length = 5 by omega]

theorem varintSliceResultAt_6 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : b5 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc6 b0 b1 b2 b3 b4 b5) ∗ ((ret + 16#64) ↦₆₄ 6#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) =
      some (vAcc6 b0 b1 b2 b3 b4 b5, rest) := by
    rw [decodeVarint]; iterate 6 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 + 1 + 1 - rest.length = 6 by omega]

theorem varintSliceResultAt_7 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : b6 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc7 b0 b1 b2 b3 b4 b5 b6) ∗ ((ret + 16#64) ↦₆₄ 7#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (vAcc7 b0 b1 b2 b3 b4 b5 b6, rest) := by
    rw [decodeVarint]; iterate 7 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - rest.length = 7 by omega]

theorem varintSliceResultAt_8 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : b7 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc8 b0 b1 b2 b3 b4 b5 b6 b7) ∗
        ((ret + 16#64) ↦₆₄ 8#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7, rest) := by
    rw [decodeVarint]; iterate 8 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
      vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - rest.length = 8 by omega]

theorem varintSliceResultAt_9 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : b8 ≤ 0x7f#8) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8) ∗
        ((ret + 16#64) ↦₆₄ 9#64) := by
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8, rest) := by
    rw [decodeVarint]; iterate 9 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8,
      vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - rest.length = 9 by omega]

theorem varintSliceResultAt_10 (A : RustAlloc) (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : ¬ 2#8 ≤ b9) :
    varintSliceResultAt A ret (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest)
      (decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) ∗
        ((ret + 16#64) ↦₆₄ 10#64) := by
  have hb9' : b9 ≤ 0x7f#8 := by revert hb9; bv_bits
  have hdec : decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9, rest) := by
    rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
    simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9', hb9,
      vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]
  simp only [hdec, varintSliceResultAt, List.length_cons,
    show rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - rest.length = 10 by omega]

theorem vAcc1_eq (b0 : BitVec 8) :
    vAcc1 b0 = (b0 &&& 0x7F#8).zeroExtend 64 := by
  dsimp [vAcc1]; bv_bits

theorem vAcc1_lt (b0 : BitVec 8) : (vAcc1 b0).toNat < 2 ^ 7 := by
  rw [vAcc1_eq]; bv_bits

theorem vAcc2_eq (b0 b1 : BitVec 8) :
    vAcc2 b0 b1 = vAcc1 b0 + ((b1 &&& 0x7F#8).zeroExtend 64 <<< 7) := by
  dsimp [vAcc2]
  exact or_eq_add_of_toNat_lt_dvd 7 (vAcc1_lt b0) (by bv_bits)

theorem vAcc2_lt (b0 b1 : BitVec 8) : (vAcc2 b0 b1).toNat < 2 ^ 14 := by
  rw [vAcc2_eq]
  have h := vAcc1_lt b0
  generalize vAcc1 b0 = acc at h ⊢
  bv_bits

theorem vAcc3_eq (b0 b1 b2 : BitVec 8) :
    vAcc3 b0 b1 b2 = vAcc2 b0 b1 + ((b2 &&& 0x7F#8).zeroExtend 64 <<< 14) := by
  dsimp [vAcc3]
  exact or_eq_add_of_toNat_lt_dvd 14 (vAcc2_lt b0 b1) (by bv_bits)

theorem vAcc3_lt (b0 b1 b2 : BitVec 8) : (vAcc3 b0 b1 b2).toNat < 2 ^ 21 := by
  rw [vAcc3_eq]
  have h := vAcc2_lt b0 b1
  generalize vAcc2 b0 b1 = acc at h ⊢
  bv_bits

theorem vAcc4_eq (b0 b1 b2 b3 : BitVec 8) :
    vAcc4 b0 b1 b2 b3 = vAcc3 b0 b1 b2 + ((b3 &&& 0x7F#8).zeroExtend 64 <<< 21) := by
  dsimp [vAcc4]
  exact or_eq_add_of_toNat_lt_dvd 21 (vAcc3_lt b0 b1 b2) (by bv_bits)

theorem vAcc4_lt (b0 b1 b2 b3 : BitVec 8) : (vAcc4 b0 b1 b2 b3).toNat < 2 ^ 28 := by
  rw [vAcc4_eq]
  have h := vAcc3_lt b0 b1 b2
  generalize vAcc3 b0 b1 b2 = acc at h ⊢
  bv_bits

theorem vAcc5_eq (b0 b1 b2 b3 b4 : BitVec 8) :
    vAcc5 b0 b1 b2 b3 b4 = vAcc4 b0 b1 b2 b3 + ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28) := by
  dsimp [vAcc5]
  exact or_eq_add_of_toNat_lt_dvd 28 (vAcc4_lt b0 b1 b2 b3) (by bv_bits)

theorem vAcc5_lt (b0 b1 b2 b3 b4 : BitVec 8) : (vAcc5 b0 b1 b2 b3 b4).toNat < 2 ^ 35 := by
  rw [vAcc5_eq]
  have h := vAcc4_lt b0 b1 b2 b3
  generalize vAcc4 b0 b1 b2 b3 = acc at h ⊢
  bv_bits

theorem vAcc6_eq (b0 b1 b2 b3 b4 b5 : BitVec 8) :
    vAcc6 b0 b1 b2 b3 b4 b5 = vAcc5 b0 b1 b2 b3 b4 + ((b5 &&& 0x7F#8).zeroExtend 64 <<< 35) := by
  dsimp [vAcc6]
  exact or_eq_add_of_toNat_lt_dvd 35 (vAcc5_lt b0 b1 b2 b3 b4) (by bv_bits)

theorem vAcc6_lt (b0 b1 b2 b3 b4 b5 : BitVec 8) : (vAcc6 b0 b1 b2 b3 b4 b5).toNat < 2 ^ 42 := by
  rw [vAcc6_eq]
  have h := vAcc5_lt b0 b1 b2 b3 b4
  generalize vAcc5 b0 b1 b2 b3 b4 = acc at h ⊢
  bv_bits

theorem vAcc7_eq (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    vAcc7 b0 b1 b2 b3 b4 b5 b6 = vAcc6 b0 b1 b2 b3 b4 b5 + ((b6 &&& 0x7F#8).zeroExtend 64 <<< 42) := by
  dsimp [vAcc7]
  exact or_eq_add_of_toNat_lt_dvd 42 (vAcc6_lt b0 b1 b2 b3 b4 b5) (by bv_bits)

theorem vAcc7_lt (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    (vAcc7 b0 b1 b2 b3 b4 b5 b6).toNat < 2 ^ 49 := by
  rw [vAcc7_eq]
  have h := vAcc6_lt b0 b1 b2 b3 b4 b5
  generalize vAcc6 b0 b1 b2 b3 b4 b5 = acc at h ⊢
  bv_bits

theorem vAcc8_eq (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 =
      vAcc7 b0 b1 b2 b3 b4 b5 b6 + ((b7 &&& 0x7F#8).zeroExtend 64 <<< 49) := by
  dsimp [vAcc8]
  exact or_eq_add_of_toNat_lt_dvd 49 (vAcc7_lt b0 b1 b2 b3 b4 b5 b6) (by bv_bits)

theorem vAcc8_lt (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7).toNat < 2 ^ 56 := by
  rw [vAcc8_eq]
  have h := vAcc7_lt b0 b1 b2 b3 b4 b5 b6
  generalize vAcc7 b0 b1 b2 b3 b4 b5 b6 = acc at h ⊢
  bv_bits

theorem vAcc9_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8 =
      vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 + ((b8 &&& 0x7F#8).zeroExtend 64 <<< 56) := by
  dsimp [vAcc9]
  exact or_eq_add_of_toNat_lt_dvd 56 (vAcc8_lt b0 b1 b2 b3 b4 b5 b6 b7) (by bv_bits)

theorem vAcc9_lt (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8).toNat < 2 ^ 63 := by
  rw [vAcc9_eq]
  have h := vAcc8_lt b0 b1 b2 b3 b4 b5 b6 b7
  generalize vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 = acc at h ⊢
  bv_bits

theorem vAcc10_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) :
    vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =
      vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8 + ((b9 &&& 0x7F#8).zeroExtend 64 <<< 63) := by
  dsimp [vAcc10]
  exact or_eq_add_of_toNat_lt_dvd 63 (vAcc9_lt b0 b1 b2 b3 b4 b5 b6 b7 b8) (by bv_bits)

theorem hw_part0_eq {b0 b1 b2 b3 : BitVec 8}
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8) :
    BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) = vAcc4 b0 b1 b2 b3 := by
  simp only [vAcc4_eq, vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_4, part0_3, part0_2]
  bv_bits

theorem hw_part1_eq {b4 b5 b6 b7 : BitVec 8}
    (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 =
      ((b4 &&& 0x7F#8).zeroExtend 64 <<< 28) + ((b5 &&& 0x7F#8).zeroExtend 64 <<< 35) +
      ((b6 &&& 0x7F#8).zeroExtend 64 <<< 42) + ((b7 &&& 0x7F#8).zeroExtend 64 <<< 49) := by
  simp only [part1_4, part1_3, part1_2]
  bv_bits

theorem hw_part01_eq {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8)
    (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    BitVec.zeroExtend 64 (part0_4 b0 b1 b2 b3 + 4026531840#32) +
      BitVec.zeroExtend 64 (part1_4 b4 b5 b6 b7 + 4026531840#32) <<< 28 =
      vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 := by
  rw [hw_part0_eq hb0 hb1 hb2 hb3, hw_part1_eq hb4 hb5 hb6 hb7,
    vAcc8_eq, vAcc7_eq, vAcc6_eq, vAcc5_eq]
  simp only [BitVec.add_assoc]

open Lean Elab Tactic Meta in
local elab "wp_ret8_bv_bits " retStx:term:max ppSpace targetVal:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let addr ← elabTerm (← `($retStx + 8#64)) none
    let rhs ← elabTerm targetVal none
    let ty ← instantiateMVars (← g.getType)
    let pExpr := ty.getArg! 3
    let some sub := pExpr.find? fun e =>
        e.isAppOfArity ``Arm64.pointsTo64 2 && e.getArg! 0 == addr
      | throwError "wp_ret8_bv_bits: no (ret + 8#64) ↦₆₄ _ found in spatial context"
    let rhsCell ← mkAppM ``Arm64.pointsTo64 #[addr, rhs]
    let cellEqTy ← mkEq sub rhsCell
    let prfMVar ← mkFreshExprMVar cellEqTy
    let gs ← getGoals
    let mut toClear : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let u := decl.userName
        if u != `b0 && u != `b1 && u != `b2 && u != `b3 && u != `b4 &&
           u != `b5 && u != `b6 && u != `b7 && u != `b8 && u != `b9 &&
           u != `hb0 && u != `hb1 && u != `hb2 && u != `hb3 && u != `hb4 &&
           u != `hb5 && u != `hb6 && u != `hb7 && u != `hb8 && u != `hb9 &&
           u != `ret then
          toClear := toClear.push decl.fvarId
    let mId ← prfMVar.mvarId!.tryClearMany toClear
    setGoals [mId]
    let hb0 := mkIdent `hb0
    let hb1 := mkIdent `hb1
    let hb2 := mkIdent `hb2
    let hb3 := mkIdent `hb3
    let hb4 := mkIdent `hb4
    let hb5 := mkIdent `hb5
    let hb6 := mkIdent `hb6
    let hb7 := mkIdent `hb7
    let hb8 := mkIdent `hb8
    evalTactic (← `(tactic| (
      apply pointsTo64_congr_val
      first
      | (rw [hw_part01_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident
         try (rw [vAcc10]; refine congrArg₂ (· ||| ·) ?_ (by clear $hb8:ident; bv_bits))
         rw [vAcc9_eq]
         bv_bits)
      | (rw [hw_part0_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
         simp only [vAcc8_eq, vAcc7_eq, vAcc6_eq, vAcc5_eq, part1_4, part1_3, part1_2]
         bv_bits)
      | (simp only [vAcc4_eq, vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_4, part0_3, part0_2]
         bv_bits))))
    setGoals gs
    let g' ← g.assert `hret8_val cellEqTy (← instantiateMVars prfMVar)
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hId := mkIdent `hret8_val
    evalTactic (← `(tactic| (rw [$hId:ident]; clear $hId:ident)))

macro "wp_reach" : tactic =>
  `(tactic| apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *]))

/-- Stack-parameterized `decodeVarintSliceSpec` (`= decodeVarintSliceSpec A` at `decodeErrorHookStack`,
`= decodeVarintSliceSpecX A` at `decodeErrorHookStackX`, `= decodeVarintSliceSpecW A` at `decodeErrorHookStackW`). -/
def decodeVarintSliceSpecGen (A : RustAlloc) (errStack : Nat) : Spec DecodeVarintSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧ VarintSlicePre x.bs⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp (0x50 + errStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ varintSliceResultAt A x.ret x.bs (decodeVarint x.bs) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp (0x50 + errStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

section
attribute [local irreducible] _root_.Arm64.Program.fnOff

set_option maxHeartbeats 8000000 in
theorem decodeVarintSlice_ok_of_hooks_gen {oimg : Option Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat} (herr : 0x50 + errStack ≤ 2 ^ 64)
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarintSliceName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      (specWithOptInv oimg (decodeErrorFromSpecWithStack A errStack))) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarintSliceName)
      (specWithOptInv oimg (decodeVarintSliceSpecGen A errStack)) := by
  have hfn := (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")
  tripleRatchet_fetches b H hfn (num% (ls_off% "prost::encoding::varint::decode_varint_slice")) 704
  clear hfn
  dsimp only [decodeVarintSliceName] at hFromCall ⊢
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr
    "prost::encoding::varint::decode_varint_slice" = entry
  generalize_entry (libsignalSessionCode.rebase b H) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  conv =>
    arg 3; arg 2
    unfold decodeVarintSliceSpecGen
    simp only [memRegion_24_cells, stackAt_decodeVarintSliceGen herr, sepExists_sepConj_left,
      sepExists_sepConj_right]
  wpp_init_optImage x s0 hinv0
  obtain ⟨ret, ptr, bs⟩ := x
  dsimp only at *
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := eq_ofNat_of_toNat_eq h_3
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) h (by simp) (by rintro _ ⟨⟩)
  apply SepWPp.of_sepWP_optImage (mid := entry + bv% (16)) hinv0
  wp_steps
  wp_reach
  intro hinv1
  suffices hjoin :
      OptCallInv oimg (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC (entry + bv% (36)) |>.setMem m) →
      SepWPp prog (s0.readReg64 Reg.lr)
      (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC (entry + bv% (36)) |>.setMem m)
      (ret ↦₆₄ v_stk_6 ∗ (ret + 8#64) ↦₆₄ v_stk_5 ∗ (ret + 16#64) ↦₆₄ v_stk_4 ∗
        (ptr ↦₈ b0 ∗ (ptr + 1#64) ↦ₛ bs1) ∗ A.pool ∗
        stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
        memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ v_stk_3 ∗
        (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
                ⌜sf.trace = s0.trace⌝ ∗
                  varintSliceResultAt A ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                  ptr ↦ₛ (b0 :: bs1) ∗ A.pool ∗
                  stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
                  memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                  (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) by
    by_cases h11 : 11 ≤ (b0 :: bs1).length
    · have hule11 := ule_11_of_ge h11 h_4
      apply SepWPp.of_sepWP_optImage (mid := entry + bv% (36)) hinv1
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      exact hjoin
    · rcases h with h11' | ⟨hne, hlast⟩
      · exact (h11 h11').elim
      · have hule11 := ule_11_of_lt h11 h_4
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
        apply SepWPp.of_sepWP_optImage (mid := entry + bv% (32)) hinv1
        conv => arg 4; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne h_4]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne h_4, pointsToBytes_cons]
        wp_reach
        intro hinv2
        apply SepWPp.of_sepWP_optImage (mid := entry + bv% (36)) hinv2
        wp_steps
        wp_reach
        exact hjoin
  intro hinv_join
  by_cases hnone : decodeVarint (b0 :: bs1) = none
  · obtain ⟨b0', b1, b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre h hnone
    cases heq
    simp only [hnone, varintSliceResultAt]
    have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
    have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
    have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
    have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
    have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
    have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
    have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
    have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
    have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
    have hovf2 := ovf_byte2 hb0 hb1
    have hovf3 := ovf_byte3 hb0 hb1 hb2
    have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
    have hovf6 := ovf_byte6 hb4 hb5
    have hovf7 := ovf_byte7 hb4 hb5 hb6
    have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
    have hb9_ule := byte9_ule_of_ge hb9
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice")) hinv_join
    conv => arg 4; simp only [pointsToBytes_cons]
    wp_steps
    wp_reach
    intro hinv_call
    refine SepWPp.call_frame_optImage (oimg := oimg) (spec := decodeErrorFromSpecWithStack A errStack)
      (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := entry + bv% (592)) hFromCall hinv_call
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [decodeErrorFromSpecWithStack, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    apply SepWP.fold (pointsTo64_entails_memRegion8 (ret + 16#64) _) (by sep_focus)
    apply SepWP.done
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
      refine ⟨?_, by simp only [arm64_norm], ?_⟩
      · intro hm_final
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm] at hm_final ⊢
        rcases hm_final with ⟨⟨hx0_ne, htr⟩, hm_final⟩
        refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ret, sm.readReg64 (Reg.gpr 0#5), ⟨htr, hx0_ne⟩, ?_⟩
        arm64_sep_close
      · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
  · apply SepWPp.of_sepWP_ret
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      rw [varintSliceResultAt_1 A ret b0 bs1 hb0]
      wp_steps
      wp_ret8_bv_bits ret (vAcc1 b0)
      conv => arg 4; simp only [← pointsToBytes_cons]
      wp_done
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) h (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps 7
      by_cases hb1 : b1 ≤ 0x7f#8
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_le hb1
        rw [varintSliceResultAt_2 A ret b0 b1 bs2 hb0 hb1]
        wp_steps
        wp_ret8_bv_bits ret (vAcc2 b0 b1)
        conv => arg 4; simp only [← pointsToBytes_cons]
        wp_done
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
        have hovf2 := ovf_byte2 hb0 hb1
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) h (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb2 : b2 ≤ 0x7f#8
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_le hb2
          rw [varintSliceResultAt_3 A ret b0 b1 b2 bs3 hb0 hb1 hb2]
          wp_steps
          wp_ret8_bv_bits ret (vAcc3 b0 b1 b2)
          conv => arg 4; simp only [← pointsToBytes_cons]
          wp_done
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) h (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, hb2, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 7
          by_cases hb3 : b3 ≤ 0x7f#8
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_le hb3
            rw [varintSliceResultAt_4 A ret b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3]
            wp_steps
            wp_ret8_bv_bits ret (vAcc4 b0 b1 b2 b3)
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
            have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
            obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) h (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb4 : b4 ≤ 0x7f#8
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_le hb4
              rw [varintSliceResultAt_5 A ret b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4]
              wp_steps
              wp_ret8_bv_bits ret (vAcc5 b0 b1 b2 b3 b4)
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
              obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) h (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 5
              by_cases hb5 : b5 ≤ 0x7f#8
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_le hb5
                rw [varintSliceResultAt_6 A ret b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                wp_steps
                wp_ret8_bv_bits ret (vAcc6 b0 b1 b2 b3 b4 b5)
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
                have hovf6 := ovf_byte6 hb4 hb5
                obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) h
                  (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                    forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                    and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb6 : b6 ≤ 0x7f#8
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_le hb6
                  rw [varintSliceResultAt_7 A ret b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                  wp_steps
                  wp_ret8_bv_bits ret (vAcc7 b0 b1 b2 b3 b4 b5 b6)
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
                  have hovf7 := ovf_byte7 hb4 hb5 hb6
                  obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                    (pre := [b0, b1, b2, b3, b4, b5, b6]) h (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 7
                  by_cases hb7 : b7 ≤ 0x7f#8
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_le hb7
                    rw [varintSliceResultAt_8 A ret b0 b1 b2 b3 b4 b5 b6 b7 bs8
                      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                    wp_steps
                    wp_ret8_bv_bits ret (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7)
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
                    have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                    obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                      (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) h (by simp)
                      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                        forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb8 : b8 ≤ 0x7f#8
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                      rw [varintSliceResultAt_9 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                      obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) h (by simp)
                        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
                          and_self])
                      have hb9 : ¬ 2#8 ≤ b9 := by
                        intro hge
                        apply hnone
                        rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
                        by_cases hb9_le : b9 ≤ 0x7f#8 <;>
                          simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                            hb6, hb7, hb8, hb9_le, hge]
                      have hb9_ule := byte9_ule_of_lt hb9
                      have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                      conv => arg 4; rw [pointsToBytes_cons]
                      rw [varintSliceResultAt_10 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done

end

theorem decodeVarintSlice_ok_of_contract {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarintSliceName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      (decodeErrorFromSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeVarintSliceName)
      (decodeVarintSliceSpec A) :=
  subroutine_ok_of_optNone
    (decodeVarintSlice_ok_of_hooks_gen (oimg := none) (errStack := decodeErrorHookStack) (by decide)
      (subroutine_ok_to_optNone hFromCall))

theorem decodeVarintSlice_ok_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeVarintSliceName)
      (decodeVarintSliceSpec A) :=
  decodeVarintSlice_ok_of_contract
    (hC.decode_error_from_ok_at decodeVarintSliceName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      (by fnoff_eq))

theorem decodeVarintSlice_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hFrom : AllocHooks A abs) :
    DecodeVarintSliceOk b C A ctl abs :=
  decodeVarintSlice_ok_of_contract
    (decodeErrorFrom_ok_at (b := b) (C := C) (ctl := ctl)
      hFrom (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")
      (k := num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      (by decide))

/-! ## Extended-stack variant (`decodeVarintSliceSpecX`) -/

theorem stackAt_decodeVarintSliceX (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStackX =
      stackAt (sp - 80#64) decodeErrorHookStackX ∗
        memRegion (sp - 80#64) 8 ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 72#64) ↦₆₄ v9) ∗ ((sp - 64#64) ↦₆₄ v8) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) :=
  stackAt_decodeVarintSliceGen (errStack := decodeErrorHookStackX) (by decide) sp

theorem decodeVarintSlice_ok_of_contract_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall0 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecX A).inImage img) :=
  decodeVarintSlice_ok_of_hooks_gen (oimg := some img) (errStack := decodeErrorHookStackX)
    (by decide) hFromCall0

theorem decodeVarintSlice_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    DecodeVarintSliceOkExtX img A ext :=
  decodeVarintSlice_ok_of_contract_x
    (hC.decode_error_from_ok_at decodeVarintSliceName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::varint::decode_varint_slice"))
      (by fnoff_eq))

/-! ## Relocatable per-block proofs (blocks 261 and 76) -/

open CryptoVerification.LibsignalSession

abbrev lsHandleAllocErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

/-- Relocatable `<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from`
(Block `261`, `0x4ada0`) meets `decodeErrorFromSpec A`. -/
theorem decode_error_from_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpec A) := by
  simp only [decodeErrorFromSpec, InImage.DecodeErrorFrom.stackAt_decodeErrorFrom]
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hpanic' : ((blkPC_261).rebase (blkPl_261).base H).externAt?
      (lsρ lsHandleAllocErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsHandleAllocErrorSym)).trans hpanic
  clear hshim halloc hpanic
  wpp_init x s0
  obtain ⟨k, w⟩ := x
  dsimp only at *
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : LayoutOk 72 8 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_261).base + bv% (32))
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine InImage.DecodeErrorFrom.sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleAllocErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (InImage.DecodeErrorFrom.allocFailedIn_of_eq
          (by simp only [Rust.panicked, wp_norm, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, InImage.DecodeErrorFrom.memRegion_40_cells (k + 8#64),
      InImage.DecodeErrorFrom.memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
      SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun k3 =>
      SepWPp.exists_elim fun k4 =>
      SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
      SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 =>
      SepWPp.exists_elim fun u8 => ?_
    refine InImage.DecodeErrorFrom.sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.fold (InImage.DecodeErrorFrom.decodeErrorWith_zero_entails A _ w _ _ _ _ _ ‹KindNoHeap w›) (by sep_focus)
    apply SepWP.fold (InImage.DecodeErrorFrom.cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_focus)
    wp_done

theorem decode_error_from_placed_ok_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A hookStack) :=
  decodeErrorFromWithStack_of_decodeErrorFrom
    (decode_error_from_placed_ok hshim halloc hpanic) hle hmax

theorem decode_error_from_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A decodeErrorHookStackX) :=
  decode_error_from_placed_ok_gen hshim halloc hpanic

theorem SepWPp.of_sepWP_lscl {prog : Program} {pl : Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ (h : LibsignalCodeLoaded pl _) hkf => h.of_keepsFrozen hkf) hcl h

theorem SepWPp.call_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic ?_
    (fun sf R' hoom_s hm => (hoom sf _ hoom_s hm).elim)
  · intro R hm
    dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  · intro sf hpcm hrunm hspm hcsm
    dsimp only [withLsCl]
    rw [sepConj_assoc]
    exact SepWPp.pure_elim (hnext sf hpcm hrunm hspm hcsm)

theorem SepWPp.call_frame_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_lscl (x := x) (F := F) hcall hcl hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

set_option maxHeartbeats 8000000 in
theorem decode_varint_slice_placed_ok_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat}
    (herr : 0x50 + errStack ≤ 2 ^ 64 := by decide)
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A errStack)) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecGen A errStack)) := by
  have hFromCall := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_76).rebase (blkPl_76).base H) hFrom
  change subroutine_ok _ (lsmpl.base 261) _ at hFromCall
  clear hFrom
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeVarintSliceSpecGen
    simp only [memRegion_24_cells, stackAt_decodeVarintSliceGen herr, sepExists_sepConj_left,
      sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨ret, ptr, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have h : VarintSlicePre bs := by assumption
  have h_4 : bs.length < 2 ^ 63 := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    apply eq_ofNat_of_toNat_eq; assumption
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) h (by simp) (by rintro _ ⟨⟩)
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (16)) hcl0
  wp_steps
  wp_reach
  intro hcl1
  suffices hjoin :
      LibsignalCodeLoaded lsmpl m →
      SepWPp ((blkPC_76).rebase (blkPl_76).base H) (s0.readReg64 Reg.lr)
      (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (36)) |>.setMem m)
      (ret ↦₆₄ v_stk_6 ∗ (ret + 8#64) ↦₆₄ v_stk_5 ∗ (ret + 16#64) ↦₆₄ v_stk_4 ∗
        (ptr ↦₈ b0 ∗ (ptr + 1#64) ↦ₛ bs1) ∗ A.pool ∗
        stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
        memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ v_stk_3 ∗
        (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
                ⌜sf.trace = s0.trace⌝ ∗
                  varintSliceResultAt A ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                  ptr ↦ₛ (b0 :: bs1) ∗ A.pool ∗
                  stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
                  memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                  (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) by
    by_cases h11 : 11 ≤ (b0 :: bs1).length
    · have hule11 := ule_11_of_ge h11 h_4
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (36)) hcl1
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      exact hjoin
    · rcases h with h11' | ⟨hne, hlast⟩
      · exact (h11 h11').elim
      · have hule11 := ule_11_of_lt h11 h_4
        have hbit_last := VarintSliceBits.getLsbD_7_beq_of_le hlast
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (32)) hcl1
        conv => arg 4; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne h_4]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne h_4, pointsToBytes_cons]
        wp_reach
        intro hcl2
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (36)) hcl2
        wp_steps
        wp_reach
        exact hjoin
  intro hcl_join
  by_cases hnone : decodeVarint (b0 :: bs1) = none
  · obtain ⟨b0', b1, b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre h hnone
    cases heq
    simp only [hnone, varintSliceResultAt]
    have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
    have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
    have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
    have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
    have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
    have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
    have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
    have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
    have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
    have hovf2 := ovf_byte2 hb0 hb1
    have hovf3 := ovf_byte3 hb0 hb1 hb2
    have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
    have hovf6 := ovf_byte6 hb4 hb5
    have hovf7 := ovf_byte7 hb4 hb5 hb6
    have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
    have hb9_ule := byte9_ule_of_ge hb9
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_join
    conv => arg 4; simp only [pointsToBytes_cons]
    wp_steps
    wp_reach
    intro hcl_call
    refine SepWPp.call_frame_lscl (spec := decodeErrorFromSpecWithStack A errStack)
      (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := (blkPl_76).base + bv% (592)) hFromCall hcl_call
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromSpecWithStack, arm64_norm]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    apply SepWPp.of_sepWP_ret
    conv => arg 4; simp only [decodeErrorFromSpecWithStack, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    apply SepWP.fold (pointsTo64_entails_memRegion8 (ret + 16#64) _) (by sep_focus)
    apply SepWP.done
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
      refine ⟨?_, by simp only [arm64_norm], ?_⟩
      · intro hm_final
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm] at hm_final ⊢
        rcases hm_final with ⟨⟨hx0_ne, htr⟩, hm_final⟩
        refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ret, sm.readReg64 (Reg.gpr 0#5), ⟨htr, hx0_ne⟩, ?_⟩
        arm64_sep_close
      · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
  · apply SepWPp.of_sepWP_ret
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      rw [varintSliceResultAt_1 A ret b0 bs1 hb0]
      wp_steps
      wp_ret8_bv_bits ret (vAcc1 b0)
      conv => arg 4; simp only [← pointsToBytes_cons]
      wp_done
    · have hbit0 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) h (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps 7
      by_cases hb1 : b1 ≤ 0x7f#8
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_le hb1
        rw [varintSliceResultAt_2 A ret b0 b1 bs2 hb0 hb1]
        wp_steps
        wp_ret8_bv_bits ret (vAcc2 b0 b1)
        conv => arg 4; simp only [← pointsToBytes_cons]
        wp_done
      · have hbit1 := VarintSliceBits.getLsbD_7_beq_of_gt hb1
        have hovf2 := ovf_byte2 hb0 hb1
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) h (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb2 : b2 ≤ 0x7f#8
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_le hb2
          rw [varintSliceResultAt_3 A ret b0 b1 b2 bs3 hb0 hb1 hb2]
          wp_steps
          wp_ret8_bv_bits ret (vAcc3 b0 b1 b2)
          conv => arg 4; simp only [← pointsToBytes_cons]
          wp_done
        · have hbit2 := VarintSliceBits.getLsbD_7_beq_of_gt hb2
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) h (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, hb2, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 7
          by_cases hb3 : b3 ≤ 0x7f#8
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_le hb3
            rw [varintSliceResultAt_4 A ret b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3]
            wp_steps
            wp_ret8_bv_bits ret (vAcc4 b0 b1 b2 b3)
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit3 := VarintSliceBits.getLsbD_7_beq_of_gt hb3
            have hovf4 := VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
            obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) h (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb4 : b4 ≤ 0x7f#8
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_le hb4
              rw [varintSliceResultAt_5 A ret b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4]
              wp_steps
              wp_ret8_bv_bits ret (vAcc5 b0 b1 b2 b3 b4)
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit4 := VarintSliceBits.getLsbD_7_beq_of_gt hb4
              obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) h (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 5
              by_cases hb5 : b5 ≤ 0x7f#8
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_le hb5
                rw [varintSliceResultAt_6 A ret b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                wp_steps
                wp_ret8_bv_bits ret (vAcc6 b0 b1 b2 b3 b4 b5)
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit5 := VarintSliceBits.getLsbD_7_beq_of_gt hb5
                have hovf6 := ovf_byte6 hb4 hb5
                obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) h
                  (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                    forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                    and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb6 : b6 ≤ 0x7f#8
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_le hb6
                  rw [varintSliceResultAt_7 A ret b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                  wp_steps
                  wp_ret8_bv_bits ret (vAcc7 b0 b1 b2 b3 b4 b5 b6)
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit6 := VarintSliceBits.getLsbD_7_beq_of_gt hb6
                  have hovf7 := ovf_byte7 hb4 hb5 hb6
                  obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                    (pre := [b0, b1, b2, b3, b4, b5, b6]) h (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 7
                  by_cases hb7 : b7 ≤ 0x7f#8
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_le hb7
                    rw [varintSliceResultAt_8 A ret b0 b1 b2 b3 b4 b5 b6 b7 bs8
                      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                    wp_steps
                    wp_ret8_bv_bits ret (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7)
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit7 := VarintSliceBits.getLsbD_7_beq_of_gt hb7
                    have hovf8 := VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                    obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                      (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) h (by simp)
                      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                        forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb8 : b8 ≤ 0x7f#8
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                      rw [varintSliceResultAt_9 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit8 := VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                      obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) h (by simp)
                        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
                          and_self])
                      have hb9 : ¬ 2#8 ≤ b9 := by
                        intro hge
                        apply hnone
                        rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
                        by_cases hb9_le : b9 ≤ 0x7f#8 <;>
                          simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                            hb6, hb7, hb8, hb9_le, hge]
                      have hb9_ule := byte9_ule_of_lt hb9
                      have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                      conv => arg 4; rw [pointsToBytes_cons]
                      rw [varintSliceResultAt_10 A ret b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done

/-- Relocatable `prost::encoding::varint::decode_varint_slice` (Block `76`, `0x23008`)
meets `withLsCodeLoaded lsmpl (decodeVarintSliceSpec A)` given a contract for `DecodeError::from` (Block `261`). -/
theorem decode_varint_slice_placed_ok_of_contract [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpec A)) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpec A)) :=
  decode_varint_slice_placed_ok_gen (errStack := decodeErrorHookStack) (by decide) hFrom

/-- Relocatable `prost::encoding::varint::decode_varint_slice` (Block `76`, `0x23008`)
meets `withLsCodeLoaded lsmpl (decodeVarintSliceSpec A)`. -/
theorem decode_varint_slice_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpec A)) :=
  decode_varint_slice_placed_ok_of_contract
    (decode_error_from_placed_ok hshim halloc hpanic)

/-- Relocatable `prost::encoding::varint::decode_varint_slice` (Block `76`, `0x23008`)
meets `withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)` given a contract for `DecodeError::from` (Block `261`). -/
theorem decode_varint_slice_placed_ok_of_contract_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromSpecWithStack A decodeErrorHookStackX)) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)) :=
  decode_varint_slice_placed_ok_gen (errStack := decodeErrorHookStackX) (by decide) hFrom

/-- Relocatable `prost::encoding::varint::decode_varint_slice` (Block `76`, `0x23008`)
meets `withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)`. -/
theorem decode_varint_slice_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A)) :=
  decode_varint_slice_placed_ok_of_contract_x
    (decode_error_from_placed_ok_x hshim halloc hpanic)

end CryptoVerification.LibsignalTripleRatchet.Prost


