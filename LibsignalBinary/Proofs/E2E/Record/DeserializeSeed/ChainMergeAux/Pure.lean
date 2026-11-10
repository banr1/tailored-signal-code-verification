/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Pure Seed-Chain Shape and Protobuf Length Bounds

Establishes structural invariants (`SeedChainShape`), varint/field equivalence lemmas, and encoded
byte-length bounds (`< 128` bytes) for seed `ChainV` values decoded by `message::merge<Chain>`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

/-! ## Seed Chain Shape -/

/-- Structural invariants of any `ChainV` appearing in `seedFields f` under `SeedOk f`. -/
def SeedChainShape (c : ChainV) : Prop :=
  ∃ (srk priv : List (BitVec 8)) (i : BitVec 32) (k : List (BitVec 8)),
    c = ⟨srk, priv, some (i, k)⟩ ∧
    srk.length = 33 ∧ (priv = [] ∨ priv.length = 32) ∧ k.length = 32

theorem seedSlice_length_32_seedChain {f : List (BitVec 8)} (o : Nat)
    (hf : f.length = 300) (ho : o + 32 ≤ 300) :
    (seedSlice f o 32).length = 32 := by
  simp only [seedSlice, List.length_take, List.length_drop, hf]
  omega

theorem seedChainShape_of_seedFields_seedChain {f : List (BitVec 8)} {c : ChainV}
    (hOk : SeedOk f)
    (hMem : SeedField.sender c ∈ seedFields f ∨ SeedField.recv c ∈ seedFields f) :
    SeedChainShape c := by
  have hf : f.length = 300 := hOk.1
  unfold seedFields at hMem
  rcases hMem with hS | hR
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      false_or] at hS
    rcases hS with (hS | hS) | hS
    · split at hS
      · simp only [List.mem_singleton, SeedField.sender.injEq] at hS
        subst hS
        refine ⟨pbPubkey (seedSlice f 97 32), seedSlice f 129 32,
          BitVec.ofNat 32 (seedU32 f 193), seedSlice f 161 32, rfl, ?_, Or.inr ?_, ?_⟩
        · simp [pbPubkey, seedSlice_length_32_seedChain 97 hf (by omega)]
        · exact seedSlice_length_32_seedChain 129 hf (by omega)
        · exact seedSlice_length_32_seedChain 161 hf (by omega)
      · simp at hS
    · split at hS <;> simp at hS
    · split at hS <;> simp at hS
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      false_or] at hR
    rcases hR with (hR | hR) | hR
    · split at hR <;> simp at hR
    · split at hR
      · simp only [List.mem_singleton, SeedField.recv.injEq] at hR
        subst hR
        refine ⟨pbPubkey (seedSlice f 198 32), [],
          BitVec.ofNat 32 (seedU32 f 262), seedSlice f 230 32, rfl, ?_, Or.inl rfl, ?_⟩
        · simp [pbPubkey, seedSlice_length_32_seedChain 198 hf (by omega)]
        · exact seedSlice_length_32_seedChain 230 hf (by omega)
      · simp at hR
    · split at hR <;> simp at hR

/-! ## Varint and Field Codec Bridges -/

private theorem toNat_and7F_64_seedChain (x : BitVec 64) : (x &&& 0x7F).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7F : BitVec 64).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem contByte_eq_seedChain (w : BitVec 64) :
    (((w &&& 0x7F) ||| 0x80).setWidth 8) = BitVec.ofNat 8 (w.toNat % 128 + 128) := by
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := w.toNat % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, toNat_and7F_64_seedChain,
    show (0x80 : BitVec 64).toNat = 128 from rfl, Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

theorem pbVarintBody_eq_encodeVarintAux_seedChain (fuel : Nat) :
    ∀ (k : Nat) (w : BitVec 64),
      fuel < k → w.toNat < 128 ^ (fuel + 1) →
      pbVarintBody fuel w.toNat = encodeVarintAux k w := by
  induction fuel with
  | zero =>
    intro k w hk hw
    rcases k with _ | k
    · omega
    · simp only [Nat.zero_add, Nat.pow_one] at hw
      simp only [pbVarintBody, encodeVarintAux, hw, ↓reduceIte]
      rfl
  | succ fuel ih =>
    intro k w hk hw
    rcases k with _ | k
    · omega
    · by_cases hlt : w.toNat < 128
      · simp only [pbVarintBody, encodeVarintAux, hlt, ↓reduceIte]
        rfl
      · simp only [pbVarintBody, encodeVarintAux, hlt, ↓reduceIte]
        rw [contByte_eq_seedChain]
        congr 1
        have hshr : (w >>> 7).toNat = w.toNat / 128 := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [← hshr]
        refine ih k (w >>> 7) (by omega) ?_
        rw [hshr]
        apply Nat.div_lt_of_lt_mul
        have hpow : 128 ^ (fuel + 1 + 1) = 128 * 128 ^ (fuel + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        omega

theorem pbVarintBody_u32_eq_encodeVarint_seedChain (i : BitVec 32) :
    pbVarintBody 5 i.toNat = encodeVarint (i.zeroExtend 64) := by
  have hi : (i.zeroExtend 64).toNat = i.toNat := BitVec.toNat_setWidth_of_le (by decide)
  rw [ ← hi]
  exact pbVarintBody_eq_encodeVarintAux_seedChain 5 10 (i.zeroExtend 64) (by omega)
    (by have := i.isLt; rw [hi]; omega)

theorem mergeUint32_pbVarintBody_seedChain (i : BitVec 32) (rest : List (BitVec 8)) :
    mergeUint32 .varint (pbVarintBody 5 i.toNat ++ rest) = some (i, rest) := by
  rw [pbVarintBody_u32_eq_encodeVarint_seedChain]
  exact mergeUint32_encode i rest

theorem encodeVarint_lt128_seedChain (n : Nat) (hn : n < 128) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : (BitVec.ofNat 64 n).toNat < 0x80 := by omega
  unfold encodeVarint encodeVarintAux
  simp only [hlt, ↓reduceIte]
  ext
  simp [BitVec.setWidth_ofNat_of_le]

theorem mergeBytes_lt128_seedChain (b rest : List (BitVec 8)) (hb : b.length < 128) :
    mergeBytes .lengthDelimited ([BitVec.ofNat 8 b.length] ++ b ++ rest) = some (b, rest) := by
  rw [List.append_assoc, ← encodeVarint_lt128_seedChain b.length hb]
  exact mergeBytes_encode b rest (by omega)

/-! ## Encoded Payload Length Bounds -/

theorem pbVarintBody_length_bounds_seedChain (fuel n : Nat) :
    1 ≤ (pbVarintBody fuel n).length ∧ (pbVarintBody fuel n).length ≤ fuel + 1 := by
  induction fuel generalizing n with
  | zero => simp [pbVarintBody]
  | succ fuel ih =>
    simp only [pbVarintBody]
    split
    · simp
    · have := ih (n / 128)
      simp only [List.length_cons]
      omega

theorem pbVarint1_length_bounds_seedChain (n : Nat) :
    (pbVarint 1 n).length ≤ 7 := by
  unfold pbVarint pbKey
  split
  · simp
  · have := pbVarintBody_length_bounds_seedChain 5 n
    simp only [List.length_append, List.length_singleton]
    omega

theorem pbBytes_length_seedChain (tag : Nat) (b : List (BitVec 8)) :
    (pbBytes tag b).length = b.length + 2 := by
  simp only [pbBytes, pbKey, List.length_append, List.length_singleton]
  omega

/-- The `ChainKey` payload `pbVarint 1 i.toNat ++ pbBytes 2 k` for a 32-byte `k` has length `34..41 < 128`. -/
theorem ckEnc_length_bounds_seedChain (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 32) :
    34 ≤ (pbVarint 1 i.toNat ++ pbBytes 2 k).length ∧
    (pbVarint 1 i.toNat ++ pbBytes 2 k).length ≤ 41 := by
  have h1 := pbVarint1_length_bounds_seedChain i.toNat
  have h2 := pbBytes_length_seedChain 2 k
  simp only [List.length_append, h2, hk]
  omega

/-- A seed chain's `c.enc` has length between `71` and `112` (`< 128`). -/
theorem chainEnc_length_bounds_seedChain {srk priv : List (BitVec 8)} {i : BitVec 32} {k : List (BitVec 8)}
    (hsrk : srk.length = 33) (hpriv : priv = [] ∨ priv.length = 32) (hk : k.length = 32) :
    71 ≤ (ChainV.enc ⟨srk, priv, some (i, k)⟩).length ∧
    (ChainV.enc ⟨srk, priv, some (i, k)⟩).length < 128 := by
  have hck := ckEnc_length_bounds_seedChain i hk
  have hsrk_b := pbBytes_length_seedChain 1 srk
  have hck_b := pbBytes_length_seedChain 3 (pbVarint 1 i.toNat ++ pbBytes 2 k)
  unfold ChainV.enc
  rcases hpriv with rfl | hpriv32
  · simp only [↓reduceIte, List.append_nil]
    rw [List.length_append, hsrk_b, hsrk, hck_b]
    omega
  · have hne : priv ≠ [] := by rintro rfl; simp at hpriv32
    have hpriv_b := pbBytes_length_seedChain 2 priv
    simp only [hne, ↓reduceIte]
    rw [List.length_append, List.length_append, hsrk_b, hsrk, hpriv_b, hpriv32, hck_b]
    omega

/-! ## Relocatable `[LibsignalPlacement]` Precondition Unpacking -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Extract `LibsignalCodeRoLoaded lsmpl s0.mem`, `SeedChainShape x.c`, and the spatial
precondition from `chainMergeSeedPlacedSpec.pre x s0 ∗ R`. -/
theorem chainMergeSeedPlacedPre_unpack [LibsignalPlacement]
    {x : ChainMergeGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ chainMergeSeedPlacedSpec.pre x s0 ∗ R) :
    LibsignalCodeRoLoaded lsmpl s0.mem ∧
      (s0.readReg64 .x0).setWidth 8 = 2#8 ∧
      s0.readReg64 .x1 = x.a ∧
      s0.readReg64 .x2 = x.bufRef ∧
      SeedChainShape x.c ∧
      ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail).length < 2 ^ 32 ∧
      (s0.mem ⊨ prostChainAt A0 x.a ⟨[], [], none⟩ ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 x.c.enc.length] ++ x.c.enc ++ x.tail) ∗
        stackAt s0.sp chainMergeStack ∗ R) := by
  obtain ⟨hcrl, hraw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [chainMergeSeedRawSpec] at hraw
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
  obtain ⟨⟨hx0, hx1, hx2, _, hSeed, hField, hlen_lt⟩, hmem⟩ := hraw
  exact ⟨hcrl, hx0, hx1, hx2, seedChainShape_of_seedFields_seedChain hSeed hField, hlen_lt, hmem⟩

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
