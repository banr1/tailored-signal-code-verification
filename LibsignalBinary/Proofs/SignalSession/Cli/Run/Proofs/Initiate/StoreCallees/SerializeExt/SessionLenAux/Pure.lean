/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# Pure Helpers for `<SessionStructure as prost::Message>::encoded_len`

Little-endian byte-unpacking bridges (`leBytes` to `unpack32` / `unpack64`), protobuf field
encoded-length lemmas, receiver-chain loop sum lemmas, and `BitVec` overflow-check helpers.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.SessionLenAux
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization

/-! ## 1. `leBytes` to `unpack32` / `unpack64` bridges -/

private theorem ofNat8_toNat_eq_truncate8 {w : Nat} (y : BitVec w) :
    BitVec.ofNat 8 y.toNat = y.truncate 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem ofNat8_div_eq_extractLsb' {w : Nat} (x : BitVec w) (i k : Nat)
    (hpow : 256 ^ i = 2 ^ k) :
    BitVec.ofNat 8 (x.toNat / 256 ^ i) = x.extractLsb' k 8 := by
  have hdiv : x.toNat / 256 ^ i = (x >>> k).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hpow]
  rw [hdiv, ofNat8_toNat_eq_truncate8]
  ext j hj
  simp

theorem leBytes_4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  simp only [leBytes, unpack32, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact ⟨ofNat8_div_eq_extractLsb' w 0 0 rfl,
         ofNat8_div_eq_extractLsb' w 1 8 rfl,
         ofNat8_div_eq_extractLsb' w 2 16 rfl,
         ofNat8_div_eq_extractLsb' w 3 24 rfl⟩

theorem leBytes_8_eq_unpack64 (v : BitVec 64) :
    leBytes 8 v.toNat = unpack64 v := by
  simp only [leBytes, unpack64, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact ⟨ofNat8_div_eq_extractLsb' v 0 0 rfl,
         ofNat8_div_eq_extractLsb' v 1 8 rfl,
         ofNat8_div_eq_extractLsb' v 2 16 rfl,
         ofNat8_div_eq_extractLsb' v 3 24 rfl,
         ofNat8_div_eq_extractLsb' v 4 32 rfl,
         ofNat8_div_eq_extractLsb' v 5 40 rfl,
         ofNat8_div_eq_extractLsb' v 6 48 rfl,
         ofNat8_div_eq_extractLsb' v 7 56 rfl⟩

theorem zeroBytes4_eq_unpack32 : ([0#8, 0#8, 0#8, 0#8] : List (BitVec 8)) = unpack32 0#32 := rfl

theorem oneBytes4_eq_unpack32 : ([1#8, 0#8, 0#8, 0#8] : List (BitVec 8)) = unpack32 1#32 := rfl

theorem keyToBytes32_length_sessLen (k : BitVec 256) :
    (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

/-! ## 2. Zero-test helpers -/

theorem ofNat64_beq_zero_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = (n == 0) := by
  cases n with
  | zero => rfl
  | succ k =>
    change (BitVec.ofNat 64 (k + 1) == 0#64) = false
    rw [beq_eq_false_iff_ne]
    intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at h1
    omega

theorem ofNat64_bne_zero_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != 0#64) = (n != 0) := by
  simp [bne, ofNat64_beq_zero_of_lt h]

theorem list_eq_nil_iff_length_beq_zero {α : Type} (xs : List α) :
    (xs.length == 0) = xs.isEmpty := by
  cases xs <;> rfl

theorem list_ne_nil_iff_length_bne_zero {α : Type} (xs : List α) :
    (xs.length != 0) = !xs.isEmpty := by
  cases xs <;> rfl

/-! ## 3. Protobuf field encoded-length lemmas -/

theorem lenField_length {t : Nat} (bs : List (BitVec 8))
    (hkey : (encodeKey t .lengthDelimited).length = 1) :
    (lenField t bs).length =
      1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  simp only [lenField, List.length_append, hkey]

theorem bv_lenField_length {t : Nat} (bs : List (BitVec 8))
    (hkey : (encodeKey t .lengthDelimited).length = 1) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (lenField t bs).length := by
  rw [lenField_length bs hkey]
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

theorem bv_bytesField_nonempty_length {t : Nat} {bs : List (BitVec 8)} (hne : bs ≠ [])
    (hkey : (encodeKey t .lengthDelimited).length = 1) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField t bs).length := by
  simp only [bytesField, hne, ↓reduceIte]
  exact bv_lenField_length bs hkey

theorem bytesField_rootKey_length (k : BitVec 256) :
    (bytesField 4 (HMAC.keyToBytes32 k)).length = 34 := by
  have hlen := keyToBytes32_length_sessLen k
  have hne : HMAC.keyToBytes32 k ≠ [] := by
    intro h; rw [h] at hlen; contradiction
  have hkey : (encodeKey 4 .lengthDelimited).length = 1 := rfl
  have hvar : (encodeVarint 32#64).length = 1 := rfl
  simp [bytesField, hne, lenField, hlen, hkey, hvar]

theorem bv_uint32Field_nonzero_length {t : Nat} {v : BitVec 32} (hne : v ≠ 0#32)
    (hkey : (encodeKey t .varint).length = 1) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field t v).length := by
  have hne' : v ≠ 0 := hne
  simp only [uint32Field, hne', ↓reduceIte, List.length_append, hkey, ← BitVec.ofNat_add,
    Nat.add_comm]

theorem bv_optUint32Field_some_length {t : Nat} (v : BitVec 32)
    (hkey : (encodeKey t .varint).length = 1) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (optUint32Field t (some v)).length := by
  simp only [optUint32Field, List.length_append, hkey, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_int32Field_nonzero_length {t : Nat} {v : BitVec 32} (hne : v ≠ 0#32)
    (hkey : (encodeKey t .varint).length = 1) :
    BitVec.ofNat 64 (encodeVarint (BitVec.signExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (int32Field t v).length := by
  have hne' : v ≠ 0 := hne
  simp only [int32Field, hne', ↓reduceIte, List.length_append, hkey, ← BitVec.ofNat_add,
    Nat.add_comm]

theorem bv_uint64Field_nonzero_length {t : Nat} {v : BitVec 64} (hne : v ≠ 0#64)
    (hkey : (encodeKey t .varint).length = 1) :
    BitVec.ofNat 64 (encodeVarint v).length + 1#64 =
      BitVec.ofNat 64 (uint64Field t v).length := by
  have hne' : v ≠ 0 := hne
  simp only [uint64Field, hne', ↓reduceIte, List.length_append, hkey, ← BitVec.ofNat_add,
    Nat.add_comm]

theorem encPendingMem_length (g : TailVecGhost) (p : PendingPreKey) :
    (encPendingMem g p).length =
      (optUint32Field 1 p.preKeyId).length +
      (bytesField 2 g.vec.bytes).length +
      (int32Field 3 p.signedPreKeyId).length +
      (uint64Field 4 p.timestamp).length := by
  simp [encPendingMem, List.length_append, Nat.add_assoc]

theorem encPendingKyber_length (k : PendingKyberPreKey) :
    (encPendingKyber k).length =
      (uint32Field 1 k.preKeyId).length +
      (bytesField 2 k.ciphertext).length := by
  simp [encPendingKyber, List.length_append]

/-! ## 4. Receiver-chains loop sum lemmas -/

/-- Sum of `body + varint(body.length)` without the 1-byte tag-7 key per element. -/
def chainNoKeyLen (gc : ChainGhost × ReceiverChain) : Nat :=
  (encChainMem gc).length + (encodeVarint (BitVec.ofNat 64 (encChainMem gc).length)).length

/-- Total tag-7 encoded bytes for a list of receiver chains. -/
def chainsTotalLen (cs : List (ChainGhost × ReceiverChain)) : Nat :=
  ((cs.map fun gc => lenField 7 (encChainMem gc)).flatten).length

theorem lenField_7_encChainMem_length (gc : ChainGhost × ReceiverChain) :
    (lenField 7 (encChainMem gc)).length = chainNoKeyLen gc + 1 := by
  rw [lenField_length (encChainMem gc) rfl, chainNoKeyLen]
  omega

theorem chainsTotalLen_nil : chainsTotalLen [] = 0 := rfl

theorem chainsTotalLen_cons (gc : ChainGhost × ReceiverChain) (cs : List (ChainGhost × ReceiverChain)) :
    chainsTotalLen (gc :: cs) = (lenField 7 (encChainMem gc)).length + chainsTotalLen cs := by
  simp [chainsTotalLen]

/-- Sum of `chainNoKeyLen` over `cs`, plus `cs.length` (the 1-byte keys), equals `chainsTotalLen cs`. -/
def chainsNoKeySum : List (ChainGhost × ReceiverChain) → Nat
  | [] => 0
  | gc :: cs => chainNoKeyLen gc + chainsNoKeySum cs

theorem chainsNoKeySum_add_length (cs : List (ChainGhost × ReceiverChain)) :
    chainsNoKeySum cs + cs.length = chainsTotalLen cs := by
  induction cs with
  | nil => rfl
  | cons gc cs ih =>
    rw [chainsNoKeySum, List.length_cons, chainsTotalLen_cons, lenField_7_encChainMem_length]
    omega

theorem encChainMem_length_le_lenField_7 (gc : ChainGhost × ReceiverChain) :
    (encChainMem gc).length < (lenField 7 (encChainMem gc)).length := by
  rw [lenField_7_encChainMem_length, chainNoKeyLen]
  omega

theorem chainNoKeyLen_lt_lenField_7 (gc : ChainGhost × ReceiverChain) :
    chainNoKeyLen gc < (lenField 7 (encChainMem gc)).length := by
  rw [lenField_7_encChainMem_length]
  omega

/-! ## 5. Top-level `encSessionMem` length decomposition -/

theorem encSessionMem_length_eq (G : SessionGhost) (s : Session (List (BitVec 8))) :
    (encSessionMem G s).length =
      (uint32Field 1 s.state.sessionVersion).length +
      (bytesField 2 G.localIk.bytes).length +
      (bytesField 3 G.remoteIk.bytes).length +
      (bytesField 4 (HMAC.keyToBytes32 s.state.rootKey)).length +
      (uint32Field 5 s.state.previousCounter).length +
      (encSenderFieldMem G.sender s.state.senderChain).length +
      chainsTotalLen (G.chains.zip s.state.receiverChains) +
      (encPendingFieldMem G.pending s.pendingPreKey).length +
      (uint32Field 10 s.remoteRegistrationId).length +
      (uint32Field 11 s.localRegistrationId).length +
      (bytesField 13 s.aliceBaseKey).length +
      (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length +
      (bytesField 15 s.state.pqRatchetState).length := by
  simp only [encSessionMem, chainsTotalLen, List.length_append]

/-! ## 6. Overflow condition helpers for `cmp` / `adds` -/

theorem ult_varint_lenField {n : Nat} {vlen : Nat}
    (h : n + vlen + 1 < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 (n + vlen + 1)) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64),
    Nat.mod_eq_of_lt h]
  omega

theorem ule_lenField_varint_false {n : Nat} {vlen : Nat}
    (h : n + vlen + 1 < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 (n + vlen + 1)) (BitVec.ofNat 64 vlen) = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64),
    Nat.mod_eq_of_lt h]
  omega

/-! ## 7. Hardware varint length lemmas -/

private theorem or_one_ne_zero (v : BitVec 64) : v ||| 1#64 ≠ 0#64 := by
  intro h
  have h0 := congrArg (fun x : BitVec 64 => x.getLsbD 0) h
  simp at h0

private theorem or_one_clz_toNat_lt (v : BitVec 64) : (v ||| 1#64).clz.toNat < 64 := by
  have hle : (v ||| 1#64).clz ≤ 64#64 := BitVec.clz_le
  have hne : (v ||| 1#64).clz ≠ 64#64 :=
    mt BitVec.clz_eq_iff_eq_zero.mp (or_one_ne_zero v)
  have hle_nat : (v ||| 1#64).clz.toNat ≤ 64 := hle
  have hne_nat : (v ||| 1#64).clz.toNat ≠ 64 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    exact h
  omega

private theorem shiftRight_lt_128_iff (v : BitVec 64) (s : Nat) :
    ((v >>> s).toNat < 128) ↔ 64 - (v ||| 1#64).clz.toNat ≤ s + 7 := by
  have hxne : v ||| 1#64 ≠ 0#64 := or_one_ne_zero v
  have hlo : 2 ^ (63 - (v ||| 1#64).clz.toNat) ≤ (v ||| 1#64).clz.toNat * 0 + (v ||| 1#64).toNat := by
    simpa using BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) hxne
  have hhi : (v ||| 1#64).toNat < 2 ^ (64 - (v ||| 1#64).clz.toNat) :=
    BitVec.toNat_lt_two_pow_sub_clz
  have h1 : (v >>> s).toNat < 128 ↔ v.toNat >>> (s + 7) = 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_eq_zero_iff_lt (by decide)).symm
  have h2 : (v ||| 1#64).toNat >>> (s + 7) = v.toNat >>> (s + 7) := by
    change (v.toNat ||| 1) >>> (s + 7) = v.toNat >>> (s + 7)
    rw [Nat.shiftRight_or_distrib]
    have h1z : 1 >>> (s + 7) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      have : 2 ^ 7 ≤ 2 ^ (s + 7) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.div_eq_of_lt (by omega)
    rw [h1z, Nat.or_zero]
  rw [h1, ← h2, Nat.shiftRight_eq_div_pow]
  constructor
  · intro hdiv
    by_contra hgt
    have hle : s + 7 ≤ 63 - (v ||| 1#64).clz.toNat := by omega
    have hpow : 2 ^ (s + 7) ≤ 2 ^ (63 - (v ||| 1#64).clz.toNat) := Nat.pow_le_pow_right (by decide) hle
    have hlt := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos (s + 7))).mp hdiv
    omega
  · intro hle
    have hpow : 2 ^ (64 - (v ||| 1#64).clz.toNat) ≤ 2 ^ (s + 7) := Nat.pow_le_pow_right (by decide) hle
    exact Nat.div_eq_of_lt (by omega)

private def clzTree (c : BitVec 64) : Nat :=
  if 64 - c.toNat ≤ 7 then 1
  else if 64 - c.toNat ≤ 14 then 2
  else if 64 - c.toNat ≤ 21 then 3
  else if 64 - c.toNat ≤ 28 then 4
  else if 64 - c.toNat ≤ 35 then 5
  else if 64 - c.toNat ≤ 42 then 6
  else if 64 - c.toNat ≤ 49 then 7
  else if 64 - c.toNat ≤ 56 then 8
  else if 64 - c.toNat ≤ 63 then 9
  else 10

private theorem hwFormula_eq_clzTree_of_lt :
    ∀ k : Fin 64,
      let c := BitVec.ofNat 64 k.val
      ((((c ^^^ 0x3f#64) + ((c ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
        BitVec.ofNat 64 (clzTree c)) := by
  decide

private theorem hwFormula_w32_eq_clzTree_of_lt :
    ∀ k : Fin 64,
      let c := BitVec.ofNat 64 k.val
      BitVec.zeroExtend 64
        ((((c.truncate 32 ^^^ 63#32) + ((c.truncate 32 ^^^ 63#32) <<< 3#32)) + 73#32)) >>> 6#64 =
        BitVec.ofNat 64 (clzTree c) := by
  decide

private theorem hwFormula_w32_natShift_eq_clzTree_of_lt :
    ∀ k : Fin 64,
      let c := BitVec.ofNat 64 k.val
      BitVec.zeroExtend 64
        ((((c.truncate 32 ^^^ 0x3f#32) + ((c.truncate 32 ^^^ 0x3f#32) <<< 3)) + 0x49#32)) >>> 6 =
        BitVec.ofNat 64 (clzTree c) := by
  decide

private theorem ushiftRight_add_64 (w : BitVec 64) (a b : Nat) :
    (w >>> a) >>> b = w >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

private theorem encodeVarint_length_eq_clzTree (v : BitVec 64) :
    (encodeVarint v).length = clzTree (v ||| 1#64).clz := by
  unfold encodeVarint clzTree
  dsimp only [encodeVarintAux]
  have h0_eq : (v.toNat < 128) ↔ 64 - (v ||| 1#64).clz.toNat ≤ 7 := by
    simpa using shiftRight_lt_128_iff v 0
  simp only [ushiftRight_add_64, Nat.reduceAdd, h0_eq, shiftRight_lt_128_iff]
  have h10 : 64 - (v ||| 1#64).clz.toNat ≤ 70 := by omega
  by_cases c1 : 64 - (v ||| 1#64).clz.toNat ≤ 7 <;> simp only [c1, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c2 : 64 - (v ||| 1#64).clz.toNat ≤ 14 <;> simp only [c2, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c3 : 64 - (v ||| 1#64).clz.toNat ≤ 21 <;> simp only [c3, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c4 : 64 - (v ||| 1#64).clz.toNat ≤ 28 <;> simp only [c4, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c5 : 64 - (v ||| 1#64).clz.toNat ≤ 35 <;> simp only [c5, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c6 : 64 - (v ||| 1#64).clz.toNat ≤ 42 <;> simp only [c6, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c7 : 64 - (v ||| 1#64).clz.toNat ≤ 49 <;> simp only [c7, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c8 : 64 - (v ||| 1#64).clz.toNat ≤ 56 <;> simp only [c8, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c9 : 64 - (v ||| 1#64).clz.toNat ≤ 63 <;> simp only [c9, ↓reduceIte, List.length_cons, List.length_nil, h10]

theorem sessHwVarintLen_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length := by
  have hlt := or_one_clz_toNat_lt v
  have hfin := hwFormula_eq_clzTree_of_lt ⟨(v ||| 1#64).clz.toNat, hlt⟩
  have hclz : BitVec.ofNat 64 (v ||| 1#64).clz.toNat = (v ||| 1#64).clz := by
    apply BitVec.eq_of_toNat_eq; simp
  dsimp only at hfin
  rw [hclz] at hfin
  rw [hfin, encodeVarint_length_eq_clzTree]

theorem sessHwVarintLen_bvShift_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  sessHwVarintLen_eq_encodeVarint_length v

theorem sessHwVarintLen_w32_eq_encodeVarint_length (v : BitVec 32) :
    BitVec.zeroExtend 64
      (((((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 63#32) +
        (((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 63#32) <<< 3#32)) + 73#32)) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length := by
  have hlt := or_one_clz_toNat_lt (BitVec.zeroExtend 64 v)
  have hfin := hwFormula_w32_eq_clzTree_of_lt ⟨(BitVec.zeroExtend 64 v ||| 1#64).clz.toNat, hlt⟩
  have hclz : BitVec.ofNat 64 (BitVec.zeroExtend 64 v ||| 1#64).clz.toNat =
      (BitVec.zeroExtend 64 v ||| 1#64).clz := by
    apply BitVec.eq_of_toNat_eq; simp
  dsimp only at hfin
  rw [hclz] at hfin
  rw [hfin, encodeVarint_length_eq_clzTree]

theorem sessHwVarintLen_w32_natShift_eq_encodeVarint_length (v : BitVec 32) :
    BitVec.zeroExtend 64
      (((((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 0x3f#32) +
        (((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 0x3f#32) <<< 3)) + 0x49#32)) >>> 6 =
      BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length :=
  sessHwVarintLen_w32_eq_encodeVarint_length v

theorem sess_truncate32_zext64_lsr6 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x >>> 6) = x >>> 6 := by
  ext i hi
  simp
  omega

theorem sess_ule_zero_64 (x : BitVec 64) : BitVec.ule 0#64 x = true := by
  simp [BitVec.ule_eq_decide]

theorem sess_ult_zero_64 (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  simp [BitVec.ult_eq_decide]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.SessionLenAux
