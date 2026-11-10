/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.ModelProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Algebraic and Round-Trip Lemmas for `SignalPqxdh.Model`

**Checked by Lean.**

Proves public-key encoding disjointness (`encodeEC_ne_encodeKEM`), fixed-output byte lengths, and
AES-256-CBC + truncated HMAC-SHA256 round-trip decryption (`aes256CbcHmac_roundtrip`) for
`LibsignalBinary/Specifications/SignalPqxdh/Model.lean`.
-/

namespace SignalPqxdh

/-- Disjointness of serialized EC and KEM public keys (discharges BJKS24's `encodeEC <> encodeKEM`). -/
theorem encodeEC_ne_encodeKEM (pkDh pkKem : Bytes) :
    encodeEC pkDh ≠ encodeKEM pkKem := by
  simp [encodeEC, encodeKEM, TAG_EC_DJB, TAG_KYBER_1024]

theorem fitBytesRef_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBytesRef n bs = bs := by
  subst h
  simp [fitBytesRef]

theorem sha512Ref_length (P : Primitives) (msg : Bytes) :
    (sha512Ref P msg).length = 64 := by
  simp [sha512Ref]

@[simp]
theorem xorBytes_length (a b : Bytes) :
    (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]

theorem hmacSha256Ref_length (P : Primitives) (key msg : Bytes) :
    (hmacSha256Ref P key msg).length = 32 := by
  simp [hmacSha256Ref, sha256Ref]

theorem toBlocks16_append_of_len16 {b : Bytes} (hb : b.length = 16) (rest : Bytes) :
    toBlocks16 (b ++ rest) = b :: toBlocks16 rest := by
  rw [toBlocks16]
  simp [hb, List.take_left' hb, List.drop_left' hb]

private theorem pkcs7Pad16_length_ge (pt : Bytes) :
    (pkcs7Pad16 pt).length ≥ 16 := by
  simp [pkcs7Pad16]
  omega

private theorem pkcs7Pad16_length_mod (pt : Bytes) :
    (pkcs7Pad16 pt).length % 16 = 0 := by
  simp [pkcs7Pad16]
  omega

private theorem pkcs7Unpad16_pad16 (pt : Bytes) :
    pkcs7Unpad16 (pkcs7Pad16 pt) = some pt := by
  have hmod : (pkcs7Pad16 pt).length % 16 = 0 := pkcs7Pad16_length_mod pt
  unfold pkcs7Unpad16
  let k := 15 - pt.length % 16
  let b : UInt8 := (k + 1).toUInt8
  have hk_le : k ≤ 15 := by omega
  have hb_nat : b.toNat = k + 1 := by
    have hlt : k + 1 < UInt8.size := by
      change k + 1 < 256
      omega
    simpa [b, Nat.toUInt8_eq] using UInt8.toNat_ofNat_of_lt' hlt
  have hrev : (pkcs7Pad16 pt).reverse = b :: (List.replicate k b ++ pt.reverse) := by
    change (pt ++ List.replicate (k + 1) b).reverse = b :: (List.replicate k b ++ pt.reverse)
    rw [List.reverse_append, List.reverse_replicate, List.replicate_succ, List.cons_append]
  rw [hrev]
  have hrep_len : (List.replicate k b).length = k := List.length_replicate
  have htake : (List.replicate k b ++ pt.reverse).take (b.toNat - 1) = List.replicate (b.toNat - 1) b := by
    rw [hb_nat]
    simp [List.take_left' hrep_len]
  have hdrop : (List.replicate k b ++ pt.reverse).drop (b.toNat - 1) = pt.reverse := by
    rw [hb_nat]
    simp [List.drop_left' hrep_len]
  have hc1 : decide (b.toNat ≥ 1) = true := by simp [hb_nat]
  have hc2 : decide (b.toNat ≤ 16) = true := by simp [hb_nat]; omega
  have hc3 : ((pkcs7Pad16 pt).length % 16 == 0) = true := by simp [hmod]
  have hc4 : ((List.replicate k b ++ pt.reverse).take (b.toNat - 1) == List.replicate (b.toNat - 1) b) = true := by
    simp [htake]
  simp only [hc1, hc2, hc3, hc4, Bool.and_self, ↓reduceIte, hdrop, List.reverse_reverse]

private theorem toBlocks16_aligned_props :
    ∀ (n : Nat) (bs : Bytes), bs.length = 16 * n →
      (∀ b ∈ toBlocks16 bs, b.length = 16) ∧ fromBlocks16 (toBlocks16 bs) = bs
  | 0, bs, hbs => by
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [toBlocks16, fromBlocks16]
  | n + 1, bs, hbs => by
    have htake_len : (bs.take 16).length = 16 := by
      simp
      omega
    have hdrop_len : (bs.drop 16).length = 16 * n := by
      simp
      omega
    have hbs_split : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
    have hstep : toBlocks16 bs = bs.take 16 :: toBlocks16 (bs.drop 16) := by
      conv => lhs; rw [hbs_split]
      exact toBlocks16_append_of_len16 htake_len (bs.drop 16)
    obtain ⟨ih_mem, ih_from⟩ := toBlocks16_aligned_props n (bs.drop 16) hdrop_len
    rw [hstep]
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb_rest
      · exact htake_len
      · exact ih_mem b hb_rest
    · simp only [fromBlocks16, List.foldr_cons]
      change bs.take 16 ++ fromBlocks16 (toBlocks16 (bs.drop 16)) = bs
      rw [ih_from, ← hbs_split]

private theorem fromBlocks16_length_and_toBlocks16 :
    ∀ (blks : List Bytes), (∀ b ∈ blks, b.length = 16) →
      (fromBlocks16 blks).length = 16 * blks.length ∧ toBlocks16 (fromBlocks16 blks) = blks
  | [], _ => by
    simp [fromBlocks16, toBlocks16]
  | b :: rest, hblks => by
    have hb : b.length = 16 := hblks b (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x.length = 16 := fun x hx => hblks x (List.mem_cons_of_mem b hx)
    obtain ⟨ih_len, ih_to⟩ := fromBlocks16_length_and_toBlocks16 rest hrest
    have hcons : fromBlocks16 (b :: rest) = b ++ fromBlocks16 rest := rfl
    rw [hcons]
    refine ⟨?_, ?_⟩
    · simp [hb, ih_len]
      omega
    · rw [toBlocks16_append_of_len16 hb, ih_to]

private theorem cbcEncBlocks_props (P : Primitives) (key : Bytes) :
    ∀ (blks : List Bytes) (iv : Bytes),
      (cbcEncBlocks P key iv blks).length = blks.length ∧
      (∀ c ∈ cbcEncBlocks P key iv blks, c.length = 16)
  | [], _ => by
    simp [cbcEncBlocks, cbcEncBlocksWith]
  | blk :: rest, iv => by
    simp only [cbcEncBlocks, cbcEncBlocksWith, List.length_cons]
    obtain ⟨ih_len, ih_mem⟩ :=
      cbcEncBlocks_props P key rest
        (fitBytesRef 16 (P.aesEncBlock (fitBytesRef 32 key) (xorBytes (fitBytesRef 16 blk) (fitBytesRef 16 iv))))
    refine ⟨congrArg (· + 1) ih_len, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc_rest
    · exact fitBytesRef_length 16 _
    · exact ih_mem c hc_rest

private theorem cbcDecBlocks_encBlocks (P : Primitives)
    (hEncLen : ∀ k b, (P.aesEncBlock k b).length = 16)
    (hCorr : ∀ k b, k.length = 32 → b.length = 16 → P.aesDecBlock k (P.aesEncBlock k b) = b)
    (key : Bytes) :
    ∀ (blks : List Bytes) (iv : Bytes), (∀ b ∈ blks, b.length = 16) →
      cbcDecBlocks P key iv (cbcEncBlocks P key iv blks) = blks
  | [], _, _ => rfl
  | blk :: rest, iv, hblks => by
    have hblk : blk.length = 16 := hblks blk (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x.length = 16 := fun x hx => hblks x (List.mem_cons_of_mem blk hx)
    simp only [cbcEncBlocks, cbcEncBlocksWith, cbcDecBlocks, cbcDecBlocksWith]
    let k32 := fitBytesRef 32 key
    let iv16 := fitBytesRef 16 iv
    have hk32 : k32.length = 32 := fitBytesRef_length 32 key
    have hiv16 : iv16.length = 16 := fitBytesRef_length 16 iv
    have hfit_blk : fitBytesRef 16 blk = blk := fitBytesRef_of_length_eq hblk
    let x := xorBytes blk iv16
    have hx_len : x.length = 16 := by
      simp [x, hblk, hiv16]
    let ctBlk := P.aesEncBlock k32 x
    have hct_len : ctBlk.length = 16 := hEncLen k32 x
    have hfit_ct : fitBytesRef 16 ctBlk = ctBlk := fitBytesRef_of_length_eq hct_len
    have hdec : P.aesDecBlock k32 ctBlk = x := hCorr k32 x hk32 hx_len
    have hfit_x : fitBytesRef 16 x = x := fitBytesRef_of_length_eq hx_len
    have hxor : xorBytes x iv16 = blk :=
      xorBytes_self_right blk iv16 (by omega)
    change xorBytes (fitBytesRef 16 (P.aesDecBlock k32 (fitBytesRef 16 (fitBytesRef 16 (P.aesEncBlock k32 (xorBytes (fitBytesRef 16 blk) iv16)))))) iv16 ::
        cbcDecBlocksWith P.aesDecBlock key (fitBytesRef 16 (fitBytesRef 16 (P.aesEncBlock k32 (xorBytes (fitBytesRef 16 blk) iv16))))
          (cbcEncBlocksWith P.aesEncBlock key (fitBytesRef 16 (P.aesEncBlock k32 (xorBytes (fitBytesRef 16 blk) iv16))) rest) =
      blk :: rest
    rw [hfit_blk]
    change xorBytes (fitBytesRef 16 (P.aesDecBlock k32 (fitBytesRef 16 (fitBytesRef 16 ctBlk)))) iv16 ::
        cbcDecBlocksWith P.aesDecBlock key (fitBytesRef 16 (fitBytesRef 16 ctBlk))
          (cbcEncBlocksWith P.aesEncBlock key (fitBytesRef 16 ctBlk) rest) =
      blk :: rest
    rw [hfit_ct, hfit_ct, hdec, hfit_x, hxor]
    congr 1
    exact cbcDecBlocks_encBlocks P hEncLen hCorr key rest ctBlk hrest

private theorem aes256Cbc_roundtrip (P : Primitives)
    (hEncLen : ∀ k b, (P.aesEncBlock k b).length = 16)
    (hCorr : ∀ k b, k.length = 32 → b.length = 16 → P.aesDecBlock k (P.aesEncBlock k b) = b)
    (key iv pt : Bytes) :
    aes256CbcDecRef P key iv (aes256CbcEncRef P key iv pt) = some pt ∧
      (aes256CbcEncRef P key iv pt).length ≥ 16 := by
  let padded := pkcs7Pad16 pt
  have hpad_ge : padded.length ≥ 16 := pkcs7Pad16_length_ge pt
  have hpad_mod : padded.length % 16 = 0 := pkcs7Pad16_length_mod pt
  have hpad_mul : padded.length = 16 * (padded.length / 16) := by omega
  obtain ⟨hblks_mem, hblks_from⟩ := toBlocks16_aligned_props (padded.length / 16) padded hpad_mul
  obtain ⟨hpad_len2, _⟩ := fromBlocks16_length_and_toBlocks16 (toBlocks16 padded) hblks_mem
  have hblks_ge1 : (toBlocks16 padded).length ≥ 1 := by
    rw [hblks_from] at hpad_len2
    omega
  obtain ⟨hct_blks_len, hct_blks_mem⟩ := cbcEncBlocks_props P key (toBlocks16 padded) iv
  obtain ⟨hct_len, hct_to⟩ :=
    fromBlocks16_length_and_toBlocks16 (cbcEncBlocks P key iv (toBlocks16 padded)) hct_blks_mem
  have hct_ge16 : (aes256CbcEncRef P key iv pt).length ≥ 16 := by
    change (fromBlocks16 (cbcEncBlocks P key iv (toBlocks16 padded))).length ≥ 16
    omega
  have hct_mod16 : (aes256CbcEncRef P key iv pt).length % 16 = 0 := by
    change (fromBlocks16 (cbcEncBlocks P key iv (toBlocks16 padded))).length % 16 = 0
    omega
  refine ⟨?_, hct_ge16⟩
  unfold aes256CbcDecRef
  have hc1 : decide ((aes256CbcEncRef P key iv pt).length ≥ 16) = true := by simp [hct_ge16]
  have hc2 : ((aes256CbcEncRef P key iv pt).length % 16 == 0) = true := by simp [hct_mod16]
  simp only [hc1, hc2, Bool.and_self, ↓reduceIte]
  change pkcs7Unpad16 (fromBlocks16 (cbcDecBlocks P key iv (toBlocks16 (fromBlocks16 (cbcEncBlocks P key iv (toBlocks16 padded)))))) = some pt
  rw [hct_to, cbcDecBlocks_encBlocks P hEncLen hCorr key (toBlocks16 padded) iv hblks_mem, hblks_from]
  exact pkcs7Unpad16_pad16 pt

theorem aes256CbcHmac_roundtrip (P : Primitives)
    (hEncLen : ∀ k b, (P.aesEncBlock k b).length = 16)
    (hCorr : ∀ k b, k.length = 32 → b.length = 16 → P.aesDecBlock k (P.aesEncBlock k b) = b)
    (mk : MessageKeys) (ad pt : Bytes) :
    aes256CbcHmacDecRef P mk ad (aes256CbcHmacEncRef P mk ad pt) = some pt := by
  obtain ⟨hcbc, hct_ge16⟩ := aes256Cbc_roundtrip P hEncLen hCorr mk.cipherKey mk.iv pt
  let ct := aes256CbcEncRef P mk.cipherKey mk.iv pt
  let mac := (hmacSha256Ref P mk.macKey (aeadMacInput ad ct)).take 8
  have hmac_len : mac.length = 8 := by
    have h32 : (hmacSha256Ref P mk.macKey (aeadMacInput ad ct)).length = 32 :=
      hmacSha256Ref_length P mk.macKey (aeadMacInput ad ct)
    simp [mac, h32]
  have htot_ge24 : (ct ++ mac).length ≥ 24 := by
    simp [hmac_len]
    omega
  have hsub8 : (ct ++ mac).length - 8 = ct.length := by
    simp [hmac_len]
  have htake : (ct ++ mac).take ((ct ++ mac).length - 8) = ct := by
    rw [hsub8]
    exact List.take_left' rfl
  have hdrop : (ct ++ mac).drop ((ct ++ mac).length - 8) = mac := by
    rw [hsub8]
    exact List.drop_left' rfl
  unfold aes256CbcHmacEncRef aes256CbcHmacDecRef
  change (if (ct ++ mac).length ≥ 24 then
      let ctLen := (ct ++ mac).length - 8
      let ct' := (ct ++ mac).take ctLen
      let tag := (ct ++ mac).drop ctLen
      let expectedTag := (hmacSha256Ref P mk.macKey (aeadMacInput ad ct')).take 8
      if tag == expectedTag then aes256CbcDecRef P mk.cipherKey mk.iv ct' else none
    else none) = some pt
  simp only [htot_ge24, ↓reduceIte]
  rw [htake, hdrop]
  change (if mac == mac then aes256CbcDecRef P mk.cipherKey mk.iv ct else none) = some pt
  simp only [BEq.rfl, ↓reduceIte]
  exact hcbc

end SignalPqxdh
