/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec

/-!
# Cryptographic and wire-format lemmas for session correctness

**Checked by Lean.**

X25519 scalar clamping, AES-256-CBC round-trip, and `SignalMessage` MAC and wire round-trip lemmas
used in `libsignal_corr`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open CryptoGames.CKA
open CryptoGames.Ratchet
open CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst
open CryptoGames.SM
open CryptoGames.SM.Construction

namespace CryptoGames.LibsignalSM.Proofs.Correctness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

theorem vector_get_set (v : List.Vector (BitVec 8) 32) (k : Fin 32) (a : BitVec 8) (i : Fin 32) :
    (v.set k a).get i = if k.val = i.val then a else v.get i := by
  rcases v with ⟨l, hl⟩
  change (l.set k.val a)[i.val]'(by simp [hl]) = if k.val = i.val then a else l[i.val]'(by simp [hl])
  exact List.getElem_set _

theorem clampScalar_get (b : List.Vector (BitVec 8) 32) (i : Fin 32) :
    (clampScalar b).get i =
      if i = 0 then b.get 0 &&& 248#8
      else if i = 31 then (b.get 31 &&& 127#8) ||| 64#8
      else b.get i := by
  unfold clampScalar
  rw [vector_get_set, vector_get_set]
  by_cases h0 : i = 0
  · subst h0; rfl
  · by_cases h31 : i = 31
    · subst h31; rfl
    · have h0' : ¬(0 = i.val) := fun h => h0 (Fin.ext h.symm)
      have h31' : ¬(31 = i.val) := fun h => h31 (Fin.ext h.symm)
      simp only [h0, h31, ↓reduceIte]
      change (if 31 = i.val then b.get 31 &&& 127#8 ||| 64#8
        else if 0 = i.val then b.get 0 &&& 248#8 else b.get i) = b.get i
      simp [h0', h31']

theorem clampScalar_idem (b : List.Vector (BitVec 8) 32) :
    clampScalar (clampScalar b) = clampScalar b := by
  apply List.Vector.ext
  intro i
  rw [clampScalar_get, clampScalar_get, clampScalar_get, clampScalar_get]
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte]
    ext j hj : 1
    simp only [BitVec.getElem_and]
    generalize (b.get 0)[j] = bit
    revert bit j hj
    decide
  · by_cases h31 : i = 31
    · subst h31
      have h31_0 : ¬((31 : Fin 32) = 0) := by decide
      simp only [h31_0, ↓reduceIte]
      ext j hj : 1
      simp only [BitVec.getElem_or, BitVec.getElem_and]
      generalize (b.get 31)[j] = bit
      revert bit j hj
      decide
    · simp [h0, h31]

theorem keyVec_get (x : BitVec 256) (i : Fin 32) :
    (Ratchet.keyToBytesVec32 x).get i = x.extractLsb' (8 * i.val) 8 := by
  simp only [Ratchet.keyToBytesVec32, HMAC.keyToBytes32, List.Vector.get, List.get_ofFn]
  rfl

theorem clampScalar_keyVec (x : BitVec 256) :
    clampScalar (Ratchet.keyToBytesVec32 x) = Ratchet.keyToBytesVec32 (clamp256 x) := by
  apply List.Vector.ext
  intro i
  rw [clampScalar_get]
  simp only [keyVec_get]
  ext j hj : 1
  by_cases h0 : i = 0
  · subst h0
    change ((x.extractLsb' 0 8 &&& 248#8)[j]) = ((clamp256 x).extractLsb' 0 8)[j]
    simp only [clamp256, BitVec.getElem_and, BitVec.getElem_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_and, Nat.zero_add]
    generalize x.getLsbD j = bit
    revert bit j hj
    decide
  · by_cases h31 : i = 31
    · subst h31
      change ((x.extractLsb' 248 8 &&& 127#8 ||| 64#8)[j]) = ((clamp256 x).extractLsb' 248 8)[j]
      simp only [clamp256, BitVec.getElem_or, BitVec.getElem_and,
        BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and]
      generalize x.getLsbD (248 + j) = bit
      revert bit j hj
      decide
    · simp only [h0, h31, ↓reduceIte, clamp256, BitVec.getElem_extractLsb',
        BitVec.getLsbD_or, BitVec.getLsbD_and]
      generalize x.getLsbD (8 * i.val + j) = bit
      revert bit j hj i h0 h31
      decide

theorem clampScalar_keyVec_clamp256 (x : BitVec 256) :
    clampScalar (Ratchet.keyToBytesVec32 (clamp256 x)) = Ratchet.keyToBytesVec32 (clamp256 x) := by
  rw [← clampScalar_keyVec, clampScalar_idem]

theorem vec32_toList (v : List.Vector (BitVec 8) 32) :
    LibsignalInst.vec32 v.toList = v := by
  apply List.Vector.eq
  rcases v with ⟨l, hl⟩
  simp [LibsignalInst.vec32, List.Vector.toList, hl]

theorem vec32_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    (LibsignalInst.vec32 bs).toList = bs := by
  simp [LibsignalInst.vec32, List.Vector.toList, h]

section LibX25519

variable {Pt : Type} [Zero Pt] [DecidableEq Pt]
variable {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
variable {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}

theorem encT_toList (hX : X25519RealizesDh C Dh encPt encT) (Q : Pt) :
    (encT Q).bytes.toList = encPt Q := by
  rw [hX.2 Q, vec32_of_length_32 (hX.1.enc_length Q)]

theorem encT_injective (hX : X25519RealizesDh C Dh encPt encT) :
    Function.Injective encT := by
  intro P Q h
  apply hX.1.enc_injective
  rw [← encT_toList hX P, ← encT_toList hX Q, h]

theorem KeyPair_generate_publicKey (hX : X25519RealizesDh C Dh encPt encT) (x : BitVec 256) :
    (KeyPair.generate C x).publicKey = encT (Dh.dh x Dh.base) := by
  dsimp only [KeyPair.generate]
  rw [clampScalar_keyVec]
  cases h : encT (Dh.dh x Dh.base) with | mk b =>
  congr 1
  apply List.Vector.eq
  have hpk := hX.1.pubKey_hook (clamp256 x)
  have hvec : LibsignalInst.vec32 (HMAC.keyToBytes32 (clamp256 x)) = Ratchet.keyToBytesVec32 (clamp256 x) := by
    apply List.Vector.eq
    simp [LibsignalInst.vec32, Ratchet.keyToBytesVec32, HMAC.keyToBytes32]
  rw [hvec, hX.1.dh_clamp] at hpk
  have henc := encT_toList hX (Dh.dh x Dh.base)
  rw [h] at henc
  rw [hpk, ← henc]

theorem KeyPair_generate_privateKey (C : Crypto) (x : BitVec 256) :
    (KeyPair.generate C x).privateKey = ⟨Ratchet.keyToBytesVec32 (clamp256 x)⟩ := by
  dsimp only [KeyPair.generate]
  rw [clampScalar_keyVec]

theorem dh_base_ne_zero (hX : X25519RealizesDh C Dh encPt encT) (x : BitVec 256) :
    Dh.dh x Dh.base ≠ 0 :=
  hX.1.dh_ne_zero x Dh.base hX.1.base_ne_zero

theorem createChain_encT (hX : X25519RealizesDh C Dh encPt encT)
    {Q : Pt} (hQ : Q ≠ 0) (rk : BitVec 256) (x : BitVec 256) :
    Ratchet.createChain C.F C.X rk (encT Q).bytes (Ratchet.keyToBytesVec32 (clamp256 x)) =
      some (Ratchet.rootKdf C.F rk (encPt (Dh.dh x Q))) := by
  dsimp only [Ratchet.createChain]
  rw [clampScalar_keyVec_clamp256]
  have hhook := hX.1.hook (clamp256 x) Q
  have hvec1 : LibsignalInst.vec32 (HMAC.keyToBytes32 (clamp256 x)) =
      Ratchet.keyToBytesVec32 (clamp256 x) := by
    apply List.Vector.eq
    simp [LibsignalInst.vec32, Ratchet.keyToBytesVec32, HMAC.keyToBytes32]
  have hvec2 : LibsignalInst.vec32 (encPt Q) = (encT Q).bytes := (hX.2 Q).symm
  rw [hvec1, hvec2, hX.1.dh_clamp x Q] at hhook
  have hne0 : encPt (Dh.dh x Q) ≠ List.replicate 32 0#8 := by
    intro heq
    have heq0 : encPt (Dh.dh x Q) = encPt 0 := heq.trans hX.1.enc_zero.symm
    exact hX.1.dh_ne_zero x Q hQ (hX.1.enc_injective heq0)
  rw [hhook]
  simp only [hne0, ↓reduceIte]

theorem rootCreateChain_encT (hX : X25519RealizesDh C Dh encPt encT)
    {Q : Pt} (hQ : Q ≠ 0) (rk : BitVec 256) (x : BitVec 256) :
    rootCreateChain C rk (encT Q) ⟨Ratchet.keyToBytesVec32 (clamp256 x)⟩ =
      Except.ok (let p := Ratchet.rootKdf C.F rk (encPt (Dh.dh x Q)); (p.1, ⟨p.2, 0⟩)) := by
  dsimp only [rootCreateChain]
  rw [createChain_encT hX hQ rk x]

end LibX25519

theorem aesCbcDecrypt_aesCbcEncrypt {E D : CBC.AesKey → CBC.Block → CBC.Block}
    (hD : ∀ k x, D k (E k x) = x) (key : CBC.AesKey) (iv : CBC.Block)
    (ptext : List (BitVec 8)) :
    aesCbcDecrypt D key iv (aesCbcEncrypt E key iv ptext) = some ptext := by
  dsimp only [aesCbcDecrypt, aesCbcEncrypt, CBC.cbcPkcs7EncryptOnly, CipherScheme.enc]
  exact CBC.cbcDecRaw_correct hD key iv ⟨ptext, rfl⟩

theorem sha256With_length (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState)
    (m : List (BitVec 8)) :
    (HMAC.sha256With F m).length = 32 := by
  dsimp only [HMAC.sha256With]
  rcases (HMAC.chunks64 (HMAC.sha256Pad m)).foldl F HMAC.sha256IV with ⟨l, hl⟩
  have hflat : ∀ xs : List (BitVec 32),
      (xs.flatMap (HMAC.toBEBytes 4)).length = 4 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x tl ih =>
      simp only [List.flatMap_cons, List.length_append, ih, HMAC.toBEBytes, List.length_ofFn,
        List.length_cons]
      omega
  change (l.flatMap (HMAC.toBEBytes 4)).length = 32
  rw [hflat, hl]

theorem hmac8_length (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState)
    (k m : List (BitVec 8)) :
    (HMAC.hmacSha256Trunc8 F k m).length = macLength := by
  dsimp only [HMAC.hmacSha256Trunc8, HMAC.hmacWith, macLength]
  rw [List.length_take, sha256With_length]
  rfl

theorem computeMac_length (F : ShaCompress) (sId rId : IdentityKey) (macKey : BitVec 256)
    (msg : List (BitVec 8)) :
    (computeMac F sId rId macKey msg).length = macLength :=
  hmac8_length F (HMAC.keyToBytes32 macKey) ((macIds sId rId).toList ++ msg)

theorem tryFrom_append_of_length_macLength (codec : SignalMessageProtoCodec)
    (ser mac₁ mac₂ : List (BitVec 8)) (hser : ser ≠ [])
    (hm₁ : mac₁.length = macLength) (hm₂ : mac₂.length = macLength) :
    SignalMessage.tryFrom codec (ser ++ mac₁) =
      (SignalMessage.tryFrom codec (ser ++ mac₂)).map
        (fun m => { m with serialized := ser ++ mac₁ }) := by
  have hlen : (ser ++ mac₁).length = (ser ++ mac₂).length := by
    rw [List.length_append, List.length_append, hm₁, hm₂]
  have hhead : (ser ++ mac₁).headD 0 = (ser ++ mac₂).headD 0 := by
    cases ser with
    | nil => contradiction
    | cons hd tl => rfl
  have htake₁ : (ser ++ mac₁).take ((ser ++ mac₁).length - macLength) = ser := by
    rw [List.length_append, hm₁, Nat.add_sub_cancel, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  have htake₂ : (ser ++ mac₂).take ((ser ++ mac₂).length - macLength) = ser := by
    rw [List.length_append, hm₂, Nat.add_sub_cancel, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  unfold SignalMessage.tryFrom
  rw [htake₁, htake₂, hlen, hhead]
  dsimp only [bind, Except.bind]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem tryFrom_new {codec : SignalMessageProtoCodec}
    (F : ShaCompress) (v : BitVec 8)
    (macKey : BitVec 256) (addrs : Option (List (BitVec 8))) (rk : PublicKey)
    (cnt prevCnt : BitVec 32) (ctext : List (BitVec 8))
    (sId rId : IdentityKey) (pq : List (BitVec 8))
    (hrt : (signalWireCodec codec).parse
      ((signalWireCodec codec).encode ⟨v, rk, cnt, prevCnt, pq, addrs⟩ ctext) =
        some (⟨v, rk, cnt, prevCnt, pq, addrs⟩, ctext)) :
    SignalMessage.tryFrom codec
        (SignalMessage.new F codec v macKey addrs rk cnt prevCnt ctext sId rId pq).serialized =
      Except.ok (SignalMessage.new F codec v macKey addrs rk cnt prevCnt ctext sId rId pq) := by
  set hdr : SignalHeader := ⟨v, rk, cnt, prevCnt, pq, addrs⟩
  set ser := (signalWireCodec codec).encode hdr ctext
  set mac := computeMac F sId rId macKey ser
  have hser_ne : ser ≠ [] := by
    dsimp only [ser, signalWireCodec, serializeContent]
    exact List.cons_ne_nil _ _
  have hmac_len : mac.length = macLength := computeMac_length F sId rId macKey ser
  have hrep_len : (List.replicate macLength (0 : BitVec 8)).length = macLength :=
    List.length_replicate
  have hnew_ser :
      (SignalMessage.new F codec v macKey addrs rk cnt prevCnt ctext sId rId pq).serialized =
        ser ++ mac := rfl
  rw [hnew_ser, tryFrom_append_of_length_macLength codec ser mac (List.replicate macLength 0)
    hser_ne hmac_len hrep_len]
  have hparse :
      (match SignalMessage.tryFrom codec (ser ++ List.replicate macLength 0) with
       | .ok m => some (m.header, m.ciphertext)
       | .error _ => none) = some (hdr, ctext) := hrt
  cases htf : SignalMessage.tryFrom codec (ser ++ List.replicate macLength 0) with
  | error e =>
    rw [htf] at hparse
    contradiction
  | ok m =>
    rw [htf] at hparse
    injection hparse with hpair
    have hhdr : m.header = hdr := congrArg Prod.fst hpair
    have hct : m.ciphertext = ctext := congrArg Prod.snd hpair
    dsimp only [SignalMessage.header, hdr] at hhdr
    injection hhdr with hv' hrk hcnt hprev hpq haddrs
    rcases m with ⟨mv, mrk, mcnt, mprev, mct, mpq, maddrs, mser⟩
    dsimp only at hv' hrk hcnt hprev hpq haddrs hct
    subst hv' hrk hcnt hprev hpq haddrs hct
    rfl

theorem verifyMac_new (F : ShaCompress) (codec : SignalMessageProtoCodec) (v : BitVec 8)
    (macKey : BitVec 256) (addrs : Option (List (BitVec 8))) (rk : PublicKey)
    (cnt prevCnt : BitVec 32) (ctext : List (BitVec 8))
    (sId rId : IdentityKey) (pq : List (BitVec 8)) :
    (SignalMessage.new F codec v macKey addrs rk cnt prevCnt ctext sId rId pq).verifyMac
      F sId rId macKey = true := by
  dsimp only [SignalMessage.verifyMac, SignalMessage.new]
  set ser := serializeContent codec v rk cnt prevCnt ctext pq addrs
  set mac := computeMac F sId rId macKey ser
  have hmac_len : mac.length = macLength := computeMac_length F sId rId macKey ser
  have htake : (ser ++ mac).take ((ser ++ mac).length - macLength) = ser := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel,
      List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop : (ser ++ mac).drop ((ser ++ mac).length - macLength) = mac := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  rw [htake, hdrop]
  exact beq_self_eq_true _

theorem verifyMacWithAddresses_new (F : ShaCompress) (codec : SignalMessageProtoCodec) (v : BitVec 8)
    (macKey : BitVec 256) (addrs expected : Option (List (BitVec 8))) (rk : PublicKey)
    (cnt prevCnt : BitVec 32) (ctext : List (BitVec 8))
    (sId rId : IdentityKey) (pq : List (BitVec 8))
    (haddrs : LibsignalAead.addressCheckPasses addrs expected = true) :
    (SignalMessage.new F codec v macKey addrs rk cnt prevCnt ctext sId rId pq).verifyMacWithAddresses
      F expected sId rId macKey = true := by
  dsimp only [SignalMessage.verifyMacWithAddresses]
  rw [verifyMac_new, Bool.true_and]
  exact haddrs

end CryptoGames.LibsignalSM.Proofs.Correctness
