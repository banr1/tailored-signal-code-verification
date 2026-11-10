/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ByteSpecs

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompI0Laws
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (StubSymbol x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol sha256CompressFunction CryptoEquationsHold)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol toEdwardsSymbol edwardsCompressSymbol edwardsNegSymbol torsionFreeSymbol doubleScalarMulSymbol scalarModOrderSymbol scalarModOrderWideSymbol mlkem768FromSeedSymbol mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol mlkem768ValidatePkSymbol libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (Records Sem Ghost randTerm leBytes X25519PubCanonical ReturnsLength ExternInterpretationTotalOnUsedSymbols)
open DY.Libsignal.Composed.Refinement.Cli (HooksMatchInterpretation ExternContractsHoldCli)
open CryptoVerification.SignalSession (CliHooks)
@[simp]
theorem leBytes_length (n v : Nat) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih (v / 256)]
theorem compI0_publicKey (sk : HwBytes) : compI0 x25519PublicKeySymbol [sk] = some (compLookupPub sk) := rfl
theorem compI0_agreement (sk pk : HwBytes) : compI0 x25519AgreementSymbol [sk, pk] = some (compLookupDh sk pk) := rfl
theorem compI0_torsion (pt : HwBytes) (b : BitVec 8) : compI0 x25519TorsionSymbol [pt, [b]] = compLookupTorsion pt b := rfl
theorem compI0_aesEncrypt (text k iv : HwBytes) : compI0 aesCbcEncryptSymbol [text, k, iv] = some (compAesPerm k iv text) := rfl
theorem compI0_aesDecrypt (text k iv : HwBytes) : compI0 aesCbcDecryptSymbol [text, k, iv] = compAesDec k iv text := rfl
theorem compI0_kyberEncaps (pk e : HwBytes) : compI0 kyberEncapsSymbol [pk, e] = some (compKyberEncaps e) := rfl
theorem compI0_kyberDecaps (sk ct : HwBytes) : compI0 kyberDecapsSymbol [sk, ct] = some (compKyberDecaps ct) := rfl
theorem compI0_toEdwards (u : HwBytes) (sign : BitVec 8) : compI0 toEdwardsSymbol [u, [sign]] = some (compToEdwards u sign) := rfl
theorem compI0_torsionFree (pt : HwBytes) : compI0 torsionFreeSymbol [pt] = some (compTorsionFree pt) := rfl
theorem compI0_hmac (k d : HwBytes) : compI0 libcruxHmacSymbol [k, d] = some (compHmac k d) := rfl
theorem compPubOfOpt_length (o : Option (Fin 12)) : (compPubOfOpt o).length = 32 := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compPubOfOpt_lt_p25519 (o : Option (Fin 12)) : leValue ((compPubOfOpt o).map BitVec.toNat) < p25519 := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compPubOfOpt_not_lowOrder (o : Option (Fin 12)) : isLowOrderKey ((compPubOfOpt o).map BitVec.toNat) = false := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compPointIdx_compPubOfOpt (o : Option (Fin 12)) : compPointIdx (compPubOfOpt o) = o := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compDhByIdx_comm : ∀ i j : Fin 12, compDhByIdx i j = compDhByIdx j i := by decide
theorem compDhByIdx_length : ∀ i j : Fin 12, (compDhByIdx i j).length = 32 := by decide
theorem compDhByIdx_ne_zero : ∀ i j : Fin 12, compDhByIdx i j ≠ List.replicate 32 0#8 := by decide
theorem compDefaultDh_length : compDefaultDh.length = 32 := leBytes_length 32 _
theorem compDefaultDh_ne_zero : compDefaultDh ≠ List.replicate 32 0#8 := by decide
theorem compEkAPub_length : compEkAPub.length = 32 := leBytes_length 32 _
theorem compEkATorsion_length : compEkATorsion.length = 32 := leBytes_length 32 _
theorem compEkAPub_not_lowOrder : isLowOrderKey (compEkAPub.map BitVec.toNat) = false := by decide
theorem compEkATorsion_not_lowOrder : isLowOrderKey (compEkATorsion.map BitVec.toNat) = false := by decide
theorem compPointIdx_ekATorsion_eq_ekAPub : compPointIdx compEkATorsion = compPointIdx compEkAPub := by decide
theorem compLookupPub_length (s : HwBytes) : (compLookupPub s).length = 32 := compPubOfOpt_length (compSecretIdx s)
theorem compLookupPub_lt_p25519 (s : HwBytes) : leValue ((compLookupPub s).map BitVec.toNat) < p25519 := compPubOfOpt_lt_p25519 (compSecretIdx s)
theorem compLookupPub_not_lowOrder (s : HwBytes) : isLowOrderKey ((compLookupPub s).map BitVec.toNat) = false := compPubOfOpt_not_lowOrder (compSecretIdx s)
theorem compPointIdx_compLookupPub (s : HwBytes) : compPointIdx (compLookupPub s) = compSecretIdx s := compPointIdx_compPubOfOpt (compSecretIdx s)
theorem compLookupDh_comm (a b : HwBytes) : compLookupDh a (compLookupPub b) = compLookupDh b (compLookupPub a) := by
  unfold compLookupDh; rw [compLookupPub_not_lowOrder b, compLookupPub_not_lowOrder a]; simp only [Bool.false_eq_true, ↓reduceIte, compPointIdx_compLookupPub]
  cases compSecretIdx a <;> cases compSecretIdx b <;> simp [compDhByIdx_comm]
theorem compLookupDh_length (s p : HwBytes) : (compLookupDh s p).length = 32 := by
  unfold compLookupDh
  split
  · simp
  · cases compSecretIdx s <;> cases compPointIdx p <;>
      simp [compDhByIdx_length, compDefaultDh_length]
theorem compLookupDh_ne_zero_of_not_lowOrder (s p : HwBytes) (hlo : isLowOrderKey (p.map BitVec.toNat) = false) : compLookupDh s p ≠ List.replicate 32 0#8 := by
  unfold compLookupDh; rw [hlo]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases compSecretIdx s <;> cases compPointIdx p
  · exact compDefaultDh_ne_zero
  · exact compDefaultDh_ne_zero
  · exact compDefaultDh_ne_zero
  · next i j => exact compDhByIdx_ne_zero i j
private theorem fin8_bv_ne_one : ∀ t : Fin 8, t.val ≠ 1 → BitVec.ofNat 8 t.val ≠ 1#8 := by decide
theorem torsionShift_compI0 (p : HwBytes) (t : Fin 8) : torsionShift compI0 p t = if t.val = 1 ∧ p = compEkAPub then compEkATorsion else p := by
  unfold torsionShift; rw [compI0_torsion]; unfold compLookupTorsion
  by_cases ht1 : t.val = 1
  · have hbv : BitVec.ofNat 8 t.val = 1#8 := by rw [ht1]
    have ht0 : t ≠ 0 := by intro h; subst h; nomatch ht1
    rw [hbv]; simp only [ht1, ht0, false_or, true_and, ↓reduceIte]
    by_cases hp : p = compEkAPub
    · subst hp; simp [compEkAPub_length, compEkATorsion_length]
    · have hbeq : (p == compEkAPub) = false := beq_false_of_ne hp; simp [hp, hbeq]
  · have hbv : BitVec.ofNat 8 t.val ≠ 1#8 := fin8_bv_ne_one t ht1; simp [ht1, hbv]
theorem compLookupDh_torsionShift (s p : HwBytes) (t : Fin 8) : compLookupDh s (torsionShift compI0 p t) = compLookupDh s p := by
  rw [torsionShift_compI0]
  split
  · next h =>
    rcases h with ⟨_, rfl⟩
    unfold compLookupDh; rw [compEkATorsion_not_lowOrder, compEkAPub_not_lowOrder, compPointIdx_ekATorsion_eq_ekAPub]
  · rfl
theorem aesSwapPair_involutive (pt ct text : HwBytes) : aesSwapPair pt ct (aesSwapPair pt ct text) = text := by
  unfold aesSwapPair; cases h1 : text == pt
  · cases h2 : text == ct
    · simp [h1, h2]
    · have htc : text = ct := eq_of_beq h2; subst htc; simp
  · have htp : text = pt := eq_of_beq h1; subst htp; simp only [beq_self_eq_true, ↓reduceIte]; cases h2 : ct == text
    · simp
    · exact eq_of_beq h2
theorem xorHeadD7_involutive (text : HwBytes) : xorHeadD7 (xorHeadD7 text) = text := by
  cases text with
  | nil => rfl
  | cons b bs =>
    dsimp only [xorHeadD7]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
private def blockSwapPair (a b x : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if x == a then b else if x == b then a else x
private theorem blockSwapPair_involutive (a b x : CryptoGames.CBC.Block) :
    blockSwapPair a b (blockSwapPair a b x) = x := by
  unfold blockSwapPair; cases h1 : x == a
  · cases h2 : x == b
    · simp [h1, h2]
    · have hxb : x = b := eq_of_beq h2; subst hxb; simp
  · have hxa : x = a := eq_of_beq h1; subst hxa
    simp only [beq_self_eq_true, ↓reduceIte]
    cases h2 : b == x
    · simp
    · exact eq_of_beq h2
theorem compAesBlock_involutive (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) :
    compAesBlock k (compAesBlock k b) = b := by
  have h : ∀ (k0 k1 k2 k3 : CryptoGames.CBC.AesKey)
      (a0 b0 a1 b1 a2 b2 a3 b3 : CryptoGames.CBC.Block),
      let f := fun x =>
        if k == k0 then blockSwapPair a0 b0 x
        else if k == k1 then blockSwapPair a1 b1 x
        else if k == k2 then blockSwapPair a2 b2 x
        else if k == k3 then blockSwapPair a3 b3 x
        else x
      f (f b) = b := by
    intro k0 k1 k2 k3 a0 b0 a1 b1 a2 b2 a3 b3 f
    dsimp only [f]
    cases k == k0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · cases k == k1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · cases k == k2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · cases k == k3 <;> simp only [Bool.false_eq_true, ↓reduceIte]
          exact blockSwapPair_involutive a3 b3 b
        · exact blockSwapPair_involutive a2 b2 b
      · exact blockSwapPair_involutive a1 b1 b
    · exact blockSwapPair_involutive a0 b0 b
  exact h _ _ _ _ _ _ _ _ _ _ _ _
private theorem zero_beq_compAesAB :
    (0#128 == compAesA0) = false ∧ (0#128 == compAesB0) = false ∧
    (0#128 == compAesA1) = false ∧ (0#128 == compAesB1) = false ∧
    (0#128 == compAesA2) = false ∧ (0#128 == compAesB2) = false ∧
    (0#128 == compAesA3) = false ∧ (0#128 == compAesB3) = false := by decide
theorem compAesBlock_zero (k : CryptoGames.CBC.AesKey) : compAesBlock k 0#128 = 0#128 := by
  obtain ⟨ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3⟩ := zero_beq_compAesAB
  have h : ∀ k0 k1 k2 k3 : CryptoGames.CBC.AesKey,
      (if k == k0 then
        if 0#128 == compAesA0 then compAesB0 else if 0#128 == compAesB0 then compAesA0 else 0#128
      else if k == k1 then
        if 0#128 == compAesA1 then compAesB1 else if 0#128 == compAesB1 then compAesA1 else 0#128
      else if k == k2 then
        if 0#128 == compAesA2 then compAesB2 else if 0#128 == compAesB2 then compAesA2 else 0#128
      else if k == k3 then
        if 0#128 == compAesA3 then compAesB3 else if 0#128 == compAesB3 then compAesA3 else 0#128
      else 0#128) = 0#128 := by
    intro k0 k1 k2 k3
    simp only [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3, Bool.false_eq_true, ↓reduceIte, ite_self]
  exact h _ _ _ _
private theorem cbcEncrypt_eq (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      CryptoGames.CBC.cbcEncrypt f iv P = ByteSpecs.cbcEncrypt f iv P
  | _, 0, _ => rfl
  | iv, _ + 1, P => by
    simp only [CryptoGames.CBC.cbcEncrypt, ByteSpecs.cbcEncrypt]
    rw [cbcEncrypt_eq f (f (P.head ^^^ iv)) P.tail]
private theorem cbcDecryptBlocks_eq (g : ByteSpecs.Block → ByteSpecs.Block)
    (iv : ByteSpecs.Block) :
    ∀ (cs : List ByteSpecs.Block),
      CryptoGames.CBC.cbcDecryptBlocks g iv cs = ByteSpecs.cbcDecryptBlocks g iv cs
  | [] => rfl
  | c :: cs => by
    simp only [CryptoGames.CBC.cbcDecryptBlocks, ByteSpecs.cbcDecryptBlocks]
    rw [cbcDecryptBlocks_eq g c cs]
private theorem aesCbcEncrypt_eq_byteSpecs
    (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (p : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p =
      (ByteSpecs.cbcEncrypt (E k) iv
        (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList.flatMap
        ByteSpecs.blockToBytesLE := by
  let vp : List.Vector (BitVec 8) p.length := ⟨p, rfl⟩
  change (CryptoGames.CBC.cbcEncrypt (E k) iv (CryptoGames.CBC.pkcs7Blocks vp)).toList.flatMap
      CryptoGames.CBC.blockToBytesLE =
    (ByteSpecs.cbcEncrypt (E k) iv (ByteSpecs.pkcs7Blocks vp)).toList.flatMap
      ByteSpecs.blockToBytesLE
  have hpk : CryptoGames.CBC.pkcs7Blocks vp = ByteSpecs.pkcs7Blocks vp := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  rw [hbl]
  exact congrArg (fun v => v.toList.flatMap ByteSpecs.blockToBytesLE)
    (hpk ▸ cbcEncrypt_eq (E k) iv (ByteSpecs.pkcs7Blocks vp))
private theorem aesCbcDecrypt_eq_byteSpecs
    (D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (c : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcDecrypt D k iv c = ByteSpecs.cbcDecRaw D k iv c := by
  unfold CryptoGames.LibsignalSession.aesCbcDecrypt CryptoGames.CBC.cbcDecRaw ByteSpecs.cbcDecRaw
  have hch : CryptoGames.CBC.chunks16 c = ByteSpecs.chunks16 c := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  have hunp : CryptoGames.CBC.pkcs7Unpad = ByteSpecs.pkcs7Unpad := rfl
  rw [hch, cbcDecryptBlocks_eq, hbl, hunp]
private theorem eq_replicate_of_all_beq :
    ∀ (l : List (BitVec 8)) (x : BitVec 8),
      l.all (· == x) = true → l = List.replicate l.length x
  | [], _, _ => rfl
  | y :: ys, x, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih := eq_replicate_of_all_beq ys x h.2
    simp only [h.1, List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
    exact ih
private theorem length_cbcDecryptBlocks (g : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      (ByteSpecs.cbcDecryptBlocks g iv cs).length = cs.length
  | _, [] => rfl
  | iv, c :: cs => by simp [ByteSpecs.cbcDecryptBlocks, length_cbcDecryptBlocks g c cs]
private theorem length_flatMap_blockToBytesLE :
    ∀ (cs : List ByteSpecs.Block),
      (cs.flatMap ByteSpecs.blockToBytesLE).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
    have h16 : (ByteSpecs.blockToBytesLE c).length = 16 := by simp [ByteSpecs.blockToBytesLE]
    simp only [List.flatMap_cons, List.length_append, h16, length_flatMap_blockToBytesLE cs,
      List.length_cons]
    omega
private def cbcEncryptList (f : ByteSpecs.Block → ByteSpecs.Block) (iv : ByteSpecs.Block) :
    List ByteSpecs.Block → List ByteSpecs.Block
  | [] => []
  | b :: bs =>
    let c := f (b ^^^ iv)
    c :: cbcEncryptList f c bs
private theorem toList_cbcEncrypt (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      (ByteSpecs.cbcEncrypt f iv P).toList = cbcEncryptList f iv P.toList
  | _, 0, P => by
    cases P with
    | mk l hl =>
      cases l with
      | nil => rfl
      | cons _ _ => cases hl
  | iv, _ + 1, P => by
    simp only [ByteSpecs.cbcEncrypt, List.Vector.toList_cons]
    rw [toList_cbcEncrypt f (f (P.head ^^^ iv)) P.tail]
    cases P with
    | mk l hl =>
      cases l with
      | nil => cases hl
      | cons b bs => rfl
private theorem cbcEncryptList_cbcDecryptBlocks {f : ByteSpecs.Block → ByteSpecs.Block}
    (hinv : ∀ b, f (f b) = b) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      cbcEncryptList f iv (ByteSpecs.cbcDecryptBlocks f iv cs) = cs
  | _, [] => rfl
  | iv, c :: cs => by
    have hxor : f ((f c ^^^ iv) ^^^ iv) = c := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, hinv]
    simp only [ByteSpecs.cbcDecryptBlocks, cbcEncryptList, hxor,
      cbcEncryptList_cbcDecryptBlocks hinv c cs]
private theorem flatMap_ofFn_chunks16 (m : Nat) :
    ∀ (bs : List (BitVec 8)), bs.length = 16 * m →
      (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * i.val)).take 16)).flatMap
          ByteSpecs.blockToBytesLE = bs := by
  induction m with
  | zero =>
    intro bs h
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | succ m ih =>
    intro bs h
    rw [List.ofFn_succ, List.flatMap_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [ByteSpecs.blockToBytesLE_bytesToBlock (bs.take 16) (by rw [List.length_take, h]; omega)]
    have hrest : (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * (i.val + 1))).take 16)) =
      List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock (((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1; ext i; rw [List.drop_drop]
      have : 16 * (i.val + 1) = 16 + 16 * i.val := by omega
      rw [this]
    rw [hrest, ih (bs.drop 16) (by simp [h]; omega), List.take_append_drop]
private theorem flatMap_chunks16 (ct : List (BitVec 8)) (h : ct.length % 16 = 0) :
    (ByteSpecs.chunks16 ct).flatMap ByteSpecs.blockToBytesLE = ct := by
  unfold ByteSpecs.chunks16
  exact flatMap_ofFn_chunks16 (ct.length / 16) ct (by omega)
private theorem chunks16_pkcs7Bytes (p : List (BitVec 8)) :
    ByteSpecs.chunks16 (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)) =
      (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
  unfold ByteSpecs.chunks16 ByteSpecs.pkcs7Blocks
  rw [List.Vector.toList_ofFn]
  have hlen :
      (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).length / 16 =
        ByteSpecs.nBlocks p.length := by
    simp only [ByteSpecs.pkcs7Bytes, List.length_append, List.Vector.toList_mk,
      List.length_replicate, ByteSpecs.padLen, ByteSpecs.nBlocks]
    omega
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [hlen]
  · simp
private theorem aesCbcEncrypt_of_decrypt
    {E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block}
    (hinv : ∀ k b, E k (E k b) = b)
    (c p : List (BitVec 8)) (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block)
    (hdec : CryptoGames.LibsignalSession.aesCbcDecrypt E k iv c = some p) :
    CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p = c := by
  rw [aesCbcDecrypt_eq_byteSpecs] at hdec
  rw [aesCbcEncrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw at hdec
  split at hdec
  · cases hdec
  · rename_i hct
    push Not at hct
    obtain ⟨hcne, hmod⟩ := hct
    have hpos : 0 < c.length := List.length_pos_iff.mpr hcne
    let m := c.length / 16
    have hm1 : 1 ≤ m := by dsimp [m]; omega
    have hclen : c.length = 16 * m := by dsimp [m]; omega
    set P := ByteSpecs.cbcDecryptBlocks (E k) iv (ByteSpecs.chunks16 c)
    set bs := P.flatMap ByteSpecs.blockToBytesLE
    have hPlen : P.length = m := by
      simp [P, length_cbcDecryptBlocks, ByteSpecs.chunks16, m]
    have hbslen : bs.length = 16 * m := by
      rw [show bs = P.flatMap ByteSpecs.blockToBytesLE from rfl,
        length_flatMap_blockToBytesLE, hPlen]
    unfold ByteSpecs.pkcs7Unpad at hdec
    cases hlast : bs.getLast? with
    | none => simp [hlast] at hdec
    | some last =>
      simp only [hlast] at hdec
      split at hdec
      · cases hdec
      · rename_i hbounds
        push Not at hbounds
        obtain ⟨hn0, hn16, hnlen⟩ := hbounds
        split at hdec
        · rename_i hall
          injection hdec with hp
          have hdrop_len : (bs.drop (bs.length - last.toNat)).length = last.toNat := by
            rw [List.length_drop]; omega
          have hdrop : bs.drop (bs.length - last.toNat) =
              List.replicate last.toNat last := by
            have := eq_replicate_of_all_beq _ _ hall
            rwa [hdrop_len] at this
          have hplen : p.length = 16 * m - last.toNat := by
            rw [← hp, List.length_take, hbslen]; omega
          have hpad : ByteSpecs.padLen p.length = last.toNat := by
            unfold ByteSpecs.padLen; rw [hplen]; omega
          have hlast_eq : BitVec.ofNat 8 (ByteSpecs.padLen p.length) = last := by
            rw [hpad]; simp
          have hbs_eq : bs = ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length) := by
            calc bs = bs.take (bs.length - last.toNat) ++ bs.drop (bs.length - last.toNat) :=
                  (List.take_append_drop _ _).symm
              _ = p ++ List.replicate last.toNat last := by rw [hp, hdrop]
              _ = p ++ List.replicate (ByteSpecs.padLen p.length)
                    (BitVec.ofNat 8 (ByteSpecs.padLen p.length)) := by rw [← hpad, hlast_eq]
              _ = ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length) := rfl
          have hP_eq : P = (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
            have hch := congrArg ByteSpecs.chunks16 hbs_eq
            simpa [bs, ByteSpecs.chunks16_flatMap, chunks16_pkcs7Bytes] using hch
          have henc : (ByteSpecs.cbcEncrypt (E k) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c := by
            rw [toList_cbcEncrypt, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks (hinv k) iv (ByteSpecs.chunks16 c)
          rw [henc, flatMap_chunks16 c hmod]
        · cases hdec
theorem compAesDec_compAesPerm (k iv text : HwBytes) :
    compAesDec k iv (compAesPerm k iv text) = some text := by
  unfold compAesDec compAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
  exact ByteSpecs.cbcDecRaw_correct compAesBlock_involutive _ _
    (⟨text, rfl⟩ : ByteSpecs.Plain text.length)
theorem compAesPerm_of_compAesDec {k iv ct pt : HwBytes}
    (h : compAesDec k iv ct = some pt) :
    compAesPerm k iv pt = ct :=
  aesCbcEncrypt_of_decrypt compAesBlock_involutive ct pt _ _ h
theorem compAesPerm_injective (k iv : HwBytes) {t1 t2 : HwBytes}
    (h : compAesPerm k iv t1 = compAesPerm k iv t2) : t1 = t2 := by
  have h1 := compAesDec_compAesPerm k iv t1
  rw [h, compAesDec_compAesPerm] at h1
  exact (Option.some.inj h1).symm
theorem compAesPerm_length (k iv text : HwBytes) :
    (compAesPerm k iv text).length = 16 * (text.length / 16 + 1) := by
  unfold compAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]
  rfl
theorem compAesPerm_length_ge_16 (k iv text : HwBytes) :
    16 ≤ (compAesPerm k iv text).length := by
  rw [compAesPerm_length]; omega
theorem compAesPerm_length_of_lt_16 (k iv text : HwBytes) (h : text.length < 16) :
    (compAesPerm k iv text).length = 16 := by
  rw [compAesPerm_length, Nat.div_eq_zero_iff.mpr (Or.inr h)]
theorem compAesPerm_length_mod_16 (k iv text : HwBytes) :
    (compAesPerm k iv text).length % 16 = 0 := by
  rw [compAesPerm_length]; omega
private theorem shiftLeft8_or_assoc (acc x y : BitVec 128) (n : Nat) :
    (((acc <<< n) ||| x) <<< 8) ||| y = (acc <<< (n + 8)) ||| ((x <<< 8) ||| y) := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft]
  by_cases h8 : i < 8
  · have hlt : i < n + 8 := by omega
    simp [h8, hlt]
  · have hsub : i - 8 < n ↔ i < n + 8 := by omega
    have hidx : i - 8 - n = i - (n + 8) := by omega
    simp [h8, hsub, hidx, Bool.or_assoc]
private theorem foldr_bytesToBlock_acc :
    ∀ (l : List (BitVec 8)) (acc : BitVec 128),
      l.foldr (fun (b : BitVec 8) (a : BitVec 128) => (a <<< 8) ||| b.zeroExtend 128) acc =
        (acc <<< (8 * l.length)) |||
          l.foldr (fun (b : BitVec 8) (a : BitVec 128) => (a <<< 8) ||| b.zeroExtend 128) 0#128
  | [], acc => by simp
  | b :: bs, acc => by
    simp only [List.foldr_cons, List.length_cons]
    rw [foldr_bytesToBlock_acc bs acc, shiftLeft8_or_assoc]
    have hmul : 8 * bs.length + 8 = 8 * (bs.length + 1) := by omega
    rw [hmul]
private theorem shiftLeft_128_eq_zero (x : BitVec 128) : x <<< (8 * 16 : Nat) = 0#128 := by
  ext i hi
  have hlt : i < 8 * 16 := hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_zero, hlt, decide_true, Bool.not_true, Bool.false_and]
theorem bytesToBlock_take16 (iv : HwBytes) :
    CryptoGames.CBC.bytesToBlock (iv.take 16) = CryptoGames.CBC.bytesToBlock iv := by
  by_cases h : iv.length ≤ 16
  · rw [List.take_of_length_le h]
  · have hlen : (iv.take 16).length = 16 := by simp; omega
    conv_rhs =>
      rw [← List.take_append_drop 16 iv]
      unfold CryptoGames.CBC.bytesToBlock
      rw [List.foldr_append, foldr_bytesToBlock_acc (iv.take 16), hlen,
        shiftLeft_128_eq_zero, BitVec.zero_or]
    rfl
theorem compAesPerm_take16_iv (k iv text : HwBytes) :
    compAesPerm k (iv.take 16) text = compAesPerm k iv text := by
  unfold compAesPerm; rw [bytesToBlock_take16]
theorem compAesDec_take16_iv (k iv ct : HwBytes) :
    compAesDec k (iv.take 16) ct = compAesDec k iv ct := by
  unfold compAesDec; rw [bytesToBlock_take16]
theorem compAesPerm_pt0 : compAesPerm compAesK0 compAesIv0 compAesPt0 = compAesCt0 := by decide
theorem compAesPerm_pt1 : compAesPerm compAesK1 compAesIv1 compAesPt1 = compAesCt1 := by decide
theorem compAesPerm_pt2 : compAesPerm compAesK2 compAesIv2 compAesPt2 = compAesCt2 := by decide
theorem compAesPerm_pt3 : compAesPerm compAesK3 compAesIv3 compAesPt3 = compAesCt3 := by decide
theorem compAesPerm_pt0_of_take16 {k iv : HwBytes} (hk : k = compAesK0) (hiv : iv.take 16 = compAesIv0) :
    compAesPerm k iv compAesPt0 = compAesCt0 := by
  rw [hk, ← compAesPerm_take16_iv, hiv, compAesPerm_pt0]
theorem compAesPerm_pt1_of_take16 {k iv : HwBytes} (hk : k = compAesK1) (hiv : iv.take 16 = compAesIv1) :
    compAesPerm k iv compAesPt1 = compAesCt1 := by
  rw [hk, ← compAesPerm_take16_iv, hiv, compAesPerm_pt1]
theorem compAesPerm_pt2_of_take16 {k iv : HwBytes} (hk : k = compAesK2) (hiv : iv.take 16 = compAesIv2) :
    compAesPerm k iv compAesPt2 = compAesCt2 := by
  rw [hk, ← compAesPerm_take16_iv, hiv, compAesPerm_pt2]
theorem compAesPerm_pt3_of_take16 {k iv : HwBytes} (hk : k = compAesK3) (hiv : iv.take 16 = compAesIv3) :
    compAesPerm k iv compAesPt3 = compAesCt3 := by
  rw [hk, ← compAesPerm_take16_iv, hiv, compAesPerm_pt3]
private theorem chunks16_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ByteSpecs.chunks16 bs =
      [ByteSpecs.bytesToBlock (bs.take 16),
       ByteSpecs.bytesToBlock ((bs.drop 16).take 16),
       ByteSpecs.bytesToBlock ((bs.drop 32).take 16),
       ByteSpecs.bytesToBlock ((bs.drop 48).take 16)] := by
  unfold ByteSpecs.chunks16
  have hdiv : bs.length / 16 = 4 := by omega
  revert hdiv
  generalize bs.length / 16 = n
  rintro rfl
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Nat.mul_zero, List.drop_zero]
private theorem chunks16_fillFresh64 (t : Nat) :
    ByteSpecs.chunks16 (Symbolic.BugInjection.fillFresh t 64) =
      [ByteSpecs.bytesToBlock ((Symbolic.BugInjection.fillFresh t 64).take 16), 0#128, 0#128, 0#128] := by
  have h0 : ByteSpecs.bytesToBlock (List.replicate 16 0#8) = 0#128 := by decide
  rw [chunks16_of_length_64 rfl]
  exact congrArg (List.cons _) (by rw [← h0]; rfl)
private theorem getLast?_flatMap_four_zero (x y z : ByteSpecs.Block) :
    ([x, y, z, 0#128].flatMap ByteSpecs.blockToBytesLE).getLast? = some 0#8 := by
  have hne : ByteSpecs.blockToBytesLE 0#128 ≠ [] := by decide
  have hlast : (ByteSpecs.blockToBytesLE 0#128).getLast? = some 0#8 := by decide
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc]
  rw [List.getLast?_append_of_ne_nil _ hne, hlast]
theorem compAesDec_fillFresh64 (k iv : HwBytes) (t : Nat) :
    compAesDec k iv (Symbolic.BugInjection.fillFresh t 64) = none := by
  unfold compAesDec
  rw [aesCbcDecrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw
  have hne : ¬ (Symbolic.BugInjection.fillFresh t 64 = [] ∨
      (Symbolic.BugInjection.fillFresh t 64).length % 16 ≠ 0) := by
    simp [Symbolic.BugInjection.fillFresh]
  simp only [hne, ↓reduceIte, chunks16_fillFresh64, ByteSpecs.cbcDecryptBlocks,
    compAesBlock_zero, BitVec.xor_self]
  unfold ByteSpecs.pkcs7Unpad
  rw [getLast?_flatMap_four_zero]
  rfl
theorem compAesPerm_ne_fillFresh64 (k iv text : HwBytes) (t : Nat) :
    compAesPerm k iv text ≠ Symbolic.BugInjection.fillFresh t 64 := by
  intro h
  have hdec := compAesDec_compAesPerm k iv text
  rw [h, compAesDec_fillFresh64] at hdec
  cases hdec
theorem compDefaultHmac_length (k d : HwBytes) : (compDefaultHmac k d).length = 32 := by simp [compDefaultHmac, compTag4, compHmacMix28]
theorem compHmac_length (k d : HwBytes) : (compHmac k d).length = 32 := by
  unfold compHmac
  split
  · dsimp only
    split
    · exact leBytes_length 32 _
    · split
      · exact leBytes_length 32 _
      · split
        · exact leBytes_length 32 _
        · exact compDefaultHmac_length k d
  · exact compDefaultHmac_length k d
theorem compI0_cryptoEquationsHold : CryptoEquationsHold compI0 where
  x25519_agreement_commutes a b := by simp only [compI0_publicKey, compI0_agreement, Option.getD_some]; exact congrArg some (compLookupDh_comm a b)
  x25519_agreement_length a p := by simp [compI0_agreement, compLookupDh_length]
  x25519_public_key_length a := by simp [compI0_publicKey, compLookupPub_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [compI0_agreement]; congr 1; have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := (by simp only [isLowOrderKey, List.length_map, hb, hb']; exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu)
    have hp : compPointIdx b = compPointIdx b' := by simp only [compPointIdx, hb, hb', hu]
    unfold compLookupDh; rw [hl, hp]
  x25519_agreement_torsion_invariant secret point t := by simp only [compI0_agreement]; exact congrArg some (compLookupDh_torsionShift secret point t)
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [compI0_agreement, Option.getD_some]; cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, iff_false]; exact compLookupDh_ne_zero_of_not_lowOrder a b h
    · unfold compLookupDh; simp [h]
  x25519_public_key_not_low_order a _ := by simp [compI0_publicKey, compLookupPub_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    rw [compI0_aesEncrypt, compI0_aesDecrypt, Option.getD_some]
    exact compAesDec_compAesPerm key iv plaintext
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    rw [compI0_aesDecrypt] at h
    rw [compI0_aesEncrypt]
    exact congrArg some (compAesPerm_of_compAesDec h)
  hmac_tag_length k d t h := by rw [compI0_hmac, Option.some.injEq] at h; rw [← h]; exact compHmac_length k d
theorem compI0_pubCanonical : X25519PubCanonical compI0 := by intro s; rw [compI0_publicKey, Option.getD_some]; exact compLookupPub_lt_p25519 s
private theorem compTorsionFree_compToEdwards_ne_one_of_uCoord_ekATorsion (k : HwBytes)
    (hu : uCoord (k.map BitVec.toNat) = uCoord (compEkATorsion.map BitVec.toNat)) :
    compTorsionFree (compToEdwards k 0#8) ≠ [1#8] := by
  have h1 : k ≠ compToEdIn1 := fun h => by
    have : uCoord (compToEdIn1.map BitVec.toNat) = uCoord (compEkATorsion.map BitVec.toNat) :=
      h ▸ hu
    revert this; decide
  have h2 : k ≠ compToEdIn2 := fun h => by
    have : uCoord (compToEdIn2.map BitVec.toNat) = uCoord (compEkATorsion.map BitVec.toNat) :=
      h ▸ hu
    revert this; decide
  unfold compToEdwards
  simp only [beq_self_eq_true, ↓reduceIte, beq_false_of_ne h1, beq_false_of_ne h2]
  split <;> decide
theorem compI0_torsionShiftsRejected : X25519TorsionShiftsRejected compI0 := by
  intro s t k _ hu hne ⟨pt, _, hto, htf⟩
  rw [compI0_publicKey, Option.getD_some, torsionShift_compI0] at hu
  rw [compI0_publicKey, Option.getD_some] at hne
  split at hu
  · rw [compI0_toEdwards, Option.some.injEq] at hto
    rw [compI0_torsionFree, Option.some.injEq, ← hto] at htf
    exact compTorsionFree_compToEdwards_ne_one_of_uCoord_ekATorsion k hu htf
  · exact hne hu
theorem compI0_externContractsHoldCli : ExternContractsHoldCli compI0 :=
  ⟨compI0_cryptoEquationsHold, compI0_pubCanonical, compI0_torsionShiftsRejected⟩
private theorem compKyberCt0_length : compKyberCt0.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt1_length : compKyberCt1.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt2_length : compKyberCt2.length = 1568 := leBytes_length 1568 _
private theorem compDefaultKyberCt_length : compDefaultKyberCt.length = 1568 := List.length_replicate
private theorem compKyberSs0_length : compKyberSs0.length = 32 := leBytes_length 32 _
private theorem compKyberSs1_length : compKyberSs1.length = 32 := leBytes_length 32 _
private theorem compKyberSs2_length : compKyberSs2.length = 32 := leBytes_length 32 _
private theorem compDefaultKyberSs_length : compDefaultKyberSs.length = 32 := List.length_replicate
theorem compKyberEncaps_length (e : HwBytes) : (compKyberEncaps e).length = 1600 := by
  unfold compKyberEncaps
  repeat (first | simp only [List.length_append, compKyberCt0_length, compKyberCt1_length, compKyberCt2_length, compDefaultKyberCt_length, compKyberSs0_length, compKyberSs1_length, compKyberSs2_length, compDefaultKyberSs_length] | split)
theorem compKyberDecaps_length (ct : HwBytes) : (compKyberDecaps ct).length = 32 := by
  unfold compKyberDecaps
  repeat (first | exact compKyberSs0_length | exact compKyberSs1_length | exact compKyberSs2_length | exact compDefaultKyberSs_length | split)
theorem compToEdwards_length (u : HwBytes) (sign : BitVec 8) : (compToEdwards u sign).length = 160 := by
  unfold compToEdwards compToEdOut0 compToEdOut1 compToEdOut2
  repeat (first | exact leBytes_length 160 _ | exact List.length_replicate | split)
def compMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true
def compBcmp0 (a b : List (BitVec 8)) : BitVec 64 :=
  if a == b then 0#64 else 1#64
theorem compBcmp0_ok (a b : List (BitVec 8)) (_ : a.length = b.length) :
    (compBcmp0 a b).setWidth 32 = 0#32 ↔ a = b := by
  unfold compBcmp0
  by_cases h : a = b
  · simp [h]
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]
def compHooks0 : CliHooks where
  C :=
    { F := sha256CompressFunction compI0
      E := compAesBlock
      D := compAesBlock
      X := fun a b => ⟨compLookupDh a.toList b.toList, compLookupDh_length a.toList b.toList⟩
      pubKey := fun a => ⟨compLookupPub a.toList, compLookupPub_length a.toList⟩ }
  Q :=
    { F512 := fun st _ => st
      montToEd := fun u sign =>
        some ⟨compToEdwards u.toList sign, compToEdwards_length u.toList sign⟩
      compress := fun _ => List.Vector.replicate 32 0#8
      edNeg := fun p => p
      isTorsionFree := fun pt => decide (compTorsionFree pt.toList = [1#8])
      dsmb := fun _ A _ => A
      scalarMod := fun s => s
      scalarWide := fun w => CryptoVerification.E2E.fitVec 32 w.toList
      encaps := fun _ rand =>
        (⟨(compKyberEncaps rand.toList).take 1568, by
            rw [List.length_take, compKyberEncaps_length]; rfl⟩,
         ⟨(compKyberEncaps rand.toList).drop 1568, by
            rw [List.length_drop, compKyberEncaps_length]⟩)
      decaps := fun _ ct => ⟨compKyberDecaps ct.toList, compKyberDecaps_length ct.toList⟩
      K := compMlKem0 }
  bcmp := compBcmp0
  bcmp_ok := compBcmp0_ok
  utf8Err := fun _ => (0#64, 0#16)
theorem compI0_hooksMatch : HooksMatchInterpretation compI0 compHooks0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _; rfl
  · intro c k iv _ _; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro pk rand
    rw [compI0_kyberEncaps]
    exact congrArg some (List.take_append_drop 1568 (compKyberEncaps rand.toList)).symm
  · intro sk ct; rfl
  · intro u sign; rfl
  · intro pt
    rw [compI0_torsionFree]
    dsimp only [compHooks0]
    simp [Option.some.injEq]
private theorem compKyberCt1_beq_ct0 : (compKyberCt1 == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compKyberCt2_beq_ct0 : (compKyberCt2 == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compKyberCt2_beq_ct1 : (compKyberCt2 == compKyberCt1) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compDefaultKyberCt_beq_ct0 : (compDefaultKyberCt == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compDefaultKyberCt_beq_ct1 : (compDefaultKyberCt == compKyberCt1) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compDefaultKyberCt_beq_ct2 : (compDefaultKyberCt == compKyberCt2) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compKyberDecaps_ct0 : compKyberDecaps compKyberCt0 = compKyberSs0 := by simp [compKyberDecaps]
private theorem compKyberDecaps_ct1 : compKyberDecaps compKyberCt1 = compKyberSs1 := by simp [compKyberDecaps, compKyberCt1_beq_ct0]
private theorem compKyberDecaps_ct2 : compKyberDecaps compKyberCt2 = compKyberSs2 := by simp [compKyberDecaps, compKyberCt2_beq_ct0, compKyberCt2_beq_ct1]
private theorem compKyberDecaps_default : compKyberDecaps compDefaultKyberCt = compDefaultKyberSs := by simp [compKyberDecaps, compDefaultKyberCt_beq_ct0, compDefaultKyberCt_beq_ct1, compDefaultKyberCt_beq_ct2]
private theorem take_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).take n = l1 := by subst h; exact List.take_left
private theorem drop_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left
theorem compI0_kyberCorrectOn (r : Records) (cts : List HwBytes) : ∀ ct ∈ cts, ∀ e ss, e.length = 32 → DY.Libsignal.Composed.Refinement.kyberEncapsBytes compI0 r e = some (ct, ss) → DY.Libsignal.Composed.Refinement.kyberDecapsBytes compI0 r ct = some ss := by
  intro ct _ e ss _ he; unfold DY.Libsignal.Composed.Refinement.kyberEncapsBytes DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm at he; rw [compI0_kyberEncaps, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨hct, hss⟩ := he; unfold DY.Libsignal.Composed.Refinement.kyberDecapsBytes; rw [compI0_kyberDecaps, Option.some.injEq]; unfold compKyberEncaps at hct hss
  split at hct <;> rename_i h0
  · simp only [h0, ↓reduceIte] at hss; rw [take_append_of_eq_length compKyberCt0_length] at hct; rw [drop_append_of_eq_length compKyberCt0_length] at hss; rw [← hct, ← hss, compKyberDecaps_ct0]
  · split at hct <;> rename_i h1
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte] at hss; rw [take_append_of_eq_length compKyberCt1_length] at hct; rw [drop_append_of_eq_length compKyberCt1_length] at hss; rw [← hct, ← hss, compKyberDecaps_ct1]
    · split at hct <;> rename_i h2
      · simp only [h0, h1, h2, Bool.false_eq_true, ↓reduceIte] at hss; rw [take_append_of_eq_length compKyberCt2_length] at hct; rw [drop_append_of_eq_length compKyberCt2_length] at hss; rw [← hct, ← hss, compKyberDecaps_ct2]
      · simp only [h0, h1, h2, Bool.false_eq_true, ↓reduceIte] at hss; rw [take_append_of_eq_length compDefaultKyberCt_length] at hct; rw [drop_append_of_eq_length compDefaultKyberCt_length] at hss; rw [← hct, ← hss, compKyberDecaps_default]
theorem torsionShift_compI0_ekAPub_one : torsionShift compI0 compEkAPub 1 = compEkATorsion := by rw [torsionShift_compI0]; simp
end Symbolic.BugInjection.Proofs.Common443.CompI0Laws
