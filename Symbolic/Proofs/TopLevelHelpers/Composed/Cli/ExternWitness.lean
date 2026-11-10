/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingProofDefs
public import Symbolic.Proofs.Swarm.WIT.Pure
public import Symbolic.Proofs.SpecLemmas.ByteSpecs

/-!
# Extern Contract and Hook Satisfiability Witness for CLI Refinement

Proves `CompExternsSatisfiableCli` by constructing `cliWitnessInterp` (realizing AES-256-CBC as
PKCS7-padded CBC over the identity block cipher and delegating all remaining extern symbols to
`witnessInterpretation`) together with a matching `CliHooks` instance `cliWitnessHooks`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction x25519AgreementSymbol
  x25519PublicKeySymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (CliHooks)
open Symbolic.Proofs.Swarm.WIT.Pure

/-! ## AES-256-CBC over identity block cipher -/

section AesCbcIdentity

def cliWitnessIdBlock : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block :=
  fun _ b => b

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

private def cbcEncryptList (iv : ByteSpecs.Block) : List ByteSpecs.Block → List ByteSpecs.Block
  | [] => []
  | b :: bs => (b ^^^ iv) :: cbcEncryptList (b ^^^ iv) bs

private theorem toList_cbcEncrypt_id :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      (ByteSpecs.cbcEncrypt (fun x => x) iv P).toList = cbcEncryptList iv P.toList
  | _, 0, P => by
    cases P with
    | mk l hl =>
      cases l with
      | nil => rfl
      | cons _ _ => cases hl
  | iv, _ + 1, P => by
    simp only [ByteSpecs.cbcEncrypt, List.Vector.toList_cons]
    rw [toList_cbcEncrypt_id (P.head ^^^ iv) P.tail]
    cases P with
    | mk l hl =>
      cases l with
      | nil => cases hl
      | cons _ _ => rfl

private theorem cbcEncryptList_cbcDecryptBlocks_id :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      cbcEncryptList iv (ByteSpecs.cbcDecryptBlocks (fun x => x) iv cs) = cs
  | _, [] => rfl
  | iv, c :: cs => by
    have hxor : (c ^^^ iv) ^^^ iv = c := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp only [ByteSpecs.cbcDecryptBlocks, cbcEncryptList, hxor,
      cbcEncryptList_cbcDecryptBlocks_id c cs]

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
  refine List.ext_getElem ?_ fun _ _ _ => ?_
  · simp [hlen]
  · simp

private theorem aesCbcEncrypt_of_decrypt_id (c p : List (BitVec 8))
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block)
    (hdec : CryptoGames.LibsignalSession.aesCbcDecrypt cliWitnessIdBlock k iv c = some p) :
    CryptoGames.LibsignalSession.aesCbcEncrypt cliWitnessIdBlock k iv p = c := by
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
    set P := ByteSpecs.cbcDecryptBlocks (cliWitnessIdBlock k) iv (ByteSpecs.chunks16 c)
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
          have henc : (ByteSpecs.cbcEncrypt (cliWitnessIdBlock k) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c := by
            change (ByteSpecs.cbcEncrypt (fun x => x) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c
            rw [toList_cbcEncrypt_id, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks_id iv (ByteSpecs.chunks16 c)
          rw [henc, flatMap_chunks16 c hmod]
        · cases hdec

end AesCbcIdentity

/-! ## Witness interpretation, hooks, and satisfiability -/

/-- Witness `ExternInterpretation` realizing AES-256-CBC via PKCS7-padded CBC over
`cliWitnessIdBlock` and delegating all other symbols to `witnessInterpretation`. -/
def cliWitnessInterp : ExternInterpretation := fun s args =>
  if s = aesCbcEncryptSymbol then
    match args with
    | [p, k, iv] =>
      some (CryptoGames.LibsignalSession.aesCbcEncrypt cliWitnessIdBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p)
    | _ => none
  else if s = aesCbcDecryptSymbol then
    match args with
    | [c, k, iv] =>
      CryptoGames.LibsignalSession.aesCbcDecrypt cliWitnessIdBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c
    | _ => none
  else witnessInterpretation s args

private theorem cliWitnessInterp_other {s : String}
    (he : s ≠ aesCbcEncryptSymbol) (hd : s ≠ aesCbcDecryptSymbol) :
    cliWitnessInterp s = witnessInterpretation s := by
  funext args; simp [cliWitnessInterp, he, hd]

private theorem cliWitnessInterp_of_witnessLength {s : String} {n : Nat}
    (hw : witnessLength s = some n) (args : List ByteString) :
    cliWitnessInterp s args = some (List.replicate n 0#8) := by
  have he : s ≠ aesCbcEncryptSymbol := by rintro rfl; cases hw
  have hd : s ≠ aesCbcDecryptSymbol := by rintro rfl; cases hw
  rw [cliWitnessInterp_other he hd]
  simp [witnessInterpretation, hw]

theorem cliWitnessInterp_total : ExternInterpretationTotalOnUsedSymbols cliWitnessInterp := by
  have rl : ∀ {s n}, witnessLength s = some n → ∀ args, ReturnsLength cliWitnessInterp s args n :=
    fun hw args => ⟨List.replicate _ 0#8, cliWitnessInterp_of_witnessLength hw args,
      List.length_replicate⟩
  exact
    ⟨fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ => by rw [cliWitnessInterp_of_witnessLength (n := 1) (by decide)]; rfl,
     fun _ _ _ _ _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ _ _ => rl (by decide) _,
     fun _ _ => by rw [cliWitnessInterp_of_witnessLength (n := 0) (by decide)]; rfl,
     fun _ _ _ _ => rl (by decide) _⟩

theorem cliWitnessInterp_cryptoEquationsHold : ExternCryptoLawsHold cliWitnessInterp := by
  have ha : cliWitnessInterp x25519AgreementSymbol = witnessInterpretation x25519AgreementSymbol :=
    cliWitnessInterp_other (by decide) (by decide)
  have hp : cliWitnessInterp x25519PublicKeySymbol = witnessInterpretation x25519PublicKeySymbol :=
    cliWitnessInterp_other (by decide) (by decide)
  have ht : cliWitnessInterp x25519TorsionSymbol = witnessInterpretation x25519TorsionSymbol :=
    cliWitnessInterp_other (by decide) (by decide)
  have hts : ∀ p t, DY.Libsignal.Refinement.torsionShift cliWitnessInterp p t =
      DY.Libsignal.Refinement.torsionShift witnessInterpretation p t := fun p t => by
    unfold DY.Libsignal.Refinement.torsionShift; rw [ht]
  have hwEq := witnessInterpretation_cryptoEquationsHold
  refine
    { x25519_agreement_commutes := fun a b => by
        simpa only [ha, hp] using hwEq.x25519_agreement_commutes a b
      x25519_agreement_length := fun a p => by
        simpa only [ha] using hwEq.x25519_agreement_length a p
      x25519_public_key_length := fun a => by
        simpa only [hp] using hwEq.x25519_public_key_length a
      x25519_agreement_reads_u_coordinate := fun a b b' hb hb' hu => by
        simpa only [ha] using hwEq.x25519_agreement_reads_u_coordinate a b b' hb hb' hu
      x25519_agreement_torsion_invariant := fun a p t => by
        simpa only [ha, hts] using hwEq.x25519_agreement_torsion_invariant a p t
      x25519_agreement_zero_iff_low_order := fun a b ha32 hb32 => by
        simpa only [ha] using hwEq.x25519_agreement_zero_iff_low_order a b ha32 hb32
      x25519_public_key_not_low_order := fun a ha32 => by
        simpa only [hp] using hwEq.x25519_public_key_not_low_order a ha32
      aes_cbc_decrypt_inverts_encrypt := fun pt k iv => by
        have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
        simp only [cliWitnessInterp, ↓reduceIte, hne, Option.getD_some,
          aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
        exact ByteSpecs.cbcDecRaw_correct (fun _ _ => rfl) _ _ (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length)
      aes_cbc_encrypt_of_decrypt := fun c k iv p _ _ hdec => by
        have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
        simp only [cliWitnessInterp, hne, ↓reduceIte] at hdec ⊢
        exact congrArg some (aesCbcEncrypt_of_decrypt_id c p _ _ hdec)
      hmac_tag_length := fun k d tag h => by
        have hm := cliWitnessInterp_other (s := "libcrux_hmac::hmac") (by decide) (by decide)
        rw [hm] at h
        exact hwEq.hmac_tag_length k d tag h }

theorem cliWitnessInterp_contracts : ExternContractsHoldCli cliWitnessInterp := by
  refine ⟨cliWitnessInterp_cryptoEquationsHold, ?_, ?_⟩
  · intro s
    rw [cliWitnessInterp_other (by decide) (by decide)]
    exact witnessInterpretation_pubCanonical s
  · rintro _ _ _ _ _ _ ⟨pt, -, -, htf⟩
    rw [cliWitnessInterp_of_witnessLength (n := 1) (by decide)] at htf
    cases htf

def cliWitnessMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true

def cliWitnessBcmp (a b : List (BitVec 8)) : BitVec 64 :=
  if a == b then 0#64 else 1#64

theorem cliWitnessBcmp_ok (a b : List (BitVec 8)) (_ : a.length = b.length) :
    (cliWitnessBcmp a b).setWidth 32 = 0#32 ↔ a = b := by
  unfold cliWitnessBcmp
  by_cases h : a = b
  · simp [h]
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-- Concrete `CliHooks` instance agreeing with `cliWitnessInterp` on all `HooksMatchInterpretation` symbols. -/
def cliWitnessHooks : CliHooks where
  C :=
    { F := sha256CompressFunction cliWitnessInterp
      E := cliWitnessIdBlock
      D := cliWitnessIdBlock
      X := fun a b => ⟨exampleAgreement a.toList b.toList, length_exampleAgreement a.toList b.toList⟩
      pubKey := fun a =>
        ⟨exampleAgreement a.toList exampleBasepoint,
         length_exampleAgreement a.toList exampleBasepoint⟩ }
  Q :=
    { F512 := fun st _ => st
      montToEd := fun _ _ => some (List.Vector.replicate 160 0#8)
      compress := fun _ => List.Vector.replicate 32 0#8
      edNeg := fun p => p
      isTorsionFree := fun _ => false
      dsmb := fun _ A _ => A
      scalarMod := fun s => s
      scalarWide := fun w => CryptoVerification.E2E.fitVec 32 w.toList
      encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
      decaps := fun _ _ => List.Vector.replicate 32 0#8
      K := cliWitnessMlKem }
  bcmp := cliWitnessBcmp
  bcmp_ok := cliWitnessBcmp_ok
  utf8Err := fun _ => (0#64, 0#16)

private theorem toList_vector_replicate (n : Nat) (x : BitVec 8) :
    (List.Vector.replicate n x).toList = List.replicate n x := rfl

theorem cliWitnessHooks_agree : HooksMatchInterpretation cliWitnessInterp cliWitnessHooks := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _
    simp only [cliWitnessInterp, ↓reduceIte]
    rfl
  · intro c k iv _ _
    have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
    simp only [cliWitnessInterp, hne, ↓reduceIte]
    rfl
  · intro a b
    rw [cliWitnessInterp_other (by decide) (by decide),
      witnessInterpretation_of_none (by decide)]
    rfl
  · intro a
    rw [cliWitnessInterp_other (by decide) (by decide),
      witnessInterpretation_of_none (by decide)]
    rfl
  · intro pk rand
    rw [cliWitnessInterp_of_witnessLength (n := 1600) (by decide)]
    dsimp only [cliWitnessHooks]
    rw [toList_vector_replicate, toList_vector_replicate, ← List.replicate_add]
  · intro sk ct
    rw [cliWitnessInterp_of_witnessLength (n := 32) (by decide)]
    rfl
  · intro u sign
    rw [cliWitnessInterp_of_witnessLength (n := 160) (by decide)]
    rfl
  · intro pt
    rw [cliWitnessInterp_of_witnessLength (n := 1) (by decide)]
    dsimp only [cliWitnessHooks]
    decide

/-- Satisfiability of the CLI protocol extern contracts and hooks (`CompExternsSatisfiableCli`). -/
theorem comp_externsSatisfiable_cli : CompExternsSatisfiableCli :=
  ⟨cliWitnessInterp, cliWitnessHooks, cliWitnessInterp_total, cliWitnessInterp_contracts,
   cliWitnessHooks_agree⟩

theorem comp_externsSatisfiable_cli_proof : CompExternsSatisfiableCli :=
  comp_externsSatisfiable_cli

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_externsSatisfiable_cli_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms comp_externsSatisfiable_cli_proof

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli
