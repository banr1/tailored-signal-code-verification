/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.WIT.Pure
public import Symbolic.Proofs.SpecLemmas.ByteSpecs
public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityBase
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates
import Symbolic.Proofs.Refinement.Composed.Cli.SDet
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDir
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDirAux

/-!
# Concrete Machine-Free Witness for `cli_hndl_witness`

Constructs the concrete extern interpretation, `PEParams`, `ProtocolSetup`, `OpaqueSymbolSemantics`, `Ghost`, and 3-event
guarded CLI trace (`init`, `breakDH`, `invertDH`) for `cli_hndl_witness`. The symbolic model
explanation (`Explains`, `BrokenDH`, `AliceDone`, `HNDLPremise`) lives in `Explains.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Witness

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open CryptoVerification.E2E (PEParams)
open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (ExternCryptoLawsHold x25519AgreementSymbol x25519PublicKeySymbol
  x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol
  sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement (X25519TorsionShiftsRejected
  kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol torsionFreeSymbol)
open DY.Libsignal.Composed.Refinement (X25519PubCanonical)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli ModelAgree)
open Symbolic.Proofs.Swarm.WIT.Pure (exampleBasepoint exampleAgreement length_exampleAgreement
  witnessLength witnessInterpretation witnessInterpretation_cryptoEquationsHold
  witnessInterpretation_pubCanonical)

/-! ## Concrete Machine-Free Interpretation and Model Parameters -/

/-- Identity block cipher for the machine-free CBC witness. -/
def idBlock : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block :=
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
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [hlen]
  · simp

private theorem aesCbcEncrypt_of_decrypt_id (c p : List (BitVec 8))
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block)
    (hdec : CryptoGames.LibsignalSession.aesCbcDecrypt idBlock k iv c = some p) :
    CryptoGames.LibsignalSession.aesCbcEncrypt idBlock k iv p = c := by
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
    set P := ByteSpecs.cbcDecryptBlocks (idBlock k) iv (ByteSpecs.chunks16 c)
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
          have henc : (ByteSpecs.cbcEncrypt (idBlock k) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c := by
            change (ByteSpecs.cbcEncrypt (fun x => x) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c
            rw [toList_cbcEncrypt_id, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks_id iv (ByteSpecs.chunks16 c)
          rw [henc, flatMap_chunks16 c hmod]
        · cases hdec

/-- Concrete machine-free `ExternInterpretation`: `witnessInterpretation` equipped with
AES-256-CBC-PKCS#7 over `idBlock` and `torsionFreeSymbol` mapped to `[1#8]`. -/
def hndlInterp : ExternInterpretation := fun sym args =>
  if sym = aesCbcEncryptSymbol then
    match args with
    | [p, k, iv] =>
      some (CryptoGames.LibsignalSession.aesCbcEncrypt idBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p)
    | _ => none
  else if sym = aesCbcDecryptSymbol then
    match args with
    | [c, k, iv] =>
      CryptoGames.LibsignalSession.aesCbcDecrypt idBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c
    | _ => none
  else if sym = torsionFreeSymbol then
    some [1#8]
  else
    witnessInterpretation sym args

private theorem hndlInterp_other {s : String}
    (he : s ≠ aesCbcEncryptSymbol) (hd : s ≠ aesCbcDecryptSymbol) (htf : s ≠ torsionFreeSymbol) :
    hndlInterp s = witnessInterpretation s := by
  funext args; simp [hndlInterp, he, hd, htf]

theorem hndlInterp_cryptoEquationsHold : ExternCryptoLawsHold hndlInterp := by
  have ha : hndlInterp x25519AgreementSymbol = witnessInterpretation x25519AgreementSymbol :=
    hndlInterp_other (by decide) (by decide) (by decide)
  have hp : hndlInterp x25519PublicKeySymbol = witnessInterpretation x25519PublicKeySymbol :=
    hndlInterp_other (by decide) (by decide) (by decide)
  have ht : hndlInterp x25519TorsionSymbol = witnessInterpretation x25519TorsionSymbol :=
    hndlInterp_other (by decide) (by decide) (by decide)
  have hts : ∀ p t, torsionShift hndlInterp p t = torsionShift witnessInterpretation p t :=
    fun p t => by unfold torsionShift; rw [ht]
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
        simp only [hndlInterp, ↓reduceIte, hne, Option.getD_some,
          aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
        exact ByteSpecs.cbcDecRaw_correct (fun _ _ => rfl) _ _ (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length)
      aes_cbc_encrypt_of_decrypt := fun c k iv p _ _ hdec => by
        have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
        simp only [hndlInterp, hne, ↓reduceIte] at hdec ⊢
        exact congrArg some (aesCbcEncrypt_of_decrypt_id c p _ _ hdec)
      hmac_tag_length := fun k d tag h => by
        have hm := hndlInterp_other (s := "libcrux_hmac::hmac") (by decide) (by decide) (by decide)
        rw [hm] at h
        exact hwEq.hmac_tag_length k d tag h }

theorem hndlInterp_torsionShiftsRejected : X25519TorsionShiftsRejected hndlInterp := by
  intro s t k _hk h1 h2
  have hnone : ∀ args, hndlInterp x25519TorsionSymbol args = none := fun _ => rfl
  have hts : torsionShift hndlInterp
      ((hndlInterp x25519PublicKeySymbol [s]).getD []) t =
      (hndlInterp x25519PublicKeySymbol [s]).getD [] := by
    unfold torsionShift
    split_ifs
    · rfl
    · rw [hnone]
  rw [hts] at h1
  exact absurd h1 h2

theorem hndlInterp_contracts : ExternContractsHoldCli hndlInterp := by
  refine ⟨hndlInterp_cryptoEquationsHold, ?_, hndlInterp_torsionShiftsRejected⟩
  intro s
  rw [hndlInterp_other (by decide) (by decide) (by decide)]
  exact witnessInterpretation_pubCanonical s

def repVec (n : Nat) (x : BitVec 8) : List.Vector (BitVec 8) n :=
  ⟨List.replicate n x, List.length_replicate⟩

def hndlMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := repVec 2400 0#8
  encaps1 _ _ := some (repVec 960 0#8, repVec 2080 0#8, repVec 32 0#8)
  encaps2 _ _ := repVec 128 0#8
  decaps _ _ _ := repVec 32 0#8
  validPk _ _ := true

/-- Concrete model primitives `P : PEParams` agreeing with `hndlInterp` and accepting `0^64`
XEdDSA signatures (`isTorsionFree = true`, `montToEd = some 0^160`, `compress = 0^32`). -/
def hndlP : PEParams where
  C :=
    { F := sha256CompressFunction hndlInterp
      E := idBlock
      D := idBlock
      X := fun a b => ⟨exampleAgreement a.toList b.toList, length_exampleAgreement a.toList b.toList⟩
      pubKey := fun a =>
        ⟨exampleAgreement a.toList exampleBasepoint,
         length_exampleAgreement a.toList exampleBasepoint⟩ }
  Q :=
    { F512 := fun st _ => st
      scalarMod := fun _ => repVec 32 0#8
      scalarWide := fun _ => repVec 32 0#8
      montToEd := fun _ _ => some (repVec 160 0#8)
      isTorsionFree := fun _ => true
      edNeg := fun _ => repVec 160 0#8
      dsmb := fun _ _ _ => repVec 160 0#8
      compress := fun _ => repVec 32 0#8
      encaps := fun _ _ => (repVec 1568 0#8, repVec 32 0#8)
      decaps := fun _ _ => repVec 32 0#8
      K := hndlMlKem }

private theorem hndlInterp_of_witnessLength {s : String} {n : Nat}
    (hw : witnessLength s = some n) (htf : s ≠ torsionFreeSymbol) (args : List ByteString) :
    hndlInterp s args = some (List.replicate n 0#8) := by
  have he : s ≠ aesCbcEncryptSymbol := by rintro rfl; cases hw
  have hd : s ≠ aesCbcDecryptSymbol := by rintro rfl; cases hw
  rw [hndlInterp_other he hd htf]
  simp [witnessInterpretation, hw]

theorem hndlP_modelAgree : ModelAgree hndlInterp hndlP := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _
    simp only [hndlInterp, ↓reduceIte]
    rfl
  · intro c k iv _ _
    have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
    simp only [hndlInterp, hne, ↓reduceIte]
    rfl
  · intro a b
    rw [hndlInterp_other (by decide) (by decide) (by decide)]
    rfl
  · intro a
    rw [hndlInterp_other (by decide) (by decide) (by decide)]
    rfl
  · intro pk rand
    rw [hndlInterp_of_witnessLength (n := 1600) (by decide) (by decide)]
    dsimp only [hndlP, repVec]
    exact congrArg some (List.replicate_add 1568 32 0#8)
  · intro sk ct
    rw [hndlInterp_of_witnessLength (n := 32) (by decide) (by decide)]
    rfl
  · intro u sign
    rw [hndlInterp_of_witnessLength (n := 160) (by decide) (by decide)]
    rfl
  · intro pt
    have h1 : torsionFreeSymbol ≠ aesCbcEncryptSymbol := by decide
    have h2 : torsionFreeSymbol ≠ aesCbcDecryptSymbol := by decide
    dsimp only [hndlP]
    simp only [hndlInterp, h1, h2, ↓reduceIte, decide_true]

/-! ## Concrete `ProtocolSetup`, `OpaqueSymbolSemantics`, and `Ghost` -/

open DY.Libsignal.PQXDH.Refinement (preKeyBundleByteLength)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost ProtocolSetupWF GhostAndSemMatchSetup GhostWF
  setupTrace setupAct setupPublic setupRandomsAt secretBytes pubBytes slice ecKey kyberKey le32
  gamma gamma' concretizeAll concretizeRandom concretizeKemPk concretizeSign randTerm kyberDecapsBytes HonestBundle vec32)
open DY.Libsignal.Composed.Refinement.Cli (bundleBlob parseBundleFiles HonestBundleFiles
  BundleFilesFlat)
open CryptoVerification.E2E (PreKeyBundleFields ResponderPreKeySecrets honestBundle initiateTapeLen)
open CryptoVerification.SignalSession (publicBundleOf bundleDir filesOf)

/-- Concrete fresh-value table: `5#8^32` for runtime draws (`22 <= t`, `n = 32`), and
`[t, 0, ..., 0]` of length `n` for setup timestamps (`t < 22`). -/
def hndlFresh (t n : Nat) : HwBytes :=
  if 22 ≤ t ∧ n = 32 then List.replicate 32 5#8
  else BitVec.ofNat 8 t :: List.replicate (n - 1) 0

theorem hndlFresh_length (t n : Nat) (hn : n ≠ 0) : (hndlFresh t n).length = n := by
  unfold hndlFresh
  split_ifs with h
  · simp [h.2]
  · simp; omega

def hndlSem : OpaqueSymbolSemantics where
  init := fun _ _ => []
  chainKey := fun _ _ _ => []
  sendState := fun _ _ => []
  sendKey := fun _ _ => []
  sendMsg := fun _ _ => []
  recvState := fun _ _ => []
  recvKey := fun _ _ => []
  kemPk := fun _ => List.replicate 1568 0#8
  kemDecap := fun _ _ => List.replicate 32 0#8
  vk := fun _ => []
  sign := fun _ _ _ => List.replicate 64 0#8

def hndlGhost : Ghost where
  σ := hndlFresh
  addr := fun _ => []

def hndlRecords : ProtocolSetup where
  alice := "alice"
  bob := "bob"
  withOpk := false
  regIdA := 10#32
  regIdB := 20#32
  spkId := 1#32
  kpkId := 2#32
  opkId := 0#32
  kyberSecB := List.replicate 3169 0#8
  fresh := hndlFresh
  opaqueBytes := gamma hndlInterp hndlSem hndlGhost

unseal DY.Bytes in
private instance : DY.Bytes.SubFunction (concretizeRandom hndlGhost) (concretizeAll hndlInterp hndlSem hndlGhost) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance : DY.Bytes.SubFunction (concretizeKemPk hndlSem) (concretizeAll hndlInterp hndlSem hndlGhost) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance : DY.Bytes.SubFunction (concretizeSign hndlSem) (concretizeAll hndlInterp hndlSem hndlGhost) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem hndl_gamma_randTerm_pos (i n : Nat) (hn : n ≠ 0) :
    gamma hndlInterp hndlSem hndlGhost (randTerm i n) = hndlFresh i n := by
  unfold gamma gamma'
  conv => lhs; unfold randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom hndlGhost) (concretizeAll hndlInterp hndlSem hndlGhost)]
  simp only [concretizeRandom, hn, ite_false]
  rfl

private theorem hndl_gamma_kemPk (sk : DY.Bytes) :
    gamma hndlInterp hndlSem hndlGhost (DY.PQKem.kemPk sk) = List.replicate 1568 0#8 := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll hndlInterp hndlSem hndlGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk hndlSem) (concretizeAll hndlInterp hndlSem hndlGhost)]
  rfl

private theorem hndl_gamma_sign (sk n m : DY.Bytes) :
    gamma hndlInterp hndlSem hndlGhost (DY.Signature.sign sk n m) = List.replicate 64 0#8 := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll hndlInterp hndlSem hndlGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign hndlSem) (concretizeAll hndlInterp hndlSem hndlGhost)]
  rfl

theorem hndlRecords_ne : hndlRecords.alice ≠ hndlRecords.bob := by decide

private theorem hndlRecords_opaque_5 :
    hndlRecords.opaqueBytes (setupPublic hndlRecords 5) = List.replicate 64 0#8 := by
  rw [Symbolic.Swarm.CREF.b1_setupPublic_5 hndlRecords hndlRecords_ne]
  exact hndl_gamma_sign _ _ _

private theorem hndlRecords_opaque_6 :
    hndlRecords.opaqueBytes (setupPublic hndlRecords 6) = List.replicate 1568 0#8 := by
  rw [Symbolic.Swarm.CREF.b1_setupPublic_6 hndlRecords hndlRecords_ne]
  exact hndl_gamma_kemPk _

private theorem hndlRecords_opaque_7 :
    hndlRecords.opaqueBytes (setupPublic hndlRecords 7) = List.replicate 64 0#8 := by
  rw [Symbolic.Swarm.CREF.b1_setupPublic_7 hndlRecords hndlRecords_ne]
  exact hndl_gamma_sign _ _ _

theorem hndlRecords_wf : ProtocolSetupWF hndlRecords := by
  have hR : setupRandomsAt hndlRecords =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq hndlRecords hndlRecords_ne]
    rfl
  refine ⟨hndlRecords_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only [hndlRecords]; exact hndlFresh_length _ _ (by decide))
  · rw [hR]
    show [hndlFresh 0 32, hndlFresh 5 32, hndlFresh 10 32,
          hndlFresh 11 64, hndlFresh 16 64, hndlFresh 17 64].Nodup
    decide
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]
    rw [hndlRecords_opaque_5]; exact List.length_replicate
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]
    rw [hndlRecords_opaque_6]; exact List.length_replicate
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]
    rw [hndlRecords_opaque_7]; exact List.length_replicate
  · exact List.length_replicate
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]
    rw [hndlRecords_opaque_6]
    show slice (List.replicate 3169 0#8) 1537 1568 = List.replicate 1568 0#8
    unfold slice
    rw [List.drop_replicate, List.take_replicate]
    rfl

theorem hndlCompat : GhostAndSemMatchSetup hndlInterp hndlRecords hndlSem hndlGhost := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun ct => ?_⟩
  unfold kyberDecapsBytes
  rw [hndlInterp_of_witnessLength (n := 32) (by decide) (by decide)]
  rfl

/-! ## Concrete CLI `init` Call, `PqModelRel`, `CliTraces`, and `InvertsGuarded` -/

open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed.Refinement (clamp x25519UCoord leBytes)
open DY.Libsignal.Composed.Refinement.Cli (initDirs peerOf commonFiles CliCall CliTurn ValidCall
  InputsFor LeaksFrom CliTraces InvertsGuarded HonestDHSecret StdinBounded BobCallAllowed
  FilesVisible FilesBounded runInput runEventOf PqModelPost PqModelRel
  parseBundleFiles_publicBundleOf bundleFilesFlat_publicBundleOf InputsEquiv sdet)
open DY.Libsignal.Composed.Refinement.Cli.SDet (RegularFileList regularFileList_encodeDir
  regularFileList_bundle_files regularFileList_coins regularFileList_pqInitInputs
  filesOf_append_of_regular mem_of_filesOf_eq_some)
open CryptoGames.LibsignalSession (KeyPair initializeInitiatorSession rootCreateChain)
open CryptoGames.Ratchet (createChain)
open CryptoVerification.E2E (LocalIdentity keyPairOf modelPrims blockLevelPrims initiateInput initiateKemCoins
  initiateState pqxdhSpqrSession djbKey vecU8 u8Vec toU8 ofU8)
open CryptoVerification.SignalSession (PqParty Inputs Outcome partyDirs coinsFile pqInitInputs
  pqInitModel pqxdhExpectedOutcome encodeDir)
open Symbolic.Swarm.CREF.Cli (pubBytes_eq_keyPairOf_of_modelAgree secretBytes_1_length
  secretBytes_2_length)
open Symbolic.Swarm.CREF.Cli.Slots (aliceInitPqParty alicePqParty_aliceInitPqParty
  alicePqParty_trusts_iff encodeDir_aliceInitPqParty commonFiles_alice_bounded
  wfPq_aliceInitPqParty pqInitInputs_files_eq AliceDirState)
open Symbolic.Proofs.Swarm.WIT.Pure (exampleAgreement_of_not_low example_result
  exampleBasepoint_not_low uOf_exampleBasepoint)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvX ofU8_toU8 u8Vec_vecU8 vecU8_length)

def hndlStA0 : PqParty := aliceInitPqParty hndlInterp hndlRecords

def hndlMeB : LocalIdentity := ⟨vec32 (secretBytes hndlRecords 1), hndlRecords.regIdB⟩

def hndlKeysB : ResponderPreKeySecrets where
  spkId := hndlRecords.spkId
  spkPriv := vec32 (secretBytes hndlRecords 2)
  kpkId := hndlRecords.kpkId
  kpkPub := repVec 1568 0#8
  kpkSec := repVec 3168 0#8
  opk := none

def hndlBundleB : PreKeyBundleFields :=
  honestBundle hndlP.C hndlMeB hndlKeysB (repVec 64 0#8) (repVec 64 0#8)

def hndlTape : List.Vector (BitVec 8) initiateTapeLen :=
  repVec initiateTapeLen 5#8

private theorem hndlBundleB_idPub :
    hndlBundleB.idPub.toList = pubBytes hndlInterp (secretBytes hndlRecords 1) := by
  dsimp only [hndlBundleB, honestBundle, hndlMeB]
  rw [← pubBytes_eq_keyPairOf_of_modelAgree hndlP_modelAgree,
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ (secretBytes_1_length hndlRecords_wf)]

private theorem hndlBundleB_spkPub :
    hndlBundleB.spkPub.toList = pubBytes hndlInterp (secretBytes hndlRecords 2) := by
  dsimp only [hndlBundleB, honestBundle, hndlKeysB]
  rw [← pubBytes_eq_keyPairOf_of_modelAgree hndlP_modelAgree,
    Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ (secretBytes_2_length hndlRecords_wf)]

private theorem slice_mid {a b c : HwBytes} {off len : Nat}
    (ha : a.length = off) (hb : b.length = len) :
    slice (a ++ b ++ c) off len = b := by
  unfold slice
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]

theorem hndlBundleB_honest :
    HonestBundle hndlInterp hndlRecords (bundleBlob (publicBundleOf hndlBundleB)) := by
  intro _
  have hEq := hndlInterp_cryptoEquationsHold
  obtain ⟨_, _, _, hs5, hk6, hs7, _, _⟩ := hndlRecords_wf
  let sk := ecKey (pubBytes hndlInterp hndlRecords.spkSecBytes)
  let ss := hndlRecords.opaqueBytes hndlRecords.spkSigTerm
  let kk := kyberKey (hndlRecords.opaqueBytes hndlRecords.pqpkPubTerm)
  let ks := hndlRecords.opaqueBytes hndlRecords.pqpkSigTerm
  let ik := ecKey (pubBytes hndlInterp hndlRecords.ikBSecBytes)
  have hid : ik.length = 33 := by simp [ik, ecKey, pubBytes, hEq.x25519_public_key_length]
  have hspk : sk.length = 33 := by simp [sk, ecKey, pubBytes, hEq.x25519_public_key_length]
  have hkpk : kk.length = 1569 := by simp [kk, kyberKey, hk6]
  have hss : ss.length = 64 := hs5
  have hks : ks.length = 64 := hs7
  have hle4 : ∀ v : BitVec 32, (le32 v).length = 4 := fun v => by simp [le32]
  let p0 := le32 hndlRecords.regIdB ++ List.replicate 38 0#8 ++ le32 hndlRecords.spkId
  have hp0 : p0.length = 46 := by simp [p0, hle4]
  have hdjb_id : djbKey hndlBundleB.idPub = ik := by
    dsimp only [djbKey, ik, ecKey, DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes]
    rw [hndlBundleB_idPub]
  have hdjb_spk : djbKey hndlBundleB.spkPub = sk := by
    dsimp only [djbKey, sk, ecKey, DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes]
    rw [hndlBundleB_spkPub]
  have hkyb : CryptoVerification.E2E.kyberKey hndlBundleB.kpkPub = kk := by
    dsimp only [hndlBundleB, honestBundle, hndlKeysB, CryptoVerification.E2E.kyberKey, repVec,
      kk, kyberKey, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]
    rw [hndlRecords_opaque_6]; rfl
  have hss_eq : hndlBundleB.spkSig.toList = ss := by
    dsimp only [hndlBundleB, honestBundle, repVec, ss,
      DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]
    rw [hndlRecords_opaque_5]; rfl
  have hks_eq : hndlBundleB.kpkSig.toList = ks := by
    dsimp only [hndlBundleB, honestBundle, repVec, ks,
      DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]
    rw [hndlRecords_opaque_7]; rfl
  have hblob : bundleBlob (publicBundleOf hndlBundleB) =
      p0 ++ sk ++ ss ++ le32 hndlRecords.kpkId ++ kk ++ ks ++ ik := by
    dsimp only [bundleBlob, publicBundleOf]
    rw [show hndlBundleB.opk = none from rfl]
    dsimp only [Option.map]
    rw [hdjb_id, hdjb_spk, hkyb, hss_eq, hks_eq]
    simp only [hndlBundleB, honestBundle, hndlMeB, hndlKeysB, p0, List.append_assoc]
  rw [hblob]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using
      slice_mid (a := p0) (b := sk)
        (c := ss ++ le32 hndlRecords.kpkId ++ kk ++ ks ++ ik) hp0 hspk
  · simpa only [List.append_assoc] using
      slice_mid (a := p0 ++ sk) (b := ss)
        (c := le32 hndlRecords.kpkId ++ kk ++ ks ++ ik)
        (by rw [List.length_append, hp0, hspk]) hss
  · simpa only [List.append_assoc] using
      slice_mid (a := p0 ++ sk ++ ss ++ le32 hndlRecords.kpkId) (b := kk)
        (c := ks ++ ik)
        (by simp only [List.length_append, hp0, hspk, hss, hle4]) hkpk
  · simpa only [List.append_assoc] using
      slice_mid (a := p0 ++ sk ++ ss ++ le32 hndlRecords.kpkId ++ kk) (b := ks) (c := ik)
        (by simp only [List.length_append, hp0, hspk, hss, hle4, hkpk]) hks
  · have hlast : p0 ++ sk ++ ss ++ le32 hndlRecords.kpkId ++ kk ++ ks ++ ik =
        (p0 ++ sk ++ ss ++ le32 hndlRecords.kpkId ++ kk ++ ks) ++ ik ++ [] := by
      simp [List.append_assoc]
    rw [hlast]
    exact slice_mid (by simp only [List.length_append, hp0, hspk, hss, hle4, hkpk, hks]) hid

private theorem exampleAgreement_pub_ne_zero (a b : HwBytes) :
    exampleAgreement a (exampleAgreement b exampleBasepoint) ≠ List.replicate 32 0#8 := by
  let w₁ := 2 + (9 + DY.X25519.leValue ((clamp b).map BitVec.toNat)) % 2 ^ 200
  have hw₁ := example_result w₁ (by omega) (by omega)
  rw [exampleAgreement_of_not_low b exampleBasepoint exampleBasepoint_not_low,
    uOf_exampleBasepoint, exampleAgreement_of_not_low a (leBytes 32 w₁) hw₁.2, hw₁.1]
  let w₂ := 2 + (w₁ + DY.X25519.leValue ((clamp a).map BitVec.toNat)) % 2 ^ 200
  have hw₂ := (example_result w₂ (by omega) (by omega)).1
  intro h
  rw [h] at hw₂
  have hz : x25519UCoord (List.replicate 32 0#8) = 0 := by decide
  omega

private theorem hndlP_X (a b : List.Vector (BitVec 8) 32) :
    (hndlP.C.X a b).toList = exampleAgreement a.toList b.toList := rfl

private theorem keyPairOf_hndlP_pub_toList (v : List.Vector (BitVec 8) 32) :
    (keyPairOf hndlP.C v).publicKey.bytes.toList =
      exampleAgreement (CryptoGames.Ratchet.clampScalar v).toList exampleBasepoint := rfl

private theorem hndlP_X_keyPairOf_pub (a v : List.Vector (BitVec 8) 32) :
    (hndlP.C.X a (keyPairOf hndlP.C v).publicKey.bytes).toList =
      exampleAgreement a.toList
        (exampleAgreement (CryptoGames.Ratchet.clampScalar v).toList exampleBasepoint) := by
  rw [hndlP_X, keyPairOf_hndlP_pub_toList]

private theorem hndl_x25519_pub_ne_zero (x : List UInt8) (v : List.Vector (BitVec 8) 32) :
    ((modelPrims nvX hndlP).x25519 x (vecU8 (keyPairOf hndlP.C v).publicKey.bytes) !=
      List.replicate 32 0) = true := by
  rw [bne_iff_ne]
  dsimp only [modelPrims, blockLevelPrims]
  rw [u8Vec_vecU8]
  intro h
  have h' : ((hndlP.C.X (CryptoGames.Ratchet.clampScalar (u8Vec 32 x))
      (keyPairOf hndlP.C v).publicKey.bytes).toList) = List.replicate 32 0#8 := by
    have h1 := congrArg ofU8 h
    dsimp only [vecU8] at h1
    rw [ofU8_toU8] at h1
    exact h1.trans rfl
  rw [hndlP_X_keyPairOf_pub] at h'
  exact exampleAgreement_pub_ne_zero _ _ h'

private theorem sha512Ref_hndl (msg : List UInt8) :
    SignalPqxdh.sha512Ref (blockLevelPrims nvX hndlP) msg = SignalPqxdh.sha512InitState := by
  have hstep : ∀ blk, SignalPqxdh.sha512Step (blockLevelPrims nvX hndlP)
      SignalPqxdh.sha512InitState blk = SignalPqxdh.sha512InitState := fun _ => rfl
  have hfold : ∀ blocks : List (List UInt8),
      blocks.foldl (SignalPqxdh.sha512Step (blockLevelPrims nvX hndlP)) SignalPqxdh.sha512InitState =
        SignalPqxdh.sha512InitState := by
    intro blocks
    induction blocks with
    | nil => rfl
    | cons blk tl ih => simp only [List.foldl_cons, hstep]; exact ih
  dsimp only [SignalPqxdh.sha512Ref]
  rw [hfold]
  rfl

private theorem sigVerify_hndl_zero64 (ikPk msg : List UInt8) (hik : ikPk.length = 32) :
    (modelPrims nvX hndlP).sigVerify ikPk msg (vecU8 (repVec 64 0#8)) = true := by
  have hsig : vecU8 (repVec 64 0#8) = List.replicate 64 0 := rfl
  dsimp only [modelPrims]
  rw [hsig]
  unfold SignalPqxdh.xeddsaVerifyRef
  simp only [hik, List.length_replicate, beq_self_eq_true, Bool.true_and, sha512Ref_hndl]
  rfl

set_option maxRecDepth 8192 in
theorem hndl_pqInitModel_ok :
    ∃ st1, pqInitModel nvX hndlP hndlStA0 hndlBundleB hndlTape = some (some (st1, [])) := by
  have htrust : hndlStA0.trusts ⟨⟨hndlBundleB.idPub⟩⟩ = true :=
    (alicePqParty_trusts_iff (alicePqParty_aliceInitPqParty hndlInterp hndlRecords)
      hndlInterp_cryptoEquationsHold hndlBundleB).mpr hndlBundleB_idPub
  have hikB : (vecU8 hndlBundleB.idPub).length = 32 := vecU8_length _
  have hsig1 := sigVerify_hndl_zero64 (vecU8 hndlBundleB.idPub)
    (SignalPqxdh.encodeEC (vecU8 hndlBundleB.spkPub)) hikB
  have hsig2 := sigVerify_hndl_zero64 (vecU8 hndlBundleB.idPub)
    (SignalPqxdh.encodeKEM (vecU8 (repVec 1568 0#8))) hikB
  have hkem : (modelPrims nvX hndlP).kemEncaps (vecU8 (repVec 1568 0#8))
      (vecU8 (initiateKemCoins hndlTape)) =
      some (vecU8 (repVec 32 0#8), vecU8 (repVec 1568 0#8)) := rfl
  have hdh1 := hndl_x25519_pub_ne_zero
    (vecU8 (keyPairOf hndlP.C hndlStA0.me.idPriv).privateKey.bytes) hndlKeysB.spkPriv
  have hdh2 := hndl_x25519_pub_ne_zero (toU8 (hndlTape.toList.take 32)) hndlMeB.idPriv
  have hdh3 := hndl_x25519_pub_ne_zero (toU8 (hndlTape.toList.take 32)) hndlKeysB.spkPriv
  have hkeys : ∃ dk hdr, SignalPqxdh.Model.initiateKeys (modelPrims nvX hndlP)
      (initiateInput hndlP hndlStA0.me hndlBundleB hndlTape) = some (dk, hdr) := by
    dsimp only [initiateInput]
    rw [show hndlBundleB.opk = none from rfl,
      show hndlBundleB.kpkPub = repVec 1568 0#8 from rfl,
      show hndlBundleB.spkSig = repVec 64 0#8 from rfl,
      show hndlBundleB.kpkSig = repVec 64 0#8 from rfl]
    dsimp only [Option.map]
    unfold SignalPqxdh.Model.initiateKeys
    simp only [«guard», bind, Bind.bind, Option.bind, pure, Pure.pure, Option.map, ↓reduceIte,
      hsig1, hsig2, hkem, SignalPqxdh.dhOptNonZero]
    dsimp only [hndlBundleB, honestBundle]
    simp only [hdh1, hdh2, hdh3, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  obtain ⟨dk, hdr, hkeys_eq⟩ := hkeys
  unfold pqInitModel initiateState
  rw [htrust]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hkeys_eq]
  dsimp only
  unfold initializeInitiatorSession rootCreateChain createChain
  have hcc : (hndlP.C.X (CryptoGames.Ratchet.clampScalar
      (KeyPair.generate hndlP.C (CryptoGames.HKDF.bytesToKey32
        ((hndlTape.toList.drop 160).take 32))).privateKey.bytes) hndlBundleB.spkPub).toList ≠
      List.replicate 32 0#8 := by
    intro h
    have hspk_eq : hndlBundleB.spkPub = (keyPairOf hndlP.C hndlKeysB.spkPriv).publicKey.bytes := rfl
    rw [hspk_eq, hndlP_X_keyPairOf_pub] at h
    exact exampleAgreement_pub_ne_zero _ _ h
  simp only [bind, Except.bind, pure, Except.pure, hcc, ↓reduceIte]
  exact ⟨_, rfl⟩

def hndlCall : CliCall where
  party := hndlRecords.alice
  cmd := .init (peerOf hndlRecords hndlRecords.alice) bundleDir
  bundle := (publicBundleOf hndlBundleB).files bundleDir
  stdin := []
  coins := hndlTape.toList

def hndlInputs : Inputs :=
  pqInitInputs hndlP hndlStA0 hndlBundleB hndlTape

theorem hndlCall_runInput : runInput hndlCall = bundleBlob (publicBundleOf hndlBundleB) := by
  unfold runInput hndlCall
  dsimp only
  rw [parseBundleFiles_publicBundleOf]
  rfl

theorem hndlCall_next :
    ValidCall hndlInterp hndlRecords
      (CliTurn.init (initDirs hndlInterp hndlRecords)) hndlCall := by
  have hEq := hndlInterp_cryptoEquationsHold
  have hwf := hndlRecords_wf
  have henc : encodeDir hndlP hndlStA0 =
      commonFiles hndlInterp hndlRecords hndlRecords.alice :=
    encodeDir_aliceInitPqParty hndlP_modelAgree hEq hwf
  have hreg_base : RegularFileList (commonFiles hndlInterp hndlRecords hndlRecords.alice) := by
    rw [← henc]
    exact regularFileList_encodeDir hndlP hndlStA0
  have hdirs : (CliTurn.init (initDirs hndlInterp hndlRecords)).dirs hndlRecords.alice =
      filesOf (commonFiles hndlInterp hndlRecords hndlRecords.alice) := by
    simp [CliTurn.init, initDirs]
  have halice_dir : AliceDirState hndlInterp hndlP hndlRecords
      ((CliTurn.init (initDirs hndlInterp hndlRecords)).dirs hndlRecords.alice) hndlStA0 :=
    ⟨alicePqParty_aliceInitPqParty hndlInterp hndlRecords,
     wfPq_aliceInitPqParty hndlP_modelAgree hEq hwf,
     by rw [hdirs, henc]⟩
  have hno_sess :
      (CliTurn.init (initDirs hndlInterp hndlRecords)).records hndlRecords hndlRecords.alice =
        none := by
    rw [AliceDirState.records_eq hndlP_modelAgree hEq hwf halice_dir]
    rfl
  have hfb : FilesBounded
      ((CliTurn.init (initDirs hndlInterp hndlRecords)).dirs hndlCall.party) := by
    dsimp only [hndlCall]
    rw [hdirs]
    intro path b hb
    obtain ⟨f, hf, _, rfl⟩ := mem_of_filesOf_eq_some hreg_base hb
    exact commonFiles_alice_bounded hEq hwf f hf
  have hflat : BundleFilesFlat hndlCall.bundle :=
    bundleFilesFlat_publicBundleOf hndlBundleB
  have hhon_files : HonestBundleFiles hndlInterp hndlRecords hndlCall.bundle := by
    intro b hb
    dsimp only [hndlCall] at hb
    rw [parseBundleFiles_publicBundleOf, Option.some.injEq] at hb
    subst hb
    exact hndlBundleB_honest
  dsimp only [ValidCall, StdinBounded, BobCallAllowed]
  refine ⟨by dsimp only [hndlCall, hndlTape, repVec]; exact List.length_replicate,
    trivial, hfb, (fun h => nomatch h),
    rfl, rfl, rfl, rfl, hno_sess, hflat, hhon_files⟩

theorem hndlInputs_for :
    InputsFor hndlCall
      ((CliTurn.init (initDirs hndlInterp hndlRecords)).dirs hndlCall.party) hndlInputs := by
  have henc : encodeDir hndlP hndlStA0 =
      commonFiles hndlInterp hndlRecords hndlRecords.alice :=
    encodeDir_aliceInitPqParty hndlP_modelAgree
      hndlInterp_cryptoEquationsHold hndlRecords_wf
  have hdirs : (CliTurn.init (initDirs hndlInterp hndlRecords)).dirs hndlCall.party =
      filesOf (encodeDir hndlP hndlStA0) := by
    dsimp only [hndlCall]
    simp only [CliTurn.init, initDirs, ↓reduceIte]
    rw [henc]
  have hreg_all := regularFileList_pqInitInputs hndlP hndlStA0 hndlBundleB hndlTape
  have hreg_dir := regularFileList_encodeDir hndlP hndlStA0
  have hreg_ext : RegularFileList hndlCall.extra :=
    (regularFileList_bundle_files (publicBundleOf hndlBundleB)).append
      (regularFileList_coins hndlTape.toList)
  refine ⟨?_, rfl, rfl, ?_, fun f hf => ⟨(hreg_all f hf).1, (hreg_all f hf).2.1, ?_⟩⟩
  · dsimp only [hndlInputs, pqInitInputs, CryptoVerification.SignalSession.pqInputs,
      hndlStA0, aliceInitPqParty, hndlCall]
    rw [Symbolic.Swarm.CREF.Cli.peerOf_eq_addrE_other,
      Symbolic.Swarm.CREF.Cli.partyOf_alice]
  · intro p _
    rw [hdirs]
    dsimp only [hndlInputs]
    rw [pqInitInputs_files_eq]
    exact filesOf_append_of_regular hreg_dir hreg_ext p
  · dsimp only [hndlInputs] at hf
    rw [pqInitInputs_files_eq, henc] at hf
    have ⟨hl, hsz⟩ : (Arm64.hasLeadingSlash f.1 || Arm64.hasDotDot f.1) = false ∧
        f.2.length < 2 ^ 31 := by
      rcases List.mem_append.mp hf with hfe | hfx
      · refine ⟨?_, commonFiles_alice_bounded hndlInterp_cryptoEquationsHold hndlRecords_wf f hfe⟩
        have hp : f.1 ∈ (commonFiles hndlInterp hndlRecords hndlRecords.alice).map Prod.fst :=
          List.mem_map_of_mem hfe
        generalize f.1 = p at hp ⊢
        clear f hf hfe
        dsimp only [commonFiles, hndlRecords, List.map] at hp
        revert p hp
        decide
      · rcases List.mem_append.mp hfx with hfb | hfc
        · refine ⟨?_, (bundleFilesFlat_publicBundleOf hndlBundleB f hfb).2⟩
          have hp : f.1 ∈ ((publicBundleOf hndlBundleB).files bundleDir).map Prod.fst :=
            List.mem_map_of_mem hfb
          generalize f.1 = p at hp ⊢
          clear f hf hfx hfb
          cases hopk : hndlBundleB.opk <;>
            simp only [CryptoVerification.SignalSession.PublicBundle.files, publicBundleOf, hopk,
              Option.map, List.map_append, List.map_cons, List.map_nil] at hp <;>
            revert p hp <;> decide
        · simp only [List.mem_singleton] at hfc
          subst hfc
          exact ⟨by decide, by dsimp only; rw [List.Vector.toList_length]; decide⟩
    rw [Bool.or_eq_false_iff] at hl
    exact ⟨hl.1, hl.2, Nat.le_trans (Nat.le_of_lt hsz) (by decide)⟩

def hndlSkA : HwBytes := secretBytes hndlRecords 0
def hndlPkA : HwBytes := pubBytes hndlInterp hndlSkA

def hndlInitEv : RunEvent := runEventOf hndlCall (some (0, []))

def hndlEvs : List CliEvent :=
  [.run hndlInitEv, .env .breakDH, .env (.invertDH hndlPkA hndlSkA)]

theorem hndl_cliTraces :
    CliTraces (PqModelRel hndlInterp hndlP) hndlInterp hndlRecords
      (CliTurn.init (initDirs hndlInterp hndlRecords)) hndlEvs := by
  obtain ⟨st1, hst1⟩ := hndl_pqInitModel_ok
  let files := filesOf (hndlInputs.files ++ encodeDir hndlP st1)
  have hobs : pqxdhExpectedOutcome hndlP hndlInputs
      (pqInitModel nvX hndlP hndlStA0 hndlBundleB hndlTape) = .exited 0 [] files := by
    rw [hst1]; rfl
  have hwf0 := wfPq_aliceInitPqParty hndlP_modelAgree
    hndlInterp_cryptoEquationsHold hndlRecords_wf
  have hdraft : DY.Libsignal.Composed.Refinement.Cli.SDet.Draft.PqModelRel
      (fun _ => nvX) (fun _ => hndlP) hndlInterp hndlInputs (.exited 0 [] files) :=
    ⟨hndlStA0, hndlInputs, hwf0, InputsEquiv.refl hndlInputs,
      Or.inl ⟨hndlBundleB, hndlTape, rfl, rfl, hobs.symm⟩⟩
  have hpost : PqModelPost hndlInterp hndlP hndlInputs (.exited 0 [] files) :=
    sdet (fun _ => nvX) (fun _ => hndlP) hndlInterp hndlInputs (.exited 0 [] files) hdraft
  have hrel : PqModelRel hndlInterp hndlP hndlInputs (some (.exited 0 [] files)) :=
    Or.inr ⟨_, rfl, hpost⟩
  have hleaks : LeaksFrom hndlRecords (CliTurn.init (initDirs hndlInterp hndlRecords)) [] :=
    fun _ h => nomatch h
  exact CliTraces.step (leaks := []) hleaks hndlCall_next hndlInputs_for hrel
    (CliTraces.breakInvert trivial (CliTraces.breakInvert trivial (CliTraces.done _)))

theorem hndl_invertsGuarded : InvertsGuarded hndlInterp hndlRecords hndlEvs := by
  intro pre post e heq
  dsimp only [hndlEvs] at heq
  rcases pre with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, pre'⟩⟩⟩
  · simp at heq
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.env.injEq] at heq
    obtain ⟨_, rfl, _⟩ := heq
    trivial
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.env.injEq] at heq
    obtain ⟨rfl, rfl, rfl, _⟩ := heq
    exact ⟨List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), Or.inl (Or.inl rfl), rfl⟩
  · simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨_, _, _, hnil⟩ := heq
    nomatch (List.append_eq_nil_iff.mp hnil.symm).2

theorem hndl_has_invertDH :
    ∃ pk sk, CliEvent.env (EnvEvent.invertDH pk sk) ∈ hndlEvs :=
  ⟨hndlPkA, hndlSkA, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))⟩

end Symbolic.Proofs.Tests.Model.ExplanationTightness.CliHndlWitness.Witness
