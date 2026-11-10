/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed
public import Symbolic.Proofs.SpecLemmas.ElfBindingProofDefs
public import Symbolic.Proofs.Swarm.WIT.Pure
public import Symbolic.Proofs.SpecLemmas.ByteSpecs
public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
import Init.Data.Repr
import Init.Data.String.Defs
import Symbolic.Proofs.Swarm.CREF.Sem
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates
import Symbolic.Proofs.Swarm.CREF.Cli.DirCodecBridge
import Symbolic.Proofs.Tests.Refinement.Cli.FilesVisibleTest -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredElfBinding -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Non-Vacuity and Witness Tests for `Composed/Cli/`

Constructs a concrete witness interpretation `cliWitnessInterp` and hooks `cliWitnessHooks`
proving `CompExternsSatisfiableCli`, provides directory and bundle helpers (`CliFilePath`,
`filesOf_append_or`, `inputsFor_of_cliFilePaths`, `filesBounded_of_cliFilePaths`,
`honestPublicBundle`), and proves satisfiability of `ValidCall` and `CliTracesMoves` from
`CliTurn.init (initDirs ...)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli

open DY
open Arm64 (FsPath FsState normalizePath)
open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction x25519AgreementSymbol
  x25519PublicKeySymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol
  torsionFreeSymbol X25519TorsionShiftsRejected preKeyBundleByteLength)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (Inputs Outcome PublicBundle CliHooks filesOf fsView
  stdioPaths partyDirs bundleDir coinsFile addressFile identityKeyPairFile registrationIdFile
  identityFile sessionFile signedPreKeyFile oneTimePreKeyFile lastResortKyberPreKeyFile
  baseKeysFile fileOfEntry SameFiles filesFold dirsFold NoFiles initFsState_entries)
open Symbolic.Proofs.Swarm.WIT.Pure

/-! ## AES-256-CBC over the Identity Block Cipher -/

section AesCbcIdentity

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
      | cons b bs => rfl

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

end AesCbcIdentity

/-! ## Witness Interpretation and Hooks (`CompExternsSatisfiableCli`) -/

def cliWitnessInterp : ExternInterpretation := fun s args =>
  if s = aesCbcEncryptSymbol then
    match args with
    | [p, k, iv] =>
      some (CryptoGames.LibsignalSession.aesCbcEncrypt idBlock
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p)
    | _ => none
  else if s = aesCbcDecryptSymbol then
    match args with
    | [c, k, iv] =>
      CryptoGames.LibsignalSession.aesCbcDecrypt idBlock
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

def cliWitnessHooks : CliHooks where
  C :=
    { F := sha256CompressFunction cliWitnessInterp
      E := idBlock
      D := idBlock
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

/-- `CompExternsSatisfiableCli` holds, witnessed by `cliWitnessInterp` and `cliWitnessHooks`. -/
theorem comp_externsSatisfiable_cli_test : CompExternsSatisfiableCli :=
  ⟨cliWitnessInterp, cliWitnessHooks, cliWitnessInterp_total, cliWitnessInterp_contracts,
   cliWitnessHooks_agree⟩

/-! ## Pointwise `filesOf` Overlay and Boundedness Helpers -/

def cliParentDirs : List String :=
  ["bundle", "identities", "sessions", "signed-pre-keys", "one-time-pre-keys",
   "one-time-kyber-pre-keys", "last-resort-kyber-pre-keys"]

def CliFilePath (p : String) : Prop :=
  (normalizePath p).isEmpty = false ∧
  (∀ d ∈ cliParentDirs, normalizePath p ≠ [d]) ∧
  (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast,
    ∃ d ∈ cliParentDirs, pref = [d]) ∧
  normalizePath p ∉ stdioPaths.map normalizePath ∧
  Arm64.hasLeadingSlash p = false ∧
  Arm64.hasDotDot p = false

instance (p : String) : Decidable (CliFilePath p) := by
  unfold CliFilePath; infer_instance

private def NoCliDirFiles (a : FsState) : Prop :=
  ∀ d ∈ cliParentDirs, fileOfEntry (a.entries [d]) = none

private theorem foldl_cliAnc_keep {a : FsState} {prefs : List FsPath}
    (ha : NoCliDirFiles a)
    (hp : ∀ pref ∈ prefs, ∃ d ∈ cliParentDirs, pref = [d]) :
    NoCliDirFiles (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) a) ∧
    SameFiles (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) a) a := by
  induction prefs generalizing a with
  | nil => exact ⟨ha, fun _ => rfl⟩
  | cons pref rest ih =>
    obtain ⟨d, hd, rfl⟩ := hp pref (List.mem_cons_self ..)
    have ha' : NoCliDirFiles (a.setEntry [d] (some .dir)) := by
      intro d' hd'
      simp only [FsState.setEntry]
      split
      · rfl
      · exact ha d' hd'
    have hs' : SameFiles (a.setEntry [d] (some .dir)) a := by
      intro q
      simp only [FsState.setEntry]
      split
      · rename_i heq
        rw [beq_iff_eq] at heq
        subst heq
        exact (ha d hd).symm
      · rfl
    obtain ⟨h1, h2⟩ := ih ha' (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
    exact ⟨h1, fun q => (h2 q).trans (hs' q)⟩

def cliStepAt (q : FsPath) (v : Option HwBytes) (x : String × HwBytes) : Option HwBytes :=
  if q = normalizePath x.1 then some x.2 else v

def cliEvalAt (q : FsPath) (v : Option HwBytes) (l : List (String × HwBytes)) : Option HwBytes :=
  l.foldl (cliStepAt q) v

private theorem filesFold_cliEvalAt :
    ∀ (l : List (String × HwBytes)) (a : FsState),
      (∀ x ∈ l, CliFilePath x.1) → NoCliDirFiles a →
      ∀ q, fileOfEntry ((filesFold l a).entries q) = cliEvalAt q (fileOfEntry (a.entries q)) l
  | [], a, _, _, _ => rfl
  | (p, bs) :: rest, a, hl, ha, q => by
    obtain ⟨_, hnotd, hanc, _⟩ := hl (p, bs) (List.mem_cons_self ..)
    dsimp only at hnotd hanc
    let a1 := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) a
    obtain ⟨ha1, hs1⟩ := foldl_cliAnc_keep ha hanc
    let a2 := a1.setFile p (some (.file bs))
    have ha2_eq : a2 = a1.setEntry (normalizePath p) (some (.file bs)) := by
      simp [a2, FsState.setFile]
    have ha2 : NoCliDirFiles a2 := by
      intro d hd
      rw [ha2_eq]
      simp only [FsState.setEntry]
      split
      · rename_i heq
        rw [beq_iff_eq] at heq
        exact absurd heq.symm (hnotd d hd)
      · exact ha1 d hd
    have hstep_q : fileOfEntry (a2.entries q) = cliStepAt q (fileOfEntry (a.entries q)) (p, bs) := by
      rw [ha2_eq]
      simp only [FsState.setEntry, cliStepAt]
      split
      · rename_i hbq
        have hq : q = normalizePath p := beq_iff_eq.mp hbq
        simp [hq, fileOfEntry]
      · rename_i hbq
        have hq : q ≠ normalizePath p := fun h => hbq (beq_iff_eq.mpr h)
        simp only [hq, ↓reduceIte]
        exact hs1 q
    have ih := filesFold_cliEvalAt rest a2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ha2 q
    simpa [filesFold, cliEvalAt, hstep_q] using ih

theorem cliFilesOf_eq_evalAt {l : List (String × HwBytes)}
    (hl : ∀ x ∈ l, CliFilePath x.1) (p : String) :
    filesOf l p =
      if normalizePath p ∈ stdioPaths.map normalizePath then none
      else if (normalizePath p).isEmpty then none
      else cliEvalAt (normalizePath p) none l := by
  unfold filesOf fsView
  split
  · rfl
  · rename_i hstdio
    show fileOfEntry ((Arm64.Process.initFsState { files := l }).files p) = _
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [initFsState_entries { files := l } (normalizePath p) hstdio]
      have hdir : dirsFold [] ({} : FsState) = {} := rfl
      rw [hdir]
      have hnd : NoCliDirFiles ({} : FsState) := fun d _ => NoFiles.base [d]
      rw [filesFold_cliEvalAt l {} hl hnd (normalizePath p), NoFiles.base (normalizePath p)]

private theorem option_or_assoc {α : Type} (a b c : Option α) :
    (a.or b).or c = a.or (b.or c) := by
  cases a <;> cases b <;> rfl

theorem cliEvalAt_or (q : FsPath) :
    ∀ (l2 : List (String × HwBytes)) (v1 : Option HwBytes),
      cliEvalAt q v1 l2 = (cliEvalAt q none l2).or v1
  | [], _ => rfl
  | x :: xs, v1 => by
    have hstep : cliStepAt q v1 x = (cliStepAt q none x).or v1 := by
      unfold cliStepAt; split <;> rfl
    change cliEvalAt q (cliStepAt q v1 x) xs = (cliEvalAt q (cliStepAt q none x) xs).or v1
    rw [cliEvalAt_or q xs (cliStepAt q v1 x), cliEvalAt_or q xs (cliStepAt q none x),
      option_or_assoc, hstep]

theorem filesOf_append_or {l1 l2 : List (String × HwBytes)}
    (hl1 : ∀ x ∈ l1, CliFilePath x.1) (hl2 : ∀ x ∈ l2, CliFilePath x.1) (p : String) :
    filesOf (l1 ++ l2) p = (filesOf l2 p).or (filesOf l1 p) := by
  have hall : ∀ x ∈ l1 ++ l2, CliFilePath x.1 := fun x hx => by
    rcases List.mem_append.mp hx with h1 | h2
    · exact hl1 x h1
    · exact hl2 x h2
  rw [cliFilesOf_eq_evalAt hall, cliFilesOf_eq_evalAt hl2, cliFilesOf_eq_evalAt hl1]
  split
  · rfl
  · split
    · rfl
    · simp only [cliEvalAt, List.foldl_append]
      exact cliEvalAt_or (normalizePath p) l2 (cliEvalAt (normalizePath p) none l1)

theorem cliEvalAt_idle {q : FsPath} :
    ∀ {l : List (String × HwBytes)}, (∀ x ∈ l, normalizePath x.1 ≠ q) →
      ∀ (v : Option HwBytes), cliEvalAt q v l = v
  | [], _, v => rfl
  | x :: xs, h, v => by
    have hx : (q = normalizePath x.1) = False :=
      eq_false (fun he => h x (List.mem_cons_self ..) he.symm)
    simp only [cliEvalAt, List.foldl_cons, cliStepAt, hx, ↓reduceIte]
    exact cliEvalAt_idle (fun y hy => h y (List.mem_cons_of_mem _ hy)) v

private theorem cliEvalAt_mem_of_some {q : FsPath} :
    ∀ {l : List (String × HwBytes)} {v : Option HwBytes} {b : HwBytes},
      cliEvalAt q v l = some b → (v = some b) ∨ (∃ x ∈ l, x.2 = b)
  | [], _, _, h => Or.inl h
  | x :: xs, v, b, h => by
    simp only [cliEvalAt, List.foldl_cons] at h
    rcases cliEvalAt_mem_of_some h with hv | ⟨y, hy, rfl⟩
    · unfold cliStepAt at hv
      split at hv
      · injection hv with hb; exact Or.inr ⟨x, List.mem_cons_self .., hb⟩
      · exact Or.inl hv
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

theorem filesBounded_of_cliFilePaths {l : List (String × HwBytes)}
    (hl : ∀ x ∈ l, CliFilePath x.1) (hb : ∀ x ∈ l, x.2.length < 2 ^ 31) :
    FilesBounded (filesOf l) := by
  intro path b hp
  rw [cliFilesOf_eq_evalAt hl] at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · rcases cliEvalAt_mem_of_some hp with hnone | ⟨x, hx, rfl⟩
      · cases hnone
      · exact hb x hx

theorem bundleFiles_cliFilePath (b : PublicBundle) :
    ∀ x ∈ b.files bundleDir, CliFilePath x.1 := by
  intro x hx
  simp only [PublicBundle.files, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | hot
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases hot' : b.oneTime with
    | none => simp [hot'] at hot
    | some ik =>
      simp only [hot', List.mem_singleton] at hot
      subst hot; dsimp only; decide

theorem extra_cliFilePath (c : CliCall) (hb : ∀ x ∈ c.bundle, CliFilePath x.1) :
    ∀ x ∈ c.extra, CliFilePath x.1 := by
  intro x hx
  simp only [CliCall.extra, List.mem_append, List.mem_singleton] at hx
  rcases hx with h1 | rfl
  · exact hb x h1
  · dsimp only; decide

theorem filesVisible_of_cliFilePaths {l : List (String × HwBytes)}
    (hl : ∀ x ∈ l, CliFilePath x.1)
    (hlen : ∀ x ∈ l, x.2.length ≤ Arm64.MAX_LFS_FILESIZE) : FilesVisible l := by
  intro f hf
  obtain ⟨hne, _, _, hstdio, hsl, hdd⟩ := hl f hf
  refine ⟨?_, hstdio, hsl, hdd, hlen f hf⟩
  intro hempty
  simp [hempty] at hne

theorem inputsFor_of_cliFilePaths (c : CliCall) (base : List (String × HwBytes))
    (hbase : ∀ x ∈ base, CliFilePath x.1)
    (hbundle : ∀ x ∈ c.bundle, CliFilePath x.1)
    (hbase_len : ∀ x ∈ base, x.2.length < 2 ^ 31)
    (hbundle_len : ∀ x ∈ c.bundle, x.2.length < 2 ^ 31)
    (hcoins_len : c.coins.length < 2 ^ 31) :
    InputsFor c (filesOf base)
      { argv := c.cmd.argv
        dirs := partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => [])
        files := base ++ c.extra
        stdin := c.stdin } := by
  have hextra : ∀ x ∈ c.extra, CliFilePath x.1 :=
    extra_cliFilePath c hbundle
  have hall : ∀ x ∈ base ++ c.extra, CliFilePath x.1 := fun x hx => by
    rcases List.mem_append.mp hx with h1 | h2
    · exact hbase x h1
    · exact hextra x h2
  have hmax : 2 ^ 31 ≤ Arm64.MAX_LFS_FILESIZE := by decide
  have hall_len : ∀ x ∈ base ++ c.extra, x.2.length ≤ Arm64.MAX_LFS_FILESIZE := fun x hx => by
    have hlt : x.2.length < 2 ^ 31 := by
      rcases List.mem_append.mp hx with h1 | h2
      · exact hbase_len x h1
      · simp only [CliCall.extra, List.mem_append, List.mem_singleton] at h2
        rcases h2 with hb | rfl
        · exact hbundle_len x hb
        · exact hcoins_len
    exact Nat.le_trans (Nat.le_of_lt hlt) hmax
  refine ⟨rfl, rfl, rfl, fun p _ => ?_, filesVisible_of_cliFilePaths hall hall_len⟩
  exact filesOf_append_or hbase hextra p

/-! ## `SamePath`, `scrub`, and `clearSession` Lemmas -/

theorem scrub_dot_coins (d : DirectorySnapshot) : scrub d "./coins" = none := rfl

theorem scrub_dot_bundle (d : DirectorySnapshot) : scrub d "./bundle/identity-key" = none := rfl

theorem scrub_filesOf_eq {base extra : List (String × HwBytes)}
    (hbase : ∀ x ∈ base, CliFilePath x.1)
    (hextra : ∀ x ∈ extra, CliFilePath x.1)
    (hno : ∀ x ∈ base, normalizePath x.1 ≠ [coinsFile] ∧
      (normalizePath x.1).head? ≠ some bundleDir)
    (honly : ∀ x ∈ extra, normalizePath x.1 = [coinsFile] ∨
      (normalizePath x.1).head? = some bundleDir) :
    scrub (filesOf (base ++ extra)) = filesOf base := by
  have hcoins : normalizePath coinsFile = [coinsFile] := by decide
  funext p
  unfold scrub
  by_cases hcond : (SamePath p coinsFile || (normalizePath p).head? == some bundleDir) = true
  · simp only [hcond, ↓reduceIte]
    symm
    rw [cliFilesOf_eq_evalAt hbase]
    split
    · rfl
    · split
      · rfl
      · apply cliEvalAt_idle
        intro x hx heq
        simp only [Bool.or_eq_true, SamePath, beq_iff_eq, hcoins] at hcond
        rcases hcond with hp1 | hp2
        · exact (hno x hx).1 (heq.trans hp1)
        · exact (hno x hx).2 (heq ▸ hp2)
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, filesOf_append_or hbase hextra p]
    have hex_none : filesOf extra p = none := by
      rw [cliFilesOf_eq_evalAt hextra]
      split
      · rfl
      · split
        · rfl
        · apply cliEvalAt_idle
          intro x hx heq
          simp only [Bool.or_eq_false_iff, SamePath, beq_eq_false_iff_ne, hcoins] at hcond
          rcases honly x hx with hx1 | hx2
          · exact hcond.1 (heq.symm.trans hx1)
          · exact hcond.2 (heq ▸ hx2)
    simp [hex_none]

theorem clearSession_filesOf_eq {r : ProtocolSetup} {p : Participant}
    {base : List (String × HwBytes)} {sPath : String} {recBytes : HwBytes}
    (hbase : ∀ x ∈ base, CliFilePath x.1)
    (hs_fp : CliFilePath sPath)
    (hno : ∀ x ∈ base, normalizePath x.1 ≠ normalizePath (sessionPathOf r p))
    (hs : SamePath sPath (sessionPathOf r p) = true)
    (other : Participant → DirectorySnapshot) (sent : List HwBytes) (bobOff : Bool) :
    (({ dirs := fun q => if q = p then filesOf (base ++ [(sPath, recBytes)]) else other q
        sent := sent
        bobOff := bobOff } : CliTurn).clearSession r p).dirs p = filesOf base := by
  have hsingle : ∀ x ∈ [(sPath, recBytes)], CliFilePath x.1 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hs_fp
  have hnorm_s : normalizePath sPath = normalizePath (sessionPathOf r p) := by
    simpa [SamePath, beq_iff_eq] using hs
  funext path
  simp only [CliTurn.clearSession, ↓reduceIte]
  by_cases hsp : SamePath path (sessionPathOf r p) = true
  · simp only [hsp, ↓reduceIte]
    symm
    rw [cliFilesOf_eq_evalAt hbase]
    split
    · rfl
    · split
      · rfl
      · apply cliEvalAt_idle
        intro x hx heq
        have hp_eq : normalizePath path = normalizePath (sessionPathOf r p) := by
          simpa [SamePath, beq_iff_eq] using hsp
        exact hno x hx (heq.trans hp_eq)
  · simp only [Bool.not_eq_true] at hsp
    simp only [hsp, Bool.false_eq_true, ↓reduceIte]
    have hnone : filesOf [(sPath, recBytes)] path = none := by
      rw [cliFilesOf_eq_evalAt hsingle]
      split
      · rfl
      · split
        · rfl
        · apply cliEvalAt_idle
          intro x hx heq
          simp only [List.mem_singleton] at hx; subst hx
          have hp_ne : normalizePath path ≠ normalizePath (sessionPathOf r p) := by
            simpa [SamePath, beq_eq_false_iff_ne] using hsp
          exact hp_ne (heq.symm.trans hnorm_s)
    rw [filesOf_append_or hbase hsingle path, hnone]
    rfl

/-! ## `HonestBundleDir` Builder and `CliTracesMoves` Satisfiability -/

def honestPublicBundle (interp : ExternInterpretation) (r : ProtocolSetup) : PublicBundle where
  registrationId := r.regIdB
  identityKey := ecKey (pubBytes interp (secretBytes r 1))
  signedId := r.spkId
  signedKey := ecKey (pubBytes interp (secretBytes r 2))
  signedSig := r.opaqueBytes (setupPublic r 5)
  kyberId := r.kpkId
  kyberKey := kyberKey (r.opaqueBytes (setupPublic r 6))
  kyberSig := r.opaqueBytes (setupPublic r 7)
  oneTime := none

private theorem slice_mid {a b c : HwBytes} {off len : Nat}
    (ha : a.length = off) (hb : b.length = len) :
    slice (a ++ b ++ c) off len = b := by
  unfold slice
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]

theorem honestBundleDir_honestPublicBundle {interp : ExternInterpretation} {r : ProtocolSetup}
    (hEq : ExternCryptoLawsHold interp) (hr : ProtocolSetupWF r) :
    HonestBundleDir interp r (honestPublicBundle interp r) := by
  obtain ⟨_, _, _, hs5, hk6, hs7, _, _⟩ := hr
  let sk := ecKey (pubBytes interp r.spkSecBytes)
  let ss := r.opaqueBytes r.spkSigTerm
  let kk := kyberKey (r.opaqueBytes r.pqpkPubTerm)
  let ks := r.opaqueBytes r.pqpkSigTerm
  let ik := ecKey (pubBytes interp r.ikBSecBytes)
  have hid : ik.length = 33 := by simp [ik, ecKey, pubBytes, hEq.x25519_public_key_length]
  have hspk : sk.length = 33 := by simp [sk, ecKey, pubBytes, hEq.x25519_public_key_length]
  have hkpk : kk.length = 1569 := by simp [kk, kyberKey, hk6]
  have hss : ss.length = 64 := hs5
  have hks : ks.length = 64 := hs7
  have hle4 : ∀ v : BitVec 32, (le32 v).length = 4 := fun v => by simp [le32]
  refine ⟨⟨hid, rfl, hspk, rfl, hss, hkpk, rfl, hks, fun _ _ h => by cases h⟩, fun _ => ?_⟩
  let p0 := le32 r.regIdB ++ List.replicate 38 0#8 ++ le32 r.spkId
  have hp0 : p0.length = 46 := by simp [p0, hle4]
  have hblob : bundleBlob (honestPublicBundle interp r) =
      p0 ++ sk ++ ss ++ le32 r.kpkId ++ kk ++ ks ++ ik := by
    simp [bundleBlob, honestPublicBundle, p0, sk, ss, kk, ks, ik, List.append_assoc,
      ProtocolSetup.ikBSecBytes, ProtocolSetup.spkSecBytes, ProtocolSetup.spkSigTerm,
      ProtocolSetup.pqpkPubTerm, ProtocolSetup.pqpkSigTerm]
  rw [hblob]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using
      slice_mid (a := p0) (b := sk)
        (c := ss ++ le32 r.kpkId ++ kk ++ ks ++ ik) hp0 hspk
  · simpa only [List.append_assoc] using
      slice_mid (a := p0 ++ sk) (b := ss)
        (c := le32 r.kpkId ++ kk ++ ks ++ ik)
        (by rw [List.length_append, hp0, hspk]) hss
  · simpa only [List.append_assoc] using
      slice_mid (a := p0 ++ sk ++ ss ++ le32 r.kpkId) (b := kk)
        (c := ks ++ ik)
        (by simp only [List.length_append, hp0, hspk, hss, hle4]) hkpk
  · simpa only [List.append_assoc] using
      slice_mid (a := p0 ++ sk ++ ss ++ le32 r.kpkId ++ kk) (b := ks) (c := ik)
        (by simp only [List.length_append, hp0, hspk, hss, hle4, hkpk]) hks
  · have hlast : p0 ++ sk ++ ss ++ le32 r.kpkId ++ kk ++ ks ++ ik =
        (p0 ++ sk ++ ss ++ le32 r.kpkId ++ kk ++ ks) ++ ik ++ [] := by
      simp [List.append_assoc]
    rw [hlast]
    exact slice_mid (by simp only [List.length_append, hp0, hspk, hss, hle4, hkpk, hks]) hid

/-! ## `textBytes`, `RecordCodecs`, `compFits`, and `filesOf` Helpers -/

private theorem drop_getElem_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) (h : i < xs.length), xs[i]'h :: xs.drop (i + 1) = xs.drop i
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, h => drop_getElem_cons xs i (Nat.lt_of_succ_lt_succ h)

private theorem drop_of_le {α : Type} :
    ∀ (xs : List α) (i : Nat), xs.length ≤ i → xs.drop i = []
  | [], _, _ => by simp
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, i + 1, h => drop_of_le xs i (Nat.le_of_succ_le_succ h)

private theorem byteArray_loop_eq (arr : Array UInt8) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop ⟨arr⟩ i r = r.reverse ++ arr.toList.drop i := by
  unfold ByteArray.toList.loop
  split
  · next h =>
    have hi : i < arr.size := h
    have his : i < arr.toList.length := by simpa using hi
    have hget : (ByteArray.mk arr).get! i = arr.toList[i]'his := by
      simp [ByteArray.get!, getElem!_pos arr i hi]
    rw [byteArray_loop_eq arr (i + 1) ((ByteArray.mk arr).get! i :: r), hget,
      List.reverse_cons, List.append_assoc, List.singleton_append, drop_getElem_cons arr.toList i his]
  · next h =>
    have hi : arr.toList.length ≤ i := by
      have : ¬ i < arr.size := h
      simp at *; omega
    rw [drop_of_le arr.toList i hi, List.append_nil]
termination_by arr.size - i
decreasing_by
  have : i < arr.size := ‹_›
  omega

private theorem toList_toByteArray_eq (l : List UInt8) : l.toByteArray.toList = l := by
  unfold ByteArray.toList
  have h1 : l.toByteArray = ⟨l.toArray⟩ := by
    ext1
    exact List.data_toByteArray
  rw [h1, byteArray_loop_eq]
  simp

theorem textBytes_eq_flatMap (s : String) :
    DY.Libsignal.Composed.Refinement.Cli.textBytes s =
      (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  have hs : String.ofList s.toList = s := by simp
  conv_lhs => rw [← hs]
  unfold DY.Libsignal.Composed.Refinement.Cli.textBytes
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode, toList_toByteArray_eq]

theorem length_textBytes_alice :
    (DY.Libsignal.Composed.Refinement.Cli.textBytes
      ({ name := aliceUuid, device := 1 } : CryptoVerification.SignalSession.Address).text).length = 38 := by
  have h1 : toString (1 : Nat) = "1" := by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl
  rw [textBytes_eq_flatMap]
  simp only [CryptoVerification.SignalSession.Address.text, aliceUuid, h1, String.toList_append]
  rfl

theorem length_textBytes_bob :
    (DY.Libsignal.Composed.Refinement.Cli.textBytes
      ({ name := bobUuid, device := 1 } : CryptoVerification.SignalSession.Address).text).length = 38 := by
  have h1 : toString (1 : Nat) = "1" := by
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl
  rw [textBytes_eq_flatMap]
  simp only [CryptoVerification.SignalSession.Address.text, bobUuid, h1, String.toList_append]
  rfl

theorem length_encodeVarintAux :
    ∀ (k : Nat) (v : BitVec 64),
      (CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (length_encodeVarintAux k _)

theorem length_encodeVarint (v : BitVec 64) :
    (CryptoVerification.LibsignalProtoCodec.encodeVarint v).length ≤ 10 :=
  length_encodeVarintAux 10 v

theorem length_encodeBytes3 (tag : Nat) (v : List (BitVec 8)) :
    (CryptoVerification.RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.RecordCodecs.encodeProto3BytesField
  split
  · simp
  · simp only [CryptoVerification.LibsignalProtoCodec.encodeBytesField,
      CryptoVerification.LibsignalProtoCodec.encodeKey, List.length_append]
    have h1 := length_encodeVarint
      (BitVec.ofNat 64 (tag * 8 + CryptoVerification.LibsignalProtoCodec.WireType.lengthDelimited.toNat))
    have h2 := length_encodeVarint (BitVec.ofNat 64 v.length)
    omega

theorem length_encodeUint32_3 (tag : Nat) (v : BitVec 32) :
    (CryptoVerification.RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Uint32Field
  split
  · simp
  · simp only [CryptoVerification.LibsignalProtoCodec.encodeUint32Field,
      CryptoVerification.LibsignalProtoCodec.encodeKey, List.length_append]
    have h1 := length_encodeVarint
      (BitVec.ofNat 64 (tag * 8 + CryptoVerification.LibsignalProtoCodec.WireType.varint.toNat))
    have h2 := length_encodeVarint (v.zeroExtend 64)
    omega

theorem commonFiles_alice_cliFilePath (interp : ExternInterpretation) (r : ProtocolSetup) :
    ∀ x ∈ commonFiles interp r r.alice, CliFilePath x.1 := by
  intro x hx
  have hpeer : peerNameOf r r.alice = bobUuid := by simp [peerNameOf]
  simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem commonFiles_bob_cliFilePath {interp : ExternInterpretation} {r : ProtocolSetup}
    (hne : r.alice ≠ r.bob) :
    ∀ x ∈ commonFiles interp r r.bob, CliFilePath x.1 := by
  intro x hx
  have hba : r.bob ≠ r.alice := hne.symm
  have hpeer : peerNameOf r r.bob = aliceUuid := by simp [peerNameOf, hba]
  simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem bobPreKeyFiles_cliFilePath {interp : ExternInterpretation} {r : ProtocolSetup}
    (hopk : r.withOpk = false) (hspk : r.spkId = 7) (hkpk : r.kpkId = 9) :
    ∀ x ∈ bobPreKeyFiles interp r, CliFilePath x.1 := by
  have h7 : toString (7 : BitVec 32).toNat = "7" := by
    change toString (7 : Nat) = "7"
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_seven.mpr rfl]; rfl
  have h9 : toString (9 : BitVec 32).toNat = "9" := by
    change toString (9 : Nat) = "9"
    rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_nine.mpr rfl]; rfl
  intro x hx
  simp only [bobPreKeyFiles, hopk, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    hspk, hkpk, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · dsimp only [signedPreKeyFile]; rw [h7]; decide
  · dsimp only [lastResortKyberPreKeyFile]; rw [h9]; decide
  · dsimp only [baseKeysFile]; rw [h9]; decide

theorem commonFiles_alice_bounded {interp : ExternInterpretation} {r : ProtocolSetup}
    (hEq : ExternCryptoLawsHold interp) (hr : ProtocolSetupWF r) :
    ∀ x ∈ commonFiles interp r r.alice, x.2.length < 2 ^ 31 := by
  intro x hx
  have hsec0 : (secretBytes r 0).length = 32 := by
    have hmem : (0, 32) ∈ setupRandomsAt r := by
      rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1]; simp
    have hl := hr.2.1 (0, 32) hmem
    simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1] using hl
  have hec0 : (ecKey (pubBytes interp (secretBytes r 0))).length = 33 := by
    simp [ecKey, pubBytes, hEq.x25519_public_key_length]
  have hpub1 : (pubBytes interp (secretBytes r 1)).length = 32 := by
    simp [pubBytes, hEq.x25519_public_key_length]
  have hadr : addrOf r r.alice = ⟨aliceUuid, 1⟩ := by simp [addrOf, nameOf]
  simp only [commonFiles, idSecret, peerIdSecret, ProtocolSetup.ikASecBytes, ProtocolSetup.ikBSecBytes,
    ↓reduceIte, regIdOf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · dsimp only; rw [hadr, length_textBytes_alice]; decide
  · dsimp only [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode]
    rw [List.length_append]
    have hb1 := length_encodeBytes3 1 (ecKey (pubBytes interp (secretBytes r 0)))
    have hb2 := length_encodeBytes3 2 (secretBytes r 0)
    rw [hec0] at hb1
    rw [hsec0] at hb2
    omega
  · dsimp only; simp [CryptoVerification.SignalSession.le32]
  · dsimp only; simp [ecKey, hpub1]

theorem commonFiles_bob_bounded {interp : ExternInterpretation} {r : ProtocolSetup}
    (hEq : ExternCryptoLawsHold interp) (hr : ProtocolSetupWF r) :
    ∀ x ∈ commonFiles interp r r.bob, x.2.length < 2 ^ 31 := by
  intro x hx
  have hba : r.bob ≠ r.alice := hr.1.symm
  have hsec1 : (secretBytes r 1).length = 32 := by
    have hmem : (5, 32) ∈ setupRandomsAt r := by
      rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1]; simp
    have hl := hr.2.1 (5, 32) hmem
    simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1] using hl
  have hpub0 : (pubBytes interp (secretBytes r 0)).length = 32 := by
    simp [pubBytes, hEq.x25519_public_key_length]
  have hec1 : (ecKey (pubBytes interp (secretBytes r 1))).length = 33 := by
    simp [ecKey, pubBytes, hEq.x25519_public_key_length]
  have hadr : addrOf r r.bob = ⟨bobUuid, 1⟩ := by simp [addrOf, nameOf, hba]
  simp only [commonFiles, idSecret, peerIdSecret, ProtocolSetup.ikASecBytes, ProtocolSetup.ikBSecBytes,
    hba, ↓reduceIte, regIdOf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · dsimp only; rw [hadr, length_textBytes_bob]; decide
  · dsimp only [CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode]
    rw [List.length_append]
    have hb1 := length_encodeBytes3 1 (ecKey (pubBytes interp (secretBytes r 1)))
    have hb2 := length_encodeBytes3 2 (secretBytes r 1)
    rw [hec1] at hb1
    rw [hsec1] at hb2
    omega
  · dsimp only; simp [CryptoVerification.SignalSession.le32]
  · dsimp only; simp [ecKey, hpub0]

theorem bobPreKeyFiles_bounded {interp : ExternInterpretation} {r : ProtocolSetup}
    (hEq : ExternCryptoLawsHold interp) (hr : ProtocolSetupWF r) (hopk : r.withOpk = false) :
    ∀ x ∈ bobPreKeyFiles interp r, x.2.length < 2 ^ 31 := by
  obtain ⟨hne, hrand, _, hs5, hk6, hs7, hsecB, _⟩ := hr
  have hsec2 : r.spkSecBytes.length = 32 := by
    have hmem : (10, 32) ∈ setupRandomsAt r := by
      rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hne]; simp
    have hl := hrand (10, 32) hmem
    simpa [ProtocolSetup.spkSecBytes, secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hne] using hl
  have hec2 : (ecKey (pubBytes interp r.spkSecBytes)).length = 33 := by
    simp [ecKey, pubBytes, hEq.x25519_public_key_length]
  have hkyb6 : (kyberKey (r.opaqueBytes r.pqpkPubTerm)).length = 1569 := by
    simp [kyberKey, hk6]
  have hkybSec : (kyberKey (r.kyberSecB.drop 1)).length = 3169 := by
    simp [kyberKey, hsecB]
  intro x hx
  simp only [bobPreKeyFiles, hopk, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · dsimp only [CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode]
    have hf5 : CryptoVerification.RecordCodecs.encodeProto3Fixed64Field 5 0 = [] := rfl
    rw [hf5, List.append_nil]
    simp only [List.length_append]
    have hu := length_encodeUint32_3 1 r.spkId
    have hb2 := length_encodeBytes3 2 (ecKey (pubBytes interp r.spkSecBytes))
    have hb3 := length_encodeBytes3 3 r.spkSecBytes
    have hb4 := length_encodeBytes3 4 (r.opaqueBytes r.spkSigTerm)
    rw [hec2] at hb2
    rw [hsec2] at hb3
    rw [hs5] at hb4
    omega
  · dsimp only [CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode]
    have hf5 : CryptoVerification.RecordCodecs.encodeProto3Fixed64Field 5 0 = [] := rfl
    rw [hf5, List.append_nil]
    simp only [List.length_append]
    have hu := length_encodeUint32_3 1 r.kpkId
    have hb2 := length_encodeBytes3 2 (kyberKey (r.opaqueBytes r.pqpkPubTerm))
    have hb3 := length_encodeBytes3 3 (kyberKey (r.kyberSecB.drop 1))
    have hb4 := length_encodeBytes3 4 (r.opaqueBytes r.pqpkSigTerm)
    rw [hkyb6] at hb2
    rw [hkybSec] at hb3
    rw [hs7] at hb4
    omega
  · dsimp only; decide

theorem initDirs_alice_no_session (interp : ExternInterpretation) (r : ProtocolSetup) :
    (CliTurn.init (initDirs interp r)).records r r.alice = none := by
  have hbase := commonFiles_alice_cliFilePath interp r
  have hsess : sessionPathOf r r.alice = sessionFile ⟨bobUuid, 1⟩ := by
    simp [sessionPathOf, peerOf, peerNameOf]
  have hidle : ∀ x ∈ commonFiles interp r r.alice,
      normalizePath x.1 ≠ normalizePath (sessionFile ⟨bobUuid, 1⟩) := by
    have h1 : toString (1 : Nat) = "1" := by
      rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl
    have hs : sessionFile ⟨bobUuid, 1⟩ = "sessions/" ++ (bobUuid ++ "." ++ "1") := by
      simp only [sessionFile, CryptoVerification.SignalSession.Address.text, h1]
    rw [hs]
    have hpeer : peerNameOf r r.alice = bobUuid := by simp [peerNameOf]
    intro x hx
    simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have hfiles : initDirs interp r r.alice (sessionPathOf r r.alice) = none := by
    simp only [initDirs, ↓reduceIte, hsess, cliFilesOf_eq_evalAt hbase]
    split
    · rfl
    · split
      · rfl
      · exact cliEvalAt_idle hidle none
  simp [CliTurn.records, CliTurn.init, hfiles]

theorem filesOf_last_session {base : List (String × HwBytes)} {sPath : String} {recBytes : HwBytes}
    (hbase : ∀ x ∈ base, CliFilePath x.1)
    (hs_fp : CliFilePath sPath)
    (hnst : normalizePath sPath ∉ stdioPaths.map normalizePath) :
    filesOf (base ++ [(sPath, recBytes)]) sPath = some recBytes := by
  have hsingle : ∀ x ∈ [(sPath, recBytes)], CliFilePath x.1 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hs_fp
  rw [filesOf_append_or hbase hsingle sPath, cliFilesOf_eq_evalAt hsingle sPath]
  simp [hnst, hs_fp.1, cliEvalAt, cliStepAt]

theorem pqFromHonest_of_mem {sent : List HwBytes} {body : HwBytes} (h : body ∈ sent) :
    PqFromHonest sent body :=
  fun m hm => ⟨body, h, m, hm, rfl⟩

theorem bytesField_aliceBaseKey_isInfix_recordBytes (rr : DY.Libsignal.Rust.RecordRec) :
    bytesField 13 rr.current.aliceBaseKey <:+: recordBytes rr := by
  let s := rr.current
  let pre := u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
    bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
    u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
    s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
    ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
    u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId
  let post := ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
    bytesField 15 s.pqRatchetState
  let body := pre ++ bytesField 13 s.aliceBaseKey ++ post
  refine ⟨(DY.Libsignal.Refinement.paddedVarint (1 * 8 + 2) 0 ++
      DY.Libsignal.Refinement.paddedVarint body.length 0) ++ pre,
    post ++ rr.previous.flatMap (msgField 2), ?_⟩
  dsimp only [s, body, pre, post, recordBytes, msgField, DY.Libsignal.Refinement.encodeField]
  simp only [List.append_assoc]

section TestRecordsWF
open DY.Libsignal.Composed

def testSem : OpaqueSymbolSemantics where
  init := fun _ _ => []
  chainKey := fun _ _ _ => []
  sendState := fun _ _ => []
  sendKey := fun _ _ => []
  sendMsg := fun _ _ => []
  recvState := fun _ _ => []
  recvKey := fun _ _ => []
  kemPk := fun _ => List.replicate 1568 0#8
  kemDecap := fun _ _ => []
  vk := fun _ => []
  sign := fun _ _ _ => List.replicate 64 0#8

def testFresh (i n : Nat) : HwBytes :=
  if n = 0 then [] else BitVec.ofNat 8 i :: List.replicate (n - 1) 0#8

def testGhost : Ghost where
  σ := testFresh
  addr := fun _ => []

def testRecords : ProtocolSetup where
  alice := "alice"
  bob := "bob"
  withOpk := false
  regIdA := 1
  regIdB := 2
  spkId := 7
  kpkId := 9
  opkId := 0
  kyberSecB := List.replicate 3169 0#8
  fresh := testFresh
  opaqueBytes := gamma cliWitnessInterp testSem testGhost

unseal DY.Bytes in
private local instance :
    DY.Bytes.SubFunction (concretizeKemPk testSem) (concretizeAll cliWitnessInterp testSem testGhost) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.kemFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

unseal DY.Bytes in
private local instance :
    DY.Bytes.SubFunction (concretizeSign testSem) (concretizeAll cliWitnessInterp testSem testGhost) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.sigFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

private theorem test_gamma_kemPk (sk : DY.Bytes) :
    gamma cliWitnessInterp testSem testGhost (DY.PQKem.kemPk sk) = List.replicate 1568 0#8 := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll cliWitnessInterp testSem testGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk testSem) (concretizeAll cliWitnessInterp testSem testGhost)]; rfl

private theorem test_gamma_sign (sk n m : DY.Bytes) :
    gamma cliWitnessInterp testSem testGhost (DY.Signature.sign sk n m) =
      List.replicate 64 0#8 := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll cliWitnessInterp testSem testGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign testSem) (concretizeAll cliWitnessInterp testSem testGhost)]; rfl

theorem testRecords_wf : ProtocolSetupWF testRecords := by
  have hNe : testRecords.alice ≠ testRecords.bob := by show "alice" ≠ "bob"; decide
  have hR : setupRandomsAt testRecords =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] :=
    Symbolic.Swarm.CREF.b1_setupRandomsAt_eq testRecords hNe
  have h5 : setupPublic testRecords 5 =
      DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))) :=
    Symbolic.Swarm.CREF.b1_setupPublic_5 testRecords hNe
  have h6 : setupPublic testRecords 6 = DY.PQKem.kemPk (randTerm 16 64) :=
    Symbolic.Swarm.CREF.b1_setupPublic_6 testRecords hNe
  have h7 : setupPublic testRecords 7 =
      DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))) :=
    Symbolic.Swarm.CREF.b1_setupPublic_7 testRecords hNe
  have o5 : testRecords.opaqueBytes (setupPublic testRecords 5) = List.replicate 64 0#8 := by
    rw [h5]; exact test_gamma_sign _ _ _
  have o6 : testRecords.opaqueBytes (setupPublic testRecords 6) = List.replicate 1568 0#8 := by
    rw [h6]; exact test_gamma_kemPk _
  have o7 : testRecords.opaqueBytes (setupPublic testRecords 7) = List.replicate 64 0#8 := by
    rw [h7]; exact test_gamma_sign _ _ _
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, List.length_replicate, ?_⟩
  · rw [hR]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hR]; decide
  · dsimp only [ProtocolSetup.spkSigTerm]; rw [o5]; exact List.length_replicate
  · dsimp only [ProtocolSetup.pqpkPubTerm]; rw [o6]; exact List.length_replicate
  · dsimp only [ProtocolSetup.pqpkSigTerm]; rw [o7]; exact List.length_replicate
  · show ((List.replicate 3169 0#8).drop 1537).take 1568 = _
    dsimp only [ProtocolSetup.pqpkPubTerm]
    rw [o6, List.drop_replicate, List.take_replicate]; rfl

end TestRecordsWF

theorem parseBundleFiles_of_honestBundleDir {interp : ExternInterpretation} {r : ProtocolSetup}
    {pb : PublicBundle} (h : HonestBundleDir interp r pb) :
    parseBundleFiles (filesOf (pb.files bundleDir)) = some pb := by
  obtain ⟨bE, rfl⟩ := (Symbolic.Swarm.CREF.Cli.bundleTyped_iff_exists_bundleE pb).mp h.1
  exact parseBundleFiles_publicBundleOf bE

theorem honestBundleDir_to_flat_and_honest {interp : ExternInterpretation} {r : ProtocolSetup}
    {pb : PublicBundle} (h : HonestBundleDir interp r pb) :
    BundleFilesFlat (pb.files bundleDir) ∧ HonestBundleFiles interp r (pb.files bundleDir) := by
  have hparse := parseBundleFiles_of_honestBundleDir h
  have hflat : BundleFilesFlat (pb.files bundleDir) := by
    obtain ⟨bE, rfl⟩ := (Symbolic.Swarm.CREF.Cli.bundleTyped_iff_exists_bundleE pb).mp h.1
    exact bundleFilesFlat_publicBundleOf bE
  refine ⟨hflat, fun b' hb' => ?_⟩
  rw [hparse, Option.some.injEq] at hb'
  subst hb'
  exact h.2

def testInitCall : CliCall where
  party := testRecords.alice
  cmd := .init (peerOf testRecords testRecords.alice) bundleDir
  bundle := (honestPublicBundle cliWitnessInterp testRecords).files bundleDir
  stdin := []
  coins := List.replicate 192 0#8

private theorem cliNextCall_testInitCall :
    ValidCall cliWitnessInterp testRecords
      (CliTurn.init (initDirs cliWitnessInterp testRecords)) testInitCall := by
  have hEq := cliWitnessInterp_cryptoEquationsHold
  have hr := testRecords_wf
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  have hbd := commonFiles_alice_bounded hEq hr
  have hdirs :
      (CliTurn.init (initDirs cliWitnessInterp testRecords)).dirs testRecords.alice =
        filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
    simp [CliTurn.init, initDirs]
  dsimp only [ValidCall, StdinBounded, BobCallAllowed, testInitCall]
  refine ⟨List.length_replicate, trivial, ?_, (fun h => nomatch h),
    rfl, rfl, rfl, rfl, initDirs_alice_no_session cliWitnessInterp testRecords,
    honestBundleDir_to_flat_and_honest (honestBundleDir_honestPublicBundle hEq hr)⟩
  rw [hdirs]
  exact filesBounded_of_cliFilePaths hbase hbd

/-- `ValidCall` is satisfiable at the initial turn `CliTurn.init (initDirs ...)`. -/
theorem cliNextCall_alice_init_satisfiable :
    ∃ c : CliCall,
      ValidCall cliWitnessInterp testRecords
        (CliTurn.init (initDirs cliWitnessInterp testRecords)) c :=
  ⟨testInitCall, cliNextCall_testInitCall⟩

/-- `CliTracesMoves` admits a non-empty 1-step trace from `CliTurn.init (initDirs ...)`. -/
theorem cliTraces_one_step_satisfiable :
    ∃ (Rel : Inputs → Option Outcome → Prop) (τ : List MachineEvent)
      (calls : List (DY.Participant × Bool)),
      τ ≠ [] ∧ calls ≠ [] ∧
      CliTracesMoves Rel cliWitnessInterp testRecords
        (CliTurn.init (initDirs cliWitnessInterp testRecords)) τ calls := by
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
  have hdirs : t0.dirs testInitCall.party =
      filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
    simp [t0, CliTurn.init, initDirs, testInitCall]
  let inp : Inputs :=
    { argv := testInitCall.cmd.argv
      dirs := partyDirs ++ [bundleDir]
      files := commonFiles cliWitnessInterp testRecords testRecords.alice ++ testInitCall.extra
      stdin := [] }
  have hinp : InputsFor testInitCall (t0.dirs testInitCall.party) inp := by
    rw [hdirs]
    exact inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
      (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
      (fun x hx => ((honestBundleDir_to_flat_and_honest
        (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
      (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)
  refine ⟨fun _ _ => True, cliEntryEvents testInitCall ++ cliExitEvents testInitCall 0 [],
    [(testInitCall.party, true)], by simp [cliEntryEvents, testInitCall], by simp, ?_⟩
  have hstep := CliTracesMoves.step
    (Rel := fun _ _ => True) (interp := cliWitnessInterp) (r := testRecords)
    (t := t0) (leaks := []) (c := testInitCall) (i := inp) (code := 0) (out := [])
    (files := t0.dirs testInitCall.party)
    (fun _ h => nomatch h) cliNextCall_testInitCall hinp trivial
    (CliTracesMoves.done (t0.after testRecords testInitCall 0 [] (t0.dirs testInitCall.party)))
  simpa using hstep

/-- Regression witness (`SamePath` / `scrub`): after a call leaves `./`-prefixed `coins` and
`bundle/` entries in `filesOf`, `InputsFor` is satisfiable on `scrub` of that output. -/
theorem inputsFor_after_scrub_dot_paths :
    ∃ i : Inputs,
      InputsFor testInitCall
        (scrub (filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice ++
          [("./coins", [1#8]), ("./bundle/identity-key", [5#8])]))) i := by
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  have hextra : ∀ x ∈ ([("./coins", [1#8]), ("./bundle/identity-key", [5#8])] :
      List (String × HwBytes)), CliFilePath x.1 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> (dsimp only; decide)
  have hno : ∀ x ∈ commonFiles cliWitnessInterp testRecords testRecords.alice,
      normalizePath x.1 ≠ [coinsFile] ∧ (normalizePath x.1).head? ≠ some bundleDir := by
    have hpeer : peerNameOf testRecords testRecords.alice = bobUuid := rfl
    intro x hx
    simp only [commonFiles, hpeer, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have honly : ∀ x ∈ ([("./coins", [1#8]), ("./bundle/identity-key", [5#8])] :
      List (String × HwBytes)),
      normalizePath x.1 = [coinsFile] ∨ (normalizePath x.1).head? = some bundleDir := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · left; decide
    · right; decide
  rw [scrub_filesOf_eq hbase hextra hno honly]
  exact ⟨_, inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
    (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
    (fun x hx => ((honestBundleDir_to_flat_and_honest
      (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
    (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)⟩

/-- `CliTracesMoves.stop` admits an aborting run (`some .aborted`) from `initDirs`. -/
theorem cliTraces_oom_stop_satisfiable :
    ∃ (τ : List MachineEvent) (calls : List (DY.Participant × Bool)),
      τ ≠ [] ∧ calls = [(testRecords.alice, false)] ∧
      CliTracesMoves (fun _ o => o = some .aborted) cliWitnessInterp testRecords
        (CliTurn.init (initDirs cliWitnessInterp testRecords)) τ calls := by
  have hbase := commonFiles_alice_cliFilePath cliWitnessInterp testRecords
  let t0 := CliTurn.init (initDirs cliWitnessInterp testRecords)
  have hdirs : t0.dirs testInitCall.party =
      filesOf (commonFiles cliWitnessInterp testRecords testRecords.alice) := by
    simp [t0, CliTurn.init, initDirs, testInitCall]
  let inp : Inputs :=
    { argv := testInitCall.cmd.argv
      dirs := partyDirs ++ [bundleDir]
      files := commonFiles cliWitnessInterp testRecords testRecords.alice ++ testInitCall.extra
      stdin := [] }
  have hinp : InputsFor testInitCall (t0.dirs testInitCall.party) inp := by
    rw [hdirs]
    exact inputsFor_of_cliFilePaths testInitCall _ hbase (bundleFiles_cliFilePath _)
      (commonFiles_alice_bounded cliWitnessInterp_cryptoEquationsHold testRecords_wf)
      (fun x hx => ((honestBundleDir_to_flat_and_honest
        (honestBundleDir_honestPublicBundle cliWitnessInterp_cryptoEquationsHold testRecords_wf)).1 x hx).2)
      (by dsimp only [testInitCall]; rw [List.length_replicate]; decide)
  refine ⟨cliEntryEvents testInitCall, [(testRecords.alice, false)],
    by simp [cliEntryEvents, testInitCall], rfl, ?_⟩
  have hstop := CliTracesMoves.stop
    (Rel := fun _ o => o = some .aborted) (interp := cliWitnessInterp) (r := testRecords)
    (t := t0) (leaks := []) (c := testInitCall) (i := inp) (o := some .aborted)
    (fun _ h => nomatch h) cliNextCall_testInitCall hinp rfl (Or.inl rfl)
  simpa [testInitCall] using hstop

/-- Monotonicity of `CliTracesMoves` in the run relation `Rel`: widening `Rel` (such as dropping a
conjunct from `elfRel`) only adds admitted CLI traces. -/
theorem cliTraces_mono
    {Rel Rel' : Inputs → Option Outcome → Prop} {interp : ExternInterpretation} {r : ProtocolSetup}
    {t : CliTurn} {τ : List MachineEvent} {calls : List (DY.Participant × Bool)}
    (hrel : ∀ i o, Rel i o → Rel' i o)
    (htr : CliTracesMoves Rel interp r t τ calls) :
    CliTracesMoves Rel' interp r t τ calls := by
  induction htr with
  | done t => exact .done t
  | clear p _ ih => exact .clear p ih
  | step hleaks hnext hinp hstep _ ih =>
    exact .step hleaks hnext hinp (hrel _ _ hstep) ih
  | stop hleaks hnext hinp hstop habort =>
    exact .stop hleaks hnext hinp (hrel _ _ hstop) habort

/-! ## Dependency Checks on `Composed/Cli/` Definitions and Witnesses -/

#print axioms DY.Libsignal.Composed.Refinement.Cli.initDirs
#print axioms DY.Libsignal.Composed.Refinement.Cli.FilesVisible
#print axioms DY.Libsignal.Composed.Refinement.Cli.InputsFor
#print axioms DY.Libsignal.Composed.Refinement.Cli.SamePath
#print axioms DY.Libsignal.Composed.Refinement.Cli.scrub
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliTurn.after
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliTurn.clearSession
#print axioms DY.Libsignal.Composed.Refinement.Cli.CoinSplit
#print axioms DY.Libsignal.Composed.Refinement.Cli.ValidCall
#print axioms DY.Libsignal.Composed.Refinement.Cli.CliTracesMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CallsMatchSchedules
#print axioms DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompAsmSecurityCliMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.HooksMatchInterpretation
#print axioms DY.Libsignal.Composed.Refinement.Cli.elfRel
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliElfMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinaryMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompAsmSecurityCliBinaryMoves
#print axioms DY.Libsignal.Composed.Refinement.Cli.CompExternsSatisfiableCli
#print axioms comp_externsSatisfiable_cli_test
#print axioms cliNextCall_alice_init_satisfiable
#print axioms cliTraces_one_step_satisfiable
#print axioms cliTraces_oom_stop_satisfiable
#print axioms cliTraces_mono

end Symbolic.Proofs.Tests.Refinement.Cli
