/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureA
public import Symbolic.Proofs.Refinement.TrWireCovered -- shake: keep
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Init.Data.String
public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
import Symbolic.Proofs.Refinement.ExecBridgeSendCtOS
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma

/-!
# Concretization Lemmas for Send-Wire Key Derivation and Serialization

Provides `SubFunction` instances and `gamma` unfolding lemmas across `kdfCk`, `trMsgKeys`,
`symEnc`, `trHonestWireMsg`, and session record erasure for `SendRetCoinsCliPure`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
open Symbolic.Swarm.CREF.TR

cref_open
open DY.Libsignal.TripleRatchet (kdfCk)
open DY.Libsignal.Refinement (sha256CompressFunction x25519PublicKeySymbol aesCbcEncryptSymbol
  encodeWith canonicalVariation encodeField)
open DY.Libsignal.TripleRatchet
open CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.SR
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.TRREF.SpqrSemOf (saltToBytes spqrIdx1Bytes spqrKeyBytes_saltToBytes)
attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set mut_exec_modifyGet mut_exec_liftE mut_exec_bind

open Swarm.Phase0WholeFunctionBridge (sessionToSessionRec senderChainToChainRec
  receiverChainToChainRec)

unseal DY.Bytes in
instance subFunction_gRandom_src (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_sendGhost_coins_all (interpretation : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) (ts : Nat) (pt coins : HwBytes) :
    gamma interpretation S (sendGhost g ts pt coins) (randTerm (ts + 1) coins.length) = coins := by
  by_cases h : coins.length = 0
  · have hnil := List.eq_nil_of_length_eq_zero h; subst hnil; unfold gamma gamma' randTerm
    rw [DY.Bytes.rec_eq (concretizeRandom (sendGhost g ts pt [])) (concretizeAll interpretation S (sendGhost g ts pt []))]; rfl
  · exact gamma_sendGhost_coins interpretation S g ts pt coins h

section FoldInstances
variable (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
unseal DY.Bytes in
instance : DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeSym interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeDhPk interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction concretizeTrunc (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance : DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
end FoldInstances

theorem gamma_litOf (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (bs : HwBytes) :
    gamma interpretation S g (litOf bs) = bs := by
  unfold gamma gamma' litOf
  show ((({ lit := ByteArray.mk (bs.map UInt8.ofBitVec).toArray } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]
  unfold concretizeLit node ofByteArray
  simp [List.map_map, Function.comp_def]

theorem gamma_spqrInit (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (a p : DY.Bytes) :
    gamma i S g (DY.Spqr.spqrInit a p) = S.init (gamma i S g a) (gamma i S g p) := by
  unfold gamma gamma' DY.Spqr.spqrInit
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll i S g)]; rfl

theorem gamma_spqrIdx_one (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    gamma i S g (DY.Spqr.encodeSpqrIndexTerm 1) = spqrIdx1Bytes := by
  unfold gamma gamma' DY.Spqr.encodeSpqrIndexTerm
  show ((({lit := ⟨#[(1 : UInt32).toUInt8, ((1 : UInt32) >>> 8).toUInt8,
    ((1 : UInt32) >>> 16).toUInt8, ((1 : UInt32) >>> 24).toUInt8]⟩} :
      DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]; rfl

theorem gamma_spqrSendState (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (st coins : DY.Bytes) :
    gamma i S g (({st, coins} : DY.Spqr.SendState.SubF DY.Bytes).pack) =
      S.sendState (gamma i S g st) (gamma i S g coins) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll i S g)]; rfl

theorem gamma_spqrSendKey (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (st coins : DY.Bytes) :
    gamma i S g (({st, coins} : DY.Spqr.SendKey.SubF DY.Bytes).pack) =
      spqrKeyBytes (S.sendKey (gamma i S g st) (gamma i S g coins)) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll i S g)]; rfl

theorem gamma_spqrSendMsg (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (st coins : DY.Bytes) :
    gamma i S g (({st, coins} : DY.Spqr.SendMsg.SubF DY.Bytes).pack) =
      S.sendMsg (gamma i S g st) (gamma i S g coins) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll i S g)]; rfl

theorem gamma_trWireMsg (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) :
    gamma i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) =
      trWireBytes
        (g.addr (DY.TrWire.trWireMsg v rk c pc ct pq ev))
        ev
        { version := v.toNat, ratchetKey := gamma i S g rk, counter := c.toNat,
          previousCounter := pc.toNat, ciphertext := gamma i S g ct }
        (gamma i S g pq) := by
  unfold gamma gamma' DY.TrWire.trWireMsg
  show ((({ version := v, senderRatchetKey := rk, counter := c, previousCounter := pc,
            ciphertext := ct, pqRatchet := pq, encodingVariation := ev } :
      DY.TrWire.TrWireMsg.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll i S g)]; rfl

theorem gamma_concat_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (a b : DY.Bytes) :
    gamma interpretation S g (DY.Concat.concat a b) = gamma interpretation S g a ++ gamma interpretation S g b := by
  unfold gamma gamma'
  show ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]; rfl

theorem gamma_symEnc_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (k iv m : DY.Bytes) :
    gamma interpretation S g (DY.SymEnc.symEnc k iv m) =
      (interpretation aesCbcEncryptSymbol [gamma interpretation S g m, gamma interpretation S g k, (gamma interpretation S g iv).take 16]).getD [] := by
  unfold gamma gamma'
  show ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSym interpretation) (concretizeAll interpretation S g)]; rfl

theorem gamma_kdfExtract_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (k m : DY.Bytes) :
    gamma interpretation S g (DY.KdfExtract.kdfExtract k m) =
      ByteSpecs.hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g k) (gamma interpretation S g m) := by
  unfold gamma gamma'
  show ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]; rfl

theorem gamma_dhPk_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dhPk sk) =
      (interpretation x25519PublicKeySymbol [clamp (gamma interpretation S g sk)]).getD [] := by
  unfold gamma gamma'
  show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeDhPk interpretation) (concretizeAll interpretation S g)]; rfl

theorem gamma_trunc8_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (m : DY.Bytes) :
    gamma interpretation S g (DY.Trunc.trunc8 m) = (gamma interpretation S g m).take 8 := by
  unfold gamma gamma'
  show ((({ input := m } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeTrunc (concretizeAll interpretation S g)]; rfl

theorem gamma_litByte_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (b : UInt8) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.litByte b) = [b.toBitVec] :=
  gamma_litOf interpretation S g [b.toBitVec]

theorem gamma_kdfCk_fst_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (ck : DY.Bytes) :
    gamma interpretation S g (kdfCk ck).1 = ByteSpecs.hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g ck) [0x02#8] := by
  change gamma interpretation S g (DY.KdfExtract.kdfExtract ck (DY.Libsignal.TripleRatchet.litByte 0x02)) = _
  rw [gamma_kdfExtract_tr, gamma_litByte_tr]; rfl

theorem gamma_kdfCk_snd_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (ck : DY.Bytes) :
    gamma interpretation S g (kdfCk ck).2 = ByteSpecs.hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g ck) [0x01#8] := by
  change gamma interpretation S g (DY.KdfExtract.kdfExtract ck (DY.Libsignal.TripleRatchet.litByte 0x01)) = _
  rw [gamma_kdfExtract_tr, gamma_litByte_tr]; rfl

theorem gamma_whisperMessageKeys_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = whisperMessageKeys := by
  have heq : gamma interpretation S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = ofByteArray "WhisperMessageKeys".toUTF8 := by
    unfold gamma gamma'
    show ((({ lit := "WhisperMessageKeys".toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
    rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]; rfl
  rw [heq, String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "WhisperMessageKeys"),
      String.toByteArray_ofList]
  decide

theorem gamma_hkdfBlock1_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (prk info : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) =
      ByteSpecs.hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g prk) (gamma interpretation S g info ++ [1#8]) := by
  change gamma interpretation S g (DY.KdfExtract.kdfExtract prk (DY.Concat.concat info (DY.Libsignal.TripleRatchet.litByte 1))) = _
  rw [gamma_kdfExtract_tr, gamma_concat_tr, gamma_litByte_tr]; rfl

theorem gamma_hkdfBlock2_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (prk info : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) =
      ByteSpecs.hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g prk)
        (gamma interpretation S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) ++ gamma interpretation S g info ++ [2#8]) := by
  change gamma interpretation S g (DY.KdfExtract.kdfExtract prk (DY.Concat.concat (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) (DY.Concat.concat info (DY.Libsignal.TripleRatchet.litByte 2)))) = _
  rw [gamma_kdfExtract_tr, gamma_concat_tr, gamma_concat_tr, gamma_litByte_tr, List.append_assoc]; rfl

theorem gamma_hkdfBlock3_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (prk info : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) =
      ByteSpecs.hmacWith (sha256CompressFunction interpretation) (gamma interpretation S g prk)
        (gamma interpretation S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) ++ gamma interpretation S g info ++ [3#8]) := by
  change gamma interpretation S g (DY.KdfExtract.kdfExtract prk (DY.Concat.concat (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) (DY.Concat.concat info (DY.Libsignal.TripleRatchet.litByte 3)))) = _
  rw [gamma_kdfExtract_tr, gamma_concat_tr, gamma_concat_tr, gamma_litByte_tr, List.append_assoc]; rfl

theorem gamma_hmac_pqSalt_eq_hkdfExtract (interpretation : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) (pqSalt seed : DY.Bytes) (salt? : Salt) (hsalt : gamma interpretation S g pqSalt = spqrKeyBytes (saltToBytes salt?)) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac pqSalt seed) =
      hkdfExtract (sha256CompressFunction interpretation) salt? (gamma interpretation S g seed) := by
  change gamma interpretation S g (DY.KdfExtract.kdfExtract pqSalt seed) = _
  rw [gamma_kdfExtract_tr, hsalt]
  change ByteSpecs.hmacWith (sha256CompressFunction interpretation)
    (DY.Libsignal.Composed.Refinement.spqrKeyBytes (saltToBytes salt?))
    (gamma interpretation S g seed) = _
  rw [spqrKeyBytes_saltToBytes]; cases salt? <;> rfl

theorem gamma_trMsgKeys_append_eq_hkdfExpand (interpretation : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) (pqSalt seed : DY.Bytes) (salt? : Salt) (hsalt : gamma interpretation S g pqSalt = spqrKeyBytes (saltToBytes salt?)) :
    let F := sha256CompressFunction interpretation; let keys := trMsgKeys pqSalt seed
    gamma interpretation S g keys.cipherKey ++ gamma interpretation S g keys.macKey ++ (gamma interpretation S g keys.iv).take 16 =
      hkdfExpand F (hkdfExtract F salt? (gamma interpretation S g seed)) whisperMessageKeys 80 := by
  dsimp only [trMsgKeys]
  rw [Proofs.libsignal.Refinement.ExecBridgeSendCtOS.hkdfExpand_80_eq_blocks, gamma_hkdfBlock3_tr,
    gamma_hkdfBlock2_tr, gamma_hkdfBlock1_tr, gamma_hmac_pqSalt_eq_hkdfExtract interpretation S g pqSalt seed salt? hsalt,
    gamma_whisperMessageKeys_tr]

theorem deriveMessageKeys_eq_tr (F : ShaCompress) (seed : List (BitVec 8)) (pqrKey : Salt) :
    let k := CryptoGames.HKDF.deriveMessageKeys F pqrKey seed
    (keyToBytes32 k.1.1).length = 32 ∧ (keyToBytes32 k.2).length = 32 ∧ (CryptoGames.CBC.blockToBytesLE k.1.2).length = 16 ∧
    hkdfExpand F (hkdfExtract F pqrKey seed) whisperMessageKeys 80 =
      keyToBytes32 k.1.1 ++ keyToBytes32 k.2 ++ CryptoGames.CBC.blockToBytesLE k.1.2 := by
  have hlen : (hkdfExpand F (hkdfExtract F pqrKey seed) whisperMessageKeys 80).length = 80 := by simp [hkdfExpand, hkdfBlocks]
  dsimp only [CryptoGames.HKDF.deriveMessageKeys, hkdf]
  generalize hkdfExpand F (hkdfExtract F pqrKey seed) whisperMessageKeys 80 = okm at hlen ⊢
  have htake1 : (okm.take 32).length = 32 := by simp [hlen]
  have htake2 : ((okm.drop 32).take 32).length = 32 := by simp [hlen]
  have htake3 : ((okm.drop 64).take 16).length = 16 := by simp [hlen]
  have hdrop64 : (okm.drop 64).take 16 = okm.drop 64 := List.take_of_length_le (by simp [hlen])
  refine ⟨by simp [keyToBytes32], by simp [keyToBytes32], by simp [CryptoGames.CBC.blockToBytesLE], ?_⟩
  rw [keyToBytes32_bytesToKey32_c _ htake1, keyToBytes32_bytesToKey32_c _ htake2, blockToBytesLE_bytesToBlock_c _ htake3, hdrop64]
  have h1 := (List.take_append_drop 32 okm).symm; have h2 := (List.take_append_drop 32 (okm.drop 32)).symm
  rw [List.drop_drop] at h2; rw [List.append_assoc, ← h2, ← h1]

theorem gamma_trMsgKeys_eq_generateKeys (interpretation : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) (pqSalt seed : DY.Bytes) (idx : BitVec 32) (salt? : Salt)
    (hsalt : gamma interpretation S g pqSalt = spqrKeyBytes (saltToBytes salt?)) :
    let F := sha256CompressFunction interpretation; let keys := trMsgKeys pqSalt seed
    let mk := MessageKeyGenerator.generateKeys F ⟨gamma interpretation S g seed, idx⟩ salt?
    keyToBytes32 mk.cipherKey = gamma interpretation S g keys.cipherKey ∧
    keyToBytes32 mk.macKey = gamma interpretation S g keys.macKey ∧
    CryptoGames.CBC.blockToBytesLE mk.iv = (gamma interpretation S g keys.iv).take 16 ∧ mk.counter = idx := by
  dsimp only [MessageKeyGenerator.generateKeys]
  set F := sha256CompressFunction interpretation; set keys := trMsgKeys pqSalt seed
  obtain ⟨hl1, hl2, _, hder_eq⟩ := deriveMessageKeys_eq_tr F (gamma interpretation S g seed) salt?
  have heq80 := (gamma_trMsgKeys_append_eq_hkdfExpand interpretation S g pqSalt seed salt? hsalt).trans hder_eq
  have hlen_c : (gamma interpretation S g keys.cipherKey).length = 32 := by dsimp only [keys, trMsgKeys]; rw [gamma_hkdfBlock1_tr]; exact length_hmacWith _ _ _
  have hlen_m : (gamma interpretation S g keys.macKey).length = 32 := by dsimp only [keys, trMsgKeys]; rw [gamma_hkdfBlock2_tr]; exact length_hmacWith _ _ _
  have h1 : gamma interpretation S g keys.cipherKey = keyToBytes32 (CryptoGames.HKDF.deriveMessageKeys F salt? (gamma interpretation S g seed)).1.1 := by
    have ht := congrArg (List.take 32) heq80; rw [List.append_assoc, List.take_left' hlen_c, List.append_assoc, List.take_left' hl1] at ht; exact ht
  have heq48 : gamma interpretation S g keys.macKey ++ (gamma interpretation S g keys.iv).take 16 =
      keyToBytes32 (CryptoGames.HKDF.deriveMessageKeys F salt? (gamma interpretation S g seed)).2 ++ CryptoGames.CBC.blockToBytesLE (CryptoGames.HKDF.deriveMessageKeys F salt? (gamma interpretation S g seed)).1.2 := by
    have hd := congrArg (List.drop 32) heq80; rw [List.append_assoc, List.drop_left' hlen_c, List.append_assoc, List.drop_left' hl1] at hd; exact hd
  have h2 : gamma interpretation S g keys.macKey = keyToBytes32 (CryptoGames.HKDF.deriveMessageKeys F salt? (gamma interpretation S g seed)).2 := by
    have ht := congrArg (List.take 32) heq48; rw [List.take_left' hlen_m, List.take_left' hl2] at ht; exact ht
  have h3 : (gamma interpretation S g keys.iv).take 16 = CryptoGames.CBC.blockToBytesLE (CryptoGames.HKDF.deriveMessageKeys F salt? (gamma interpretation S g seed)).1.2 := by
    have hd := congrArg (List.drop 32) heq48; rw [List.drop_left' hlen_m, List.drop_left' hl2] at hd; exact hd
  exact ⟨h1.symm, h2.symm, h3.symm, rfl⟩

theorem gamma_trHonestWireMsg (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (haddr : g.addr (trHonestWireMsg rk c pc ct pq) = []) :
    gamma interpretation S g (trHonestWireMsg rk c pc ct pq) =
      encodeWith canonicalVariation
        { version := 4, ratchetKey := gamma interpretation S g rk, counter := c.toNat, previousCounter := pc.toNat, ciphertext := gamma interpretation S g ct } ++
        (if gamma interpretation S g pq = [] then [] else encodeField 5 0 0 (.bytes (gamma interpretation S g pq))) := by
  unfold trHonestWireMsg at haddr ⊢; rw [gamma_trWireMsg, haddr]
  rw [DY.Libsignal.TripleRatchet.Refinement.trWireBytes_canonical]
  simp only [↓reduceIte, List.append_nil]; rfl

theorem eraseSkipped_eraseUnmodelled_sessionToSessionRec_TR (s : Session (List (BitVec 8))) :
    eraseSkipped (eraseUnmodelled (sessionToSessionRec s)) =
      { sessionVersion := s.state.sessionVersion, localIdentityPublic := s.state.localIdentity.serialize,
        remoteIdentityPublic := (s.state.remoteIdentity.map IdentityKey.serialize).getD [],
        rootKey := CryptoGames.HMAC.keyToBytes32 s.state.rootKey, previousCounter := s.state.previousCounter,
        senderChain := s.state.senderChain.map senderChainToChainRec,
        receiverChains := s.state.receiverChains.map fun rc =>
          { senderRatchetKey := rc.senderRatchetKey.serialize, senderRatchetKeyPrivate := [],
            chainKey := rc.chainKey.map fun ck => (ck.index, CryptoGames.HMAC.keyToBytes32 ck.key), messageKeys := [] },
        pendingPreKey := none, remoteRegistrationId := 0, localRegistrationId := 0,
        aliceBaseKey := [], pendingKyberPreKey := none, pqRatchetState := s.state.pqRatchetState } := by
  simp [eraseSkipped, eraseUnmodelled, sessionToSessionRec, receiverChainToChainRec]

end Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
