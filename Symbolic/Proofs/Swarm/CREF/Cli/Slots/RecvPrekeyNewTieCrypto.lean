/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelDefs
public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.ModelProofs.AdvanceAndFrame
import Symbolic.Proofs.Refinement.LemmasPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewSpqr
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Fresh Pre-Key Receive Decrypt Unpacking

Unpacks a successful `tryDecryptWithStateW` execution on a freshly initialized recipient session
(`st0.receiverChains = []`) into its DH-ratchet `rootCreateChain` step, `chainStepN` message key
derivation, SPQR V1 receive step, MAC verification, and AES-CBC decryption.
-/

@[expose] public section

set_option autoImplicit false
cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.Cli

theorem ofFn_getD_toList_32 {l : HwBytes} (hl : l.length = 32) :
    (List.Vector.ofFn (n := 32) (fun i => l.getD i.val 0#8)).toList = l := by
  rw [List.Vector.toList_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, hl]
  · intro j _hj1 hj2
    rw [List.getElem_ofFn]
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]

theorem vector32_eq_ofFn_getD {v : List.Vector (BitVec 8) 32} {l : HwBytes}
    (h : v.toList = l) :
    v = List.Vector.ofFn (fun i => l.getD i.val 0#8) := by
  apply List.Vector.eq
  have hl : l.length = 32 := h ▸ v.2
  rw [h, ofFn_getD_toList_32 hl]

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply List.Vector.eq
  rw [Proofs.libsignal.RngG.CliPure.DecCrypto.clampScalar_toList_eq_clamp_toList,
      Proofs.libsignal.RngG.CliPure.DecCrypto.clampScalar_toList_eq_clamp_toList,
      DY.Libsignal.TripleRatchet.Refinement.clamp_clamp]

theorem clampScalar_ofFn_clamp_toList {b : HwBytes} (hb : b.length = 32) :
    (Ratchet.clampScalar (List.Vector.ofFn (n := 32) (fun i =>
      (DY.Libsignal.TripleRatchet.Refinement.clamp b).getD i.val 0#8))).toList =
    DY.Libsignal.TripleRatchet.Refinement.clamp b := by
  have hcl : (DY.Libsignal.TripleRatchet.Refinement.clamp b).length = 32 := by
    simp [DY.Libsignal.TripleRatchet.Refinement.clamp, hb]
  rw [Proofs.libsignal.RngG.CliPure.DecCrypto.clampScalar_toList_eq_clamp_toList,
    ofFn_getD_toList_32 hcl,
    DY.Libsignal.TripleRatchet.Refinement.clamp_clamp]

theorem setReceiverChainKey_senderChain {their : PublicKey} {ck : ChainKey}
    {r_in r_out : RatchetState}
    (h : Mut.exec (RatchetState.setReceiverChainKey their ck) r_in = (.ok (), r_out)) :
    r_out.senderChain = r_in.senderChain := by
  unfold RatchetState.setReceiverChainKey at h
  rw [mut_exec_bind, mut_exec_get] at h
  dsimp only at h
  cases hidx : r_in.findReceiverChainIndex their with
  | none => rw [hidx, mut_exec_throw] at h; cases h
  | some chainIdx =>
    rw [hidx] at h; dsimp only at h
    cases hrc : r_in.receiverChains[chainIdx]? with
    | none => rw [hrc, mut_exec_throw] at h; cases h
    | some c =>
      rw [hrc, mut_exec_set] at h
      injection h with _ hr
      rw [← hr]

theorem storeSkippedKey_senderChain {their : PublicKey} {mkg : MessageKeyGenerator}
    {r_in r_out : RatchetState}
    (h : Mut.exec (RatchetState.storeSkippedKey their mkg) r_in = (.ok (), r_out)) :
    r_out.senderChain = r_in.senderChain := by
  unfold RatchetState.storeSkippedKey at h
  rw [mut_exec_bind, mut_exec_get] at h
  dsimp only at h
  cases hidx : r_in.findReceiverChainIndex their with
  | none => rw [hidx, mut_exec_throw] at h; cases h
  | some chainIdx =>
    rw [hidx] at h; dsimp only at h
    cases hrc : r_in.receiverChains[chainIdx]? with
    | none => rw [hrc, mut_exec_throw] at h; cases h
    | some c =>
      rw [hrc, mut_exec_set] at h
      injection h with _ hr; rw [← hr]

theorem advanceChain_ok_inv_ck_and_senderChain
    (F : ShaCompress) (their : PublicKey) (target : BitVec 32) :
    ∀ (steps : Nat) (ck ck_out : ChainKey) (r_in r_out : RatchetState),
      ck.index.toNat + steps = target.toNat →
      Mut.exec (RatchetState.advanceChain F their target steps ck) r_in = (.ok ck_out, r_out) →
      ck_out = CryptoVerification.SessionModel.chainStepN F steps ck ∧
      r_out.senderChain = r_in.senderChain
  | 0, ck, ck_out, r_in, r_out, _, h => by
    unfold RatchetState.advanceChain at h
    rw [mut_exec_pure] at h
    injection h with h1 h2
    injection h1 with hck
    subst hck h2
    exact ⟨rfl, rfl⟩
  | n + 1, ck, ck_out, r_in, r_out, htgt, h => by
    have hlt : ck.index < target := by simp [BitVec.lt_def]; omega
    unfold RatchetState.advanceChain at h
    simp only [hlt, ↓reduceIte] at h
    rw [mut_exec_bind] at h
    rcases hs1 : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r_in with
      ⟨e1 | u1, r1⟩
    · rw [hs1] at h; cases h
    · rw [hs1] at h; dsimp only at h
      have hr1_sc : r1.senderChain = r_in.senderChain := storeSkippedKey_senderChain hs1
      rw [mut_exec_bind, mut_exec_liftE] at h
      rcases hn1 : ck.nextChainKey F with e2 | ck1
      · rw [hn1] at h; cases h
      · rw [hn1] at h; dsimp only at h
        have hstep1 : ck1 = CryptoVerification.SessionModel.AdvanceAndFrame.step1 F ck ∧
            ck1.index.toNat = ck.index.toNat + 1 := by
          unfold ChainKey.nextChainKey at hn1
          split at hn1
          · cases hn1
          · rename_i hmax
            injection hn1 with heq
            rw [← heq]
            refine ⟨rfl, ?_⟩
            have hlt32 : target.toNat < 2 ^ 32 := target.isLt
            have h1 : (1 : BitVec 32).toNat = 1 := rfl
            dsimp only
            rw [BitVec.toNat_add, h1]
            omega
        obtain ⟨hck_rec, hsc_rec⟩ :=
          advanceChain_ok_inv_ck_and_senderChain F their target n ck1 ck_out r1 r_out
            (by omega) h
        rw [hck_rec, hstep1.1]
        exact ⟨rfl, hsc_rec.trans hr1_sc⟩

/-- When `ck.index = 0`, an `.ok` execution of `consumeMessageKey` advances `ck` by
`counter.toNat <= r1.maxForwardJumps` steps and preserves `senderChain`. -/
theorem consumeMessageKey_index_zero_ok_inv
    {F : ShaCompress} {their : PublicKey} {ck : ChainKey}
    {counter : BitVec 32} {msgType : MessageType}
    {r1 r2 : RatchetState} {mkGen : MessageKeyGenerator}
    (hidx : ck.index = 0)
    (hok : Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r1 =
      (.ok mkGen, r2)) :
    counter.toNat ≤ r1.maxForwardJumps ∧
    mkGen = (CryptoVerification.SessionModel.chainStepN F counter.toNat ck).messageKeys F ∧
    r2.senderChain = r1.senderChain := by
  rcases Proofs.libsignal.RngG.CliPure.DecCrypto.consumeMessageKey_ok_inv hok with
    ⟨hlt, _⟩ | ⟨_, hle, ck_adv, _ck_next, r_adv, hadv, _hnext, hset, hmk⟩
  · exfalso
    rw [hidx] at hlt
    simp [BitVec.lt_def] at hlt
  · have hsub : counter - ck.index = counter := by rw [hidx]; simp
    rw [hsub] at hle hadv
    obtain ⟨hck_adv, hsc_adv⟩ :=
      advanceChain_ok_inv_ck_and_senderChain F their counter counter.toNat ck ck_adv r1 r_adv
        (by simp [hidx]) hadv
    have hsc_set := setReceiverChainKey_senderChain hset
    exact ⟨hle, hmk.trans (congrArg (fun c => ChainKey.messageKeys F c) hck_adv),
      hsc_set.trans hsc_adv⟩

/-- On a freshly initialized `RatchetState` (`r0.receiverChains = []`), `ensureReceiverChain`
must execute `dhRatchetStep`, preserving `maxForwardJumps` and replacing `senderChain` with a
freshly generated clamped key pair. -/
theorem ensureReceiverChain_nil_ok_inv
    {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hr0 : r0.receiverChains = [])
    (hok : Mut.exec (RatchetState.ensureReceiverChain C their coins) r0 = (.ok ck, r1)) :
    ∃ (sc : SenderChain) (newRootKey : BitVec 256),
      r0.senderChain = some sc ∧
      rootCreateChain C r0.rootKey their sc.ratchetKey.privateKey = .ok (newRootKey, ck) ∧
      ck.index = 0 ∧
      r1.maxForwardJumps = r0.maxForwardJumps ∧
      (∀ sc1, r1.senderChain = some sc1 →
        Ratchet.clampScalar sc1.ratchetKey.privateKey.bytes = sc1.ratchetKey.privateKey.bytes) := by
  rcases Proofs.libsignal.RngG.CliPure.DecCrypto.ensureReceiverChain_ok_inv hok with
    ⟨hfind, _⟩ | ⟨_, hdh⟩
  · exfalso
    unfold RatchetState.findReceiverChainKey at hfind
    rw [hr0] at hfind
    cases hidx : r0.findReceiverChainIndex their <;> simp [hidx] at hfind
  · have hidx := Proofs.libsignal.RngG.CliPure.DecCrypto.dhRatchetStep_ok_index_eq_zero hdh
    obtain ⟨sc, newRootKey, _finalRk, _senderCk, hsc, hrc1, _hrc2, hr1⟩ :=
      Proofs.libsignal.RngG.CliPure.DecCrypto.dhRatchetStep_ok_inv hdh
    refine ⟨sc, newRootKey, hsc, hrc1, hidx, by rw [hr1], ?_⟩
    intro sc1 hsc1
    rw [hr1] at hsc1
    dsimp only at hsc1
    injection hsc1 with hsc1_eq
    rw [← hsc1_eq]
    dsimp only [KeyPair.generate]
    exact clampScalar_idem _

/-- Any `.ok` SPQR V1 receive step on Bob's initial `spqrInitB` state requires a non-empty
`pqRatchet` payload (`[]` decodes as version `0 < 1`, failing `minimumVersion`). -/
theorem spqrV1WithMac_recv_spqrInitB_ok_pqRatchet_ne_nil
    {F : ShaCompress} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {mac : Symbolic.Swarm.SHARED.HookAuth.HmacFn}
    {pqr pqRatchet st' : HwBytes} {salt : CryptoGames.HKDF.Salt}
    (hpqr : pqr.length = 32)
    (hok : (Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac F K mac).recv
      (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitB F K mac pqr [1#8]) pqRatchet =
      .ok (st', salt)) :
    pqRatchet ≠ [] := by
  rintro rfl
  unfold Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac
    CryptoVerification.LibsignalSpqrV1.toSpqrModel
    CryptoVerification.LibsignalSpqrV1.recv at hok
  dsimp only at hok
  have hpre : CryptoVerification.LibsignalSpqrV1.msgPreamble [] =
      .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } := rfl
  rw [hpre, decodeState_spqrInitB_b2a_eq F K mac hpqr] at hok
  have hminv : (b0VnPb pqr).minVersion.truncate 8 = 1#8 := rfl
  dsimp only [CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind] at hok
  simp [hminv] at hok

private theorem nck_length_hmacWith (F : ShaCompress) (k m : HwBytes) :
    (CryptoGames.HMAC.hmacWith F k m).length = 32 := by
  change (ByteSpecs.sha256With F _).length = 32
  unfold ByteSpecs.sha256With
  generalize (ByteSpecs.chunks64 (ByteSpecs.sha256Pad _)).foldl F ByteSpecs.sha256IV = s
  rcases s with ⟨l, hl⟩
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    cases hl
  rfl

private theorem hmacWith_eq_byteSpecs (F : ShaCompress) (k m : HwBytes) :
    CryptoGames.HMAC.hmacWith F k m = ByteSpecs.hmacWith F k m := rfl

theorem generateKeys_salt_eq_bytes
    (F : ShaCompress) (mkg : MessageKeyGenerator) (pqrKey : CryptoGames.HKDF.Salt) :
    let prk := CryptoGames.HKDF.hkdfExtract F pqrKey mkg.seed
    let mk := mkg.generateKeys F pqrKey
    let t1 := CryptoGames.HMAC.hmacWith F prk
      ([] ++ CryptoGames.HKDF.whisperMessageKeys ++ [1#8])
    let t2 := CryptoGames.HMAC.hmacWith F prk
      (t1 ++ CryptoGames.HKDF.whisperMessageKeys ++ [2#8])
    let t3 := CryptoGames.HMAC.hmacWith F prk
      (t2 ++ CryptoGames.HKDF.whisperMessageKeys ++ [3#8])
    CryptoGames.HMAC.keyToBytes32 mk.cipherKey = t1 ∧
    CryptoGames.HMAC.keyToBytes32 mk.macKey = t2 ∧
    CryptoGames.CBC.blockToBytesLE mk.iv = t3.take 16 ∧
    mk.macKey = CryptoGames.HKDF.bytesToKey32 t2 := by
  intro prk mk t1 t2 t3
  have hnck : ∀ k m, (CryptoGames.HMAC.hmacWith F k m).length = 32 := nck_length_hmacWith F
  have ht1 : t1.length = 32 := hnck _ _
  have ht2 : t2.length = 32 := hnck _ _
  have h80 : CryptoGames.HKDF.hkdfExpand F prk CryptoGames.HKDF.whisperMessageKeys 80 =
      t1 ++ t2 ++ t3.take 16 := by
    dsimp only [CryptoGames.HKDF.hkdfExpand]
    have h3 : (80 + 31) / 32 = 3 := rfl
    have hblocks :
        (CryptoGames.HKDF.hkdfBlocks F prk CryptoGames.HKDF.whisperMessageKeys 3).flatten =
          (t1 ++ t2) ++ t3 := by
      simp [CryptoGames.HKDF.hkdfBlocks, t1, t2, t3, List.append_assoc]
    have hlen12 : (t1 ++ t2).length = 64 := by simp [ht1, ht2]
    rw [h3, hblocks, List.take_append, List.take_of_length_le (by omega), hlen12]
  have hmk_def : mk = ⟨(CryptoGames.HKDF.deriveMessageKeys F pqrKey mkg.seed).1.1,
      (CryptoGames.HKDF.deriveMessageKeys F pqrKey mkg.seed).2,
      (CryptoGames.HKDF.deriveMessageKeys F pqrKey mkg.seed).1.2, mkg.counter⟩ := rfl
  have hokm : CryptoGames.HKDF.hkdf F pqrKey mkg.seed CryptoGames.HKDF.whisperMessageKeys 80 =
      t1 ++ t2 ++ t3.take 16 := h80
  have hc_take : (t1 ++ t2 ++ t3.take 16).take 32 = t1 := by
    rw [List.append_assoc, List.take_left' ht1]
  have hm_take : ((t1 ++ t2 ++ t3.take 16).drop 32).take 32 = t2 := by
    rw [List.append_assoc, List.drop_left' ht1, List.take_left' ht2]
  have hiv_take : ((t1 ++ t2 ++ t3.take 16).drop 64).take 16 = t3.take 16 := by
    have h12 : (t1 ++ t2).length = 64 := by simp [ht1, ht2]
    rw [← h12, List.drop_left, List.take_take, Nat.min_self]
  have hc_key : mk.cipherKey = CryptoGames.HKDF.bytesToKey32 t1 := by
    rw [hmk_def]; dsimp only [CryptoGames.HKDF.deriveMessageKeys]; rw [hokm, hc_take]
  have hm_key : mk.macKey = CryptoGames.HKDF.bytesToKey32 t2 := by
    rw [hmk_def]; dsimp only [CryptoGames.HKDF.deriveMessageKeys]; rw [hokm, hm_take]
  have hiv_blk : mk.iv = CryptoGames.CBC.bytesToBlock (t3.take 16) := by
    rw [hmk_def]; dsimp only [CryptoGames.HKDF.deriveMessageKeys]; rw [hokm, hiv_take]
  have ht3_len : (t3.take 16).length = 16 := by
    have ht3 : t3.length = 32 := hnck _ _
    simp [ht3]
  refine ⟨?_, ?_, ?_, hm_key⟩
  · rw [hc_key, Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 t1 ht1]
  · rw [hm_key, Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 t2 ht2]
  · rw [hiv_blk, Proofs.libsignal.RngG.CliPure.DecCrypto.blockToBytesLE_bytesToBlock_of_length_eq_16 _ ht3_len]

theorem generateKeys_eq_trMsgKeys_of_prk
    (F : ShaCompress) (mkg : MessageKeyGenerator) (pqrKey : CryptoGames.HKDF.Salt)
    (salt seed : HwBytes)
    (hprk : CryptoGames.HKDF.hkdfExtract F pqrKey mkg.seed =
      CryptoGames.HMAC.hmacWith F salt seed) :
    let mk := mkg.generateKeys F pqrKey
    CryptoGames.HMAC.keyToBytes32 mk.cipherKey = TR.trCipherKeyBytes F salt seed ∧
    CryptoGames.HMAC.keyToBytes32 mk.macKey = TR.trMacKeyBytes F salt seed ∧
    CryptoGames.CBC.blockToBytesLE mk.iv = (TR.trIvBytes F salt seed).take 16 ∧
    mk.macKey = CryptoGames.HKDF.bytesToKey32 (TR.trMacKeyBytes F salt seed) := by
  obtain ⟨hc, hm, hiv, hm_key⟩ := generateKeys_salt_eq_bytes F mkg pqrKey
  have hinfo : CryptoGames.HKDF.whisperMessageKeys = TR.whisperMessageKeysBytes := rfl
  dsimp only at hc hm hiv hm_key ⊢
  rw [hprk, hinfo] at hc hm hiv hm_key
  simp only [hmacWith_eq_byteSpecs, List.nil_append, List.append_assoc] at hc hm hiv hm_key
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [TR.trCipherKeyBytes, TR.hkdfBlock1Bytes, List.append_assoc] using hc
  · simpa [TR.trMacKeyBytes, TR.hkdfBlock2Bytes, TR.hkdfBlock1Bytes, List.append_assoc] using hm
  · simpa [TR.trIvBytes, TR.hkdfBlock3Bytes, TR.hkdfBlock2Bytes, TR.hkdfBlock1Bytes,
      List.append_assoc] using hiv
  · simpa [TR.trMacKeyBytes, TR.hkdfBlock2Bytes, TR.hkdfBlock1Bytes, List.append_assoc] using hm_key

theorem chainStepN_key_eq_chainKeyAtBytes
    (F : ShaCompress) :
    ∀ (n : Nat) (ck0 : HwBytes) (idx : BitVec 32),
      ck0.length = 32 →
      (CryptoVerification.SessionModel.chainStepN F n
        ⟨CryptoGames.HKDF.bytesToKey32 ck0, idx⟩).key =
        CryptoGames.HKDF.bytesToKey32 (TR.chainKeyAtBytes F ck0 n) ∧
      (TR.chainKeyAtBytes F ck0 n).length = 32
  | 0, ck0, _idx, hlen => ⟨rfl, hlen⟩
  | n + 1, ck0, idx, hlen => by
    have hstep :
        CryptoGames.Ratchet.chainHmac F (CryptoGames.HKDF.bytesToKey32 ck0)
          CryptoGames.Ratchet.chainKeySeed =
          ByteSpecs.hmacWith F ck0 [0x02#8] := by
      unfold CryptoGames.Ratchet.chainHmac CryptoGames.Ratchet.chainKeySeed
      rw [Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 ck0 hlen]
      rfl
    have hlen1 : (ByteSpecs.hmacWith F ck0 [0x02#8]).length = 32 :=
      TR.length_hmacWith F _ _
    simp only [CryptoVerification.SessionModel.chainStepN, TR.chainKeyAtBytes]
    change (CryptoVerification.SessionModel.chainStepN F n
      (CryptoVerification.SessionModel.AdvanceAndFrame.step1 F
        ⟨CryptoGames.HKDF.bytesToKey32 ck0, idx⟩)).key = _ ∧ _
    unfold CryptoVerification.SessionModel.AdvanceAndFrame.step1
    rw [hstep]
    exact chainStepN_key_eq_chainKeyAtBytes F n _ (idx + 1) hlen1

theorem chainStepN_messageKeys_seed_eq_recvSeedBytes
    (F : ShaCompress) (n : Nat) (ck0 : HwBytes) (idx : BitVec 32) (hlen : ck0.length = 32) :
    ((CryptoVerification.SessionModel.chainStepN F n
      ⟨CryptoGames.HKDF.bytesToKey32 ck0, idx⟩).messageKeys F).seed =
      TR.recvSeedBytes F ck0 n := by
  obtain ⟨hkey, hlen_n⟩ := chainStepN_key_eq_chainKeyAtBytes F n ck0 idx hlen
  unfold ChainKey.messageKeys CryptoGames.Ratchet.chainHmac CryptoGames.Ratchet.messageKeySeed
    TR.recvSeedBytes
  dsimp only
  rw [hkey, Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 _ hlen_n]
  rfl

/-- Inverts `rootCreateChain` on 32-byte keys, proving `their.bytes` is not low-order and
`ck` equals `(bytesToKey32 (TR.createChainKeyBytes interp rk their.bytes.toList ourSk), 0)`. -/
theorem rootCreateChain_ok_bytes_and_not_lowOrder
    {interp : ExternInterpretation}
    (hExt : ExternContractsHoldCli interp)
    {rk ourSk : HwBytes} {newRk : BitVec 256}
    {their : PublicKey} {our : PrivateKey} {ck : ChainKey}
    (hrk : rk.length = 32) (hourSk : ourSk.length = 32)
    (hcl : (Ratchet.clampScalar our.bytes).toList =
      DY.Libsignal.TripleRatchet.Refinement.clamp ourSk)
    (hok : rootCreateChain (Proofs.libsignal.Hooks2.cryptoOf' interp)
      (CryptoGames.HKDF.bytesToKey32 rk) their our = .ok (newRk, ck)) :
    DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat) = false ∧
    ck = ⟨CryptoGames.HKDF.bytesToKey32
      (TR.createChainKeyBytes interp rk their.bytes.toList ourSk), 0⟩ ∧
    (TR.createChainKeyBytes interp rk their.bytes.toList ourSk).length = 32 := by
  have hcl_len : (DY.Libsignal.TripleRatchet.Refinement.clamp ourSk).length = 32 := by
    simp [DY.Libsignal.TripleRatchet.Refinement.clamp, hourSk]
  have htheir_len : their.bytes.toList.length = 32 := their.bytes.2
  have hag_len : (TR.dhAgreeBytes interp ourSk their.bytes.toList).length = 32 :=
    hExt.1.x25519_agreement_length _ _
  have hX_toList :
      ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
        their.bytes).toList =
        TR.dhAgreeBytes interp ourSk their.bytes.toList := by
    unfold Proofs.libsignal.Hooks2.cryptoOf' TR.dhAgreeBytes
    dsimp only
    rw [hcl]
    exact Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hag_len
  have hlow : DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat) = false := by
    cases hl : DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat)
    · rfl
    · exfalso
      have hz := (hExt.1.x25519_agreement_zero_iff_low_order
        (DY.Libsignal.TripleRatchet.Refinement.clamp ourSk) their.bytes.toList
        hcl_len htheir_len).mpr hl
      have hz' : ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
          their.bytes).toList = List.replicate 32 0#8 := by
        rw [hX_toList]; exact hz
      rw [Proofs.libsignal.RngG.CliPure.DecCrypto.rootCreateChain_of_rel_lowOrder interp _ _ _ _ _ hz'] at hok
      cases hok
  unfold rootCreateChain Ratchet.createChain Ratchet.rootKdf at hok
  dsimp only at hok
  by_cases hzero :
      ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
        their.bytes).toList = List.replicate 32 0#8
  · simp [hzero] at hok
  · simp only [hzero, ↓reduceIte] at hok
    injection hok with hpair
    obtain ⟨_, hck⟩ := Prod.mk.inj hpair
    rw [← hck]
    let F := sha256CompressFunction interp
    have hsalt : CryptoGames.HKDF.hkdfExtract F
        (Ratchet.rootSalt (CryptoGames.HKDF.bytesToKey32 rk))
        ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
          their.bytes).toList =
        CryptoGames.HMAC.hmacWith F rk (TR.dhAgreeBytes interp ourSk their.bytes.toList) := by
      have hrs : (Ratchet.rootSalt (CryptoGames.HKDF.bytesToKey32 rk)).map List.Vector.toList =
          some (CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 rk)) := rfl
      unfold CryptoGames.HKDF.hkdfExtract
      rw [hrs, Option.getD_some,
        Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 rk hrk,
        hX_toList]
    have h64 := Proofs.libsignal.RngG.CliPure.DecCrypto.hkdf_64_whisperRatchet F
      (Ratchet.rootSalt (CryptoGames.HKDF.bytesToKey32 rk))
      ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
        their.bytes).toList
    have hwr : Ratchet.whisperRatchetInfo = TR.whisperRatchetBytes := rfl
    have hck_bytes :
        ((CryptoGames.HKDF.hkdf F
          (Ratchet.rootSalt (CryptoGames.HKDF.bytesToKey32 rk))
          ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
            their.bytes).toList Ratchet.whisperRatchetInfo 64).drop 32).take 32 =
        TR.createChainKeyBytes interp rk their.bytes.toList ourSk := by
      rw [h64.2.2]
      unfold TR.createChainKeyBytes TR.hkdfBlock2Bytes TR.hkdfBlock1Bytes
      rw [hsalt, hwr]
      simp [hmacWith_eq_byteSpecs, List.append_assoc, F]
    have hcc_len : (TR.createChainKeyBytes interp rk their.bytes.toList ourSk).length = 32 :=
      TR.length_hmacWith _ _ _
    refine ⟨hlow, ?_, hcc_len⟩
    change ChainKey.mk (CryptoGames.HKDF.bytesToKey32
        (((CryptoGames.HKDF.hkdf F
          (Ratchet.rootSalt (CryptoGames.HKDF.bytesToKey32 rk))
          ((Proofs.libsignal.Hooks2.cryptoOf' interp).X (Ratchet.clampScalar our.bytes)
            their.bytes).toList Ratchet.whisperRatchetInfo 64).drop 32).take 32)) 0 = _
    rw [hck_bytes]

/-- Unpack an `.ok` execution of `tryDecryptWithStateW` on a fresh session (`st0.receiverChains = []`)
into its DH-ratchet `rootCreateChain`, `chainStepN` message key generator, SPQR V1 `.recv`,
`verifyMac`, AES-CBC decryption, `pendingPreKey = false`, and clamped `st'.senderChain`. -/
theorem tryDecryptWithStateW_nil_unpack
    {interp : ExternInterpretation}
    {expected : Option HwBytes} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st0 st' : SessionState HwBytes} {pt : HwBytes}
    (hr0 : st0.receiverChains = [])
    (hok : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
      (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
      (Symbolic.Swarm.CREF.Cli.pureSpqrOf interp) expected msg msgType coins) st0 =
      (.ok pt, st')) :
    st'.pendingPreKey = false ∧
    (∀ sc1, st'.senderChain = some sc1 →
      Ratchet.clampScalar sc1.ratchetKey.privateKey.bytes = sc1.ratchetKey.privateKey.bytes) ∧
    msg.counter.toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps ∧
    ∃ (remIk : IdentityKey) (sc0 : SenderChain) (newRk : BitVec 256) (ck : ChainKey)
      (newPqrState : HwBytes) (pqrKey : CryptoGames.HKDF.Salt),
      st0.remoteIdentity = some remIk ∧
      st0.senderChain = some sc0 ∧
      rootCreateChain (Proofs.libsignal.Hooks2.cryptoOf' interp) st0.rootKey
        msg.senderRatchetKey sc0.ratchetKey.privateKey = .ok (newRk, ck) ∧
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).recv st0.pqRatchetState msg.pqRatchet =
        .ok (newPqrState, pqrKey) ∧
      let F := sha256CompressFunction interp
      let mkGen := (CryptoVerification.SessionModel.chainStepN F msg.counter.toNat ck).messageKeys F
      let mks := mkGen.generateKeys F pqrKey
      msg.verifyMac F remIk st0.localIdentity mks.macKey = true ∧
      interp aesCbcDecryptSymbol
        [msg.ciphertext, CryptoGames.HMAC.keyToBytes32 mks.cipherKey,
         CryptoGames.CBC.blockToBytesLE mks.iv] = some pt := by
  obtain ⟨remIk, tr_out, hrem, htr, hst'⟩ :=
    Proofs.libsignal.RngG.CliPure.DecCrypto.tryDecryptWithStateW_interpW_ok_inv hok
  obtain ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, hens, hcmk, hspqr, hmac_addr, hdec, htr_out⟩ :=
    Proofs.libsignal.RngG.CliPure.DecCrypto.tripleRatchet_decryptW_interpW_ok_inv htr
  obtain ⟨sc0, newRk, hsc0, hrc1, hidx0, hmfj, hr1_cl⟩ :=
    ensureReceiverChain_nil_ok_inv hr0 hens
  obtain ⟨hctr_le, hmkGen, hr2_sc⟩ := consumeMessageKey_index_zero_ok_inv hidx0 hcmk
  have hF_eq : (Proofs.libsignal.Hooks2.cryptoOf' interp).F = sha256CompressFunction interp := rfl
  rw [hF_eq] at hmkGen hdec
  have hmac : msg.verifyMac (sha256CompressFunction interp) remIk st0.localIdentity
      (mkGen.generateKeys (sha256CompressFunction interp) pqrKey).macKey = true :=
    (Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hmac_addr |>.1
  have hctr_le' : msg.counter.toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps := by
    rw [hmfj] at hctr_le
    exact hctr_le
  have hst'_cl : ∀ sc1, st'.senderChain = some sc1 →
      Ratchet.clampScalar sc1.ratchetKey.privateKey.bytes = sc1.ratchetKey.privateKey.bytes := by
    intro sc1 hsc1
    rw [hst', htr_out] at hsc1
    dsimp only at hsc1
    rw [hr2_sc] at hsc1
    exact hr1_cl sc1 hsc1
  refine ⟨by rw [hst'], hst'_cl, hctr_le',
    remIk, sc0, newRk, ck, newPqrState, pqrKey, hrem, hsc0, hrc1, hspqr, ?_, ?_⟩
  · rw [← hmkGen]
    exact hmac
  · rw [← hmkGen]
    exact hdec

end Symbolic.Swarm.CREF.Cli.Slots
