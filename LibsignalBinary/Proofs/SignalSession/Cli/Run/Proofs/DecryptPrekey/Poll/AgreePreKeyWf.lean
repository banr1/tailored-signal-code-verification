/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins

/-!
# Canonical Pre-Key Record Inversion under `PreKeyFilesWf`

Under `PreKeyFilesWf W F`, any record returned by `getSignedPreKey`, `getPreKey`, or
`KyberGhost.get` on `StoresGhost.opened` is the canonical deserialization of `signedRecordBytes`,
`oneTimeRecordBytes`, or `kyberRecordBytes`, pinning its public and private key byte fields and
lengths for `StageP2` and `pkStoreKeys` agreement.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

theorem signed_canonical_of_preKeysWf {W : PEParams} {F : FsFiles}
    (hwf : PreKeyFilesWf W F) {id : BitVec 32} {sr : SignedPreKeyRecord}
    (hget : getSignedPreKey cliIo.rd F StoresGhost.opened.signed id = .ok sr) :
    ∃ k : PqSignedKey,
      sr = ⟨⟨id, djbKey (keyPairOf W.C k.priv).publicKey.bytes,
              k.priv.toList, k.sig.toList, k.timestamp⟩⟩ ∧
      pkVec? 32 sr.signedPreKey.privateKey = some k.priv := by
  unfold getSignedPreKey at hget
  rcases hd : StoresGhost.opened.signed.get cliIo.rd F (keyName id) with _ | bs
  · rw [hd] at hget; cases hget
  · rcases hwf.signed id bs hd with rfl | ⟨k, rfl⟩
    · rw [hd] at hget; cases hget
    · rw [hd] at hget
      have hdec : SignedPreKeyRecord.deserialize (signedRecordBytes W.C id k) =
          .ok ⟨⟨id, djbKey (keyPairOf W.C k.priv).publicKey.bytes,
                k.priv.toList, k.sig.toList, k.timestamp⟩⟩ := by
        have h := SignedPreKeyRecordStructure.decode_encode
          ⟨id, djbKey (keyPairOf W.C k.priv).publicKey.bytes,
            k.priv.toList, k.sig.toList, k.timestamp⟩
          (by simp [djbKey]) (by simp [k.priv.toList_length]) (by simp [k.sig.toList_length])
        unfold signedRecordBytes SignedPreKeyRecord.deserialize
        rw [h]
      cases hne : signedRecordBytes W.C id k with
      | nil => rw [hne] at hget; cases hget
      | cons b rest =>
        rw [hne] at hget hdec
        dsimp only [Cli.record, Bind.bind, Except.bind, Except.map] at hget
        rw [hdec] at hget
        dsimp only at hget
        injection hget with hsr
        subst hsr
        exact ⟨k, rfl, DecPkS0.pkVec?_toList k.priv⟩

theorem oneTime_canonical_of_preKeysWf {W : PEParams} {F : FsFiles}
    (hwf : PreKeyFilesWf W F) {id : BitVec 32} {r : PreKeyRecord}
    (hget : getPreKey cliIo.rd F StoresGhost.opened.oneTime id = .ok r) :
    ∃ sk : List.Vector (BitVec 8) 32,
      r = ⟨⟨id, djbKey (keyPairOf W.C sk).publicKey.bytes, sk.toList⟩⟩ ∧
      pkVec? 32 r.preKey.privateKey = some sk := by
  unfold getPreKey at hget
  rcases hd : StoresGhost.opened.oneTime.get cliIo.rd F (keyName id) with _ | bs
  · rw [hd] at hget; cases hget
  · rcases hwf.oneTime id bs hd with rfl | ⟨sk, rfl⟩
    · rw [hd] at hget; cases hget
    · rw [hd] at hget
      have hdec : PreKeyRecord.deserialize (oneTimeRecordBytes W.C id sk) =
          .ok ⟨⟨id, djbKey (keyPairOf W.C sk).publicKey.bytes, sk.toList⟩⟩ := by
        have h := PreKeyRecordStructure.decode_encode
          ⟨id, djbKey (keyPairOf W.C sk).publicKey.bytes, sk.toList⟩
          (by simp [djbKey]) (by simp [sk.toList_length])
        unfold oneTimeRecordBytes PreKeyRecord.deserialize
        rw [h]
      cases hne : oneTimeRecordBytes W.C id sk with
      | nil => rw [hne] at hget; cases hget
      | cons b rest =>
        rw [hne] at hget hdec
        dsimp only [Cli.record, Bind.bind, Except.bind, Except.map] at hget
        rw [hdec] at hget
        dsimp only at hget
        injection hget with hr
        subst hr
        exact ⟨sk, rfl, DecPkS0.pkVec?_toList sk⟩

theorem kyber_canonical_of_preKeysWf {W : PEParams} {F : FsFiles}
    (hwf : PreKeyFilesWf W F) {id : BitVec 32} {kr : KyberPreKeyRecord}
    (hget : StoresGhost.opened.kyber.get cliIo.rd F id = .ok kr) :
    ∃ k : PqKyberKey,
      kr = ⟨⟨id, kyberKey k.pub, 8#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩⟩ ∧
      pkVecTag? 8 1568 kr.signedPreKey.publicKey = some k.pub ∧
      pkVecTag? 8 3168 kr.signedPreKey.privateKey = some k.sec := by
  have hdeser : ∀ k : PqKyberKey,
       KyberPreKeyRecord.deserialize (kyberRecordBytes id k) =
        .ok ⟨⟨id, kyberKey k.pub, 8#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩⟩ := by
    intro k
    have h := SignedPreKeyRecordStructure.decode_encode
      ⟨id, kyberKey k.pub, 8#8 :: k.sec.toList, k.sig.toList, k.timestamp⟩
      (by simp [kyberKey]) (by simp [k.sec.toList_length]) (by simp [k.sig.toList_length])
    unfold kyberRecordBytes KyberPreKeyRecord.deserialize
    rw [h]
  unfold KyberGhost.get at hget
  rcases h1 : StoresGhost.opened.kyber.oneTime.get cliIo.rd F (keyName id) with
    _ | _ | ⟨b1, bs1⟩
  · rw [h1] at hget; cases hget
  · rw [h1] at hget
    dsimp only [Cli.record, Bind.bind, Except.bind, Pure.pure, Except.pure] at hget
    rcases h2 : StoresGhost.opened.kyber.lastResort.get cliIo.rd F (keyName id) with
      _ | _ | ⟨b2, bs2⟩
    · rw [h2] at hget; cases hget
    · rw [h2] at hget; cases hget
    · rcases hwf.kyberLastResort id (b2 :: bs2) h2 with hnil | ⟨k, hk⟩
      · cases hnil
      · rw [h2] at hget
        have hdec := hk ▸ hdeser k
        dsimp only [Cli.record, Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure] at hget
        rw [hdec] at hget
        dsimp only at hget
        injection hget with hkr
        subst hkr
        exact ⟨k, rfl, DecPkS0.pkVecTag?_cons_self 8#8 k.pub,
          DecPkS0.pkVecTag?_cons_self 8#8 k.sec⟩
  · rcases hwf.kyberOneTime id (b1 :: bs1) h1 with hnil | ⟨k, hk⟩
    · cases hnil
    · rw [h1] at hget
      have hdec := hk ▸ hdeser k
      dsimp only [Cli.record, Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure] at hget
      rw [hdec] at hget
      dsimp only at hget
      injection hget with hkr
      subst hkr
      exact ⟨k, rfl, DecPkS0.pkVecTag?_cons_self 8#8 k.pub,
        DecPkS0.pkVecTag?_cons_self 8#8 k.sec⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
