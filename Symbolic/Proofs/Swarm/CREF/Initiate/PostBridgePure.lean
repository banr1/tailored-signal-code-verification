/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35CliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Session Initiation Postcondition Bridge

Connects the byte-level postcondition `AliceInitiatedV1PostPure` of a successful `initiate` run
and an `aliceStart` trace step to `PureAliceInitPending`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.COMPOSED
open CryptoVerification.E2E.Record

/-- Session-record postcondition of a successful `initiate` run producing `recState`. -/
def AliceInitiatedV1PostPure (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes) : Prop :=
  let g0 : Ghost := ⟨fun _ _ => [], fun _ => []⟩
  let S0 : OpaqueSymbolSemantics := compSemOf interpretation r
  let agr0 := aliceLitAgreement r bundle ds
  let pqr0 := gamma interpretation S0 g0 agr0.2.pqr
  let pqBytes := S0.init pqr0 [0#8]
  ∃ (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
    (spkId kyberPreKeyId remoteRegId : BitVec 32),
    let sess := aliceInitiatedSessionV1
      ourIdentity theirIdentity theirRatchetKey baseKey rk1 ck0 sendingKeyPair ck1 opkId?
      spkId kyberPreKeyId remoteRegId r.regIdA
      (kyberKey (gamma interpretation S0 g0 agr0.1)) pqBytes
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recState sess ∧
    TR.Pure.slots_RecordInScopeP ⟨some sess⟩ ∧
    TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ ∧
    recState.length < 2 ^ 62 ∧
    ourIdentity.serialize = ecKey (pubBytes interpretation (secretBytes r 0)) ∧
    theirIdentity.serialize = ecKey (pubBytes interpretation (secretBytes r 1)) ∧
    baseKey.serialize = ecKey (pubBytes interpretation (ds.getD 0 [])) ∧
    sendingKeyPair.publicKey.bytes.toList = pubBytes interpretation (ds.getD 33 []) ∧
    ck1.index = 0#32 ∧
    CryptoGames.HMAC.keyToBytes32 ck1.key =
      gamma interpretation S0 g0
        (DY.Libsignal.PQXDH.createChain agr0.2.rk
          (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
          (hwLit (ds.getD 33 []))).2 ∧
    CryptoGames.HMAC.keyToBytes32 rk1 =
      gamma interpretation S0 g0
        (DY.Libsignal.TripleRatchet.createChain agr0.2.rk
          (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
          (hwLit (ds.getD 33 []))).1 ∧
    sendingKeyPair.privateKey.bytes.toList = clamp (ds.getD 33 []) ∧
    theirRatchetKey.serialize = ecKey (pubBytes interpretation (secretBytes r 2)) ∧
    CryptoGames.HMAC.keyToBytes32 ck0 = gamma interpretation S0 g0 agr0.2.ck ∧
    (opkId?, spkId, kyberPreKeyId) = DY.Libsignal.Composed.Refinement.bundlePreKeyIds bundle

theorem gamma_tr_createChain_fst (interpretation : ExternInterpretation)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (rk theirPk ourSk : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.createChain rk theirPk ourSk).1 =
      createChainRootBytes interpretation
        (gamma interpretation S g rk) (gamma interpretation S g theirPk)
        (gamma interpretation S g ourSk) := by
  have hcc : (DY.Libsignal.TripleRatchet.createChain rk theirPk ourSk).1 =
      DY.Libsignal.TripleRatchet.hkdfBlock1
        (DY.Libsignal.TripleRatchet.hmac rk (PQXDH.agree theirPk ourSk))
        (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
  rw [hcc, TR.gamma_hkdfBlock1, TR.gamma_hmac, TR.gamma_agree interpretation hEq,
      TR.gamma_whisperRatchet]; rfl

/-- Pure byte-level form of `AliceInitiatedV1PostPure`. -/
theorem aliceInitiatedV1_bytes_pure
    (interpretation : ExternInterpretation)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (r : ProtocolSetup) (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes)
    (hV1 : AliceInitiatedV1PostPure interpretation r bundle ds recState) :
    let F := DY.Libsignal.Refinement.sha256CompressFunction interpretation
    let kdfB := pqxdhKdfBytes F (aliceLitIkmBytes interpretation r bundle ds)
    let ctB := kemEncapCtBytes interpretation (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds)
    let pqBytes := (compSemOf interpretation r).init kdfB.2.2 [0#8]
    ∃ (ourIdentity theirIdentity : IdentityKey)
      (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
      (sendingKeyPair : KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
      (spkId kyberPreKeyId remoteRegId : BitVec 32),
      let sess := aliceInitiatedSessionV1
        ourIdentity theirIdentity theirRatchetKey baseKey rk1 ck0 sendingKeyPair ck1 opkId?
        spkId kyberPreKeyId remoteRegId r.regIdA (kyberKey ctB) pqBytes
      TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recState sess ∧
      TR.Pure.slots_RecordInScopeP ⟨some sess⟩ ∧
      TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ ∧
      recState.length < 2 ^ 62 ∧
      ourIdentity.serialize = ecKey (pubBytes interpretation (secretBytes r 0)) ∧
      theirIdentity.serialize = ecKey (pubBytes interpretation (secretBytes r 1)) ∧
      baseKey.serialize = ecKey (pubBytes interpretation (ds.getD 0 [])) ∧
      sendingKeyPair.publicKey.bytes.toList = pubBytes interpretation (ds.getD 33 []) ∧
      ck1.index = 0#32 ∧
      CryptoGames.HMAC.keyToBytes32 ck1.key =
        createChainKeyBytes interpretation
          kdfB.1 (pubBytes interpretation (secretBytes r 2)) (ds.getD 33 []) ∧
      CryptoGames.HMAC.keyToBytes32 rk1 =
        createChainRootBytes interpretation
          kdfB.1 (pubBytes interpretation (secretBytes r 2)) (ds.getD 33 []) ∧
      sendingKeyPair.privateKey.bytes.toList = clamp (ds.getD 33 []) ∧
      theirRatchetKey.serialize = ecKey (pubBytes interpretation (secretBytes r 2)) ∧
      CryptoGames.HMAC.keyToBytes32 ck0 = kdfB.2.1 ∧
      (opkId?, spkId, kyberPreKeyId) = DY.Libsignal.Composed.Refinement.bundlePreKeyIds bundle := by
  intro F kdfB ctB pqBytes
  let g0 : Ghost := ⟨fun _ _ => [], fun _ => []⟩
  let S0 : OpaqueSymbolSemantics := compSemOf interpretation r
  let agr0 := aliceLitAgreement r bundle ds
  have hstate := hV1
  have ⟨hct, hrk, hck, hpqr⟩ :
      gamma interpretation S0 g0 agr0.1 = ctB ∧
      gamma interpretation S0 g0 agr0.2.rk = kdfB.1 ∧
      gamma interpretation S0 g0 agr0.2.ck = kdfB.2.1 ∧
      gamma interpretation S0 g0 agr0.2.pqr = kdfB.2.2 := by
    have hopk0 :
        ((if bundle[4]? = some 1#8 then some (hwLit (slice bundle 10 32)) else none).map
          (gamma interpretation S0 g0)) =
        if bundle[4]? = some 1#8 then some (slice bundle 10 32) else none := by
      split_ifs <;> [exact congrArg some (gamma_hwLit interpretation S0 g0 (slice bundle 10 32)); rfl]
    exact comp_gamma_aliceAgreement interpretation hEq r g0 bundle ds
      (gamma_hwLit interpretation S0 g0 (secretBytes r 0))
      (gamma_hwLit interpretation S0 g0 (ds.getD 0 []))
      (by rw [gamma_dhPk, gamma_hwLit]; rfl)
      (by rw [gamma_dhPk, gamma_hwLit]; rfl)
      (gamma_hwLit interpretation S0 g0 (r.opaqueBytes (setupPublic r 6)))
      hopk0
      (gamma_hwLit interpretation S0 g0 (entropyBytes ds))
  have hcc2 :
      gamma interpretation S0 g0
        (DY.Libsignal.PQXDH.createChain agr0.2.rk
          (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
          (hwLit (ds.getD 33 []))).2 =
      createChainKeyBytes interpretation
        kdfB.1 (pubBytes interpretation (secretBytes r 2)) (ds.getD 33 []) := by
    rw [gamma_pqxdh_createChain_snd interpretation hEq S0 g0, hrk,
        gamma_dhPk, gamma_hwLit, gamma_hwLit]; rfl
  have hcc1 :
      gamma interpretation S0 g0
        (DY.Libsignal.TripleRatchet.createChain agr0.2.rk
          (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
          (hwLit (ds.getD 33 []))).1 =
      createChainRootBytes interpretation
        kdfB.1 (pubBytes interpretation (secretBytes r 2)) (ds.getD 33 []) := by
    rw [gamma_tr_createChain_fst interpretation hEq S0 g0, hrk,
        gamma_dhPk, gamma_hwLit, gamma_hwLit]; rfl
  have ⟨ourIdentity, theirIdentity, theirRatchetKey, baseKey, rk1, ck0,
    sendingKeyPair, ck1, opkId?, spkId, kyberPreKeyId, remoteRegId,
    hcanon, hscopeP, hscopeQ, hlen62, hourId, htheirId, hbaseKey, hsendPub, hckIdx, hckKey,
    hrk1, hsendPriv, htheirRatchet, hck0, hbids⟩ := hstate
  have hpq_eq : S0.init (gamma interpretation S0 g0 agr0.2.pqr) [0#8] = pqBytes := by
    rw [hpqr]
  rw [hct, hpq_eq] at hcanon hscopeP hscopeQ
  rw [hcc2] at hckKey
  rw [hcc1] at hrk1
  rw [hck] at hck0
  exact ⟨ourIdentity, theirIdentity, theirRatchetKey, baseKey, rk1, ck0,
    sendingKeyPair, ck1, opkId?, spkId, kyberPreKeyId, remoteRegId,
    hcanon, hscopeP, hscopeQ, hlen62, hourId, htheirId, hbaseKey, hsendPub, hckIdx, hckKey,
    hrk1, hsendPriv, htheirRatchet, hck0, hbids⟩

private theorem length_le_lenField (tag : Nat) (body : List (BitVec 8)) :
    body.length ≤ (CryptoVerification.E2E.Record.lenField tag body).length := by
  simp only [CryptoVerification.E2E.Record.lenField, List.length_append]; omega

/-- An accepted `initiate` step explained by `aliceStart` establishes `PureAliceInitPending`
for `recState`. -/
theorem initiate_post_bridge (interpretation : ExternInterpretation)
    (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    {who : List Participant} (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (bundle : HwBytes) (ds : List HwBytes) (recState : HwBytes)
    (bh : DY.Libsignal.PQXDH.BundleHandles)
    (hhon : HonestBundle interpretation r bundle)
    (hV1 : AliceInitiatedV1PostPure interpretation r bundle ds recState)
    (hds_lens : ds.map List.length = initiateFullDrawLengths)
    (hm : MatchedPrefix interpretation r (compSemOf interpretation r) who g
      (ms ++ [.aliceStart r.alice r.bob 4 6 bh 35])
      (acc ++ (.recv bundle :: ds.map MachineEvent.rng))) :
    PureAliceInitPending interpretation r (compSemOf interpretation r) g
      (ms ++ [.aliceStart r.alice r.bob 4 6 bh 35]) recState := by
  have hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation := hext.1
  let S := compSemOf interpretation r
  let tr := runTraceMoves r ms
  have hNe : r.alice ≠ r.bob := hwf.1
  let F := DY.Libsignal.Refinement.sha256CompressFunction interpretation
  let kdfB := pqxdhKdfBytes F (aliceLitIkmBytes interpretation r bundle ds)
  let ctB := kemEncapCtBytes interpretation (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds)
  let pqBytes := S.init kdfB.2.2 [0#8]
  have ⟨ourIdentity, theirIdentity, theirRatchetKey, baseKey, rk1, ck0,
    sendingKeyPair, ck1, opkId?, spkId, kyberPreKeyId, remoteRegId,
    hcanon, hscopeP, hscopeQ, hlen62, hourId, htheirId, hbaseKey, hsendPub, hckIdx, hckKey,
    hrk1, hsendPriv, htheirRatchet, hck0, _⟩ :=
    aliceInitiatedV1_bytes_pure interpretation hEq r bundle ds recState hV1
  let sess := aliceInitiatedSessionV1
    ourIdentity theirIdentity theirRatchetKey baseKey rk1 ck0 sendingKeyPair ck1 opkId?
    spkId kyberPreKeyId remoteRegId r.regIdA (kyberKey ctB) pqBytes
  have hds_len : ds.length = 34 := by
    have := congrArg List.length hds_lens
    simpa [initiateFullDrawLengths] using this
  have hsplit_ds : ds = ds.take 32 ++ ds.drop 32 := (List.take_append_drop 32 ds).symm
  have hdrop_len : (ds.drop 32).length = 2 := by simp [hds_len]
  rcases List.length_eq_two.1 hdrop_len with ⟨d32, d33, hd32_33⟩
  have hmap_eq : acc ++ (.recv bundle :: ds.map MachineEvent.rng) =
      (acc ++ (.recv bundle :: (ds.take 32).map MachineEvent.rng) ++ [MachineEvent.rng d32]) ++ [MachineEvent.rng d33] := by
    conv => lhs; rw [hsplit_ds]
    simp [hd32_33, List.append_assoc]
  have hhm_for := hm.2.2.2.2.2
  rcases aliceStart_next_cases r.alice r.bob 4 6 bh 35 tr with hnext_id | hnext_rnd |
    ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest,
      hstA, hregB, hspk_msg, hspkSig_msg, hpq_msg, hpqSig_msg, hopkH, hnext_ok⟩
  · exfalso
    have hF0 := hhm_for; rw [runVis_snoc, hmap_eq, vis_aliceStart_of_next_id hnext_id] at hF0
    have hlast := (forall₂_snoc_inv hF0).2.1; simp [eventKind] at hlast
  · exfalso
    have hF0 := hhm_for; rw [runVis_snoc, hmap_eq, vis_aliceStart_of_next_rnd hnext_rnd] at hF0
    have h1 : runVis r ms ++ [⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList), .bundle, none⟩, rngEntry (randTerm tr.length 32)] =
        (runVis r ms ++ [⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList), .bundle, none⟩]) ++ [rngEntry (randTerm tr.length 32)] := by
      simp [List.append_assoc]
    rw [h1] at hF0; have hpenult := (forall₂_snoc_inv (forall₂_snoc_inv hF0).1).2.1; simp [eventKind] at hpenult
  · have hle_tr : setupTrace r ≤ tr := setupTrace_le_runTrace r ms
    have hikA_eq : ikA = setupSecret r 0 := by
      unfold CompTrace.PQXDHStoredAt at hstA
      rw [at?_4_of_le r hNe hle_tr] at hstA
      injection hstA with h1; injection h1 with h2; injection h2 with _ h3; injection h3 with _ h4; exact h4.symm
    have hikB_eq : ikB = setupPublic r 2 := by
      simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hregB
      rw [at?_6_of_le r hNe hle_tr] at hregB
      injection hregB with h1; injection h1 with h2; injection h2 with _ h3 _ _; exact h3.symm
    subst hikA_eq hikB_eq
    let o := CompTrace.aliceOut tr (setupSecret r 0) (setupPublic r 2) spk pqpk opk
    have htr' : runTraceMoves r (ms ++ [.aliceStart r.alice r.bob 4 6 bh 35]) = aliceStartTrOfOut tr r.alice r.bob o := by
      rw [runTrace_snoc]; exact hnext_ok
    have hF_all := hhm_for; rw [runVis_snoc, vis_aliceStart_35 hnext_ok] at hF_all
    have hlen35 :
        ((.recv bundle :: ds.map MachineEvent.rng) : List MachineEvent).length =
        ((⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList), .bundle, none⟩ : VisEntry) ::
          (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }])).length := by
      simp [kyberCoinEntries, hds_len]
    have hF_tail := forall₂_append_suffix_of_length_eq hF_all hlen35
    cases hF_tail with
    | cons hhead hF_rng =>
      have hspk_get := getMessageSentAt_of_netMsgAt hspk_msg
      have hspkSig_get := getMessageSentAt_of_netMsgAt hspkSig_msg
      have hpq_get := getMessageSentAt_of_netMsgAt hpq_msg
      have hpqSig_get := getMessageSentAt_of_netMsgAt hpqSig_msg
      have hrec_eq : received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
          [spk, spkSig, pqpk, pqpkSig] ++ opk.toList := by
        rcases hopkH with ⟨hbh_none, rfl⟩ | ⟨idx, u, hbh_some, rfl, hu_msg⟩
        · simp [received, hbh_none, hspk_get, hspkSig_get, hpq_get, hpqSig_get]
        · have hu_get := getMessageSentAt_of_netMsgAt hu_msg
          simp [received, hbh_some, hspk_get, hspkSig_get, hpq_get, hpqSig_get, hu_get]
      have hBM : PreKeyBundleLayoutMatches interpretation S g bundle ([spk, spkSig, pqpk, pqpkSig] ++ opk.toList) := by
        rw [← hrec_eq]; exact hhead.2
      obtain ⟨hγ_spk, hγ_pqpk, hopk_map⟩ := bundleMatches_honest hBM hhon
      obtain ⟨hγ_ek, hγ_e, hγ_dhs⟩ := rng_vis_aliceStart_35 hds_lens hF_rng
      have hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation := hext.1
      have hs0 := (gamma_setupSecret interpretation r hNe S g hm.1).1
      obtain ⟨hp0, hp2, hp6⟩ := gamma_setupPublic_0_2_6 interpretation r S g hm.1 hNe
      have hcomp_agr := comp_gamma_aliceAgreement interpretation hEq r g bundle ds
        hs0 hγ_ek hp2 hγ_spk hγ_pqpk hopk_map hγ_e
      have ho_ikA : o.ikA = DY.DiffieHellman.dhPk (setupSecret r 0) := rfl
      have ho_ikB : o.ikB = setupPublic r 2 := rfl
      have ho_spk : o.spk = spk := rfl
      have ho_ek : o.ek = DY.DiffieHellman.dhPk (randTerm tr.length 32) := rfl
      have ho_ct : gamma interpretation S g o.ct = ctB := hcomp_agr.1
      have ho_rk : gamma interpretation S g o.keys.rk = kdfB.1 := hcomp_agr.2.1
      have ho_ck : gamma interpretation S g o.keys.ck = kdfB.2.1 := hcomp_agr.2.2.1
      have ho_pqr : gamma interpretation S g o.keys.pqr = kdfB.2.2 := hcomp_agr.2.2.2
      have hdhs_len : (gamma interpretation S g (randTerm (tr.length + 2) 32)).length = 32 := by
        have hget := congrArg (fun l : List Nat => l[33]?) hds_lens
        simp [initiateFullDrawLengths] at hget
        rw [hγ_dhs]
        rcases h33 : ds[33]? with _ | d33 <;> simp [List.getD_eq_getElem?_getD, h33] at hget ⊢; exact hget
      have hck0_len : (gamma interpretation S g o.keys.ck).length = 32 :=
        (length_gamma_pqxdhKdf interpretation S g _).2.1
      have hourId_st : ourIdentity.serialize = gamma interpretation S g (PQXDH.serializedIk o.ikA) := by
        rw [hourId, ho_ikA, gamma_serializedIk, gamma_dhPk, hs0]; rfl
      have htheirId_st : theirIdentity.serialize = gamma interpretation S g (PQXDH.serializedIk o.ikB) := by
        rw [htheirId, ho_ikB, gamma_serializedIk, hp2]
      have hrk1_st : CryptoGames.HMAC.keyToBytes32 rk1 =
          gamma interpretation S g (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).1 := by
        rw [hrk1, ho_spk, gamma_tr_createChain_fst interpretation hEq S g, ho_rk, hγ_spk, hγ_dhs]
      have hsendPub_st : sendingKeyPair.publicKey.bytes.toList =
          gamma interpretation S g (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) := by
        rw [hsendPub, gamma_dhPk, hγ_dhs]; rfl
      have hsendPriv_st : sendingKeyPair.privateKey.bytes.toList =
          clamp (gamma interpretation S g (randTerm (tr.length + 2) 32)) := by
        rw [hsendPriv, hγ_dhs]
      have hckKey_st : CryptoGames.HMAC.keyToBytes32 ck1.key =
          gamma interpretation S g (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).2 := by
        rw [hckKey, ho_spk, gamma_createChain_snd interpretation hEq S g, ho_rk, hγ_spk, hγ_dhs]
      have htheirRatchet_st : theirRatchetKey.serialize = TR.serializedKey (gamma interpretation S g o.spk) := by
        rw [htheirRatchet, ho_spk, hγ_spk]
      have hck0_st : CryptoGames.HMAC.keyToBytes32 ck0 = gamma interpretation S g o.keys.ck := by
        rw [hck0, ho_ck]
      have hpq_st : pqBytes = gamma interpretation S g (DY.Spqr.spqrInit o.keys.pqr TripleRatchet.spqrA2B) := by
        dsimp only [pqBytes]; rw [gamma_spqrInit, ho_pqr, gamma_spqrParams_a2b]
      let st := aliceStartState tr r.bob o
      refine ⟨sess, ⟨sendingKeyPair, ck1⟩, theirIdentity,
        { preKeyId := opkId?, signedPreKeyId := spkId, baseKey := baseKey, timestamp := 0#64 },
        { preKeyId := kyberPreKeyId, ciphertext := kyberKey ctB },
        st, tr.length + 8, tr.length + 3, tr.length + 4, o.ek, o.ct,
        hcanon, hscopeP, hscopeQ, ?_, ?_, rfl, rfl, ?_, ?_, rfl, rfl, rfl,
        hourId_st, rfl, htheirId_st, rfl, hsendPub_st, hckKey_st, hckIdx, rfl, rfl, ?_, rfl, congrArg kyberKey ho_ct.symm, hpq_st, ?_⟩
      · rw [htr']; exact getLocalState_aliceStartTrOfOut tr r.alice r.bob o
      · rw [htr']; exact isCurrentSnapshot_aliceStartTrOfOut tr r.alice r.bob o
      · rw [htr']; exact getMessageSentAt_ek_aliceStartTrOfOut tr r.alice r.bob o
      · rw [htr']; exact getMessageSentAt_ct_aliceStartTrOfOut tr r.alice r.bob o
      · rw [hbaseKey, ho_ek, gamma_dhPk, hγ_ek]; rfl
      · refine ⟨sessionToRecordRecPending sess, ?_,
          aliceStart_stateRel_pending interpretation r g tr o
            ourIdentity theirIdentity theirRatchetKey baseKey rk1 ck0 sendingKeyPair ck1
            opkId? spkId kyberPreKeyId remoteRegId (kyberKey ctB) pqBytes
            hdhs_len hck0_len hourId_st htheirId_st hrk1_st hsendPub_st hsendPriv_st
            hckIdx hckKey_st htheirRatchet_st hck0_st hpq_st,
          trKeyShape_aliceStartState interpretation r g tr o ds hds_lens hγ_dhs, ?_, ?_⟩
        · have hsess_len : (CryptoVerification.E2E.Record.encSession sess).length < 2 ^ 62 := by
            have hle := length_le_lenField 1 (CryptoVerification.E2E.Record.encSession sess)
            have hcan_len : recState.length = (CryptoVerification.E2E.Record.lenField 1 (CryptoVerification.E2E.Record.encSession sess)).length :=
              congrArg List.length hcanon.1
            omega
          have hpq_len : pqBytes.length < 2 ^ 63 := by
            have hle : pqBytes.length ≤ (CryptoVerification.E2E.Record.bytesField 15 pqBytes).length := by
              unfold CryptoVerification.E2E.Record.bytesField
              split_ifs with h <;> [simp [h]; exact length_le_lenField 15 pqBytes]
            have hsub : (CryptoVerification.E2E.Record.bytesField 15 sess.state.pqRatchetState).length ≤
                (CryptoVerification.E2E.Record.encSession sess).length := by
              unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega
            change (CryptoVerification.E2E.Record.bytesField 15 pqBytes).length ≤ _ at hsub; omega
          have hrc_len : ∀ rc ∈ sess.state.receiverChains,
              (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64 := by
            intro rc hrc
            dsimp only [sess, aliceInitiatedSessionV1, aliceInitiatedStateV1] at hrc
            simp only [List.mem_singleton] at hrc; subst hrc
            have h1 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 1 theirRatchetKey.serialize
            have h2 := Swarm.Phase0WholeFunctionBridge.lenField_length_le 3 (CryptoVerification.E2E.Record.encChainKey ⟨ck0, 0#32⟩)
            have h3 := Swarm.Phase0WholeFunctionBridge.encChainKey_length_lt ⟨ck0, 0#32⟩
            have hpub : theirRatchetKey.serialize.length = 33 := by simp [CryptoGames.LibsignalSession.PublicKey.serialize]
            simp only [CryptoVerification.E2E.Record.encReceiverChain,
              Option.map_some, CryptoVerification.E2E.Record.msgField, List.map_nil, List.flatten_nil, List.append_nil,
              List.length_append]; omega
          rw [hcanon.1, recordBytes_sessionToRecordRecPending sess
            (by simp [sess, aliceInitiatedSessionV1, CryptoGames.LibsignalSession.PublicKey.serialize])
            hpq_len
            (by intro rc hrc mk hmk
                dsimp only [sess, aliceInitiatedSessionV1, aliceInitiatedStateV1] at hrc
                simp only [List.mem_singleton] at hrc; subst hrc; cases hmk)
            hrc_len (Nat.lt_trans hsess_len (by decide))]
        · intro c hc
          dsimp only [sessionToRecordRecPending, sess, aliceInitiatedSessionV1,
            aliceInitiatedStateV1, Swarm.Phase0WholeFunctionBridge.sessionToSessionRec,
            Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec] at hc
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc; subst hc; rfl
        · dsimp only [sessionToRecordRecPending, sess, aliceInitiatedSessionV1,
            aliceInitiatedStateV1, Swarm.Phase0WholeFunctionBridge.sessionToSessionRec,
            Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec]
          simp

end Symbolic.Swarm.CREF.CliPure.IniPure

namespace Symbolic.Swarm.CREF.CliPure
export IniPure (AliceInitiatedV1PostPure)
end Symbolic.Swarm.CREF.CliPure
