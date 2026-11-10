/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewWire
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecord.DRBound
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewParams
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.OooRpkPure
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewContract
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewDecrypt
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewInv
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewModel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewTie
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewTieCrypto
import Symbolic.Proofs.Swarm.CREF.Grow.PqInit
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Fresh Pre-Key Receive Accept Bundle

Assembles `HonestIdentity`, base-key freshness, `RecvAcceptContractPure`, `RpkAcceptBin`, and
`AcceptD.AcceptTieD` (`rpkNew_accept_tie_bundle`) for Bob's fresh pre-key `recv` acceptance step.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (StateAndMessage)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli

theorem opk_removed_of_events_eq {used flag q : Bool}
    (heq : flag = q) (hq : q = true) :
    (used || flag) = true := by
  rw [heq, hq, Bool.or_true]

theorem theirId_eq_of_idPub_toList {interp : ExternInterpretation} {r : ProtocolSetup} {m : PreKeyMessageFields}
    (h : m.idPub.toList = pubBytes interp (secretBytes r 0)) :
    (⟨⟨m.idPub⟩⟩ : IdentityKey) =
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 0)).getD i.val 0#8)⟩⟩ := by
  congr 2
  exact vector32_eq_ofFn_getD h

theorem ourId_eq_of_idPriv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r) (hagree : ModelAgree interp P) {me : LocalIdentity}
    (hid : me.idPriv = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 1)) :
    (⟨(keyPairOf P.C me.idPriv).publicKey⟩ : IdentityKey) =
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 1)).getD i.val 0#8)⟩⟩ := by
  rw [hid]
  have hec := ecKey_pubBytes_eq_djbKey_keyPairOf hagree (secretBytes_length_bob hr).2.1
  have htl : (keyPairOf P.C (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 1))).publicKey.bytes.toList =
      pubBytes interp (secretBytes r 1) :=
    (List.cons.inj hec.symm).2
  exact congrArg IdentityKey.mk (congrArg PublicKey.mk (vector32_eq_ofFn_getD htl))

theorem me_bob_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r) {accepted : List HwBytes} {stB : PqParty} {d : DirectorySnapshot}
    (hB : PqPartyInv interp P r accepted r.bob stB d) :
    stB.me.idPriv = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 1) ∧
    stB.me.regId = r.regIdB := by
  have hme := hB.me_eq
  have hid : idSecret r r.bob = secretBytes r 1 := by unfold idSecret ProtocolSetup.ikBSecBytes; simp [hr.1.symm]
  have hreg : regIdOf r r.bob = r.regIdB := by unfold regIdOf; simp [hr.1.symm]
  rw [hme, hid, hreg]
  exact ⟨rfl, rfl⟩

theorem version_eq_four_of_st0_eq {v : BitVec 8}
    (hv4 : (4#32 : BitVec 32).toNat = v.toNat) :
    v = 4#8 :=
  BitVec.eq_of_toNat_eq hv4.symm

theorem preKeyFieldsOf_kyberCiphertext_eq_some
    (m : PreKeyMessageFields) (inner : SignalMessage) :
    (rpkNew_preKeyFieldsOf m inner).kyberCiphertext = some (kyberKey m.kyberCt.toList) ∧
    m.kyberCt.toList.length = 1568 :=
  ⟨rfl, m.kyberCt.2⟩

theorem acceptInput_dh1_dh2_dh3_kem_bob
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r) (hAgree : ModelAgree interp P) (X : UnreachedPqxdhPrimitives)
    {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} (inner : SignalMessage)
    (hsk1 : (secretBytes r 1).length = 32)
    (hsk2 : (secretBytes r 2).length = 32)
    (hid_me : me.idPriv = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 1))
    (hid_pub : m.idPub.toList = pubBytes interp (secretBytes r 0))
    (hspk : k.spkPriv = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 2))
    (hkpk : k.kpkSec = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 3168 (r.kyberSecB.drop 1)) :
    let inp := CryptoVerification.E2E.acceptInput P me k m
    let pf := rpkNew_preKeyFieldsOf m inner
    ofU8 ((CryptoVerification.E2E.modelPrims X P).x25519
      inp.spkBSk inp.hdr.ikAPk) =
      TR.dhAgreeBytes interp (secretBytes r 2) (pubBytes interp (secretBytes r 0)) ∧
    ofU8 ((CryptoVerification.E2E.modelPrims X P).x25519
      inp.ikBSk inp.hdr.ekAPk) =
      TR.dhAgreeBytes interp (secretBytes r 1) (TR.ekBytes pf) ∧
    ofU8 ((CryptoVerification.E2E.modelPrims X P).x25519
      inp.spkBSk inp.hdr.ekAPk) =
      TR.dhAgreeBytes interp (secretBytes r 2) (TR.ekBytes pf) ∧
    (((CryptoVerification.E2E.modelPrims X P).kemDecaps
      inp.pqspkBSk inp.hdr.kemCt).map ofU8) =
      some ((kyberDecapsBytes interp r m.kyberCt.toList).getD []) := by
  intro inp pf
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [inp, CryptoVerification.E2E.acceptInput]
    rw [hspk, x25519_modelPrims_keyPairOf_bytesToVec hAgree X hsk2 m.idPub, hid_pub]
  · dsimp only [inp, CryptoVerification.E2E.acceptInput]
    rw [hid_me, x25519_modelPrims_keyPairOf_bytesToVec hAgree X hsk1 m.baseKey,
      ← ekBytes_preKeyFieldsOf m inner]
  · dsimp only [inp, CryptoVerification.E2E.acceptInput]
    rw [hspk, x25519_modelPrims_keyPairOf_bytesToVec hAgree X hsk2 m.baseKey,
      ← ekBytes_preKeyFieldsOf m inner]
  · dsimp only [inp, CryptoVerification.E2E.acceptInput]
    rw [hkpk]
    exact kemDecaps_modelPrims_bob_bytesToVec hAgree hr X m.kyberCt

theorem acceptInput_opk_bob
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {used : Bool}
    (hAgree : ModelAgree interp P) (X : UnreachedPqxdhPrimitives)
    {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} (inner : SignalMessage)
    (hsk6 : r.withOpk = true → (secretBytes r 6).length = 32)
    (hk_post : BobKeysForPost r used m k) :
    let inp := CryptoVerification.E2E.acceptInput P me k m
    let pf := rpkNew_preKeyFieldsOf m inner
    (pf.preKeyId = none ∧ inp.hdr.opkId? = none ∧ inp.opkBSk? = none) ∨
      (∃ id1 id2 opkSk,
        pf.preKeyId = some id1 ∧
        inp.hdr.opkId? = some id2 ∧
        inp.opkBSk? = some opkSk ∧
        ofU8 ((CryptoVerification.E2E.modelPrims X P).x25519
          opkSk inp.hdr.ekAPk) =
          TR.dhAgreeBytes interp (secretBytes r 6) (TR.ekBytes pf)) := by
  intro inp pf
  rcases hk_post.opk_cases with ⟨hm_none, hk_none⟩ | ⟨hyes, _, hm_some, hk_some⟩
  · left
    exact ⟨hm_none,
      by simp [inp, CryptoVerification.E2E.acceptInput, hm_none],
      by simp [inp, CryptoVerification.E2E.acceptInput, hk_none, hm_none]⟩
  · right
    refine ⟨r.opkId, CryptoVerification.E2E.u32 r.opkId,
      vecU8 (keyPairOf P.C
        (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 6))).privateKey.bytes,
      hm_some,
      by simp [inp, CryptoVerification.E2E.acceptInput, hm_some],
      by simp [inp, CryptoVerification.E2E.acceptInput, hk_some, hm_some], ?_⟩
    dsimp only [inp, CryptoVerification.E2E.acceptInput]
    rw [x25519_modelPrims_keyPairOf_bytesToVec hAgree X (hsk6 hyes) m.baseKey,
      ← ekBytes_preKeyFieldsOf m inner]

theorem bobKdf_eq_of_acceptKeys
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {used : Bool}
    (hr : ProtocolSetupWF r) (hAgree : ModelAgree interp P) (X : UnreachedPqxdhPrimitives)
    {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} (inner : SignalMessage)
    {dk : SignalPqxdh.DRKey}
    (hsk1 : (secretBytes r 1).length = 32)
    (hsk2 : (secretBytes r 2).length = 32)
    (hsk6 : r.withOpk = true → (secretBytes r 6).length = 32)
    (hid_me : me.idPriv = Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 (secretBytes r 1))
    (hid_pub : m.idPub.toList = pubBytes interp (secretBytes r 0))
    (hk_post : BobKeysForPost r used m k)
    (hacc : SignalPqxdh.Model.acceptKeys (CryptoVerification.E2E.modelPrims X P)
      (CryptoVerification.E2E.acceptInput P me k m) = some dk) :
    let pf := rpkNew_preKeyFieldsOf m inner
    let F := DY.Libsignal.Refinement.sha256CompressFunction interp
    let dh1 := TR.dhAgreeBytes interp (secretBytes r 2) (pubBytes interp (secretBytes r 0))
    let dh2 := TR.dhAgreeBytes interp (secretBytes r 1) (TR.ekBytes pf)
    let dh3 := TR.dhAgreeBytes interp (secretBytes r 2) (TR.ekBytes pf)
    let dh4 := pf.preKeyId.map (fun _ => TR.dhAgreeBytes interp (secretBytes r 6) (TR.ekBytes pf))
    let ss := (kyberDecapsBytes interp r m.kyberCt.toList).getD []
    let kdf := TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
    ofU8 dk.rootKey = kdf.1 ∧
      ofU8 dk.chainKey = kdf.2.1 ∧
      ofU8 dk.pqrKey = kdf.2.2 ∧
      kdf.1.length = 32 ∧ kdf.2.1.length = 32 ∧ kdf.2.2.length = 32 := by
  obtain ⟨hdh1, hdh2, hdh3, hkem⟩ :=
    acceptInput_dh1_dh2_dh3_kem_bob hr hAgree X inner hsk1 hsk2 hid_me hid_pub
      hk_post.k_spkPriv_eq hk_post.k_kpkSec_eq
  have hopk := acceptInput_opk_bob (me := me) hAgree X inner hsk6 hk_post
  have hres := rpkNew_acceptKeys_eq_pqxdhKdfBytes hAgree hdh1 hdh2 hdh3 hopk hkem hacc
  dsimp only at hres ⊢
  exact hres

theorem acceptTieD_of_bob
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {pf : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    {st0 st' : SessionState HwBytes}
    (hd : d.length = 32)
    (hrecTie : AcceptRecTie r pf (pf.baseKey.take 33) st' sm)
    (hinv : AcceptSt0ModelInvs interp r pf st0)
    (hsc0 : ∀ sc, st0.senderChain = some sc →
      sc.ratchetKey.privateKey.bytes =
        List.Vector.ofFn (fun i =>
          (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8))
    (hdec_empty : Mut.exec
      (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
        (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
        (Symbolic.Swarm.CREF.CliPure.pureSpqrEmptyAsNone (DY.Libsignal.Refinement.sha256CompressFunction interp)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp))
        ((CryptoVerification.E2E.pqxdhSessionParams P).expectedAddrs .B)
        pf.inner .preKey (HKDF.bytesToKey32 d)) st0 = (.ok pt, st')) :
    AcceptD.AcceptTieD interp r pf d pt sm := by
  refine ⟨st0, st', (CryptoVerification.E2E.pqxdhSessionParams P).expectedAddrs .B, hrecTie, hinv, hsc0, ?_⟩
  rw [coinsOf_eq_bytesToKey32 hd]
  exact hdec_empty

theorem recvAcceptContractPure_of_bob
    {interp : ExternInterpretation} {r : ProtocolSetup} {used : Bool}
    {m : PreKeyMessageFields} {inner : SignalMessage} {k : ResponderPreKeySecrets}
    {sm : StateAndMessage} {d ct_wire pt : HwBytes}
    (hp0 : (pubBytes interp (secretBytes r 0)).length = 32)
    (hp1 : (pubBytes interp (secretBytes r 1)).length = 32)
    (hlen64 : m.inner.length < 2 ^ 64)
    (htf : SignalMessage.tryFrom protoSignalCodec m.inner = .ok inner)
    (hd : d.length = 32)
    (hk_post : BobKeysForPost r used m k)
    (hopk_rem : (sm.message[opkRemovedIdx]?).any (· != 0#8) = (rpkNew_preKeyFieldsOf m inner).preKeyId.isSome)
    (hv4 : (4#32 : BitVec 32).toNat = (rpkNew_preKeyFieldsOf m inner).inner.messageVersion.toNat)
    (hctr_le : (rpkNew_preKeyFieldsOf m inner).inner.counter.toNat ≤
      DY.Libsignal.TripleRatchet.maxForwardJumps)
    (hpq_ne : (rpkNew_preKeyFieldsOf m inner).inner.pqRatchet ≠ [])
    (hbase : (((rpkNew_preKeyFieldsOf m inner).baseKey.take 33).drop 1).length = 32 ∧
      DY.X25519.leValue ((((rpkNew_preKeyFieldsOf m inner).baseKey.take 33).drop 1).map BitVec.toNat) <
        DY.X25519.p25519 ∧
      DY.X25519.isLowOrderKey ((((rpkNew_preKeyFieldsOf m inner).baseKey.take 33).drop 1).map BitVec.toNat) =
        false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interp
        (((rpkNew_preKeyFieldsOf m inner).baseKey.take 33).drop 1))
    (hlow : DY.X25519.isLowOrderKey
      ((rpkNew_preKeyFieldsOf m inner).inner.senderRatchetKey.bytes.toList.map BitVec.toNat) = false)
    (hser : (rpkNew_preKeyFieldsOf m inner).inner.serialized = (rpkNew_preKeyFieldsOf m inner).message)
    (hct : (rpkNew_preKeyFieldsOf m inner).kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hmac_all : ∀ S : OpaqueSymbolSemantics,
      S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interp →
      (rpkNew_preKeyFieldsOf m inner).inner.verifyMac (DY.Libsignal.Refinement.sha256CompressFunction interp)
        ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 0)).getD i.val 0#8)⟩⟩
        ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 1)).getD i.val 0#8)⟩⟩
        (CryptoGames.HKDF.bytesToKey32
          (TR.trMacKeyBytes (DY.Libsignal.Refinement.sha256CompressFunction interp)
            (TR.bobSaltSeedBytes interp r S (rpkNew_preKeyFieldsOf m inner) ct_wire).1
            (TR.bobSaltSeedBytes interp r S (rpkNew_preKeyFieldsOf m inner) ct_wire).2)) = true)
    (hdec_all : ∀ S : OpaqueSymbolSemantics,
      S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interp →
      interp DY.Libsignal.Refinement.aesCbcDecryptSymbol
        [(rpkNew_preKeyFieldsOf m inner).inner.ciphertext,
         TR.trCipherKeyBytes (DY.Libsignal.Refinement.sha256CompressFunction interp)
           (TR.bobSaltSeedBytes interp r S (rpkNew_preKeyFieldsOf m inner) ct_wire).1
           (TR.bobSaltSeedBytes interp r S (rpkNew_preKeyFieldsOf m inner) ct_wire).2,
         (TR.trIvBytes (DY.Libsignal.Refinement.sha256CompressFunction interp)
           (TR.bobSaltSeedBytes interp r S (rpkNew_preKeyFieldsOf m inner) ct_wire).1
           (TR.bobSaltSeedBytes interp r S (rpkNew_preKeyFieldsOf m inner) ct_wire).2).take 16] = some pt) :
    RecvAcceptContractPure interp r used (wirePrekey :: m.bytes) sm
      (rpkNew_preKeyFieldsOf m inner) d ct_wire pt :=
  { parse := parsePreKeyWire_preKeyMsgE_ok m inner hlen64 htf
    outer_ver := rfl
    spkId_eq := hk_post.spkId_eq
    kpkId_eq := congrArg some hk_post.kpkId_eq
    kyber_ct := hct
    ct_len := hct_len
    d_len := hd
    opk_ok := opk_ok_of_bobKeysForPost inner hk_post
    opk_removed := fun hq => opk_removed_of_events_eq hopk_rem hq
    counter_le := hctr_le
    pqRatchet_ne_nil := hpq_ne
    version := version_eq_four_of_st0_eq hv4
    baseKey_ok := hbase
    ratchetKey_ok := hlow
    mac_eq := fun S hS => verifyMac_true_imp_bobExpectedMacBytes hp0 hp1 hser (hmac_all S hS)
    dec_eq := hdec_all }

theorem drCaps_and_extLen_pqSession_of_reachPq
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState HwBytes}
    (hrpq : ReachablePqxdhSession W me x g)
    (hppk : g.session.pendingPreKey = false) :
    Symbolic.Swarm.TRREF.GrowthRecord.DRCaps (pqSession x g) ∧
    Symbolic.Swarm.TRREF.GrowthRecord.extLen (pqSession x g) ≤ 93 := by
  obtain ⟨_, hseeds, hrcLe, _, _, hrep, _, _, _, habk, _⟩ := reachPq_inv hrpq
  refine ⟨⟨hrcLe, fun c hc => ⟨hrep.1 c hc, hseeds c hc⟩⟩, ?_⟩
  unfold Symbolic.Swarm.TRREF.GrowthRecord.extLen
  have hp1 := pqSession_pendingPreKey_of_false x g hppk
  have hp2 : (pqSession x g).pendingKyberPreKey = none := by simp [hppk]
  have hu10 := Symbolic.Swarm.TRREF.GrowthRecord.uint32Field_length_le' 10
    (pqSession x g).remoteRegistrationId
  have hu11 := Symbolic.Swarm.TRREF.GrowthRecord.uint32Field_length_le' 11
    (pqSession x g).localRegistrationId
  have hb13 := Symbolic.Swarm.TRREF.GrowthRecord.bytesField_length_le' 13
    (pqSession x g).aliceBaseKey
  have habk' : (pqSession x g).aliceBaseKey.length = 33 := by
    rw [pqSession_aliceBaseKey]; exact habk
  rw [habk'] at hb13
  rw [hp1, hp2]
  simp only [Option.map_none, CryptoVerification.E2E.Record.msgField, List.length_nil]
  omega

theorem encodeRecordX_length_eq_encodeRecord_pqSession
    (x : RecordExtras) (g : GhostState HwBytes) :
    (encodeRecordUnderExtras (fun _ => x) g).length =
      (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length := by
  rw [encodeRecordX_eq_encodeRecord_pqSession]

/-- Minimal `PqParty` carrying `stB`'s identity and `session := some (x, g)` with empty key stores,
discharging `PqxdhPartyInSpecDomain` without bounding the post-accept `.base-keys` store. -/
def minSessionParty (stB : PqParty) (x : RecordExtras) (g : GhostState HwBytes) : PqParty :=
  { party := stB.party
    me := stB.me
    peerId := none
    session := some (x, g)
    signed := []
    oneTime := []
    kyberOneTime := []
    kyberLastResort := [] }

theorem encodeDir_minSessionParty (W : PEParams) (stB : PqParty)
    (x : RecordExtras) (g : GhostState HwBytes) :
    encodeDir W (minSessionParty stB x g) =
      [(addressFile, CryptoVerification.SignalSession.textBytes (partyAddress stB.party).text),
       (identityKeyPairFile, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
         ⟨djbKey (keyPairOf W.C stB.me.idPriv).publicKey.bytes, stB.me.idPriv.toList⟩),
       (registrationIdFile, CryptoVerification.SignalSession.le32 stB.me.regId),
       (sessionFile (partyAddress stB.party.other), encodeRecordUnderExtras (fun _ => x) g)] := rfl

@[simp] theorem minSessionParty_session (stB : PqParty)
    (x : RecordExtras) (g : GhostState HwBytes) :
    (minSessionParty stB x g).session = some (x, g) := rfl

theorem wfPq_minSessionParty
    {W : PEParams} {stB : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    (hwfB : PqxdhPartyInSpecDomain W stB)
    (hrpq : ReachablePqxdhSession W stB.me x g)
    (hparty : g.party = stB.party)
    (hrec_lt : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) :
    PqxdhPartyInSpecDomain W (minSessionParty stB x g) := by
  refine ⟨?_, ?_, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil⟩
  · intro x' g' hs
    simp only [minSessionParty, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨⟨g, hrpq, rfl, rfl⟩, hparty, hrec_lt⟩
  · intro f hf
    rw [encodeDir_minSessionParty] at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact hwfB.2.1 (addressFile, CryptoVerification.SignalSession.textBytes (partyAddress stB.party).text)
        (by unfold encodeDir; simp)
    · exact hwfB.2.1 (identityKeyPairFile,
        CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
          ⟨djbKey (keyPairOf W.C stB.me.idPriv).publicKey.bytes, stB.me.idPriv.toList⟩)
        (by unfold encodeDir; simp)
    · exact hwfB.2.1 (registrationIdFile, CryptoVerification.SignalSession.le32 stB.me.regId)
        (by unfold encodeDir; simp)
    · exact ⟨hrec_lt, fun _ =>
        LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.reachPq_encodeRecordX_length_le_fileCapBytes hrpq⟩

theorem encodeRecordX_lt_2_31_of_pqRatchetState_le
    {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState HwBytes}
    (hrpq : ReachablePqxdhSession W me x g)
    (hppk : g.session.pendingPreKey = false)
    (hpq : g.session.pqRatchetState.length ≤ 2 ^ 20) :
    (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
  obtain ⟨hcaps, hext⟩ := drCaps_and_extLen_pqSession_of_reachPq hrpq hppk
  have h1 := Symbolic.Swarm.TRREF.GrowthRecord.encodeRecord_le_of_caps (pqSession x g) hcaps
  have hD : Symbolic.Swarm.TRREF.GrowthRecord.DRMAX = 600000 := rfl
  rw [encodeRecordX_length_eq_encodeRecord_pqSession]
  rw [hD, pqSession_state] at h1
  omega

theorem spqrInitOf_b2a_ooo_and_len_le (interp : ExternInterpretation) {k : HwBytes}
    (hk : k.length = 32) :
    Grow.SpqrOooBounded (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interp k [1#8]) ∧
    (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interp k [1#8]).length ≤ 1208 := by
  refine ⟨(RpkCli.spqrOooBounded_spqrInitOf_b2a interp k (by omega)).1, ?_⟩
  rw [Symbolic.Swarm.CREF.Grow.spqrInitOf_b2a_eq_is1StateRaw]
  have h1 := CryptoVerification.SpqrV1.Top.StateSize.SymP3.encodeState_length_le_rawPqState
    (is1StateRaw (DY.Libsignal.Refinement.sha256CompressFunction interp) .b2a k)
  have h2 := is1StateRaw_rawPqState_le (DY.Libsignal.Refinement.sha256CompressFunction interp) .b2a k
  change (CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw _).length ≤ _ at h1
  omega

/-- Derives `HonestIdentity`, base-key freshness, state length bound, `opkRemovedIdx` agreement,
`RecvAcceptContractPure`, `RpkAcceptBin`, and `AcceptD.AcceptTieD` from a model fresh pre-key accept. -/
theorem rpkNew_accept_tie_bundle
    {interp : ExternInterpretation} {P : PEParams} {X : UnreachedPqxdhPrimitives} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r)
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hBridge : RpkModelHookBridge interp P)
    (hmlkem : Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp = P.Q.K)
    (hhmac : Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp =
      Symbolic.Swarm.SHARED.HookAuth.hmacFnOfSha P.C.F)
    {t : CliTurn} {accepted : List HwBytes} {stB st1 : PqParty}
    {m : PreKeyMessageFields} {inner : SignalMessage} {k : ResponderPreKeySecrets}
    {x : RecordExtras} {g : GhostState HwBytes} {coins pt : HwBytes}
    (hwfB : PqxdhPartyInSpecDomain P stB)
    (hB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob))
    (hcoins : coins.length = 32)
    (hlt : m.inner.length + 2048 < 2 ^ 32)
    (htf : SignalMessage.tryFrom protoSignalCodec m.inner = .ok inner)
    (htrust : stB.trusts ⟨⟨m.idPub⟩⟩ = true)
    (hk : preKeysNamedBy stB m = some k)
    (hdec : recvPrekeyState X P stB.party stB.me k m
      (CryptoGames.HKDF.bytesToKey32 coins) = some (some (x, g, pt)))
    (hmk : markKyberUsed stB m = some st1) :
    let pf := rpkNew_preKeyFieldsOf m inner
    let sm : StateAndMessage := ⟨encodeRecordUnderExtras (fun _ => x) g, preKeyStoreEventsBytes m ++ pt⟩
    ∃ ct_wire : HwBytes,
      DY.Libsignal.Composed.Refinement.HonestIdentity interp r (wirePrekey :: m.bytes) ∧
      (∀ q, DY.Libsignal.Composed.Refinement.parsePreKeyWire (wirePrekey :: m.bytes) = some q →
        q.baseKey.take 33 ∉ accepted) ∧
      sm.state.length < 2 ^ 64 ∧
      (sm.message[opkRemovedIdx]?).any (· != 0#8) = pf.preKeyId.isSome ∧
      RecvAcceptContractPure interp r (t.opkUsed r) (wirePrekey :: m.bytes) sm pf coins ct_wire pt ∧
      RpkAcceptBin pf sm ∧
      AcceptD.AcceptTieD interp r pf coins pt sm := by
  intro pf sm
  have hlen64 : m.inner.length < 2 ^ 64 := by omega
  have hpartyB : stB.party = .B := by rw [hB.party_eq]; unfold partyOf; simp [hr.1.symm]
  obtain ⟨hid_me, hreg_me⟩ := me_bob_of_pqPartyInv hr hB
  obtain ⟨_, hid_pub, hhon⟩ := pqPartyInv_bob_honestIdentity hr hagree hB hlen64 htrust
  have hk_post := pqPartyInv_bob_keysFor_inv hr.1 hB hk
  have hfresh_djb := (pqPartyInv_bob_markKyberUsed_inv hr.1 hB hk_post.spkId_eq hk_post.kpkId_eq hmk).1
  have hfresh := fresh_of_parse_preKeyMsgE hlen64 hfresh_djb
  have hdecB : recvPrekeyState X P .B stB.me k m (CryptoGames.HKDF.bytesToKey32 coins) =
      some (some (x, g, pt)) := hpartyB ▸ hdec
  obtain ⟨inner', dk, st', htf', _, _, hacc, hdec_rec, hx, hg, hrpq⟩ :=
    recvPrekeyState_some_some_inv hdecB
  have hinner_eq : inner = inner' := Except.ok.inj (htf.symm.trans htf')
  subst inner'
  have hsk0 : (secretBytes r 0).length = 32 := rpkNew_secretBytes_0_length hr
  have hsk1 : (secretBytes r 1).length = 32 := (secretBytes_length_bob hr).2.1
  have hsk2 : (secretBytes r 2).length = 32 := secretBytes_2_length hr
  have hsk6 : r.withOpk = true → (secretBytes r 6).length = 32 := secretBytes_6_length hr
  have hp0 : (pubBytes interp (secretBytes r 0)).length = 32 :=
    pubBytes_length_of_modelAgree hagree hsk0
  have hp1 : (pubBytes interp (secretBytes r 1)).length = 32 :=
    pubBytes_length_of_modelAgree hagree hsk1
  obtain ⟨hrk_eq, hck_eq, hpqr_eq, _, _, hpqr_len⟩ :=
    bobKdf_eq_of_acceptKeys hr hagree X inner hsk1 hsk2 hsk6 hid_me hid_pub hk_post hacc
  have hpq_init := spqrPq_init_b2a_eq_spqrInitOf hagree hmlkem hhmac hpqr_len
  conv at hpq_init => lhs; rw [← hpqr_eq]
  obtain ⟨hct, hct_len⟩ := preKeyFieldsOf_kyberCiphertext_eq_some m inner
  have hbase := rpkNew_acceptKeys_baseKey_ok_of_idPriv hagree hext hr hid_me
    (preKeyFieldsOf_baseKey_take_33 m inner) hacc
  have hmsg := signalMessage_tryFrom_ok_serialized_and_len htf
  have htheir := theirId_eq_of_idPub_toList hid_pub
  have hour := ourId_eq_of_idPriv hr hagree hid_me
  have hspk_priv : (keyPairOf P.C k.spkPriv).privateKey.bytes =
      List.Vector.ofFn (fun i =>
        (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8) := by
    rw [hk_post.k_spkPriv_eq]; exact keyPairOf_bytesToVec_privateKey_eq_ofFn P.C hsk2
  let st0_raw : SessionState HwBytes :=
    initializeRecipientSession (CryptoVerification.E2E.pqxdhSpqrSession P)
      ⟨(keyPairOf P.C stB.me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf P.C k.spkPriv)
      (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
      (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  change SessionState.tryDecryptFromRecord P.C (CryptoVerification.E2E.pqxdhSpqrSession P)
    ((CryptoVerification.E2E.pqxdhSessionParams P).expectedAddrs .B) inner .preKey
    (CryptoGames.HKDF.bytesToKey32 coins) st0_raw = (.ok pt, st') at hdec_rec
  obtain ⟨hv_st0, _, _, _, _, _, hpq_st0⟩ :=
    initializeRecipientSession_fields (CryptoVerification.E2E.pqxdhSpqrSession P)
      ⟨(keyPairOf P.C stB.me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf P.C k.spkPriv)
      (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
      (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  obtain ⟨hinv0, hsc0⟩ := acceptSt0ModelInvs_of_initializeRecipientSession
    (CryptoVerification.E2E.pqxdhSpqrSession P)
    (rk0 := ofU8 dk.rootKey) (ck0 := ofU8 dk.chainKey) (pqr0 := ofU8 dk.pqrKey)
    hct hct_len hbase hmsg htheir hour hspk_priv ⟨hrk_eq, hck_eq, hpq_init⟩
  obtain ⟨st0, hst0_eq⟩ : ∃ st0 : SessionState HwBytes, st0_raw = st0 := ⟨st0_raw, rfl⟩
  change st0_raw.version = 4#32 at hv_st0
  change st0_raw.pqRatchetState = _ at hpq_st0
  change AcceptSt0ModelInvs interp r pf st0_raw at hinv0
  change ∀ sc, st0_raw.senderChain = some sc → _ at hsc0
  rw [hst0_eq] at hdec_rec hv_st0 hpq_st0 hinv0 hsc0
  obtain ⟨hver0_eq, hdecW, hdec_empty⟩ := tryDecryptFromRecord_ok_to_emptyAsNone hext hBridge hdec_rec
  obtain ⟨hppk, hcl', hctr_le, hpq_ne, hbase', hlow, hmsg', ct_wire, hct', hct_len', hmac_all, hdec_all⟩ :=
    bobSaltSeed_keys_of_st0Invs hext hsk2 hinv0 hdecW
  obtain ⟨hooo_init, hlen_init⟩ := spqrInitOf_b2a_ooo_and_len_le interp hpqr_len
  have hooo0 : Grow.SpqrOooBounded st0.pqRatchetState := by rw [hpq_st0, hpq_init]; exact hooo_init
  have hlen0_lt : st0.pqRatchetState.length ≤ 1208 := by rw [hpq_st0, hpq_init]; exact hlen_init
  have hspqr_rfl : Symbolic.Swarm.CREF.Cli.pureSpqrOf interp = Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp := rfl
  have hdecW_pure := hdecW
  rw [hspqr_rfl] at hdecW_pure
  have hpq_grow := (RpkCli.spqrOooBounded_tryDecryptWithStateW_pureSpqrOf _ _ interp _ _ _ _ _ _ _
    hdecW_pure hooo0 (by omega)).2
  have hpq_st'_le : g.session.pqRatchetState.length ≤ 2 ^ 20 := by rw [hg]; dsimp only; omega
  have hppk_g : g.session.pendingPreKey = false := by rw [hg]; exact hppk
  have hrec_lt31 : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 :=
    encodeRecordX_lt_2_31_of_pqRatchetState_le hrpq hppk_g hpq_st'_le
  have hg_party : g.party = stB.party := by rw [hg, hpartyB]
  have hwf_min := wfPq_minSessionParty hwfB hrpq hg_party hrec_lt31
  obtain ⟨hrecTie, hBin, hst_lt64, hopk_rem⟩ :=
    acceptRecTie_and_rpkAcceptBin_of_wfPq hwf_min (minSessionParty_session stB x g)
      hx hreg_me hg hppk hcl'
  have hv4 : (4#32 : BitVec 32).toNat = pf.inner.messageVersion.toNat := by rw [← hv_st0]; exact hver0_eq
  have hcontract := recvAcceptContractPure_of_bob hp0 hp1 hlen64 htf hcoins hk_post hopk_rem
    hv4 hctr_le hpq_ne hbase' hlow hmsg'.1 hct' hct_len' hmac_all hdec_all
  have hTie := acceptTieD_of_bob hcoins hrecTie hinv0 hsc0 hdec_empty
  exact ⟨ct_wire, hhon, hfresh, hst_lt64, hopk_rem, hcontract, hBin, hTie⟩

end Symbolic.Swarm.CREF.Cli.Slots
