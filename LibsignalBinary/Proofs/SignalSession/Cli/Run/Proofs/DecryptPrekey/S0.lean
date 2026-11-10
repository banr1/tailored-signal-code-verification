/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.HsOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok

/-!
# Slot Semantics and Domain Preconditions for `decrypt_prekey`

Defines the model semantics `decPkDef` and domain precondition `DecPkOk₀` for
`signal_session_handshake::decrypt_prekey`, and connects them to the PQXDH responder model
via `decPkOk₀_pqRecv`, `pqDecryptPrekeyAgrees_decPkDef`, and `RunHsOk`:
- `decPkDef` loads the peer session record, checks peer identity trust, either decrypts under a
  matching current session (`SessionState.tryDecryptFromRecord`) or initializes a responder session
  via `PqxdhCorrectModel.recvPrekeyState` and consumes the Kyber/one-time pre-keys, saves the peer
  identity, and stores the updated session record;
- `DecPkOk₀` characterizes well-formed pre-key inputs (canonical pre-key files, typed version-4
  `PreKeySignalMessage` with a matching or absent current session, derived key pairs, and bounded
  last-resort `.base-keys` files).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-! ## Typed pre-key message parsing -/

/-- Model `PreKeySignalMessage` produced by `PreKeySignalMessage::try_from` on `m.bytes` when `m.inner` parses to `i`. -/
def pmOfE (m : PreKeyMessageFields) (i : SignalMessage) : PreKeySignalMessage :=
  E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel
    { ptr := 0, sret := 0, regId := m.regId, opkId := m.opkId, spkId := m.spkId, kpkId := m.kpkId,
      kyberCt := m.kyberCt, baseKey := m.baseKey, idPub := m.idPub, inner := m.inner } i

/-- States that `S.pksmParse` on `m.bytes` (for `m.inner.length + 2048 < 2 ^ 32`) yields `pmOfE m i` for a parsed `SignalMessage` `i`. -/
def PksmTyped (S : RunSem) : Prop :=
  ∀ (m : PreKeyMessageFields) (pm : PreKeySignalMessage), m.inner.length + 2048 < 2 ^ 32 →
    S.pksmParse m.bytes = some pm →
    ∃ i : SignalMessage, SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧ pm = pmOfE m i

/-- Strips leading tag byte `tag` and packages the remaining `n` bytes as a vector, or `none` on mismatch. -/
def pkVecTag? (tag : BitVec 8) (n : Nat) (l : List (BitVec 8)) :
    Option (List.Vector (BitVec 8) n) :=
  match l with
  | t :: rest => if h : t = tag ∧ rest.length = n then some ⟨rest, h.2⟩ else none
  | [] => none

/-- Packages a byte list of length `n` as a vector, or `none` if `l.length ≠ n`. -/
def pkVec? (n : Nat) (l : List (BitVec 8)) : Option (List.Vector (BitVec 8) n) :=
  if h : l.length = n then some ⟨l, h⟩ else none

/-- Extracts `PreKeyMessageFields` from a version-4 `PreKeySignalMessage` carrying a 1568-byte
tag-`8` Kyber ciphertext, inverting `pmOfE` on valid inner messages (`pkToE?_pmOfE`). -/
def pkToE? (pm : PreKeySignalMessage) : Option PreKeyMessageFields :=
  if pm.messageVersion ≠ 4 then none
  else
    match pm.kyberPayload with
    | none => none
    | some kp =>
      match pkVecTag? 8 1568 kp.ciphertext with
      | none => none
      | some ct =>
        some { regId := pm.registrationId, opkId := pm.preKeyId, spkId := pm.signedPreKeyId,
               kpkId := kp.preKeyId, kyberCt := ct, baseKey := pm.baseKey.bytes,
               idPub := pm.identityKey.publicKey.bytes, inner := pm.message.serialized }

/-! ## Domain preconditions (`DecPkOk₀`) -/

/-- Canonical well-formedness of pre-key store files: every signed, one-time EC, and Kyber
pre-key file is either empty or the canonical `encodeDir` record for its identifier. -/
structure PreKeyFilesWf (W : PEParams) (F : FsFiles) : Prop where
  signed : ∀ i bs, StoresGhost.opened.signed.get cliIo.rd F (keyName i) = .ok bs →
    bs = [] ∨ ∃ k, bs = signedRecordBytes W.C i k
  oneTime : ∀ i bs, StoresGhost.opened.oneTime.get cliIo.rd F (keyName i) = .ok bs →
    bs = [] ∨ ∃ sk, bs = oneTimeRecordBytes W.C i sk
  kyberOneTime : ∀ i bs, StoresGhost.opened.kyber.oneTime.get cliIo.rd F (keyName i) = .ok bs →
    bs = [] ∨ ∃ k, bs = kyberRecordBytes i k
  kyberLastResort : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (keyName i) = .ok bs →
    bs = [] ∨ ∃ k, bs = kyberRecordBytes i k

/-- Session-matching predicate (`promote_matching_session`): `s.state.version` equals the
message version and `s.aliceBaseKey` equals the serialized base key. -/
def SessMatchesPm (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) : Prop :=
  s.state.version = pm.messageVersion.zeroExtend 32 ∧ s.aliceBaseKey = pm.baseKey.serialize

instance (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) : Decidable (SessMatchesPm s pm) := by
  unfold SessMatchesPm; infer_instance

/-- Domain precondition on files and parsed message `pm` for `decrypt_prekey` (complementing
`S.filesOk`): domain party addresses, typed `pm = pmOfE m i`, matching current session if present,
distinct accounts, canonical key pairs and pre-key files, and `< 2 ^ 32`-byte `.base-keys` files. -/
structure DecPkOk₀ (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop where
  party : ∃ P : Party, peer = RunRefine.addrValE P.other ∧ me = RunRefine.addrValE P
  typed : ∃ (m : PreKeyMessageFields) (i : SignalMessage), m.inner.length + 2048 < 2 ^ 32 ∧
    SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧ pm = pmOfE m i
  sessMatch : ∀ r s, Slots.loadRec Scope F peer = .ok (some r) → r.currentSession = some s →
    SessMatchesPm s pm
  distinctAcct : ¬ SameServiceId peer me
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  idPairDerived : ∀ kp, StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp →
    kp.identityKey.publicKey = (keyPairOf W.C kp.privateKey.bytes).publicKey
  preKeysWf : PreKeyFilesWf W F
  baseKeysLt : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName i) = .ok bs →
    bs.length < 2 ^ 32

/-! ## Model semantics (`decPkDef`) -/

/-- Reads responder signed, Kyber, and optional one-time pre-key secrets for `m` from `F`,
returning `none` when any lookup or key decode fails. -/
def pkStoreKeys (F : FsFiles) (m : PreKeyMessageFields) : Option ResponderPreKeySecrets :=
  let g := StoresGhost.opened
  match getSignedPreKey cliIo.rd F g.signed m.spkId, g.kyber.get cliIo.rd F m.kpkId with
  | .ok sr, .ok kr =>
    match pkVec? 32 sr.signedPreKey.privateKey, pkVecTag? 8 1568 kr.signedPreKey.publicKey,
        pkVecTag? 8 3168 kr.signedPreKey.privateKey with
    | some spk, some kpub, some ksec =>
      let opk : Option (Option (BitVec 32 × List.Vector (BitVec 8) 32)) :=
        match m.opkId with
        | none => some none
        | some j =>
          match getPreKey cliIo.rd F g.oneTime j with
          | .ok r => (pkVec? 32 r.preKey.privateKey).map fun sk => some (j, sk)
          | .error _ => none
      opk.map fun o =>
        { spkId := m.spkId, spkPriv := spk, kpkId := m.kpkId, kpkPub := kpub, kpkSec := ksec,
          opk := o }
    | _, _, _ => none
  | _, _ => none

/-- Converts the first 32 coin bytes (zero-padded past the end) into a little-endian `BitVec 256`. -/
def pkRecvCoins (c : List (BitVec 8)) : BitVec 256 :=
  HKDF.bytesToKey32 (c.take 32 ++ List.replicate (32 - c.length) 0#8)

/-- Model semantics of `signal_session_handshake::decrypt_prekey` on files `F`, addresses
`peer` and `_me`, parsed message `pm`, and coin tape `coins`. Returns `none` on decryption panic
and `some none` on protocol rejection. -/
noncomputable def decPkDef (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer _me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8)) : SlotAns (List (BitVec 8)) :=
  let g := StoresGhost.opened
  let P := initParty peer
  match Slots.loadRec Scope F peer with
  | .error _ => some none
  | .ok r =>
    match g.identity.trusted cliIo.rd F peer pm.identityKey with
    | .error _ => some none
    | .ok false => some none
    | .ok true =>
      let saved := g.identity.saveUpd cliIo.rd F peer pm.identityKey
      match r.bind (·.currentSession) with
      | some s =>
        if SessMatchesPm s pm then
          if s.state.remoteIdentity ≠ some pm.identityKey then some none
          else
            match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P)
                pm.message .preKey (pkRecvCoins coins) s.state with
            | (.ok pt, st) =>
              some (some ({ g with
                identity := saved
                sessions := g.sessions.put (addressText peer)
                  (E2E.Record.encodeRecord
                    { currentSession := some { s with state := st, pendingPreKey := none,
                                                      pendingKyberPreKey := none } }) }, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none
        else some none
      | none =>
        match pkToE? pm with
        | none => some none
        | some m =>
          match pkStoreKeys F m, g.identity.keyPair cliIo.rd F, g.identity.regId cliIo.rd F with
          | some k, .ok kp, .ok reg =>
            match recvPrekeyState X W P ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
            | none => none
            | some none => some none
            | some (some (x, gs, pt)) =>
              match g.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
              | (.error _, _) => some none
              | (.ok (), kyber') =>
                let oneTime' := match pm.preKeyId with
                  | none => g.oneTime
                  | some j => (removePreKey cliIo.rd F g.oneTime j).2
                some (some ({ g with
                  identity := saved
                  kyber := kyber'
                  oneTime := oneTime'
                  sessions := g.sessions.put (addressText peer) (encodeRecordUnderExtras (fun _ => x) gs) },
                  pt))
          | _, _, _ => some none

/-- `pkToE?` left-inverts `pmOfE` whenever `SignalMessage.tryFrom` accepts `m.inner`. -/
theorem pkToE?_pmOfE (m : PreKeyMessageFields) (i : SignalMessage)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i) : pkToE? (pmOfE m i) = some m := by
  cases m with
  | mk regId opkId spkId kpkId kyberCt baseKey idPub inner =>
    have hser := DecPkS0.tryFrom_serialized hi
    have hct : pkVecTag? 8#8 1568 (8#8 :: kyberCt.toList) = some kyberCt := by
      rcases kyberCt with ⟨l, hl⟩
      simp [pkVecTag?, hl]
    simp [pkToE?, pmOfE, E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel,
      E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.kyberBytes, hct, hser]

/-! ## Stack budget and PQXDH model agreement -/

/-- Stack budget for `decrypt_prekey`: `2144`-byte wrapper frame plus `2 ^ 20`-byte responder
poll budget plus `B.dirGetNeed` for nested `Dir::get` calls. -/
abbrev cliDecryptPrekeyNeed (B : RunBudgets) : Nat :=
  2144 + 1048576 + B.dirGetNeed

/-- States that `Scope` covers every session record produced in the PQXDH specification domain. -/
def ScopeCoversPq (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (st : PqParty) x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
    Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)

/-- Establishes `DecPkOk₀` on PQXDH pre-key receive inputs `pqRecvInputs` when any current session matches `m`. -/
theorem decPkOk₀_pqRecv (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope) (st : PqParty)
    (m : PreKeyMessageFields) (i : SignalMessage) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    DecPkOk₀ W Scope (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) (pmOfE m i) := by
  refine ⟨⟨st.party, rfl, rfl⟩, ⟨m, i, hm, hi, rfl⟩, ?_, InitS0.distinctAcct_party st.party,
    DecPkS0.keyPairLt_pqRecv W st _ rc hwf, DecPkS0.idPairDerived_pqRecv W st _ rc,
    ⟨DecPkS0.signedWf_pqRecv W st _ rc, DecPkS0.oneTimeWf_pqRecv W st _ rc,
      DecPkS0.kyberOneTimeWf_pqRecv W st _ rc, DecPkS0.kyberLastResortWf_pqRecv W st _ rc⟩,
    DecPkS0.baseKeysLt_pqRecv W st _ rc hwf⟩
  intro r s hload hcur
  exact DecPkS0.sessMatch_pqRecv W Scope hinj st (fun x g => hcov st x g hwf) m _ rc hmatch
    hload hcur

/-- Establishes `PqDecryptPrekeyAgrees` when `S.decryptPrekey = decPkDef X W Scope`. -/
theorem pqDecryptPrekeyAgrees_decPkDef (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS : S.decryptPrekey = decPkDef X W Scope) (hpksm : PksmTyped S)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope) :
    RunRefine.PqDecryptPrekeyAgrees S X W := by
  exact DecPkS0.pqDecryptPrekeyAgrees_decPkDef S X W Scope hS hpksm hinj hcov

/-! ### `RunHsOk` on domain inputs -/

theorem runHsOk_pqInit (S : RunSem) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none)
    (hinit : ∀ F peer me, InitOk₀ W F peer me → S.initOk F peer me) :
    RunHsOk S (pqInitInputs W st b t) := by
  exact DecPkS0.pqInit S W st b t hwf hs hinit

theorem runHsOk_pqSend (S : RunSem) (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : RunHsOk S (pqSendInputs W st m r) := by
  exact DecPkS0.pqSend S W st m r

/-- Discharges `RunHsOk` on pre-key `recv` inputs (`wirePrekey :: m.bytes`) via `PksmTyped` and `decPkOk₀_pqRecv`. -/
theorem runHsOk_pqRecvPrekey (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hdec : ∀ F peer me pm, DecPkOk₀ W Scope F peer me pm → S.decPkOk F peer me pm)
    (hpksm : PksmTyped S) (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: m.bytes) rc) := by
  refine DecPkS0.pqRecvPrekey S W st m rc fun pm hparse => ?_
  obtain ⟨i, hi, rfl⟩ := hpksm m pm hm hparse
  exact hdec _ _ _ _ (decPkOk₀_pqRecv W Scope hinj hcov st m i rc hwf hm hi hmatch)

theorem runHsOk_pqRecvOther (S : RunSem) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h3 : c.head? ≠ some wirePrekey) : RunHsOk S (pqRecvInputs W st c rc) := by
  exact DecPkS0.pqRecvOther S W st c rc h3

theorem runHsOk_smSend (S : RunSem) (g : GhostState (List (BitVec 8))) (m : List (BitVec 8)) :
    RunHsOk S (smSendInputs g m) := by
  exact DecPkS0.smSend S g m

theorem runHsOk_smRecv (S : RunSem) (g : GhostState (List (BitVec 8))) (c : List (BitVec 8))
    (rc : BitVec 256) : RunHsOk S (smRecvInputs g c rc) := by
  exact DecPkS0.smRecv S g c rc

end CryptoVerification.SignalSession.Cli.RunProofs
