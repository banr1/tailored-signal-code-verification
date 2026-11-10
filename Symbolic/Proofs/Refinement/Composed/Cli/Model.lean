/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch

/-!
# Machine-Free PQXDH CLI Model Target

Instantiates `CompRefinesCli` with model-level primitive parameters `P : PEParams`, primitive
agreement `ModelAgree`, and the PQXDH run relation `PqModelRel`, forming the machine-free
intermediate target `CompRefinesCliModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

/-- Zero-pads or truncates `b` to 32 bytes. -/
def vec32 (b : HwBytes) : List.Vector (BitVec 8) 32 := ⟨(b ++ List.replicate 32 0).take 32, by simp⟩

end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction x25519AgreementSymbol x25519PublicKeySymbol
  aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol
  torsionFreeSymbol)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields UnreachedPqxdhPrimitives PEParams RecordExtras initiateTapeLen
  wireWhisper wirePrekey)
open CryptoVerification.SignalSession (Inputs Outcome PqParty filesOf pqInitInputs pqSendInputs
  pqRecvInputs pqxdhExpectedOutcome pqInitModel pqSendModel pqRecvWhisperModel pqRecvPrekeyModel
  PqSessionMatches PqxdhPartyInSpecDomain OutcomeMatchesModelExceptPath sessionFile partyAddress)

/-- Agreement between `interp` and the model primitives `P` on SHA-256 compression, AES-256-CBC,
X25519, Kyber-1024, Montgomery-to-Edwards conversion, and torsion checking. -/
def ModelAgree (interp : ExternInterpretation) (P : PEParams) : Prop :=
  P.C.F = sha256CompressFunction interp ∧
  (∀ p k iv : ByteString, k.length = 32 → iv.length = 16 →
    interp aesCbcEncryptSymbol [p, k, iv] =
      some (CryptoGames.LibsignalSession.aesCbcEncrypt P.C.E (CryptoGames.HKDF.bytesToKey32 k)
        (CryptoGames.CBC.bytesToBlock iv) p)) ∧
  (∀ c k iv : ByteString, k.length = 32 → iv.length = 16 →
    interp aesCbcDecryptSymbol [c, k, iv] =
      CryptoGames.LibsignalSession.aesCbcDecrypt P.C.D (CryptoGames.HKDF.bytesToKey32 k)
        (CryptoGames.CBC.bytesToBlock iv) c) ∧
  (∀ a b : List.Vector (BitVec 8) 32,
    interp x25519AgreementSymbol [a.toList, b.toList] = some (P.C.X a b).toList) ∧
  (∀ a : List.Vector (BitVec 8) 32,
    interp x25519PublicKeySymbol [a.toList] = some (P.C.pubKey a).toList) ∧
  (∀ (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32),
    interp kyberEncapsSymbol [pk.toList, rand.toList] =
      some ((P.Q.encaps pk rand).1.toList ++ (P.Q.encaps pk rand).2.toList)) ∧
  (∀ (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568),
    interp kyberDecapsSymbol [sk.toList, ct.toList] = some (P.Q.decaps sk ct).toList) ∧
  (∀ (u : List.Vector (BitVec 8) 32) (sign : BitVec 8),
    interp toEdwardsSymbol [u.toList, [sign]] = (P.Q.montToEd u sign).map List.Vector.toList) ∧
  (∀ pt : List.Vector (BitVec 8) 160,
    P.Q.isTorsionFree pt = decide (interp torsionFreeSymbol [pt.toList] = some [1#8]))

/-- Equivalence of CLI `Inputs` up to directory-snapshot extensionality under `filesOf`. -/
def InputsEquiv (i i' : Inputs) : Prop :=
  i.argv = i'.argv ∧ i.dirs = i'.dirs ∧ i.stdin = i'.stdin ∧
    ∀ p, filesOf i.files p = filesOf i'.files p

/-! ## Extended PQXDH model outcomes -/

open CryptoVerification.E2E (encodeRecordUnderExtras encStateUnderExtras lenField)

/-- Serialized `RecordStructure` produced when promoting a non-matching session `(x, g)` beneath
a newly established session `(x', g')`, clearing `pendingPreKey` on the archived session. -/
def noMatchRecordBytes (x : RecordExtras) (g : GhostState HwBytes) (x' : RecordExtras)
    (g' : GhostState HwBytes) : HwBytes :=
  encodeRecordUnderExtras (fun _ => x') g' ++
    lenField 2 (encStateUnderExtras x { g.session with pendingPreKey := false })

/-- Specifies that when `pqRecvPrekeyModel` accepts on a cleared session and produces `(x', g')`,
an exited run writes `noMatchRecordBytes x g x' g'` to the peer session file. -/
def NoMatchSessionFile (X : UnreachedPqxdhPrimitives) (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256) (o : Outcome) : Prop :=
  ∀ st' out x' g', pqRecvPrekeyModel X P { st with session := none } m rc = some (some (st', out)) →
    st'.session = some (x', g') →
    ∀ code out' fs, o = .exited code out' fs →
      fs (sessionFile (partyAddress st.party.other)) = some (noMatchRecordBytes x g x' g')

open CryptoGames.LibsignalSession (IdentityKey SessionState)
open CryptoVerification.E2E (pqxdhSpqrSession pqxdhSessionParams)

/-- Extracts `PreKeyMessageFields` from a pre-key message body when `parsePreKey` succeeds at
version 4 with a 1568-byte Kyber ciphertext prefixed by `0x08`. -/
def preKeyOfBody? (body : HwBytes) : Option PreKeyMessageFields :=
  match parsePreKey body, decodePreKey (body.drop 1) with
  | some q, some raw =>
    if q.version = 4 then
      match q.kyberPreKeyId, q.kyberCiphertext with
      | some kid, some (t :: ct) =>
        if h : t = 0x08#8 ∧ ct.length = 1568 then
          some { regId := raw.registrationId.getD 0, opkId := q.preKeyId, spkId := q.signedPreKeyId,
                 kpkId := kid, kyberCt := ⟨ct, h.2⟩, baseKey := vec32 (q.baseKey.drop 1),
                 idPub := vec32 (q.identityKey.drop 1), inner := q.message }
        else none
      | _, _ => none
    else none
  | _, _ => none

/-- Checks whether an existing session `(x, g)` matches parsed pre-key fields `q` on
`aliceBaseKey` and `sessionVersion`. -/
def PqFieldsMatch (x : RecordExtras) (g : GhostState HwBytes) (q : PreKeyFields) : Prop :=
  x.aliceBaseKey = q.baseKey.take 33 ∧ g.session.sessionVersion.toNat = q.version

/-- Model transition for decrypting a parsed pre-key message `q` against a matching existing
session `(x, g)`. -/
def pqRecvMatchingFieldsModel (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState HwBytes) (q : PreKeyFields) (rc : BitVec 256) :
    Option (Option (PqParty × HwBytes)) :=
  let idA : IdentityKey := ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩
  if !st.trusts idA then some none
  else if g.session.remoteIdentity ≠ some idA then some none
  else
    match SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g.party) q.inner .preKey rc g.session with
    | (.ok pt, s) =>
      some (some ({ st with peerId := some idA, session := some (x, { g with session := s }) }, pt))
    | (.error .panic, _) => none
    | (.error _, _) => some none

open CryptoVerification.SignalSession (pqInputs publicBundleOf bundleDir)

/-- CLI `init` inputs for party `st` over an arbitrary bundle file list `files` and 192-byte
randomness tape `t`. -/
def pqInitInputsF (P : PEParams) (st : PqParty) (files : List (String × HwBytes))
    (t : List.Vector (BitVec 8) initiateTapeLen) : Inputs :=
  pqInputs P st (.init (partyAddress st.party.other) bundleDir) files t.toList []

/-- Outcome equivalence up to `scrub` on directory snapshots. -/
def ScrubAgree : Outcome → Outcome → Prop
  | .aborted, .aborted => True
  | .exited c out fs, .exited c' out' fs' => c = c' ∧ out = out' ∧ ∀ p, scrub fs p = scrub fs' p
  | _, _ => False

/-- Postcondition on an outcome `o` for CLI input `i` combining `CliSpecPqxdh`,
`CliSpecPqxdhNoMatch`, archived session-file contents, general pre-key `recv` cases, and
flat-bundle `init` cases. -/
structure PqModelPost (_interp : ExternInterpretation) (P : PEParams) (i : Inputs)
    (o : Outcome) : Prop where
  init : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (b : PreKeyBundleFields)
      (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none →
    InputsEquiv i (pqInitInputs P st b t) →
    o = pqxdhExpectedOutcome P (pqInitInputs P st b t) (pqInitModel X P st b t)
  send : ∀ (st : PqParty) (m : HwBytes) (coins : List.Vector (BitVec 8) 64),
    PqxdhPartyInSpecDomain P st → m.length < 2 ^ 32 →
    InputsEquiv i (pqSendInputs P st m coins) →
    o = pqxdhExpectedOutcome P (pqSendInputs P st m coins) (pqSendModel P st m coins.toList)
  recvWhisper : ∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    InputsEquiv i (pqRecvInputs P st (wireWhisper :: body) rc) →
    o = pqxdhExpectedOutcome P (pqRecvInputs P st (wireWhisper :: body) rc) (pqRecvWhisperModel P st body rc)
  recvPrekey : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: m.bytes) rc) →
    o = pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: m.bytes) rc) (pqRecvPrekeyModel X P st m rc)
  recvPrekeyNoMatch : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (x : RecordExtras)
      (g : GhostState HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → m.inner.length + 2048 < 2 ^ 32 →
    ¬ PqSessionMatches x g m →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: m.bytes) rc) →
    OutcomeMatchesModelExceptPath P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
      (sessionFile (partyAddress st.party.other))
      (pqRecvPrekeyModel X P { st with session := none } m rc) o
  recvOther : ∀ (st : PqParty) (c : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → c.length < 2 ^ 32 →
    c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
    InputsEquiv i (pqRecvInputs P st c rc) →
    o = .exited 1 [] (filesOf (pqRecvInputs P st c rc).files)
  recvPrekeyNoMatchSession : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (x : RecordExtras)
      (g : GhostState HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → m.inner.length + 2048 < 2 ^ 32 →
    ¬ PqSessionMatches x g m →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: m.bytes) rc) →
    NoMatchSessionFile X P st x g m rc o
  recvPrekeyReject : ∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 → parsePreKey body = none →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = .exited 1 [] (filesOf (pqRecvInputs P st (wirePrekey :: body) rc).files)
  recvPrekeyUntyped : ∀ (st : PqParty) (body : HwBytes) (q : PreKeyFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 → parsePreKey body = some q → preKeyOfBody? body = none →
    (∀ x g, st.session = some (x, g) → ¬ PqFieldsMatch x g q) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = .exited 1 [] (filesOf (pqRecvInputs P st (wirePrekey :: body) rc).files)
  recvPrekeyMatching : ∀ (st : PqParty) (x : RecordExtras) (g : GhostState HwBytes)
      (body : HwBytes) (q : PreKeyFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → body.length < 2 ^ 32 → parsePreKey body = some q →
    PqFieldsMatch x g q →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: body) rc)
      (pqRecvMatchingFieldsModel P st x g q rc)
  recvPrekeyParsed : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (body : HwBytes) (m : PreKeyMessageFields)
      (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 → preKeyOfBody? body = some m →
    m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    o = pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: body) rc) (pqRecvPrekeyModel X P st m rc)
  recvPrekeyParsedNoMatch : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (x : RecordExtras)
      (g : GhostState HwBytes) (body : HwBytes) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → body.length < 2 ^ 32 →
    preKeyOfBody? body = some m → m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    OutcomeMatchesModelExceptPath P (pqRecvInputs P st (wirePrekey :: body) rc)
        (sessionFile (partyAddress st.party.other))
        (pqRecvPrekeyModel X P { st with session := none } m rc) o ∧
      NoMatchSessionFile X P st x g m rc o
  initFiles : ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (files : List (String × HwBytes)) (b : PreKeyBundleFields)
      (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files →
    parseBundleFiles (filesOf files) = some (publicBundleOf b) →
    InputsEquiv i (pqInitInputsF P st files t) →
    ScrubAgree o (pqxdhExpectedOutcome P (pqInitInputsF P st files t) (pqInitModel X P st b t))
  initReject : ∀ (st : PqParty) (files : List (String × HwBytes))
      (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none → BundleFilesFlat files → parseBundleFiles (filesOf files) = none →
    InputsEquiv i (pqInitInputsF P st files t) →
    o = .exited 1 [] (filesOf (pqInitInputsF P st files t).files)

/-- Run relation satisfied when execution aborts or exits in a state satisfying `PqModelPost`. -/
def PqModelRel (interp : ExternInterpretation) (P : PEParams) (i : Inputs)
    (o : Option Outcome) : Prop :=
  o = some .aborted ∨ ∃ out_o, o = some out_o ∧ PqModelPost interp P i out_o

/-- Whole-protocol CLI refinement instantiated with `ModelAgree` and `PqModelRel`. -/
def CompRefinesCliModel : Prop :=
  CompRefinesCli ModelAgree PqModelRel

end DY.Libsignal.Composed.Refinement.Cli
