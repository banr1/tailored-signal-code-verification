/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessOom
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Whole-Process ELF Interface Bundle for Extended Pre-Key and Initiate Clauses

Packages the `OutcomeOrExcusedAbort` whole-process propositions and `MuslElf` structural
witness for a `signal-session` ELF image across baseline, extended pre-key `recv`, and
flat-bundle `init` execution paths.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Reconstructs the `Session` stored on disk for a PQXDH domain session `(x, g)`. -/
def d3PqSessionOf (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    Session (List (BitVec 8)) where
  state := g.session
  pendingPreKey := if g.session.pendingPreKey then some x.pending else none
  pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
  localRegistrationId := x.localRegistrationId
  remoteRegistrationId := x.remoteRegistrationId
  aliceBaseKey := x.aliceBaseKey

/-- Pure Path-B matching-session pre-key `recv` model on arbitrary wire `PreKeySignalMessage`. -/
def d3PqRecvMatchingModel (W : PEParams) (st : PqParty)
    (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (pm : PreKeySignalMessage) (rc : BitVec 256) :
    Option (Option (PqParty × List (BitVec 8))) :=
  let idA := pm.identityKey
  if !st.trusts idA then some none
  else if g.session.remoteIdentity ≠ some idA then some none
  else
    match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) pm.message .preKey rc g.session with
    | (.ok pt, s') =>
      some (some ({ st with
        peerId := some idA
        session := some (x, { g with session := s' }) }, pt))
    | (.error .panic, _) => none
    | (.error _, _) => some none

/-- Exact `SessionRecord` wire encoding written when an incoming pre-key message creates `(x', g')`
over a non-matching session `(x, g)`. -/
def d3NoMatchRecordBytes (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (x' : RecordExtras) (g' : GhostState (List (BitVec 8))) : List (BitVec 8) :=
  encodeRecordUnderExtras (fun _ => x') g' ++
    E2E.Record.lenField 2 (encStateUnderExtras x { g.session with pendingPreKey := false })

/-- Session-file content specification on an accepted non-matching pre-key `recv` over `(x, g)`. -/
def D3NoMatchSessionFile (X : UnreachedPqxdhPrimitives) (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState (List (BitVec 8))) (m : PreKeyMessageFields) (rc : BitVec 256) (o : Outcome) : Prop :=
  ∀ st' out x' g', pqRecvPrekeyModel X P { st with session := none } m rc = some (some (st', out)) →
    st'.session = some (x', g') →
    ∀ code out' fs, o = .exited code out' fs →
      fs (sessionFile (partyAddress st.party.other)) = some (d3NoMatchRecordBytes x g x' g')

/-- Bundled `MuslElf` validation hypotheses for a `signal-session` ELF image `elf`. -/
structure CliElfMuslHyp (elf : ElfImage) (muslCode : List (BitVec 8)) : Prop where
  elfStaticOk : Cli.ElfStaticOk elf
  tokenCells  : CliElfTokenCells elf
  musl        : CliElfMusl elf muslCode
  codeEndLe   : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat
  fetchStart  : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64
  fetchExit   : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64
  mainOff     : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta
  frozen      : CliElfFrozen elf cliImg
  statics     : CliElfStatics (patchElfTokens elf) cliImg

/-- Baseline `CliSpecPqxdhOrExcusedAbort` and `CliSpecPqxdhNoMatchOrExcusedAbort` specification on `elf`. -/
def CliPqBinaryCorrectOomD3 (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives),
    CliSpecPqxdhOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatchOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩

/-- Complete whole-process `OutcomeOrExcusedAbort` bundle for a `signal-session` ELF image `elf` across
baseline, extended pre-key `recv`, and flat-bundle `init` execution paths. -/
structure CliPqBinaryV2Oom (elf : ElfImage) : Prop where
  musl : ∃ muslCode, CliElfMuslHyp elf muslCode
  base : CliPqBinaryCorrectOomD3 elf
  canonicalNoMatch :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 →
        (wirePrekey :: m.bytes).length ≤ stdinCapBytes →
        ¬ PqSessionMatches x g m →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
          (fun o => OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
            D3NoMatchSessionFile X WP st x g m rc o)
  recvOverStdinCap :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        (wirePrekey :: body).length ≤ 2 ^ 32 →
        (wirePrekey :: body).length > stdinCapBytes →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
          (· = .exited 2 [] (filesOf inp.files))
  pksmParseNone :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        body.length < 2 ^ 32 →
        (wirePrekey :: body).length ≤ stdinCapBytes →
        Pksm.pksmParse body = none →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
          (· = .exited 1 [] (filesOf inp.files))
  untypedReject :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256),
        body.length < 2 ^ 32 →
        (wirePrekey :: body).length ≤ stdinCapBytes →
        Pksm.pksmParse body = some pm → pkToE? pm = none →
        (∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
          (· = .exited 1 [] (filesOf inp.files))
  matchingPathB :
    ∀ (W : CliHooks) (st : PqParty) (x : RecordExtras)
      (g : GhostState (List (BitVec 8))) (body : List (BitVec 8))
      (pm : PreKeySignalMessage) (rc : BitVec 256),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = some (x, g) → (wirePrekey :: body).length ≤ 2 ^ 32 →
      (wirePrekey :: body).length ≤ stdinCapBytes →
      Pksm.pksmParse body = some pm → SessMatchesPm (d3PqSessionOf x g) pm →
      let WP : PEParams := ⟨W.C, W.Q⟩
      let inp := pqRecvInputs WP st (wirePrekey :: body) rc
      OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
        (· = pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc))
  validMatch :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256),
        body.length < 2 ^ 32 →
        (wirePrekey :: body).length ≤ stdinCapBytes →
        Pksm.pksmParse body = some pm → pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
          (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc))
  validOver :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256),
        body.length < 2 ^ 32 →
        (wirePrekey :: body).length ≤ stdinCapBytes →
        Pksm.pksmParse body = some pm → pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (cliRunHitsAllocFailure elf W) (cliRunAbortOnPanic elf W) inp
          (fun o => OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
            D3NoMatchSessionFile X WP st x g m rc o)
  initSem :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives),
      ∃ (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop),
        subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
          (CryptoVerification.SignalSession.mainSpecTight E2E.HooksE.A0 cliImg
            Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) (RunCompose.runRel S)) ∧
        S.initiate = initDef X ⟨W.C, W.Q⟩ ∧
        S.filesOk = Slots.filesOk₀ Scope (fun _ => True) ∧
        S.initOk = InitOk₀ ⟨W.C, W.Q⟩

/-- Raw ELF-byte lifting of `CliPqBinaryV2Oom`. -/
def LibsignalCliPqBinaryV2Oom (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqBinaryV2Oom elf

end LibsignalBinary.Proofs.SignalSession.Cli.D3
