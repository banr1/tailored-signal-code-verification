/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.BundleGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.BundleGeneralParse
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesExtParity
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Two-Placement Whole-Process ELF Interface Bundle (`CliPqBinaryV2OomF3Placed`)

Two-placement `(mpl, mmpl : Obj.MultiPlacement)` whole-process `OutcomeOrExcusedAbort`
specification for the `signal-session` ELF image over `Placed.cliRunPlacedSig mpl mmpl elf W`
and `CliReachesOOMPlaced mpl mmpl elf W` (`DEV-CLI15`: total except `.OutOfMemory`),
combining `CliPqxdhElfCorrectPlaced` with `recvOverStdinCap`, `canonicalNoMatch`, extended
pre-key `recv`, and flat-bundle `init` clauses.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (libsignalSessionLib)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
  initiateTapeLen wirePrekey
)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhElfCorrectPlaced CliReachesOOMPlaced Inputs OutcomeMatchesModelExceptPath
  OutcomeOrExcusedAbort PqParty PqSessionMatches PqxdhPartyInSpecDomain bundleDir filesOf
  partyAddress pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome
  publicBundleOf sessionFile stdinCapBytes
)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  D3NoMatchSessionFile d3PqRecvMatchingModel d3PqSessionOf
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (
  BundleReadWithinCap InputsEquivRaw parseBundleDir
)

/-- Raw CLI `init` input with arbitrary flat bundle file entries `files`. -/
def pqInitInputsFRaw (P : PEParams) (st : PqParty)
    (files : List (String × List (BitVec 8)))
    (t : List.Vector (BitVec 8) initiateTapeLen) : Inputs :=
  pqInputs P st (.init (partyAddress st.party.other) bundleDir) files t.toList []

/-- Flat bundle file entries: every path normalizes to `[bundleDir, name]` and has length `< 2^31`. -/
def BundleFilesFlatRaw (files : List (String × List (BitVec 8))) : Prop :=
  ∀ f ∈ files, (∃ name, Arm64.normalizePath f.1 = [bundleDir, name]) ∧ f.2.length < 2 ^ 31

/-- Complete two-placement `(mpl, mmpl)` whole-process `OutcomeOrExcusedAbort` bundle for a
`signal-session` ELF image `elf` across baseline PQXDH, `recvOverStdinCap`,
`canonicalNoMatch`, extended pre-key `recv`, and flat-bundle `init` clauses. -/
structure CliPqBinaryV2OomF3Placed (mpl mmpl : MultiPlacement) (elf : ElfImage) : Prop where
  base : CliPqxdhElfCorrectPlaced mpl mmpl elf
  recvOverStdinCap :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        (wirePrekey :: body).length > stdinCapBytes →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = .exited 2 [] (filesOf inp.files))
  canonicalNoMatch :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (fun o => if (wirePrekey :: m.bytes).length > stdinCapBytes then
              o = .exited 2 [] (filesOf inp.files)
            else
              OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
              D3NoMatchSessionFile X WP st x g m rc o)
  pksmParseNone :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = none →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then
            .exited 2 [] (filesOf inp.files)
          else
            .exited 1 [] (filesOf inp.files))
  untypedReject :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = none →
        (∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then
            .exited 2 [] (filesOf inp.files)
          else
            .exited 1 [] (filesOf inp.files))
  matchingPathB :
    ∀ (W : CliHooks) (st : PqParty) (x : RecordExtras)
      (g : GhostState (List (BitVec 8))) (body : List (BitVec 8))
      (pm : PreKeySignalMessage) (rc : BitVec 256),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = some (x, g) →
      (wirePrekey :: body).length ≤ 2 ^ 32 →
      pksmParse body = some pm → SessMatchesPm (d3PqSessionOf x g) pm →
      let WP : PEParams := ⟨W.C, W.Q⟩
      let inp := pqRecvInputs WP st (wirePrekey :: body) rc
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) inp
        (· = if (wirePrekey :: body).length > stdinCapBytes then
          .exited 2 [] (filesOf inp.files)
        else
          pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc))
  validMatch :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
        (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then
            .exited 2 [] (filesOf inp.files)
          else
            pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc))
  validOver :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
      ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
        (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
        m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (fun o => if (wirePrekey :: body).length > stdinCapBytes then
              o = .exited 2 [] (filesOf inp.files)
            else
              OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
              D3NoMatchSessionFile X WP st x g m rc o)
  initFiles :
    ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (st : PqParty)
      (files : List (String × List (BitVec 8))) (b : PreKeyBundleFields)
      (t : List.Vector (BitVec 8) initiateTapeLen) (i : Inputs),
      InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t) →
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
      BundleFilesFlatRaw files →
      BundleReadWithinCap (filesOf files) bundleDir →
      parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b) →
      cliRunPlacedSig mpl mmpl elf W i = none ∨
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) i
          (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
            (pqInitModel X ⟨W.C, W.Q⟩ st b t))
  initReject :
    ∀ (W : CliHooks) (st : PqParty) (files : List (String × List (BitVec 8)))
      (t : List.Vector (BitVec 8) initiateTapeLen) (i : Inputs),
      InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t) →
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
      BundleFilesFlatRaw files →
      parseBundleDir (filesOf files) bundleDir = none →
      cliRunPlacedSig mpl mmpl elf W i = none ∨
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) i
          (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files))
  initOverFileCap :
    ∀ (W : CliHooks) (st : PqParty) (files : List (String × List (BitVec 8)))
      (t : List.Vector (BitVec 8) initiateTapeLen) (i : Inputs),
      InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t) →
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
      BundleFilesFlatRaw files →
      ¬ BundleReadWithinCap (filesOf files) bundleDir →
      cliRunPlacedSig mpl mmpl elf W i = none ∨
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) i
          (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files))

/-- Raw ELF-byte lifting of `CliPqBinaryV2OomF3Placed` at specific placements `(mpl, mmpl)`. -/
def LibsignalCliPqBinaryV2OomF3PlacedAt (mpl mmpl : MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqBinaryV2OomF3Placed mpl mmpl elf

/-- Universally quantified two-placement ELF-byte lifting of `CliPqBinaryV2OomF3Placed`
across all `libsignalSessionLib.LinkedAt bytes mpl` and
`VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl`. -/
def LibsignalCliPqBinaryV2OomF3Placed (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
