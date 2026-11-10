/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkA1
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlot
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj

/-!
# Instantiation of `signal_session::run` into `main` and Domain Refinement Bridges

Wires `RunCompose.run_ok'` and `runRel_dom` at `cliRunSem` into `main_ok_a1`, combining `mainSpec` /
`mainSpecTight` with `RunRefine`, `RunBounds`, `RunFilesOk`, `RunEncOk`, `RunHsOk`, and `CommitOk`
to establish SM-domain (`main_ok_cli_sm`, `cliBinaryCorrect_of_slots`) and 5-clause PQXDH-domain
(`main_ok_cli_pq`) correctness, together with `(P, A, ext)` generalizations.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Default unreached `UnreachedPqxdhPrimitives` witness (used when instantiating `RunSem` for the SM domain,
which never invokes `initiate` or `decrypt_prekey`). -/
def defaultModelExtras : UnreachedPqxdhPrimitives where
  sigPkGen _ := []
  sigSign _ _ _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  kemKeyGen _ := ([], [])
  pow8 _ := []
  isValidDhTriple _ _ _ := false

/-- Concrete `RunSem` (`S₀`) at `Slots.scopeIn` for `encDef`, `decSigDef`, `initDef` (`InitOk₀`),
`filesOk₀`, and `encOk₀`, parameterized over `decPk`, `decPkOk`, and `pksmParse`. -/
noncomputable def cliRunSem (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef ⟨W.C, W.Q⟩ Slots.scopeIn
  decryptSignal := decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn
  initiate := initDef X ⟨W.C, W.Q⟩
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ ⟨W.C, W.Q⟩
  decPkOk := decPkOk

/-- Existential witness for the all-inputs `PreKeySignalMessage::try_from` slot. -/
def CliPksmSlotExists (img : Obj.Image) (W : CliHooks) : Prop :=
  ∃ pksmParse : List (BitVec 8) → Option PreKeySignalMessage,
    ∀ S : RunSem, S.pksmParse = pksmParse →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
        ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
        (pksmSlotSpec E2E.HooksE.A0 img S)

/-- Existential witness for the `decrypt_prekey` slot. -/
def CliDecPkSlotExists (img : Obj.Image) (W : CliHooks) : Prop :=
  ∃ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
        SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (decPkNeed : Nat),
    decPkNeed ≤ 4194304 ∧
    ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPk →
      S.decPkOk = decPkOk →
      needs.decryptPrekey = decPkNeed →
      (slotsOf E2E.HooksE.A0 img S needs).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName

/-- PQXDH pre-key slot and model-agreement bundle. -/
structure CliPqPrekeyBundle (img : Obj.Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Type where
  decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
    SlotAns (List (BitVec 8))
  decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop
  pksmParse : List (BitVec 8) → Option PreKeySignalMessage
  decPkNeed : Nat
  needLe : decPkNeed ≤ 4194304
  pksmSlot : ∀ S : RunSem, S.pksmParse = pksmParse →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec E2E.HooksE.A0 img S)
  decPkSlot : ∀ (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPk →
    S.decPkOk = decPkOk →
    needs.decryptPrekey = decPkNeed →
    (slotsOf E2E.HooksE.A0 img S needs).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName
  pksmAgrees : ∀ S : RunSem, S.pksmParse = pksmParse → PksmParseAgrees S
  decPkAgrees : ∀ S : RunSem, S.decryptPrekey = decPk → PqDecryptPrekeyAgrees S X ⟨W.C, W.Q⟩
  decPkDomOk : ∀ (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256) (pm : PreKeySignalMessage),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    pksmParse m.bytes = some pm →
    decPkOk (runFiles (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc))
      (addrValE st.party.other) (addrValE st.party) pm
  decPkCommitOk : ∀ (S : RunSem) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256),
    S.decryptPrekey = decPk → S.pksmParse = pksmParse →
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)))

/-- Assemble all six `RunCallees` fields at `cliRunSem`. -/
theorem runCallees_cli {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdecPkSlot : (slotsOf E2E.HooksE.A0 img (cliRunSem X W decPk decPkOk pksmParse)
      (cliRunNeeds decPkNeed)).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName) :
    RunCallees img E2E.HooksE.A0 (cliExterns W) cliRunBudgets
      (slotsOf E2E.HooksE.A0 img (cliRunSem X W decPk decPkOk pksmParse)
        (cliRunNeeds decPkNeed)) := by
  let S := cliRunSem X W decPk decPkOk pksmParse
  let hh := RunHooks.cli W img
  let hRead := cliReadFile_ok W img cliRunBudgets.readFile
  exact
    { readFile := hRead
      encrypt := cliEncrypt_slotOk W cliRunBudgets S Slots.scopeIn (cliRunNeeds decPkNeed)
        himg hh hRead Slots.encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
        (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl
      decryptSignal := cliDecryptSignal_slotOk W cliRunBudgets S Slots.scopeIn
        (cliRunNeeds decPkNeed) himg hh hRead Slots.encodeInjOn_deserializeScopeP_Q (fun _ h => h)
        rfl (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl
      initiate := cliInitiate_slotOk W X cliRunBudgets S (cliRunNeeds decPkNeed)
        himg hh hRead rfl (fun _ _ _ _ hi => hi) rfl
      decryptPrekey := hdecPkSlot
      kemDeserialize := hc_kemDeserialize_of_hooks hh }

/-- Instantiates `RunCompose.run_ok'` at `Run := runRel (cliRunSem ...)`. -/
theorem hrun_cli {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hdecPkSlot : (slotsOf E2E.HooksE.A0 img (cliRunSem X W decPk decPkOk pksmParse)
      (cliRunNeeds decPkNeed)).decryptPrekey.Ok img (cliExterns W) wrapDecryptPrekeyName)
    (hpksmSlot : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec E2E.HooksE.A0 img (cliRunSem X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr runName)
      ((runSpec E2E.HooksE.A0 img uuidTryParse
        (runRel (cliRunSem X W decPk decPkOk pksmParse)) cliWrOk cliResStack).inImage img) :=
  RunCompose.run_ok' himg (RunHooks.cli W img)
    (runCallees_cli X W decPk decPkOk pksmParse decPkNeed himg hdecPkSlot)
    hpksmSlot (runNeed_cli_le_resStack hdecNeed) cliResStack_le_63

/-- Instantiates `main_ok_a1` with `hrun_cli` and `@RunCompose.runRel_dom`. -/
theorem main_ok_cli {cliImg : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hdecPkSlot : (slotsOf E2E.HooksE.A0 cliImg (cliRunSem X W decPk decPkOk pksmParse)
      (cliRunNeeds decPkNeed)).decryptPrekey.Ok cliImg (cliExterns W) wrapDecryptPrekeyName)
    (hpksmSlot : subroutine_ok (tripleRatchetProgAtExt cliImg.base (cliExterns W))
      ((tripleRatchetProgAtExt cliImg.base (cliExterns W)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec E2E.HooksE.A0 cliImg (cliRunSem X W decPk decPkOk pksmParse))) :
    subroutine_ok (cliProg cliImg (cliExterns W)) (entryOf cliImg mainName)
      (mainSpec E2E.HooksE.A0 cliImg cliMainStk (cliStatics cliImg)
        (runRel (cliRunSem X W decPk decPkOk pksmParse))) :=
  main_ok_a1 W himg
    (hrun_cli X W decPk decPkOk pksmParse decPkNeed himg hdecNeed hdecPkSlot hpksmSlot)
    (fun _ _ hr => RunCompose.runRel_dom hr)

/-- Instantiates `main_ok_a1_tight` with `@RunCompose.runRel_dom` and a `runSpecTight`
subroutine witness `hrun`. -/
theorem main_ok_cli_of_runTight {cliImg : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hrun : subroutine_ok (mProg cliImg (cliExterns W)) ((mProg cliImg (cliExterns W)).fnAddr runName)
      ((runSpecTight E2E.HooksE.A0 cliImg uuidTryParse
        (runRel (cliRunSem X W decPk decPkOk pksmParse)) cliWrOk cliResStack).inImage cliImg)) :
    subroutine_ok (cliProg cliImg (cliExterns W)) (entryOf cliImg mainName)
      (mainSpecTight E2E.HooksE.A0 cliImg cliMainStk (cliStatics cliImg)
        (runRel (cliRunSem X W decPk decPkOk pksmParse))) :=
  main_ok_a1_tight W himg hrun (fun _ _ hr => RunCompose.runRel_dom hr)

/-! ## Parameterized `(P, A, ext)` Generalizations -/

/-- `cliRunSem` parameterized over `P : PEParams` instead of `W : CliHooks` (`W.bcmp` and
`W.utf8Err` are unused in `cliRunSem`). -/
noncomputable def cliRunSemExt (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef P Slots.scopeIn
  decryptSignal := decSigDef P Slots.scopeIn
  initiate := initDef X P
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ P
  decPkOk := decPkOk

theorem cliRunSem_eq_ext (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) :
    cliRunSem X W decPk decPkOk pksmParse = cliRunSemExt X ⟨W.C, W.Q⟩ decPk decPkOk pksmParse :=
  rfl

/-- `CliPksmSlotExists` generalized to `(A : RustAlloc)` and `(ext : String → Option (State → State))`
via `cliExternsWith ext`. -/
def CliPksmSlotExistsExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∃ pksmParse : List (BitVec 8) → Option PreKeySignalMessage,
    ∀ S : RunSem, S.pksmParse = pksmParse →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
        (pksmSlotSpec A img S)

theorem cliPksmSlotExists_iff_ext (img : Obj.Image) (W : CliHooks) :
    CliPksmSlotExists img W ↔ CliPksmSlotExistsExt img E2E.HooksE.A0 (cliHookExterns W) :=
  Iff.rfl

/-- `CliDecPkSlotExists` generalized to `(A : RustAlloc)` and `(ext : String → Option (State → State))`
via `cliExternsWith ext`. -/
def CliDecPkSlotExistsExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∃ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
        SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (decPkNeed : Nat),
    decPkNeed ≤ 4194304 ∧
    ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPk →
      S.decPkOk = decPkOk →
      needs.decryptPrekey = decPkNeed →
      (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName

theorem cliDecPkSlotExists_iff_ext (img : Obj.Image) (W : CliHooks) :
    CliDecPkSlotExists img W ↔ CliDecPkSlotExistsExt img E2E.HooksE.A0 (cliHookExterns W) :=
  Iff.rfl

/-- Any D2(c) `decrypt_prekey` slot witness at budget `cliDecPkNeed₀`
(`= cliDecryptPrekeyNeed cliRunBudgets` definitionally) discharges `CliDecPkSlotExistsExt`. -/
theorem cliDecPkSlotExistsExt_of_d2c {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {decPkD2c : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOkD2c : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    (hd2c : ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPkD2c →
      S.decPkOk = decPkOkD2c →
      needs.decryptPrekey = cliDecPkNeed₀ →
      (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName) :
    CliDecPkSlotExistsExt img A ext :=
  ⟨decPkD2c, decPkOkD2c, cliDecPkNeed₀, by decide, hd2c⟩

/-- `CliPqPrekeyBundle` generalized to `(P : PEParams) (A : RustAlloc)` and `cliExternsWith ext`
(including `S.pksmParse = pksmParse →` in `decPkAgrees`, matching `CliPqPrekeyBundleS0`). -/
structure CliPqPrekeyBundleExt (img : Obj.Image) (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State)) : Type where
  decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
    SlotAns (List (BitVec 8))
  decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop
  pksmParse : List (BitVec 8) → Option PreKeySignalMessage
  decPkNeed : Nat
  needLe : decPkNeed ≤ 4194304
  pksmSlot : ∀ S : RunSem, S.pksmParse = pksmParse →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S)
  decPkSlot : ∀ (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPk →
    S.decPkOk = decPkOk →
    needs.decryptPrekey = decPkNeed →
    (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName
  pksmAgrees : ∀ S : RunSem, S.pksmParse = pksmParse → PksmParseAgrees S
  decPkAgrees : ∀ S : RunSem, S.decryptPrekey = decPk → S.pksmParse = pksmParse →
    PqDecryptPrekeyAgrees S X P
  decPkDomOk : ∀ (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256) (pm : PreKeySignalMessage),
    PqxdhPartyInSpecDomain P st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    pksmParse m.bytes = some pm →
    decPkOk (runFiles (pqRecvInputs P st (wirePrekey :: m.bytes) rc))
      (addrValE st.party.other) (addrValE st.party) pm
  decPkCommitOk : ∀ (S : RunSem) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256),
    S.decryptPrekey = decPk → S.pksmParse = pksmParse →
    PqxdhPartyInSpecDomain P st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    CommitOk (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs P st (wirePrekey :: m.bytes) rc)))

/-- Upstream callee/hook bundle consumed by `runCallees_ext` and `hrun_ext` at
`(P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))`. -/
structure RunInstCalleeDepsExt (img : Obj.Image) (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  hooks : RunHooks img A (cliExternsWith ext)
  readFile : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
    ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
    (readFileSpec cliIo.rd cliWrOk A img cliRunBudgets.readFile)
  encrypt : ∀ (S : RunSem) (needs : RunNeeds),
    S.encrypt = encDef P Slots.scopeIn →
    (∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      Slots.FilesOkPeer Slots.scopeIn F peer ∧ Slots.encOk₀ Slots.scopeIn F peer coins) →
    needs.encrypt = cliEncryptNeed cliRunBudgets →
    (slotsOf A img S needs).encrypt.Ok img (cliExternsWith ext) wrapEncryptName
  decryptSignal : ∀ (S : RunSem) (needs : RunNeeds),
    S.decryptSignal = decSigDef P Slots.scopeIn →
    (∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Slots.scopeIn F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name) →
    needs.decryptSignal = cliDecryptSignalNeed cliRunBudgets →
    (slotsOf A img S needs).decryptSignal.Ok img (cliExternsWith ext) wrapDecryptSignalName
  initiate : ∀ (S : RunSem) (needs : RunNeeds),
    S.initiate = initDef X P →
    (∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ P F peer me) →
    needs.initiate = cliInitiateNeed cliRunBudgets →
    (slotsOf A img S needs).initiate.Ok img (cliExternsWith ext) wrapInitiateName

/-- Assemble all six `RunCallees` fields at `cliRunSemExt` and `cliExternsWith ext`. -/
theorem runCallees_ext {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State))
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdeps : RunInstCalleeDepsExt img X P A ext)
    (hdecPkSlot : (slotsOf A img (cliRunSemExt X P decPk decPkOk pksmParse)
      (cliRunNeeds decPkNeed)).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName) :
    RunCallees img A (cliExternsWith ext) cliRunBudgets
      (slotsOf A img (cliRunSemExt X P decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)) :=
  { readFile := hdeps.readFile
    encrypt := hdeps.encrypt _ _ rfl (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl
    decryptSignal := hdeps.decryptSignal _ _ rfl (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl
    initiate := hdeps.initiate _ _ rfl (fun _ _ _ _ hi => hi) rfl
    decryptPrekey := hdecPkSlot
    kemDeserialize := hc_kemDeserialize_of_hooks hdeps.hooks }

/-- Instantiates `RunCompose.run_ok'` at `Run := runRel (cliRunSemExt ...)` for arbitrary
`(P, A, ext)`. -/
theorem hrun_ext {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State))
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdeps : RunInstCalleeDepsExt img X P A ext)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hdecPkSlot : (slotsOf A img (cliRunSemExt X P decPk decPkOk pksmParse)
      (cliRunNeeds decPkNeed)).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName)
    (hpksmSlot : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img (cliRunSemExt X P decPk decPkOk pksmParse))) :
    subroutine_ok (mProg img (cliExternsWith ext)) ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpecTight A img uuidTryParse
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse)) cliWrOk cliResStack).inImage img) :=
  RunCompose.run_ok' himg hdeps.hooks
    (runCallees_ext X P A ext decPk decPkOk pksmParse decPkNeed hdeps hdecPkSlot)
    hpksmSlot (runNeed_cli_le_resStack_ext hdecNeed) cliResStack_le_63

/-- Parameterized `main_ok_ext_tight` interface at `(A, ext)`. -/
def MainOkA1TightAt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {Run : Inputs → Cli.RunAnswer → Prop},
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpecTight A img uuidTryParse Run cliWrOk cliResStack).inImage img) →
    (∀ i a, Run i a → DomainArgv i) →
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpecTight A img cliMainStk (cliStatics img) Run)

/-- `main_ok_cli_of_runTight` generalized to `(P : PEParams) (A : RustAlloc)` and `cliExternsWith ext`. -/
theorem main_ok_cli_ext_of_runTight {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State))
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (hmainA1 : MainOkA1TightAt img A ext)
    (hrun : subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpecTight A img uuidTryParse
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse)) cliWrOk cliResStack).inImage img)) :
    subroutine_ok (cliProg img (cliExternsWith ext)) (entryOf img mainName)
      (mainSpecTight A img cliMainStk (cliStatics img)
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse))) :=
  hmainA1 hrun (fun _ _ hr => RunCompose.runRel_dom hr)

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem varint_length_le_5 {n : Nat} (hn : n < 2 ^ 32) :
    (Prost.varint n).length ≤ 5 := by
  unfold Prost.varint; split
  · simp
  · dsimp only [List.length_cons]; unfold Prost.varint; split
    · simp
    · dsimp only [List.length_cons]; unfold Prost.varint; split
      · simp
      · dsimp only [List.length_cons]; unfold Prost.varint; split
        · simp
        · dsimp only [List.length_cons]; unfold Prost.varint
          have h5 : n / 128 / 128 / 128 / 128 < 128 := by omega
          simp [h5]

private theorem key_length_le_5 {tag wt : Nat} (h : 8 * tag + wt < 2 ^ 32) :
    (Prost.key tag wt).length ≤ 5 :=
  varint_length_le_5 h

private theorem uint32Field_length_le_10 {tag : Nat} (ht : 8 * tag < 2 ^ 32)
    (ov : Option (BitVec 32)) :
    (Prost.uint32Field tag ov).length ≤ 10 := by
  cases ov with
  | none => simp [Prost.uint32Field]
  | some v =>
    simp only [Prost.uint32Field, List.length_append]
    have h1 := key_length_le_5 (wt := 0) (by omega)
    have h2 := varint_length_le_5 v.isLt
    omega

private theorem bytesField_some_length_le {tag : Nat} {bs : List (BitVec 8)}
    (ht : 8 * tag + 2 < 2 ^ 32) (hbs : bs.length < 2 ^ 32) :
    (Prost.bytesField tag (some bs)).length ≤ bs.length + 10 := by
  simp only [Prost.bytesField, List.length_append]
  have h1 := key_length_le_5 ht
  have h2 := varint_length_le_5 hbs
  omega

theorem preKeyMsgE_bytes_lt_2_32 {m : PreKeyMessageFields} (hm : m.inner.length + 2048 < 2 ^ 32) :
    m.bytes.length < 2 ^ 32 := by
  simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  have h1 := uint32Field_length_le_10 (tag := 1) (by decide) m.opkId
  have h2 := bytesField_some_length_le (tag := 2) (bs := djbKey m.baseKey) (by decide)
    (by simp [djbKey])
  have h3 := bytesField_some_length_le (tag := 3) (bs := djbKey m.idPub) (by decide)
    (by simp [djbKey])
  have h4 := bytesField_some_length_le (tag := 4) (bs := m.inner) (by decide) (by omega)
  have h5 := uint32Field_length_le_10 (tag := 5) (by decide) (some m.regId)
  have h6 := uint32Field_length_le_10 (tag := 6) (by decide) (some m.spkId)
  have h7 := uint32Field_length_le_10 (tag := 7) (by decide) (some m.kpkId)
  have h8 := bytesField_some_length_le (tag := 8) (bs := kyberKey m.kyberCt) (by decide)
    (by simp [kyberKey])
  have hdjb1 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hdjb2 : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hkyb : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  omega

/-- SM-domain `main` composition: instantiates `main_ok_a1` with `RunCompose.runRel_dom` and
`RunCompose.run_ok'` at `Run := runRel S₀`, bridging `smSendInputs` and `smRecvInputs` to
`smSendModel` / `smRecvModel` and `CommitOk`. -/
theorem main_ok_cli_sm {cliImg : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpksm : Cli.MainHops.CliPksmSlotExists cliImg W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExists cliImg W) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨pksmParse, hpksmSlot⟩ := hpksm
  obtain ⟨decPk, decPkOk, decPkNeed, hdecNeed, hdecPkSlot⟩ := hdecPk
  let S : RunSem := cliRunSem defaultModelExtras W decPk decPkOk pksmParse
  have hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) (runRel S)) :=
    main_ok_cli defaultModelExtras W decPk decPkOk pksmParse decPkNeed himg hdecNeed
      (hdecPkSlot S (cliRunNeeds decPkNeed) rfl rfl rfl rfl)
      (hpksmSlot S rfl)
  have hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  clear_value S
  have hcovSm := ratchetScopeCoversSm_scopeIn W.C
  have hagEnc : SmEncryptAgrees S W.C :=
    smEncryptAgrees_encDef S ⟨W.C, W.Q⟩ Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovSm
  have hagDec : SmDecryptSignalAgrees S W.C :=
    smDecryptSignalAgrees_decSigDef S ⟨W.C, W.Q⟩ Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovSm
  refine ⟨runRel S, hmain, fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · exact ⟨runAns S (smSendInputs g m),
      ⟨domainArgv_smSend g m, runBounds_smSend g m hm,
        runFilesOk_smSend_cli (S := S) hS_files g m hg,
        runEncOk_smSend_cli (S := S) hS_encOk g m hg,
        runHsOk_smSend_cli S g m, rfl⟩,
      RunRefine.runAns_smSend S W.C hagEnc g m hg hm,
      commitOk_smSend_encDef (S := S) (W := ⟨W.C, W.Q⟩) hS_enc g m⟩
  · exact ⟨runAns S (smRecvInputs g c rc),
      ⟨domainArgv_smRecv g c rc, runBounds_smRecv g c rc hc,
        runFilesOk_smRecv_cli (S := S) hS_files g c rc hg,
        Slots.runEncOk_smRecv S g c rc,
        runHsOk_smRecv_cli S g c rc, rfl⟩,
      RunRefine.runAns_smRecv S W.C hagDec g c rc hg hc,
      commitOk_smRecv_decSigDef (S := S) (W := ⟨W.C, W.Q⟩) hS_dec g c rc⟩

/-- Tightened SM-domain `main` composition producing `mainSpecTight` and SM `send`/`recv` model
agreement from a family of `runSpecTight` subroutine witnesses `hrun`. -/
theorem main_ok_cli_sm_of_runTight {cliImg : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpksm : Cli.MainHops.CliPksmSlotExists cliImg W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExists cliImg W)
    (hrun : ∀ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
        List (BitVec 8) → SlotAns (List (BitVec 8)))
      (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
      (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOf E2E.HooksE.A0 cliImg (cliRunSem defaultModelExtras W decPk decPkOk pksmParse)
        (cliRunNeeds decPkNeed)).decryptPrekey.Ok cliImg (cliExterns W) wrapDecryptPrekeyName →
      subroutine_ok (tripleRatchetProgAtExt cliImg.base (cliExterns W))
        ((tripleRatchetProgAtExt cliImg.base (cliExterns W)).fnAddr
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
        (pksmSlotSpec E2E.HooksE.A0 cliImg
          (cliRunSem defaultModelExtras W decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProg cliImg (cliExterns W))
        ((Cli.MainHops.mProg cliImg (cliExterns W)).fnAddr Cli.MainHops.runName)
        ((Cli.MainHops.runSpecTight E2E.HooksE.A0 cliImg uuidTryParse
          (runRel (cliRunSem defaultModelExtras W decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpecTight E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨pksmParse, hpksmSlot⟩ := hpksm
  obtain ⟨decPk, decPkOk, decPkNeed, hdecNeed, hdecPkSlot⟩ := hdecPk
  let S : RunSem := cliRunSem defaultModelExtras W decPk decPkOk pksmParse
  have hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpecTight E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)
        (runRel S)) :=
    main_ok_cli_of_runTight defaultModelExtras W decPk decPkOk pksmParse himg
      (hrun decPk decPkOk pksmParse decPkNeed hdecNeed
        (hdecPkSlot S (cliRunNeeds decPkNeed) rfl rfl rfl rfl)
        (hpksmSlot S rfl))
  have hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  clear_value S
  have hcovSm := ratchetScopeCoversSm_scopeIn W.C
  have hagEnc : SmEncryptAgrees S W.C :=
    smEncryptAgrees_encDef S ⟨W.C, W.Q⟩ Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovSm
  have hagDec : SmDecryptSignalAgrees S W.C :=
    smDecryptSignalAgrees_decSigDef S ⟨W.C, W.Q⟩ Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovSm
  refine ⟨runRel S, hmain, fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · exact ⟨runAns S (smSendInputs g m),
      ⟨domainArgv_smSend g m, runBounds_smSend g m hm,
        runFilesOk_smSend_cli (S := S) hS_files g m hg,
        runEncOk_smSend_cli (S := S) hS_encOk g m hg,
        runHsOk_smSend_cli S g m, rfl⟩,
      RunRefine.runAns_smSend S W.C hagEnc g m hg hm,
      commitOk_smSend_encDef (S := S) (W := ⟨W.C, W.Q⟩) hS_enc g m⟩
  · exact ⟨runAns S (smRecvInputs g c rc),
      ⟨domainArgv_smRecv g c rc, runBounds_smRecv g c rc hc,
        runFilesOk_smRecv_cli (S := S) hS_files g c rc hg,
        Slots.runEncOk_smRecv S g c rc,
        runHsOk_smRecv_cli S g c rc, rfl⟩,
      RunRefine.runAns_smRecv S W.C hagDec g c rc hg hc,
      commitOk_smRecv_decSigDef (S := S) (W := ⟨W.C, W.Q⟩) hS_dec g c rc⟩

/-- PQXDH-domain `main` composition: instantiates `main_ok_a1` at `Run := runRel S₀` and proves
all 5 domain clauses of `CliSpecPqxdh` (`init`, `send`, `recv` Whisper, `recv` PreKey, and `recv`
malformed wire prefix) together with `CommitOk`. -/
theorem main_ok_cli_pq {cliImg : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpre : Cli.MainHops.CliPqPrekeyBundle cliImg X W) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let S : RunSem := cliRunSem X W hpre.decPk hpre.decPkOk hpre.pksmParse
  have hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) (runRel S)) :=
    main_ok_cli X W hpre.decPk hpre.decPkOk hpre.pksmParse hpre.decPkNeed himg hpre.needLe
      (hpre.decPkSlot S (cliRunNeeds hpre.decPkNeed) rfl rfl rfl rfl)
      (hpre.pksmSlot S rfl)
  have hS_enc : S.encrypt = encDef WP Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef WP Slots.scopeIn := rfl
  have hS_init : S.initiate = initDef X WP := rfl
  have hS_decPk : S.decryptPrekey = hpre.decPk := rfl
  have hS_pksm : S.pksmParse = hpre.pksmParse := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  have hS_initOk : S.initOk = InitOk₀ WP := rfl
  have hS_decPkOk : S.decPkOk = hpre.decPkOk := rfl
  clear_value S
  have hcovPq := ratchetScopeCoversPq_scopeIn WP
  have hagInit : PqInitiateAgrees S X WP := InitS0.pqInitiateAgrees_initDef_proof S X WP hS_init
  have hagEnc : PqEncryptAgrees S WP :=
    pqEncryptAgrees_encDef S WP Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovPq
  have hagDec : PqDecryptSignalAgrees S WP :=
    pqDecryptSignalAgrees_decSigDef S WP Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovPq
  have hagPksm : PksmParseAgrees S := hpre.pksmAgrees S hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X WP := hpre.decPkAgrees S hS_decPk
  refine ⟨runRel S, hmain, fun st hst => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b t hnone
    exact ⟨runAns S (pqInitInputs WP st b t),
      ⟨domainArgv_pqInit WP st b t, runBounds_pqInit WP st b t,
        runFilesOk_pqInit_cli (S := S) hS_files WP st b t hst,
        Slots.runEncOk_pqInit S WP st b t,
        runHsOk_pqInit_cli (S := S) (W := WP) hS_initOk st b t hst hnone, rfl⟩,
      RunRefine.runAns_pqInit S X WP hagInit st b t hst hnone,
      commitOk_pqInit_initDef (S := S) (X := X) (W := WP) hS_init st b t⟩
  · intro m r hm
    exact ⟨runAns S (pqSendInputs WP st m r),
      ⟨domainArgv_pqSend WP st m r, runBounds_pqSend WP st m r hm,
        runFilesOk_pqSend_cli (S := S) hS_files WP st m r hst,
        Slots.runEncOk_pqSend (S := S) hS_encOk WP st m r,
        runHsOk_pqSend_cli S WP st m r, rfl⟩,
      RunRefine.runAns_pqSend S WP hagEnc st m r hst hm,
      commitOk_pqSend_encDef (S := S) (W := WP) hS_enc st m r⟩
  · intro c rc hc
    have hnot3 : (wireWhisper :: c).head? ≠ some wirePrekey := by simp [wireWhisper, wirePrekey]
    exact ⟨runAns S (pqRecvInputs WP st (wireWhisper :: c) rc),
      ⟨domainArgv_pqRecv WP st (wireWhisper :: c) rc,
        runBounds_pqRecv WP st (wireWhisper :: c) rc (Nat.succ_le_of_lt hc),
        runFilesOk_pqRecv_cli (S := S) hS_files WP st (wireWhisper :: c) rc hst,
        Slots.runEncOk_pqRecv S WP st (wireWhisper :: c) rc,
        runHsOk_pqRecvOther_cli S WP st (wireWhisper :: c) rc hnot3, rfl⟩,
      RunRefine.runAns_pqRecvWhisper S WP hagDec st c rc hst hc,
      commitOk_pqRecvWhisper_decSigDef (S := S) (W := WP) hS_dec st c rc⟩
  · intro m rc hm hmatch
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
        Slots.runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_of_decPkOk (S := S) WP st m rc
          (fun pm hpm => hS_decPkOk ▸ hpre.decPkDomOk st m rc pm hst hm hmatch (hS_pksm ▸ hpm)),
        rfl⟩,
      RunRefine.runAns_pqRecvPrekey S X WP hagPksm hagDecPk st m rc hst hm hmatch,
      hpre.decPkCommitOk S st m rc hS_decPk hS_pksm hst hm hmatch⟩
  · intro c rc hc h2 h3
    refine ⟨runAns S (pqRecvInputs WP st c rc),
      ⟨domainArgv_pqRecv WP st c rc,
        runBounds_pqRecv WP st c rc (Nat.le_of_lt hc),
        runFilesOk_pqRecv_cli (S := S) hS_files WP st c rc hst,
        Slots.runEncOk_pqRecv S WP st c rc,
        runHsOk_pqRecvOther_cli S WP st c rc h3, rfl⟩,
      ?_, commitOk_pqRecvBad S WP st c rc h2 h3⟩
    rw [runAns_pqRecvBad S WP st c rc h2 h3]
    rfl

/-- End-to-end whole-process SM correctness: combines `cliBinaryCorrect_of_parts_observe`
(`ProcessBridge.lean`) with `main_ok_cli_sm` at `A := E2E.HooksE.A0` and a ghost token-patched
ELF `elf'` (`DEV-CLI10`), reducing `CliBinaryCorrect elf` to image/ELF/harness facts and the
two pre-key slot existence witnesses (`hpksm`, `hdecPk`). -/
theorem cliBinaryCorrect_of_slots {cliImg : Obj.Image} {elf elf' : ElfImage} {Fr : SepProp}
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hbase : cliImg.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness elf' (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hpksm : ∀ W : CliHooks, Cli.MainHops.CliPksmSlotExists cliImg W)
    (hdecPk : ∀ W : CliHooks, Cli.MainHops.CliDecPkSlotExists cliImg W) :
    CliBinaryCorrect elf :=
  cliBinaryCorrect_of_parts_observe himg hbase hcode hpatch hE hH fun W =>
    main_ok_cli_sm W himg (hpksm W) (hdecPk W)

/-! ## Parameterized `(P, A, ext)` SM & PQXDH Tight Domain Compositions -/

/-- Direct SM-domain `mainSpecTight` composition from a concrete `runSpecTight` witness `hrun` at
`cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse`. -/
theorem main_ok_cli_sm_tight_ext_of_hrun {img : Obj.Image} (P : PEParams)
    (A : RustHeap.RustAlloc) (ext : String → Option (State → State))
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (hmainA1 : Cli.MainHops.MainOkA1TightAt img A ext)
    (hrun : subroutine_ok (Cli.MainHops.mProg img (cliExternsWith ext))
      ((Cli.MainHops.mProg img (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
      ((Cli.MainHops.runSpecTight A img uuidTryParse
        (runRel (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse))
        Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage img)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel P.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  let S : RunSem := cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse
  have hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) (runRel S)) :=
    main_ok_cli_ext_of_runTight defaultModelExtras P A ext decPk decPkOk pksmParse hmainA1 hrun
  have hS_enc : S.encrypt = encDef P Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef P Slots.scopeIn := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  clear_value S
  have hcovSm := ratchetScopeCoversSm_scopeIn P.C
  have hagEnc : SmEncryptAgrees S P.C :=
    smEncryptAgrees_encDef S P Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovSm
  have hagDec : SmDecryptSignalAgrees S P.C :=
    smDecryptSignalAgrees_decSigDef S P Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovSm
  refine ⟨runRel S, hmain, fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · exact ⟨runAns S (smSendInputs g m),
      ⟨domainArgv_smSend g m, runBounds_smSend g m hm,
        runFilesOk_smSend_cli (S := S) hS_files g m hg,
        runEncOk_smSend_cli (S := S) hS_encOk g m hg,
        runHsOk_smSend_cli S g m, rfl⟩,
      RunRefine.runAns_smSend S P.C hagEnc g m hg hm,
      commitOk_smSend_encDef (S := S) (W := P) hS_enc g m⟩
  · exact ⟨runAns S (smRecvInputs g c rc),
      ⟨domainArgv_smRecv g c rc, runBounds_smRecv g c rc hc,
        runFilesOk_smRecv_cli (S := S) hS_files g c rc hg,
        Slots.runEncOk_smRecv S g c rc,
        runHsOk_smRecv_cli S g c rc, rfl⟩,
      RunRefine.runAns_smRecv S P.C hagDec g c rc hg hc,
      commitOk_smRecv_decSigDef (S := S) (W := P) hS_dec g c rc⟩

/-- `main_ok_cli_sm_of_runTight` generalized to `(P : PEParams) (A : RustHeap.RustAlloc)` and
`cliExternsWith ext`. -/
theorem main_ok_cli_sm_ext_of_runTight {img : Obj.Image} (P : PEParams)
    (A : RustHeap.RustAlloc) (ext : String → Option (State → State))
    (hmainA1 : Cli.MainHops.MainOkA1TightAt img A ext)
    (hpksm : Cli.MainHops.CliPksmSlotExistsExt img A ext)
    (hdecPk : Cli.MainHops.CliDecPkSlotExistsExt img A ext)
    (hrun : ∀ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
        List (BitVec 8) → SlotAns (List (BitVec 8)))
      (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
      (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOf A img (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse)
        (cliRunNeeds decPkNeed)).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
        (pksmSlotSpec A img
          (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProg img (cliExternsWith ext))
        ((Cli.MainHops.mProg img (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
        ((Cli.MainHops.runSpecTight A img uuidTryParse
          (runRel (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage img)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel P.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨pksmParse, hpksmSlot⟩ := hpksm
  obtain ⟨decPk, decPkOk, decPkNeed, hdecNeed, hdecPkSlot⟩ := hdecPk
  let S : RunSem := cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse
  exact main_ok_cli_sm_tight_ext_of_hrun P A ext decPk decPkOk pksmParse hmainA1
    (hrun decPk decPkOk pksmParse decPkNeed hdecNeed
      (hdecPkSlot S (cliRunNeeds decPkNeed) rfl rfl rfl rfl)
      (hpksmSlot S rfl))

/-- Parameterized SM-domain `mainSpecTight` composition from `RunInstCalleeDepsExt`, matching
`ProcessOomExt.MainOkCliSmTightExt img` definitionally. -/
theorem main_ok_cli_sm_tight_ext_of_deps {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdeps : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      Cli.MainHops.RunInstCalleeDepsExt img defaultModelExtras P A ext)
    (hmainA1 : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext → Cli.MainHops.MainOkA1TightAt img A ext)
    (hpksm : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext → Cli.MainHops.CliPksmSlotExistsExt img A ext)
    (hdecPk : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext → Cli.MainHops.CliDecPkSlotExistsExt img A ext) :
    ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      ∃ Run : Inputs → Cli.RunAnswer → Prop,
        subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
          (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
        (∀ g m, Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
          ∃ a, Run (smSendInputs g m) a ∧
            observe (smSendInputs g m).files a =
              observe (smSendInputs g m).files (smSendModel P.C g m) ∧
            Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
        (∀ g c rc, Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
          ∃ a, Run (smRecvInputs g c rc) a ∧
            observe (smRecvInputs g c rc).files a =
              observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc) ∧
            Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) :=
  fun P A ext hOk =>
    main_ok_cli_sm_ext_of_runTight P A ext (hmainA1 P A ext hOk) (hpksm P A ext hOk)
      (hdecPk P A ext hOk) fun decPk decPkOk pksmParse need hle hd hp =>
        hrun_ext defaultModelExtras P A ext decPk decPkOk pksmParse need himg
          (hdeps P A ext hOk) hle hd hp

/-- PQXDH 5-clause `mainSpecTight` composition at `(P : PEParams) (A : RustHeap.RustAlloc)` and
`cliExternsWith ext`, matching the body of `ProcessOomExt.MainOkCliPqTightExt`. -/
theorem main_ok_cli_pq_tight_ext_of_deps {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustHeap.RustAlloc) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hdeps : Cli.MainHops.RunInstCalleeDepsExt img X P A ext)
    (hmainA1 : Cli.MainHops.MainOkA1TightAt img A ext)
    (hpre : Cli.MainHops.CliPqPrekeyBundleExt img X P A ext) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain P st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs P st b t) a ∧
            observe (pqInitInputs P st b t).files a =
              pqxdhExpectedOutcome P (pqInitInputs P st b t) (pqInitModel X P st b t) ∧
            Cli.CommitOk (pqInitInputs P st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs P st m r) a ∧
            observe (pqSendInputs P st m r).files a =
              pqxdhExpectedOutcome P (pqSendInputs P st m r) (pqSendModel P st m r.toList) ∧
            Cli.CommitOk (pqSendInputs P st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs P st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs P st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome P (pqRecvInputs P st (wireWhisper :: c) rc)
                (pqRecvWhisperModel P st c rc) ∧
            Cli.CommitOk (pqRecvInputs P st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs P st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X P st m rc) ∧
            Cli.CommitOk (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs P st c rc) a ∧
            observe (pqRecvInputs P st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs P st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs P st c rc) (Cli.MainResult.ofAnswer a)) := by
  let S : RunSem := cliRunSemExt X P hpre.decPk hpre.decPkOk hpre.pksmParse
  have hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) (runRel S)) :=
    main_ok_cli_ext_of_runTight X P A ext hpre.decPk hpre.decPkOk hpre.pksmParse hmainA1
      (hrun_ext X P A ext hpre.decPk hpre.decPkOk hpre.pksmParse hpre.decPkNeed himg hdeps
        hpre.needLe
        (hpre.decPkSlot S (cliRunNeeds hpre.decPkNeed) rfl rfl rfl rfl)
        (hpre.pksmSlot S rfl))
  have hS_enc : S.encrypt = encDef P Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef P Slots.scopeIn := rfl
  have hS_init : S.initiate = initDef X P := rfl
  have hS_decPk : S.decryptPrekey = hpre.decPk := rfl
  have hS_pksm : S.pksmParse = hpre.pksmParse := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  have hS_initOk : S.initOk = InitOk₀ P := rfl
  have hS_decPkOk : S.decPkOk = hpre.decPkOk := rfl
  clear_value S
  have hcovPq := ratchetScopeCoversPq_scopeIn P
  have hagInit : PqInitiateAgrees S X P := InitS0.pqInitiateAgrees_initDef_proof S X P hS_init
  have hagEnc : PqEncryptAgrees S P :=
    pqEncryptAgrees_encDef S P Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovPq
  have hagDec : PqDecryptSignalAgrees S P :=
    pqDecryptSignalAgrees_decSigDef S P Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovPq
  have hagPksm : PksmParseAgrees S := hpre.pksmAgrees S hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X P := hpre.decPkAgrees S hS_decPk hS_pksm
  refine ⟨runRel S, hmain, fun st hst => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b t hnone
    exact ⟨runAns S (pqInitInputs P st b t),
      ⟨domainArgv_pqInit P st b t, runBounds_pqInit P st b t,
        runFilesOk_pqInit_cli (S := S) hS_files P st b t hst,
        Slots.runEncOk_pqInit S P st b t,
        runHsOk_pqInit_cli (S := S) (W := P) hS_initOk st b t hst hnone, rfl⟩,
      RunRefine.runAns_pqInit S X P hagInit st b t hst hnone,
      commitOk_pqInit_initDef (S := S) (X := X) (W := P) hS_init st b t⟩
  · intro m r hm
    exact ⟨runAns S (pqSendInputs P st m r),
      ⟨domainArgv_pqSend P st m r, runBounds_pqSend P st m r hm,
        runFilesOk_pqSend_cli (S := S) hS_files P st m r hst,
        Slots.runEncOk_pqSend (S := S) hS_encOk P st m r,
        runHsOk_pqSend_cli S P st m r, rfl⟩,
      RunRefine.runAns_pqSend S P hagEnc st m r hst hm,
      commitOk_pqSend_encDef (S := S) (W := P) hS_enc st m r⟩
  · intro c rc hc
    have hnot3 : (wireWhisper :: c).head? ≠ some wirePrekey := by simp [wireWhisper, wirePrekey]
    exact ⟨runAns S (pqRecvInputs P st (wireWhisper :: c) rc),
      ⟨domainArgv_pqRecv P st (wireWhisper :: c) rc,
        runBounds_pqRecv P st (wireWhisper :: c) rc (Nat.succ_le_of_lt hc),
        runFilesOk_pqRecv_cli (S := S) hS_files P st (wireWhisper :: c) rc hst,
        Slots.runEncOk_pqRecv S P st (wireWhisper :: c) rc,
        runHsOk_pqRecvOther_cli S P st (wireWhisper :: c) rc hnot3, rfl⟩,
      RunRefine.runAns_pqRecvWhisper S P hagDec st c rc hst hc,
      commitOk_pqRecvWhisper_decSigDef (S := S) (W := P) hS_dec st c rc⟩
  · intro m rc hm hmatch
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm)
    exact ⟨runAns S (pqRecvInputs P st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv P st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv P st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli (S := S) hS_files P st (wirePrekey :: m.bytes) rc hst,
        Slots.runEncOk_pqRecv S P st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_of_decPkOk (S := S) P st m rc
          (fun pm hpm => hS_decPkOk ▸ hpre.decPkDomOk st m rc pm hst hm hmatch (hS_pksm ▸ hpm)),
        rfl⟩,
      RunRefine.runAns_pqRecvPrekey S X P hagPksm hagDecPk st m rc hst hm hmatch,
      hpre.decPkCommitOk S st m rc hS_decPk hS_pksm hst hm hmatch⟩
  · intro c rc hc h2 h3
    refine ⟨runAns S (pqRecvInputs P st c rc),
      ⟨domainArgv_pqRecv P st c rc,
        runBounds_pqRecv P st c rc (Nat.le_of_lt hc),
        runFilesOk_pqRecv_cli (S := S) hS_files P st c rc hst,
        Slots.runEncOk_pqRecv S P st c rc,
        runHsOk_pqRecvOther_cli S P st c rc h3, rfl⟩,
      ?_, commitOk_pqRecvBad S P st c rc h2 h3⟩
    rw [runAns_pqRecvBad S P st c rc h2 h3]
    rfl

end CryptoVerification.SignalSession
