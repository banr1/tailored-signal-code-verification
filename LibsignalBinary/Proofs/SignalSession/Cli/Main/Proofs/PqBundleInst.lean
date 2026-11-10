/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryProof
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkA1 -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Slot -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj -- shake: keep
public import ProofLib.SepLogic.WPp -- shake: keep

/-!
# PQXDH Pre-Key Slot Bundle and `MainOkCliPq` / `MainOkCliSm` Instantiation

Packages concrete `PreKeySignalMessage::try_from` (`Pksm.pksmParse`) and `decrypt_prekey`
(`decPkDef`, `DecPkOk₀`) proofs into `CliPqPrekeyBundleS0`, discharging `MainOkCliSm`, `MainOkCliPq`,
and their tightened (`mainSpecTight`) and `CliExternsOk`-parameterized counterparts.
-/

@[expose] public section

set_option autoImplicit false

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

/-- `cliDecryptPrekeyNeed cliRunBudgets` (`1,083,600`) fits within `runNeed_cli_le_resStack`'s
`4,194,304` (`4 MiB`) callee cap. -/
theorem cliDecryptPrekeyNeed_le : cliDecryptPrekeyNeed cliRunBudgets ≤ 4194304 := by
  decide

/-- Concrete witness for `CliPksmSlotExists img W` via `Pksm.pksmParse` and `cliPksmTryFrom_ok`. -/
theorem cliPksmSlotExists_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    CliPksmSlotExists img W :=
  ⟨Pksm.pksmParse, fun _ hS =>
    cliPksmTryFrom_ok himg (RunHooks.cli W img).alloc (fun b => congrFun hS b)⟩

/-- Concrete witness for `CliDecPkSlotExists img W` via `decPkDef`, `DecPkOk₀`, and
`cliDecryptPrekey_slotOk`. -/
theorem cliDecPkSlotExists_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    CliDecPkSlotExists img W :=
  ⟨decPkDef defaultModelExtras ⟨W.C, W.Q⟩ Slots.scopeIn,
    DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn,
    cliDecryptPrekeyNeed cliRunBudgets,
    cliDecryptPrekeyNeed_le,
    fun S needs hfiles hdec hdecOk hneed =>
      cliDecryptPrekey_slotOk W defaultModelExtras cliRunBudgets S Slots.scopeIn needs himg
        (RunHooks.cli W img)
        (cliReadFile_ok W img cliRunBudgets.readFile)
        (Slots.sessDeserialize_scopeKit_cli W himg)
        Slots.encodeInjOn_deserializeScopeP_Q
        (fun _ h => h)
        hdec
        (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
        hneed⟩

/-- `DecPkOk₀` holds on `pqRecvInputs` whenever `Pksm.pksmParse m.bytes = some pm`. -/
theorem decPkDomOk_cli (W : PEParams) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (pm : PreKeySignalMessage)
    (hst : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m)
    (hparse : Pksm.pksmParse m.bytes = some pm) :
    DecPkOk₀ W Slots.scopeIn
      (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (addrValE st.party.other) (addrValE st.party) pm := by
  obtain ⟨i, hi, rfl⟩ := pksmParse_bytes_typed hm hparse
  exact decPkOk₀_pqRecv W Slots.scopeIn encodeInjOn_scopeIn
    (ratchetScopeCoversPq_scopeIn W) st m i rc hst hm hi hmatch

/-- Complete PQXDH pre-key slot + model-agreement bundle at `(X, W)` (`CliPqPrekeyBundle` with the
`S.pksmParse = pksmParse` hypothesis included on `decPkAgrees`, matching `decPkCommitOk`). -/
structure CliPqPrekeyBundleS0 (img : Obj.Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Type where
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
  decPkAgrees : ∀ S : RunSem, S.decryptPrekey = decPk → S.pksmParse = pksmParse →
    PqDecryptPrekeyAgrees S X ⟨W.C, W.Q⟩
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

/-- Concrete `S₀` instantiation of `CliPqPrekeyBundleS0` from `cliPksmTryFrom_ok`,
`pksmCanonical_S0`, `cliDecryptPrekey_slotOk`, `pqDecryptPrekeyAgrees_decPkDef`,
`decPkDomOk_cli`, and `decPkCommitOk_cli`. -/
noncomputable def cliPqPrekeyBundle {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    CliPqPrekeyBundleS0 img X W where
  decPk := decPkDef X ⟨W.C, W.Q⟩ Slots.scopeIn
  decPkOk := DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn
  pksmParse := Pksm.pksmParse
  decPkNeed := cliDecryptPrekeyNeed cliRunBudgets
  needLe := cliDecryptPrekeyNeed_le
  pksmSlot := fun _ hS =>
    cliPksmTryFrom_ok himg (RunHooks.cli W img).alloc (fun b => congrFun hS b)
  decPkSlot := fun S needs hfiles hdec hdecOk hneed =>
    cliDecryptPrekey_slotOk W X cliRunBudgets S Slots.scopeIn needs himg
      (RunHooks.cli W img)
      (cliReadFile_ok W img cliRunBudgets.readFile)
      (Slots.sessDeserialize_scopeKit_cli W himg)
      Slots.encodeInjOn_deserializeScopeP_Q
      (fun _ h => h)
      hdec
      (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
      hneed
  pksmAgrees := fun _ hS => pksmParseAgrees_S0 hS
  decPkAgrees := fun S hdec hpksm =>
    pqDecryptPrekeyAgrees_decPkDef S X ⟨W.C, W.Q⟩ Slots.scopeIn hdec (pksmTyped_S0 hpksm)
      encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn ⟨W.C, W.Q⟩)
  decPkDomOk := fun st m rc pm hst hm hmatch hparse =>
    decPkDomOk_cli ⟨W.C, W.Q⟩ st m rc pm hst hm hmatch hparse
  decPkCommitOk := fun S st m rc hdec hpksm hwf hm hmatch =>
    decPkCommitOk_cli S st m rc hdec hpksm hwf hm hmatch

noncomputable abbrev cliPqPrekeyBundleS0 {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    CliPqPrekeyBundleS0 img X W :=
  cliPqPrekeyBundle X W himg

/-! ## Parameterized `(P, A, ext)` Pre-Key Slot & `S₀` Bundle Generalizations -/

/-- `cliDecryptPrekeyNeed extRunBudgets` fits within `4,194,304` (`4 MiB`). -/
theorem cliDecryptPrekeyNeed_ext_le : cliDecryptPrekeyNeed extRunBudgets ≤ 4194304 := by
  decide

/-- Concrete witness for `CliPksmSlotExistsExt img A ext` from `CliExternsOk P A ext` via
`Pksm.pksmParse`, `(RunHooksExt.of_externsOk hOk img).alloc`, and `cliPksmTryFrom_ok`. -/
theorem cliPksmSlotExists_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    CliPksmSlotExistsExt img A ext :=
  ⟨Pksm.pksmParse, fun _ hS =>
    cliPksmTryFrom_ok himg (RunHooksExt.of_externsOk hOk img).alloc (fun b => congrFun hS b)⟩

/-- Unconditional witness for `CliDecPkSlotExistsExt img A ext` (for SM-domain instantiation, where
`smSendInputs` uses `send` and `smRecvInputs` uses `2 ‖ c` so `decPkOk` is never invoked): choosing
`decPkOk := fun _ _ _ _ => False` makes `decPkSlotSpec`'s precondition contradictory. -/
theorem cliDecPkSlotExists_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    CliDecPkSlotExistsExt img A ext := by
  refine ⟨fun _ _ _ _ _ => none, fun _ _ _ _ => False, 0, Nat.zero_le _, ?_⟩
  intro S needs _ _ hdecOk _ stk _ _
  apply subroutine_ok_of_sepWPp_init
  intro g R s0 _ _ hpre _
  dsimp only [slotsOf, mkSlot] at hpre
  simp only [decPkSlotSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj, hdecOk,
    and_false, false_and] at hpre

/-- Concrete witness for `CliDecPkSlotExistsExt img A ext` at `decPkDef` and `DecPkOk₀` from
`CliExternsOk P A ext`, `sessDeserializeSpec`, and `CliDpPollOkStateExtStmt`. -/
theorem cliDecPkSlotExists_ext_of_poll {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hpoll : CliDpPollOkStateExtStmt) :
    CliDecPkSlotExistsExt img A ext :=
  ⟨decPkDef defaultModelExtras P Slots.scopeIn,
    DecPkOk₀ P Slots.scopeIn,
    cliDecryptPrekeyNeed cliRunBudgets,
    cliDecryptPrekeyNeed_le,
    fun S needs hfiles hdec hdecOk hneed =>
      cliDecryptPrekey_slotOk_of_poll_ext P A ext defaultModelExtras cliRunBudgets S Slots.scopeIn
        needs hOk himg (RunHooksExt.of_externsOk hOk img)
        (cliReadFile_ok_cliExternsWith hOk img (stk := cliRunBudgets.readFile))
        hDeser
        Slots.encodeInjOn_deserializeScopeP_Q
        (fun _ h => h)
        hdec
        (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
        hpoll
        hneed⟩

abbrev CliPqPrekeyBundleS0Ext (img : Obj.Image) (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (A : RustAlloc) (ext : String → Option (State → State)) : Type :=
  CliPqPrekeyBundleExt img X P A ext

/-- Parameterized `(P, A, ext)` `S₀` instantiation of `CliPqPrekeyBundleS0Ext` from
`CliExternsOk P A ext`, `cliPksmTryFrom_ok`, `cliDecryptPrekey_slotOk_of_poll_ext`,
`pqDecryptPrekeyAgrees_decPkDef`, `decPkDomOk_cli`, and `decPkCommitOk_cli`. -/
noncomputable def cliPqPrekeyBundle_ext {img : Obj.Image} (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hpoll : CliDpPollOkStateExtStmt) :
    CliPqPrekeyBundleS0Ext img X P A ext where
  decPk := decPkDef X P Slots.scopeIn
  decPkOk := DecPkOk₀ P Slots.scopeIn
  pksmParse := Pksm.pksmParse
  decPkNeed := cliDecryptPrekeyNeed cliRunBudgets
  needLe := cliDecryptPrekeyNeed_le
  pksmSlot := fun _ hS =>
    cliPksmTryFrom_ok himg (RunHooksExt.of_externsOk hOk img).alloc (fun b => congrFun hS b)
  decPkSlot := fun S needs hfiles hdec hdecOk hneed =>
    cliDecryptPrekey_slotOk_of_poll_ext P A ext X cliRunBudgets S Slots.scopeIn needs
      hOk himg (RunHooksExt.of_externsOk hOk img)
      (cliReadFile_ok_cliExternsWith hOk img (stk := cliRunBudgets.readFile))
      hDeser
      Slots.encodeInjOn_deserializeScopeP_Q
      (fun _ h => h)
      hdec
      (fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩)
      hpoll
      hneed
  pksmAgrees := fun _ hS => pksmParseAgrees_S0 hS
  decPkAgrees := fun S hdec hpksm =>
    pqDecryptPrekeyAgrees_decPkDef S X P Slots.scopeIn hdec (pksmTyped_S0 hpksm)
      encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn P)
  decPkDomOk := fun st m rc pm hst hm hmatch hparse =>
    decPkDomOk_cli P st m rc pm hst hm hmatch hparse
  decPkCommitOk := fun S st m rc hdec hpksm hwf hm hmatch =>
    decPkCommitOk_cli S st m rc hdec hpksm hwf hm hmatch

noncomputable abbrev cliPqPrekeyBundleS0_ext {img : Obj.Image} (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit A img))
    (hpoll : CliDpPollOkStateExtStmt) :
    CliPqPrekeyBundleS0Ext img X P A ext :=
  cliPqPrekeyBundle_ext X hOk himg hDeser hpoll

/-- Discharges `MainOkA1TightAt img A ext` from `CliExternsOk P A ext` and
`Obj.Loads libsignalSessionImage img` via `MainHops.main_ok_ext_tight`. -/
theorem mainOkA1TightAt_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkA1TightAt cliImg A ext :=
  fun hrun hdom => main_ok_ext_tight hOk himg hrun hdom

/-- `main_ok_cli_of_runTight` generalized to `(P, A, ext)` under `CliExternsOk P A ext`,
discharging `MainOkA1TightAt` via `main_ok_ext_tight`. -/
theorem main_ok_cli_of_runTight_ext (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hrun : subroutine_ok (mProg cliImg (cliExternsWith ext))
      ((mProg cliImg (cliExternsWith ext)).fnAddr runName)
      ((runSpecTight A cliImg uuidTryParse
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse)) cliWrOk cliResStack).inImage cliImg)) :
    subroutine_ok (cliProg cliImg (cliExternsWith ext)) (entryOf cliImg mainName)
      (mainSpecTight A cliImg cliMainStk (cliStatics cliImg)
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse))) :=
  main_ok_cli_ext_of_runTight X P A ext decPk decPkOk pksmParse
    (mainOkA1TightAt_ext hOk himg) hrun

/-- Non-tight (`mainSpec`) counterpart of `main_ok_cli_of_runTight_ext` via `MainHops.main_ok_ext`. -/
theorem main_ok_cli_of_run_ext (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hrun : subroutine_ok (mProg cliImg (cliExternsWith ext))
      ((mProg cliImg (cliExternsWith ext)).fnAddr runName)
      ((runSpec A cliImg uuidTryParse
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse)) cliWrOk cliResStack).inImage cliImg)) :
    subroutine_ok (cliProg cliImg (cliExternsWith ext)) (entryOf cliImg mainName)
      (mainSpec A cliImg cliMainStk (cliStatics cliImg)
        (runRel (cliRunSemExt X P decPk decPkOk pksmParse))) :=
  main_ok_ext hOk himg hrun (fun _ _ hr => RunCompose.runRel_dom hr)

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

/-- `main`-level 5-clause PQXDH functional specification at `HooksE.A0` across all `(X, W)`
(the PQXDH counterpart to `MainOkCliSm img` in `CliBinaryProof.lean`). -/
def MainOkCliPq (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpec E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a))

/-- `main_ok_cli_pq` over `CliPqPrekeyBundleS0`: instantiates `MainHops.main_ok_cli` at
`Run := runRel S₀` and discharges all 5 clauses of `CliSpecPqxdh` together with `CommitOk`. -/
theorem main_ok_cli_pq_s0 (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpre : Cli.MainHops.CliPqPrekeyBundleS0 cliImg X W) :
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
  have hagDecPk : PqDecryptPrekeyAgrees S X WP := hpre.decPkAgrees S hS_decPk hS_pksm
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

/-- Discharges `MainOkCliPq cliImg` from `Obj.Loads libsignalSessionImage cliImg` via
`cliPqPrekeyBundleS0`. -/
theorem main_ok_cli_pq_inst
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkCliPq cliImg :=
  fun X W => main_ok_cli_pq_s0 X W himg (cliPqPrekeyBundleS0 X W himg)

/-- Discharges `MainOkCliSm cliImg` from `Obj.Loads libsignalSessionImage cliImg` via
`cliPksmSlotExists_cli` and `cliDecPkSlotExists_cli`. -/
theorem main_ok_cli_sm_inst
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkCliSm cliImg :=
  fun W => main_ok_cli_sm W himg (cliPksmSlotExists_cli W himg) (cliDecPkSlotExists_cli W himg)

/-! ## Tightened PQXDH & SM `main` Specifications (`Cli.mainSpecTight`) -/

/-- Tightened `main`-level 5-clause PQXDH functional specification at `HooksE.A0` across all
`(X, W)`, replacing `Cli.mainSpec` in `MainOkCliPq` with `Cli.mainSpecTight`. -/
def Cli.MainOkCliPqTight (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a))

/-- `Cli.MainOkCliPqTight` weakens directly to `MainOkCliPq` via `Cli.subroutine_ok_mainSpec_of_tight`. -/
theorem Cli.MainOkCliPqTight.toMainOkCliPq {img : Obj.Image} (h : Cli.MainOkCliPqTight img) :
    MainOkCliPq img := by
  intro X W
  obtain ⟨Run, hmain, hclauses⟩ := h X W
  exact ⟨Run, Cli.subroutine_ok_mainSpec_of_tight hmain, hclauses⟩

/-- Tightened SM-domain `main` specification (`MainOkCliSm` with `Cli.mainSpecTight`). -/
def Cli.MainOkCliSmTight (img : Obj.Image) : Prop :=
  ∀ W : CliHooks,
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

/-- `Cli.MainOkCliSmTight` weakens directly to `MainOkCliSm` via `Cli.subroutine_ok_mainSpec_of_tight`. -/
theorem Cli.MainOkCliSmTight.toMainOkCliSm {img : Obj.Image} (h : Cli.MainOkCliSmTight img) :
    MainOkCliSm img := by
  intro W
  obtain ⟨Run, hmain, hsend, hrecv⟩ := h W
  exact ⟨Run, Cli.subroutine_ok_mainSpec_of_tight hmain, hsend, hrecv⟩

/-- Tightened `main_ok_cli_pq_s0` over `CliPqPrekeyBundleS0` and a `runSpecTight` subroutine
witness `hrun`. -/
theorem main_ok_cli_pq_s0_of_runTight (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpre : Cli.MainHops.CliPqPrekeyBundleS0 cliImg X W)
    (hrun : subroutine_ok (Cli.MainHops.mProg cliImg (cliExterns W))
      ((Cli.MainHops.mProg cliImg (cliExterns W)).fnAddr Cli.MainHops.runName)
      ((Cli.MainHops.runSpecTight E2E.HooksE.A0 cliImg uuidTryParse
        (runRel (cliRunSem X W hpre.decPk hpre.decPkOk hpre.pksmParse))
        Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpecTight E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
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
      (Cli.mainSpecTight E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)
        (runRel S)) :=
    main_ok_cli_of_runTight X W hpre.decPk hpre.decPkOk hpre.pksmParse himg hrun
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
  have hagDecPk : PqDecryptPrekeyAgrees S X WP := hpre.decPkAgrees S hS_decPk hS_pksm
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

/-- Discharges `MainOkCliPqTight img` from `Obj.Loads libsignalSessionImage img` and a
`runSpecTight` witness at `cliPqPrekeyBundleS0 X W himg`. -/
theorem main_ok_cli_pq_inst_of_runTight
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hrun : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      let hpre := cliPqPrekeyBundleS0 X W himg
      subroutine_ok (Cli.MainHops.mProg cliImg (cliExterns W))
        ((Cli.MainHops.mProg cliImg (cliExterns W)).fnAddr Cli.MainHops.runName)
        ((Cli.MainHops.runSpecTight E2E.HooksE.A0 cliImg uuidTryParse
          (runRel (cliRunSem X W hpre.decPk hpre.decPkOk hpre.pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    Cli.MainOkCliPqTight cliImg :=
  fun X W => main_ok_cli_pq_s0_of_runTight X W himg (cliPqPrekeyBundleS0 X W himg) (hrun X W)

/-- Discharges `MainOkCliSmTight cliImg` from `Obj.Loads libsignalSessionImage cliImg` and a
`runSpecTight` witness family. -/
theorem main_ok_cli_sm_inst_of_runTight
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hrun : ∀ (W : CliHooks)
        (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
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
    Cli.MainOkCliSmTight cliImg :=
  fun W => main_ok_cli_sm_of_runTight W himg (cliPksmSlotExists_cli W himg)
    (cliDecPkSlotExists_cli W himg) (hrun W)

/-- Discharges `Cli.MainOkCliPqTight cliImg` unconditionally from
`Obj.Loads libsignalSessionImage cliImg`. -/
theorem Cli.main_ok_cli_pq_tight_inst
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    Cli.MainOkCliPqTight cliImg :=
  main_ok_cli_pq_inst_of_runTight himg fun X W =>
    let hpre := cliPqPrekeyBundleS0 X W himg
    Cli.MainHops.hrun_cli X W hpre.decPk hpre.decPkOk hpre.pksmParse hpre.decPkNeed himg
      hpre.needLe
      (hpre.decPkSlot _ _ rfl rfl rfl rfl)
      (hpre.pksmSlot _ rfl)

/-- Discharges `Cli.MainOkCliSmTight cliImg` unconditionally from
`Obj.Loads libsignalSessionImage cliImg`. -/
theorem Cli.main_ok_cli_sm_tight_inst
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    Cli.MainOkCliSmTight cliImg :=
  main_ok_cli_sm_inst_of_runTight himg
    (fun W decPk decPkOk pksmParse decPkNeed hneed hdec hpksm =>
      Cli.MainHops.hrun_cli defaultModelExtras W decPk decPkOk pksmParse decPkNeed
        himg hneed hdec hpksm)

/-! ## Parameterized `(P, A, ext)` PQXDH & SM `main` Generalizations -/

/-- Reducible shorthand for the parameterized `(P, A, ext)` 5-clause PQXDH `mainSpecTight`
contract (definitionally equal to `ProcessOomExt.MainOkCliPqTightExt`). -/
abbrev Cli.PqBundleExt.MainOkCliPqTightExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
    CliExternsOk P A ext →
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
            Cli.CommitOk (pqRecvInputs P st c rc) (Cli.MainResult.ofAnswer a))

/-- Reducible shorthand for the parameterized `(P, A, ext)` SM-domain `mainSpecTight` contract
(definitionally identical to `ProcessOomExt.MainOkCliSmTightExt` and
`ProcessOom.MainOkCliSmTightExt`). -/
abbrev Cli.PqBundleExt.MainOkCliSmTightExt (img : Obj.Image) : Prop :=
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
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

/-- Parameterized `(P, A, ext)` generalization of `main_ok_cli_pq_s0_of_runTight`: discharges
all 5 `CliSpecPqxdh` clauses under `Cli.mainSpecTight` on `Cli.cliProg img (cliExternsWith ext)` from
`CliExternsOk P A ext`, `CliPqPrekeyBundleS0Ext`, and a `runSpecTight` witness `hrun` on
`Cli.MainHops.mProg img (cliExternsWith ext)`. -/
theorem main_ok_cli_pq_s0_of_runTight_ext (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpre : Cli.MainHops.CliPqPrekeyBundleS0Ext cliImg X P A ext)
    (hrun : subroutine_ok (Cli.MainHops.mProg cliImg (cliExternsWith ext))
      ((Cli.MainHops.mProg cliImg (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
      ((Cli.MainHops.runSpecTight A cliImg uuidTryParse
        (runRel (cliRunSemExt X P hpre.decPk hpre.decPkOk hpre.pksmParse))
        Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExternsWith ext)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpecTight A cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
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
  have hmain : subroutine_ok (Cli.cliProg cliImg (cliExternsWith ext)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpecTight A cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) (runRel S)) :=
    Cli.MainHops.main_ok_cli_of_runTight_ext X hpre.decPk hpre.decPkOk hpre.pksmParse hOk himg hrun
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

/-- Non-tight (`Cli.mainSpec`) counterpart of `main_ok_cli_pq_s0_of_runTight_ext`, generalizing
`main_ok_cli_pq_s0` to `(P, A, ext)` via `Cli.subroutine_ok_mainSpec_of_tight` (`runSpecTight = runSpec`). -/
theorem main_ok_cli_pq_s0_ext (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpre : Cli.MainHops.CliPqPrekeyBundleS0Ext cliImg X P A ext)
    (hrun : subroutine_ok (Cli.MainHops.mProg cliImg (cliExternsWith ext))
      ((Cli.MainHops.mProg cliImg (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
      ((Cli.MainHops.runSpec A cliImg uuidTryParse
        (runRel (cliRunSemExt X P hpre.decPk hpre.decPkOk hpre.pksmParse))
        Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExternsWith ext)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpec A cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
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
  obtain ⟨Run, hmain, hclauses⟩ := main_ok_cli_pq_s0_of_runTight_ext X hOk himg hpre hrun
  exact ⟨Run, Cli.subroutine_ok_mainSpec_of_tight hmain, hclauses⟩

/-- Parameterized `(P, A, ext)` generalization of `main_ok_cli_pq_inst_of_runTight`: discharges
`MainOkCliPqTightExt cliImg` from `Obj.Loads libsignalSessionImage cliImg`, `sessDeserializeSpec`,
`CliDpPollOkStateExtStmt`, and a `runSpecTight` witness at `cliPqPrekeyBundleS0_ext`. -/
theorem main_ok_cli_pq_inst_of_runTight_ext
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hDeser : ∀ {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)},
      CliExternsOk P A ext →
      subroutine_ok (tripleRatchetProgAtExt cliImg.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt cliImg.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
        (sessDeserializeSpec Slots.scopeKit A cliImg))
    (hpoll : CliDpPollOkStateExtStmt)
    (hrun : ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
        (ext : String → Option (State → State)) (hOk : CliExternsOk P A ext),
      let hpre := Cli.MainHops.cliPqPrekeyBundleS0_ext X hOk himg (hDeser hOk) hpoll
      subroutine_ok (Cli.MainHops.mProg cliImg (cliExternsWith ext))
        ((Cli.MainHops.mProg cliImg (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
        ((Cli.MainHops.runSpecTight A cliImg uuidTryParse
          (runRel (cliRunSemExt X P hpre.decPk hpre.decPkOk hpre.pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    Cli.PqBundleExt.MainOkCliPqTightExt cliImg :=
  fun X P A ext hOk =>
    let hpre := Cli.MainHops.cliPqPrekeyBundleS0_ext X hOk himg (hDeser hOk) hpoll
    main_ok_cli_pq_s0_of_runTight_ext X hOk himg hpre (hrun X P A ext hOk)

/-- Parameterized `(P, A, ext)` generalization of `RunInst.main_ok_cli_sm_of_runTight`: discharges
`MainOkA1TightAt cliImg A ext` unconditionally from `hOk` and `himg` via `main_ok_ext_tight`. -/
theorem main_ok_cli_sm_of_runTight_ext
    {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpksm : CliPksmSlotExistsExt cliImg A ext)
    (hdecPk : CliDecPkSlotExistsExt cliImg A ext)
    (hrun : ∀ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
          List (BitVec 8) → SlotAns (List (BitVec 8)))
        (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
        (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOf A cliImg (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse)
        (cliRunNeeds decPkNeed)).decryptPrekey.Ok cliImg (cliExternsWith ext) wrapDecryptPrekeyName →
      subroutine_ok (tripleRatchetProgAtExt cliImg.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt cliImg.base (cliExternsWith ext)).fnAddr
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
        (pksmSlotSpec A cliImg
          (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProg cliImg (cliExternsWith ext))
        ((Cli.MainHops.mProg cliImg (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
        ((Cli.MainHops.runSpecTight A cliImg uuidTryParse
          (runRel (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg cliImg (cliExternsWith ext)) (entryOf cliImg Cli.mainName)
        (Cli.mainSpecTight A cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run) ∧
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
  main_ok_cli_sm_ext_of_runTight P A ext (Cli.MainHops.mainOkA1TightAt_ext hOk himg)
    hpksm hdecPk hrun

/-- Parameterized `(P, A, ext)` generalization of `main_ok_cli_sm_inst_of_runTight`: discharges
`MainOkCliSmTightExt cliImg` from `Obj.Loads libsignalSessionImage cliImg` and a `runSpecTight` witness
family `hrun` (discharging BOTH `CliPksmSlotExistsExt` and `CliDecPkSlotExistsExt` unconditionally
via `cliPksmSlotExists_ext` and `cliDecPkSlotExists_ext`). -/
theorem main_ok_cli_sm_inst_of_runTight_ext
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hrun : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      ∀ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
          List (BitVec 8) → SlotAns (List (BitVec 8)))
        (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
        (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOf A cliImg (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse)
        (cliRunNeeds decPkNeed)).decryptPrekey.Ok cliImg (cliExternsWith ext) wrapDecryptPrekeyName →
      subroutine_ok (tripleRatchetProgAtExt cliImg.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt cliImg.base (cliExternsWith ext)).fnAddr
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
        (pksmSlotSpec A cliImg
          (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProg cliImg (cliExternsWith ext))
        ((Cli.MainHops.mProg cliImg (cliExternsWith ext)).fnAddr Cli.MainHops.runName)
        ((Cli.MainHops.runSpecTight A cliImg uuidTryParse
          (runRel (cliRunSemExt defaultModelExtras P decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack).inImage cliImg)) :
    Cli.PqBundleExt.MainOkCliSmTightExt cliImg :=
  fun P A ext hOk =>
    main_ok_cli_sm_of_runTight_ext hOk himg
      (Cli.MainHops.cliPksmSlotExists_ext hOk himg)
      Cli.MainHops.cliDecPkSlotExists_ext
      (hrun P A ext hOk)

/-- Discharges `MainOkCliPqTightExt cliImg` from `himg`, `sessDeserializeSpec`,
`CliDpPollOkStateExtStmt`, and `RunInstCalleeDepsExt` via `cliPqPrekeyBundleS0_ext` and
`Cli.MainHops.hrun_ext`. -/
theorem Cli.main_ok_cli_pq_tight_inst_ext
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hDeser : ∀ {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)},
      CliExternsOk P A ext →
      subroutine_ok (tripleRatchetProgAtExt cliImg.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt cliImg.base (cliExternsWith ext)).fnAddr Cli.recordDeserializeName)
        (sessDeserializeSpec Slots.scopeKit A cliImg))
    (hpoll : CliDpPollOkStateExtStmt)
    (hdeps : ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
        (ext : String → Option (State → State)),
      CliExternsOk P A ext → Cli.MainHops.RunInstCalleeDepsExt cliImg X P A ext) :
    Cli.PqBundleExt.MainOkCliPqTightExt cliImg :=
  main_ok_cli_pq_inst_of_runTight_ext himg hDeser hpoll fun X P A ext hOk =>
    let hpre := Cli.MainHops.cliPqPrekeyBundleS0_ext X hOk himg (hDeser hOk) hpoll
    Cli.MainHops.hrun_ext X P A ext hpre.decPk hpre.decPkOk hpre.pksmParse hpre.decPkNeed
      himg (hdeps X P A ext hOk) hpre.needLe
      (hpre.decPkSlot _ _ rfl rfl rfl rfl)
      (hpre.pksmSlot _ rfl)

/-- Discharges `MainOkCliSmTightExt cliImg` from `himg` and `RunInstCalleeDepsExt`. -/
theorem Cli.main_ok_cli_sm_tight_inst_ext
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hdeps : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      Cli.MainHops.RunInstCalleeDepsExt cliImg defaultModelExtras P A ext) :
    Cli.PqBundleExt.MainOkCliSmTightExt cliImg :=
  main_ok_cli_sm_inst_of_runTight_ext himg
    (fun P A ext hOk decPk decPkOk pksmParse decPkNeed hneed hdec hpksm =>
      Cli.MainHops.hrun_ext defaultModelExtras P A ext decPk decPkOk pksmParse decPkNeed
        himg (hdeps P A ext hOk) hneed hdec hpksm)

end CryptoVerification.SignalSession
