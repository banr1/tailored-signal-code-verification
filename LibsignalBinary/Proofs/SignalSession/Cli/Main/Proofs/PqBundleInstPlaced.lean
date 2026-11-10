/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable PQXDH Pre-Key Slot Bundle and `MainOkCliPqPlaced` (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` counterpart of `PqBundleInst.lean` over
`cliGhostExterns gh (cliExternsPlaced mmpl W)`, instantiating `CliPqPrekeyBundlePlaced`,
`MainOkCliPqTightPlaced`, and `MainOkCliSmTightPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

theorem cliDecryptPrekeyNeed_le : cliDecryptPrekeyNeed cliRunBudgets_placed ≤ 4194304 := by
  decide

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
  exact decPkOk₀_pqRecv W Slots.scopeIn encodeInjOn_scopeIn_placed
    (ratchetScopeCoversPq_scopeIn_placed W) st m i rc hst hm hi hmatch

/-- Concrete witness for `CliPksmSlotExistsPlaced mmpl gh W` from `SubsetA4PksmTryFromPlaced`. -/
theorem cliPksmSlotExists_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hW : SubsetA4PksmTryFromPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    CliPksmSlotExistsPlaced mmpl gh W :=
  ⟨Pksm.pksmParse, fun _ hS =>
    cliPksmTryFrom_placed_at_block
      (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      hW (fun b => congrFun hS b)⟩

/-- Concrete witness for `CliDecPkSlotExistsPlaced mmpl gh W` from a `decryptPrekey.OkPlaced`
witness at `decPkDef defaultModelExtras_placed ⟨W.C, W.Q⟩ Slots.scopeIn` and
`DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn`. -/
theorem cliDecPkSlotExists_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hdecPkSlot : ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPkDef defaultModelExtras_placed ⟨W.C, W.Q⟩ Slots.scopeIn →
      S.decPkOk = DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn →
      needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed →
      (slotsOfPlaced E2E.HooksE.A0 S needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    CliDecPkSlotExistsPlaced mmpl gh W :=
  ⟨decPkDef defaultModelExtras_placed ⟨W.C, W.Q⟩ Slots.scopeIn,
    DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn,
    cliDecryptPrekeyNeed cliRunBudgets_placed,
    cliDecryptPrekeyNeed_le,
    hdecPkSlot⟩

abbrev CliPqPrekeyBundleS0Placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Type :=
  CliPqPrekeyBundlePlaced mmpl gh X W

/-- Concrete `S₀` instantiation of `CliPqPrekeyBundlePlaced` from `cliPksmTryFrom_placed_at_block`,
`hdecPkSlot`, `pqDecryptPrekeyAgrees_decPkDef`, `decPkDomOk_cli`, and `decPkCommitOk_cli`. -/
noncomputable def cliPqPrekeyBundlePlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hW : SubsetA4PksmTryFromPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hdecPkSlot : ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Slots.scopeIn →
      S.decPkOk = DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn →
      needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed →
      (slotsOfPlaced E2E.HooksE.A0 S needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    CliPqPrekeyBundlePlaced mmpl gh X W where
  decPk := decPkDef X ⟨W.C, W.Q⟩ Slots.scopeIn
  decPkOk := DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn
  pksmParse := Pksm.pksmParse
  decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed
  needLe := cliDecryptPrekeyNeed_le
  pksmSlot := fun _ hS =>
    cliPksmTryFrom_placed_at_block
      (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      hW (fun b => congrFun hS b)
  decPkSlot := hdecPkSlot
  pksmAgrees := fun _ hS => pksmParseAgrees_S0 hS
  decPkAgrees := fun S hdec hpksm =>
    pqDecryptPrekeyAgrees_decPkDef S X ⟨W.C, W.Q⟩ Slots.scopeIn hdec (pksmTyped_S0 hpksm)
      encodeInjOn_scopeIn_placed (ratchetScopeCoversPq_scopeIn_placed ⟨W.C, W.Q⟩)
  decPkDomOk := fun st m rc pm hst hm hmatch hparse =>
    decPkDomOk_cli ⟨W.C, W.Q⟩ st m rc pm hst hm hmatch hparse
  decPkCommitOk := fun S st m rc hdec hpksm hwf hm hmatch =>
    decPkCommitOk_cli S st m rc hdec hpksm hwf hm hmatch

noncomputable abbrev cliPqPrekeyBundleS0Placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hW : SubsetA4PksmTryFromPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hdecPkSlot : ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Slots.scopeIn →
      S.decPkOk = DecPkOk₀ ⟨W.C, W.Q⟩ Slots.scopeIn →
      needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed →
      (slotsOfPlaced E2E.HooksE.A0 S needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    CliPqPrekeyBundleS0Placed mmpl gh X W :=
  cliPqPrekeyBundlePlaced mmpl gh X W hW hdecPkSlot

/-- Proves `runSpecTightPlaced` at `Run := runRel (cliRunSem_placed ...)` on Block `617`
(`mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`) from `RunArmsPlaced`,
`RunHooksPlaced`, and `RunCalleesPlaced`. -/
theorem hrun_cli_of_callees_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hRunHooks : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (harms : RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
      (cliRunSem_placed X W decPk decPkOk pksmParse) (cliRunNeeds_placed decPkNeed) cliResStack)
    (hc : RunCalleesPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
      cliRunBudgets_placed
      (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)))
    (hpksmSlot : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse)) cliWrOk cliResStack) :=
  RunCompose.run_ok_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    harms hRunHooks hc hpksmSlot
    (runNeed_cli_le_resStack_placed hdecNeed) cliResStack_le_63_placed

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.LibsignalPublicApi.StoreKit

abbrev main_ok_cli_pq_s0_placed_of_runTight := @main_ok_cli_pq_placed_of_runTight

theorem main_ok_cli_pq_inst_placed_of_runTight [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpre : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      Cli.MainHops.CliPqPrekeyBundleS0Placed mmpl gh X W)
    (hrun : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      let b := hpre X W
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 579)
        (Cli.MainHops.runSpecTightPlaced
          (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) E2E.HooksE.A0 uuidTryParse
          (runRel (cliRunSem_placed X W b.decPk b.decPkOk b.pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack)) :
    MainOkCliPqTightPlaced mmpl gh :=
  fun _ X W =>
    main_ok_cli_pq_placed_of_runTight mmpl gh X W
      (hMainHooks W) (hpre X W) (hrun X W)

theorem main_ok_cli_sm_inst_placed_of_runTight [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpksm : ∀ W : CliHooks, Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : ∀ W : CliHooks, Cli.MainHops.CliDecPkSlotExistsPlaced mmpl gh W)
    (hrun : ∀ (W : CliHooks)
        (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
          List (BitVec 8) → SlotAns (List (BitVec 8)))
        (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
        (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOfPlaced E2E.HooksE.A0
        (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (CryptoVerification.blkPl_111).base
        (pksmSlotSpecPlaced E2E.HooksE.A0
          (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 579)
        (Cli.MainHops.runSpecTightPlaced
          (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) E2E.HooksE.A0 uuidTryParse
          (runRel (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack)) :
    MainOkCliSmTightPlaced mmpl gh :=
  fun _ W =>
    main_ok_cli_sm_placed_of_runTight mmpl gh W
      (hMainHooks W) (hpksm W) (hdecPk W) (hrun W)

theorem Cli.main_ok_cli_pq_tight_inst_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks,
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpre : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      Cli.MainHops.CliPqPrekeyBundleS0Placed mmpl gh X W)
    (harms : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      let b := hpre X W
      RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
        (cliRunSem_placed X W b.decPk b.decPkOk b.pksmParse) (cliRunNeeds_placed b.decPkNeed)
        Cli.MainHops.cliResStack)
    (hc : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      let b := hpre X W
      RunCalleesPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
        cliRunBudgets_placed
        (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W b.decPk b.decPkOk b.pksmParse)
          (cliRunNeeds_placed b.decPkNeed))) :
    MainOkCliPqTightPlaced mmpl gh :=
  main_ok_cli_pq_inst_placed_of_runTight mmpl gh hMainHooks hpre fun X W =>
    let b := hpre X W
    Cli.MainHops.hrun_cli_of_callees_placed mmpl gh X W b.decPk b.decPkOk b.pksmParse b.decPkNeed
      b.needLe (hRunHooks W) (harms X W) (hc X W) (b.pksmSlot _ rfl)

theorem Cli.main_ok_cli_sm_tight_inst_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks,
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpksm : ∀ W : CliHooks, Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : ∀ W : CliHooks, Cli.MainHops.CliDecPkSlotExistsPlaced mmpl gh W)
    (harms : ∀ (W : CliHooks)
        (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
          List (BitVec 8) → SlotAns (List (BitVec 8)))
        (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
        (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
        (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed) Cli.MainHops.cliResStack)
    (hc : ∀ (W : CliHooks)
        (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
          List (BitVec 8) → SlotAns (List (BitVec 8)))
        (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
        (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      (slotsOfPlaced E2E.HooksE.A0
        (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
        cliRunBudgets_placed
        (slotsOfPlaced E2E.HooksE.A0
          (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)
          (cliRunNeeds_placed decPkNeed))) :
    MainOkCliSmTightPlaced mmpl gh :=
  main_ok_cli_sm_inst_placed_of_runTight mmpl gh hMainHooks hpksm hdecPk
    (fun W decPk decPkOk pksmParse decPkNeed hneed hdec hpksmSlot =>
      Cli.MainHops.hrun_cli_of_callees_placed mmpl gh defaultModelExtras_placed W decPk decPkOk
        pksmParse decPkNeed hneed (hRunHooks W) (harms W decPk decPkOk pksmParse decPkNeed)
        (hc W decPk decPkOk pksmParse decPkNeed hdec) hpksmSlot)

end CryptoVerification.SignalSession
