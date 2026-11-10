/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Relocatable Non-Matching Pre-Key (`NoMatch`) `main`-Level Instantiation

Relocatable `[LibsignalPlacement]` and `[LibsignalFullPlacement]` counterparts of
`RunInstNoMatch.lean` over `cliGhostExterns gh (cliExternsPlaced mmpl W)`, proving
`MainOkPqAllTightPlaced`, `MainOkPqAllTightFrozenPlaced`, and canonical-path `ObservedExceptNormPlaced`
corollaries.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Concrete D2(c)-extended `RunSem` at `Slots.scopeIn`, using `decPkDefD2c` and `DecPkOkD2c`. -/
noncomputable def cliRunSemD2c_placed (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSem_placed X W
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse

/-- `main` satisfies `mainSpecTightPlaced` at `Run := runRel (cliRunSemD2c_placed X W)` from
`CliA0MainHooks`, `CliPubCalleesPlaced`, `CliSlotCalleesPlaced`, `DecPkD2cSlotOkPlaced`, and
`PksmSlotOkPlaced`. -/
theorem main_ok_cli_d2c_tight_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : CliA0MainHooks mmpl gh W)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hslot : DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : PksmSlotOkPlaced mmpl gh W) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 cliMainStk cliStaticsPlaced (runRel (cliRunSemD2c_placed X W))) :=
  main_ok_cli_placed_of_runTight mmpl gh X W hMainHooks
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse
    (hrun_cli_d2c_tight_placed mmpl gh X W hpub hslots hslot hpksm)

/-- `main` satisfies `mainSpecPlaced` at `Run := runRel (cliRunSemD2c_placed X W)` from
`CliA0MainHooks`, `CliPubCalleesPlaced`, `CliSlotCalleesPlaced`, `DecPkD2cSlotOkPlaced`, and
`PksmSlotOkPlaced`. -/
theorem main_ok_cli_d2c_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : CliA0MainHooks mmpl gh W)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hslot : DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : PksmSlotOkPlaced mmpl gh W) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 cliMainStk cliStaticsPlaced (runRel (cliRunSemD2c_placed X W))) :=
  subroutine_ok_mainSpecPlaced_of_tight
    (main_ok_cli_d2c_tight_placed mmpl gh X W hMainHooks hpub hslots hslot hpksm)

/-- `signal_session::run` satisfies `runSpecTightPlaced (LibsignalFrozen lsmpl)` at
`cliRunSem_placed` with `decPkDefD2c` and `DecPkOkD2c` under `[LibsignalFullPlacement]`. -/
theorem hrun_cli_d2c_tight_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hpub : CliPubCalleesFrozenPlaced mmpl gh W)
    (hslots : CliSlotCalleesFullPlaced mmpl gh X W)
    (hslot : DecPkD2cSlotOkFrozenPlaced mmpl gh W)
    (hpksm : PksmSlotOkPlaced mmpl gh W) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn) Pksm.pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_full_placed mmpl gh X W
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse
    (cliDecryptPrekeyNeed cliRunBudgets_placed)
    cliDecryptPrekeyNeed_le
    hpub
    hslots
    (hslot X _ (cliRunNeeds_placed (cliDecryptPrekeyNeed cliRunBudgets_placed)) rfl rfl rfl rfl)
    (hpksm _ rfl)

/-- `main` satisfies `mainSpecTightPlaced (LibsignalFrozen lsmpl)` at
`Run := runRel (cliRunSemD2c_placed X W)` under `[LibsignalFullPlacement]`. -/
theorem main_ok_cli_d2c_tight_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : CliA0MainHooks mmpl gh W)
    (hpub : CliPubCalleesFrozenPlaced mmpl gh W)
    (hslots : CliSlotCalleesFullPlaced mmpl gh X W)
    (hslot : DecPkD2cSlotOkFrozenPlaced mmpl gh W)
    (hpksm : PksmSlotOkPlaced mmpl gh W) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlaced (LibsignalFrozen lsmpl)
        E2E.HooksE.A0 cliMainStk cliStaticsPlaced (runRel (cliRunSemD2c_placed X W))) :=
  main_ok_cli_placed_of_runTight mmpl gh X W hMainHooks
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse
    (hrun_cli_d2c_tight_full_placed mmpl gh X W hpub hslots hslot hpksm)

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## 1. Tightened 6-Clause & `ObservedExceptNormPlaced` `main`-Level Specifications -/

/-- D2(c) `MainOkOverPlaced` specification on
`Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
def MainOkOverPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

/-- Tightened D2(c) `MainOkOverTightPlaced` specification on
`Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
def MainOkOverTightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

theorem MainOkOverTightPlaced.toMainOkOverPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkOverTightPlaced mmpl gh) : MainOkOverPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hclause⟩ := h hDropNz X W
  exact ⟨Run, Cli.subroutine_ok_mainSpecPlaced_of_tight hmain, hclause⟩

/-- Clause 6 (`NoMatch`) of `MainOkPqAllTightPlaced` / `MainOkPqAllPlaced`: on a
`PqxdhPartyInSpecDomain` state `st` whose current session `st.session = some (x₀, g₀)` does not
match `m` (`¬ PqSessionMatches x₀ g₀ m`), `Run` agrees with
`pqRecvPrekeyModel X WP { st with session := none } m rc` with exact 2-session outcome
`d2cObserve_placed`, canonical-path `ObservedExceptNormPlaced`, and `Cli.CommitOk`. -/
def MainOkNoMatchClausePlaced (WP : PEParams) (X : UnreachedPqxdhPrimitives)
    (Run : Inputs → Cli.RunAnswer → Prop) (st : PqParty) : Prop :=
  ∀ (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8))) (m : PreKeyMessageFields) (rc : BitVec 256),
    st.session = some (x₀, g₀) →
    m.inner.length + 2048 < 2 ^ 32 →
    ¬ PqSessionMatches x₀ g₀ m →
    ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
      observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
        d2cObserve_placed WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) st.party.other x₀ g₀
          (pqRecvPrekeyModel X WP { st with session := none } m rc) ∧
      ObservedExceptNormPlaced WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (sessionFile (partyAddress st.party.other))
        (pqRecvPrekeyModel X WP { st with session := none } m rc)
        (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
      Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (Cli.MainResult.ofAnswer a)

/-- Tightened 6-clause PQXDH + `NoMatch` `main`-level specification extending
`MainOkCliPqTightPlaced` with `MainOkNoMatchClausePlaced` on the same `Run` witness. -/
def MainOkPqAllTightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) ∧
        MainOkNoMatchClausePlaced WP X Run st

/-- Legacy `Cli.mainSpecPlaced` counterpart of `MainOkPqAllTightPlaced`. -/
def MainOkPqAllPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) ∧
        MainOkNoMatchClausePlaced WP X Run st

/-- Standalone tightened D2(c) `NoMatch` `main`-level specification (`MainOkNoMatchTightPlaced`). -/
def MainOkNoMatchTightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st → MainOkNoMatchClausePlaced WP X Run st

/-- Standalone D2(c) `NoMatch` `main`-level specification (`MainOkNoMatchPlaced`). -/
def MainOkNoMatchPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st → MainOkNoMatchClausePlaced WP X Run st

/-- Canonical-path (`ObservedExceptNormPlaced`) counterpart to `MainOkOverTightPlaced`. -/
abbrev MainOkOverNormTightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  MainOkOverTightPlaced mmpl gh

/-- Canonical-path (`ObservedExceptNormPlaced`) counterpart to `MainOkOverPlaced`. -/
abbrev MainOkOverNormPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  MainOkOverPlaced mmpl gh

theorem MainOkPqAllTightPlaced.toMainOkPqAllPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightPlaced mmpl gh) : MainOkPqAllPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, Cli.subroutine_ok_mainSpecPlaced_of_tight hmain, hcl⟩

theorem MainOkPqAllTightPlaced.toMainOkCliPqTightPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightPlaced mmpl gh) : MainOkCliPqTightPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, hmain, fun st hst =>
    let ⟨c1, c2, c3, c4, c5, _⟩ := hcl st hst
    ⟨c1, c2, c3, c4, c5⟩⟩

theorem MainOkPqAllTightPlaced.toMainOkNoMatchTightPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightPlaced mmpl gh) : MainOkNoMatchTightPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, hmain, fun st hst => (hcl st hst).2.2.2.2.2⟩

theorem MainOkPqAllTightPlaced.toMainOkOverNormTightPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightPlaced mmpl gh) : MainOkOverNormTightPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  refine ⟨Run, hmain, fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem MainOkPqAllPlaced.toMainOkCliPqPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllPlaced mmpl gh) : MainOkCliPqPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, hmain, fun st hst =>
    let ⟨c1, c2, c3, c4, c5, _⟩ := hcl st hst
    ⟨c1, c2, c3, c4, c5⟩⟩

theorem MainOkPqAllPlaced.toMainOkNoMatchPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllPlaced mmpl gh) : MainOkNoMatchPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, hmain, fun st hst => (hcl st hst).2.2.2.2.2⟩

theorem MainOkPqAllPlaced.toMainOkOverNormPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllPlaced mmpl gh) : MainOkOverNormPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  refine ⟨Run, hmain, fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem MainOkOverNormTightPlaced.toMainOkOverNormPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkOverNormTightPlaced mmpl gh) : MainOkOverNormPlaced mmpl gh :=
  MainOkOverTightPlaced.toMainOkOverPlaced h

/-! ## 2. Proof of `MainOkPqAllTightPlaced` & `MainOkOverNormTightPlaced` from `DecPkD2cSlotOkPlaced` -/

private theorem main_ok_cli_pq_all_tight_of_runSem_placed [LibsignalPlacement]
    {CodeOk : Memory → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (S : RunSem)
    (hmain : subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 617)
      (Cli.mainSpecTightPlaced CodeOk
        E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced (runRel S)))
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ Slots.scopeIn)
    (hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn)
    (hS_init : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hS_decPk : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (hS_pksm : S.pksmParse = Pksm.pksmParse)
    (hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True))
    (hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn)
    (hS_initOk : S.initOk = InitOk₀ ⟨W.C, W.Q⟩)
    (hS_decPkOk : S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced CodeOk
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) ∧
        MainOkNoMatchClausePlaced WP X Run st := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hcovPq := ratchetScopeCoversPq_scopeIn_placed WP
  have hagInit : PqInitiateAgrees S X WP := InitS0.pqInitiateAgrees_initDef_proof S X WP hS_init
  have hagEnc : PqEncryptAgrees S WP :=
    pqEncryptAgrees_encDef_placed S WP Slots.scopeIn hS_enc encodeInjOn_scopeIn_placed hcovPq
  have hagDec : PqDecryptSignalAgrees S WP :=
    pqDecryptSignalAgrees_decSigDef_placed S WP Slots.scopeIn hS_dec encodeInjOn_scopeIn_placed hcovPq
  have hagPksm : PksmParseAgrees S := pksmParseAgrees_S0 hS_pksm
  have hpksmT : PksmTyped S := pksmTyped_S0 hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X WP :=
    pqDecryptPrekeyAgrees_decPkDefD2c_placed S X WP Slots.scopeIn hS_decPk hpksmT encodeInjOn_scopeIn_placed hcovPq
  refine ⟨runRel S, hmain, fun st hst => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b t hnone
    exact ⟨runAns S (pqInitInputs WP st b t),
      ⟨domainArgv_pqInit WP st b t, runBounds_pqInit WP st b t,
        runFilesOk_pqInit_cli_placed (S := S) hS_files WP st b t hst,
        Slots.runEncOk_pqInit S WP st b t,
        runHsOk_pqInit_cli_placed (S := S) (W := WP) hS_initOk st b t hst hnone, rfl⟩,
      RunRefine.runAns_pqInit S X WP hagInit st b t hst hnone,
      commitOk_pqInit_initDef_placed (S := S) (X := X) (W := WP) hS_init st b t⟩
  · intro m r hm
    exact ⟨runAns S (pqSendInputs WP st m r),
      ⟨domainArgv_pqSend WP st m r, runBounds_pqSend WP st m r hm,
        runFilesOk_pqSend_cli_placed (S := S) hS_files WP st m r hst,
        Slots.runEncOk_pqSend (S := S) hS_encOk WP st m r,
        runHsOk_pqSend_cli_placed S WP st m r, rfl⟩,
      RunRefine.runAns_pqSend S WP hagEnc st m r hst hm,
      commitOk_pqSend_encDef_placed (S := S) (W := WP) hS_enc st m r⟩
  · intro c rc hc
    have hnot3 : (wireWhisper :: c).head? ≠ some wirePrekey := by simp [wireWhisper, wirePrekey]
    exact ⟨runAns S (pqRecvInputs WP st (wireWhisper :: c) rc),
      ⟨domainArgv_pqRecv WP st (wireWhisper :: c) rc,
        runBounds_pqRecv WP st (wireWhisper :: c) rc (Nat.succ_le_of_lt hc),
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wireWhisper :: c) rc hst,
        Slots.runEncOk_pqRecv S WP st (wireWhisper :: c) rc,
        runHsOk_pqRecvOther_cli_placed S WP st (wireWhisper :: c) rc hnot3, rfl⟩,
      RunRefine.runAns_pqRecvWhisper S WP hagDec st c rc hst hc,
      commitOk_pqRecvWhisper_decSigDef_placed (S := S) (W := WP) hS_dec st c rc⟩
  · intro m rc hm hmatch
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32_placed hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
        Slots.runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_d2c_placed hS_decPkOk hS_pksm st m rc hst hm, rfl⟩,
      RunRefine.runAns_pqRecvPrekey S X WP hagPksm hagDecPk st m rc hst hm hmatch,
      commitOk_pqRecvPrekey_decPkDefD2c_placed hS_decPk st m.bytes rc⟩
  · intro c rc hc h2 h3
    refine ⟨runAns S (pqRecvInputs WP st c rc),
      ⟨domainArgv_pqRecv WP st c rc,
        runBounds_pqRecv WP st c rc (Nat.le_of_lt hc),
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st c rc hst,
        Slots.runEncOk_pqRecv S WP st c rc,
        runHsOk_pqRecvOther_cli_placed S WP st c rc h3, rfl⟩,
      ?_, commitOk_pqRecvBad_placed S WP st c rc h2 h3⟩
    rw [runAns_pqRecvBad S WP st c rc h2 h3]
    rfl
  · intro x₀ g₀ m rc hs hm hnot
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32_placed hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
        Slots.runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_d2c_placed hS_decPkOk hS_pksm st m rc hst hm, rfl⟩,
      runAns_pqRecvPrekey_noMatch_exact_placed S X WP Slots.scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn_placed hcovPq st x₀ g₀ m rc hst hs hm hnot,
      runAns_pqRecvPrekey_noMatch_exceptNorm_placed S X WP Slots.scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn_placed hcovPq st x₀ g₀ m rc hst hs hm hnot,
      commitOk_pqRecvPrekey_decPkDefD2c_placed hS_decPk st m.bytes rc⟩

set_option maxHeartbeats 800000 in
/-- Discharges `MainOkPqAllTightPlaced` (all 5 `CliSpecPqxdh` clauses + Clause 6 `NoMatch` under
`mainSpecTightPlaced` at `runRel (cliRunSemD2c_placed X W)`) from `CliA0MainHooks`,
`CliPubCalleesPlaced`, `CliSlotCalleesPlaced`, `DecPkD2cSlotOkPlaced`, and `PksmSlotOkPlaced`. -/
theorem main_ok_cli_pq_all_tight_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hpub : ∀ W : CliHooks, CliPubCalleesPlaced mmpl gh W)
    (hslots : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), CliSlotCalleesPlaced mmpl gh X W)
    (hslot : ∀ W : CliHooks, DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : ∀ W : CliHooks, PksmSlotOkPlaced mmpl gh W) :
    MainOkPqAllTightPlaced mmpl gh :=
  fun _ X W =>
    main_ok_cli_pq_all_tight_of_runSem_placed mmpl gh X W (cliRunSemD2c_placed X W)
      (main_ok_cli_d2c_tight_placed mmpl gh X W (hMainHooks W) (hpub W) (hslots X W) (hslot W)
        (hpksm W))
      rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Tightened 6-clause PQXDH + `NoMatch` `main`-level specification under `LibsignalFrozen lsmpl`. -/
def MainOkPqAllTightFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) ∧
        MainOkNoMatchClausePlaced WP X Run st

/-- Tightened 5-clause `MainOkCliPqTightPlaced` counterpart under `LibsignalFrozen lsmpl`. -/
def MainOkCliPqTightFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
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

/-- Tightened D2(c) `MainOkOverTightPlaced` counterpart under `LibsignalFrozen lsmpl`. -/
def MainOkOverTightFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

/-- Standalone tightened D2(c) `NoMatch` `main`-level specification under `LibsignalFrozen lsmpl`. -/
def MainOkNoMatchTightFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st → MainOkNoMatchClausePlaced WP X Run st

theorem MainOkPqAllTightFrozenPlaced.toMainOkCliPqTightFrozenPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightFrozenPlaced mmpl gh) : MainOkCliPqTightFrozenPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, hmain, fun st hst =>
    let ⟨c1, c2, c3, c4, c5, _⟩ := hcl st hst
    ⟨c1, c2, c3, c4, c5⟩⟩

theorem MainOkPqAllTightFrozenPlaced.toMainOkNoMatchTightFrozenPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightFrozenPlaced mmpl gh) : MainOkNoMatchTightFrozenPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  exact ⟨Run, hmain, fun st hst => (hcl st hst).2.2.2.2.2⟩

theorem MainOkPqAllTightFrozenPlaced.toMainOkOverTightFrozenPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkPqAllTightFrozenPlaced mmpl gh) : MainOkOverTightFrozenPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hcl⟩ := h hDropNz X W
  refine ⟨Run, hmain, fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

set_option maxHeartbeats 800000 in
/-- Discharges `MainOkPqAllTightFrozenPlaced` under `[LibsignalFullPlacement]` from
`CliA0MainHooks`, `CliPubCalleesFrozenPlaced`, `CliSlotCalleesFullPlaced`,
`DecPkD2cSlotOkFrozenPlaced`, and `PksmSlotOkPlaced`. -/
theorem main_ok_cli_pq_all_tight_full_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hpub : ∀ W : CliHooks, CliPubCalleesFrozenPlaced mmpl gh W)
    (hslots : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), CliSlotCalleesFullPlaced mmpl gh X W)
    (hslot : ∀ W : CliHooks, DecPkD2cSlotOkFrozenPlaced mmpl gh W)
    (hpksm : ∀ W : CliHooks, PksmSlotOkPlaced mmpl gh W) :
    MainOkPqAllTightFrozenPlaced mmpl gh :=
  fun _ X W =>
    main_ok_cli_pq_all_tight_of_runSem_placed mmpl gh X W (cliRunSemD2c_placed X W)
      (main_ok_cli_d2c_tight_full_placed mmpl gh X W (hMainHooks W) (hpub W) (hslots X W)
        (hslot W) (hpksm W))
      rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem main_ok_cli_pq_all_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hpub : ∀ W : CliHooks, CliPubCalleesPlaced mmpl gh W)
    (hslots : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), CliSlotCalleesPlaced mmpl gh X W)
    (hslot : ∀ W : CliHooks, DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : ∀ W : CliHooks, PksmSlotOkPlaced mmpl gh W) :
    MainOkPqAllPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_placed mmpl gh hMainHooks hpub hslots hslot hpksm).toMainOkPqAllPlaced

theorem main_ok_over_norm_tight_placed_of_slot [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hpub : ∀ W : CliHooks, CliPubCalleesPlaced mmpl gh W)
    (hslots : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), CliSlotCalleesPlaced mmpl gh X W)
    (hslot : ∀ W : CliHooks, DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : ∀ W : CliHooks, PksmSlotOkPlaced mmpl gh W) :
    MainOkOverNormTightPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_placed mmpl gh hMainHooks hpub hslots hslot hpksm).toMainOkOverNormTightPlaced

theorem main_ok_cli_pq_no_match_tight_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hpub : ∀ W : CliHooks, CliPubCalleesPlaced mmpl gh W)
    (hslots : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), CliSlotCalleesPlaced mmpl gh X W)
    (hslot : ∀ W : CliHooks, DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : ∀ W : CliHooks, PksmSlotOkPlaced mmpl gh W) :
    MainOkPqAllTightPlaced mmpl gh :=
  main_ok_cli_pq_all_tight_placed mmpl gh hMainHooks hpub hslots hslot hpksm

theorem main_ok_cli_pq_no_match_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hpub : ∀ W : CliHooks, CliPubCalleesPlaced mmpl gh W)
    (hslots : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks), CliSlotCalleesPlaced mmpl gh X W)
    (hslot : ∀ W : CliHooks, DecPkD2cSlotOkPlaced mmpl gh W)
    (hpksm : ∀ W : CliHooks, PksmSlotOkPlaced mmpl gh W) :
    MainOkPqAllPlaced mmpl gh :=
  main_ok_cli_pq_all_placed mmpl gh hMainHooks hpub hslots hslot hpksm

/-- Canonical-path (`ObservedExceptNormPlaced`) counterpart to `CliSpecPqxdhNoMatch`. -/
abbrev CliSpecPqNoMatchNorm (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  CliSpecPqxdhNoMatch run X W

end CryptoVerification.SignalSession
