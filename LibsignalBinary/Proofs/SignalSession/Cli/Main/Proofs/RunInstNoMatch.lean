/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliPqBinaryProof
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatch -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds -- shake: keep

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Non-Matching Pre-Key (`NoMatch`) `main`-Level Instantiation & ELF Bridges

Wires `cliRunSemD2c` (`decPkDefD2c`, `DecPkOkD2c`) into `mainSpecTight`, establishing the unified
6-clause PQXDH + non-matching pre-key `recv` specification (`MainOkPqAllTight`, `MainOkOverNormTight`),
per-input ELF bridges under `RunAllocOk`, unconditional `cliImg` instantiations, and `CliExternsOk`
generalizations.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Concrete D2(c)-extended `RunSem` at `Slots.scopeIn`, using `decPkDefD2c` and `DecPkOkD2c`. -/
noncomputable def cliRunSemD2c (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSem X W
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse

/-- Concrete D2(c) instantiation of `CliPqPrekeyBundleS0` from `DecPkD2cSlotOk img`. -/
noncomputable def cliPqPrekeyBundleD2c {img : Obj.Image} (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hslot : DecPkD2cSlotOk img) :
    CliPqPrekeyBundleS0 img X W where
  decPk := decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn
  decPkOk := DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn
  pksmParse := Pksm.pksmParse
  decPkNeed := cliDecryptPrekeyNeed cliRunBudgets
  needLe := cliDecryptPrekeyNeed_le
  pksmSlot := fun _ hS =>
    cliPksmTryFrom_ok himg (RunHooks.cli W img).alloc (fun b => congrFun hS b)
  decPkSlot := fun S needs hfiles hdec hdecOk hneed =>
    hslot X W S needs hfiles hdec hdecOk hneed
  pksmAgrees := fun _ hS => pksmParseAgrees_S0 hS
  decPkAgrees := fun S hdec hpksm =>
    pqDecryptPrekeyAgrees_decPkDefD2c S X ⟨W.C, W.Q⟩ Slots.scopeIn hdec (pksmTyped_S0 hpksm)
      encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn ⟨W.C, W.Q⟩)
  decPkDomOk := fun st m rc pm hst hm _hmatch hparse =>
    decPkDomOk_d2c_cli ⟨W.C, W.Q⟩ st m rc pm hst hm hparse
  decPkCommitOk := fun S st m rc hdec hpksm hwf hm hmatch =>
    decPkCommitOk_d2c_cli S st m rc hdec hpksm hwf hm hmatch

/-- `main` satisfies `mainSpecTight` at `Run := runRel (cliRunSemD2c X W)`, given
`DecPkD2cSlotOk cliImg`. -/
theorem main_ok_cli_d2c_tight (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hslot : DecPkD2cSlotOk cliImg) :
    subroutine_ok (cliProg cliImg (cliExterns W)) (entryOf cliImg mainName)
      (SignalSession.mainSpecTight E2E.HooksE.A0 cliImg cliMainStk (cliStatics cliImg)
        (runRel (cliRunSemD2c X W))) :=
  main_ok_cli_of_runTight X W
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse
    himg
    (hrun_cli_d2c_tight X W himg hslot)

/-- `main` satisfies `mainSpec` at `Run := runRel (cliRunSemD2c X W)`, given
`DecPkD2cSlotOk cliImg`. -/
theorem main_ok_cli_d2c (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hslot : DecPkD2cSlotOk cliImg) :
    subroutine_ok (cliProg cliImg (cliExterns W)) (entryOf cliImg mainName)
      (mainSpec E2E.HooksE.A0 cliImg cliMainStk (cliStatics cliImg) (runRel (cliRunSemD2c X W))) :=
  SignalSession.subroutine_ok_mainSpec_of_tight (main_ok_cli_d2c_tight X W himg hslot)

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli hiding
  mainSpecTight subroutine_ok_mainSpec_of_tight MainOkCliPqTight MainOkCliSmTight
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen

/-! ## 1. Tightened 6-Clause & `ObservedExceptNorm` `main`-Level Specifications -/

/-- Clause 6 (`NoMatch`) of `MainOkPqAllTight` / `MainOkPqAll`: on a `PqxdhPartyInSpecDomain` state
`st` whose current session `st.session = some (x₀, g₀)` does not match `m`
(`¬ PqSessionMatches x₀ g₀ m`), `Run` agrees with `pqRecvPrekeyModel X WP { st with session := none } m rc`
with exact 2-session outcome `d2cObserve`, canonical-path `ObservedExceptNorm` outside
`sessionFile (partyAddress st.party.other)`, and `Cli.CommitOk`. -/
def MainOkNoMatchClause (WP : PEParams) (X : UnreachedPqxdhPrimitives)
    (Run : Inputs → Cli.RunAnswer → Prop) (st : PqParty) : Prop :=
  ∀ (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8))) (m : PreKeyMessageFields) (rc : BitVec 256),
    st.session = some (x₀, g₀) →
    m.inner.length + 2048 < 2 ^ 32 →
    ¬ PqSessionMatches x₀ g₀ m →
    ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
      observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
        d2cObserve WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) st.party.other x₀ g₀
          (pqRecvPrekeyModel X WP { st with session := none } m rc) ∧
      ObservedExceptNorm WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (sessionFile (partyAddress st.party.other))
        (pqRecvPrekeyModel X WP { st with session := none } m rc)
        (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
      Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (Cli.MainResult.ofAnswer a)

/-- Tightened 6-clause PQXDH + `NoMatch` `main`-level specification extending `MainOkCliPqTight img`
with `MainOkNoMatchClause` on the same `Run` witness. -/
def MainOkPqAllTight (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
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
        MainOkNoMatchClause WP X Run st

/-- Legacy `Cli.mainSpec` counterpart of `MainOkPqAllTight`. -/
def MainOkPqAll (img : Obj.Image) : Prop :=
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
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) ∧
        MainOkNoMatchClause WP X Run st

/-- Standalone tightened D2(c) `NoMatch` `main`-level specification (`MainOkNoMatchTight`). -/
def MainOkNoMatchTight (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st → MainOkNoMatchClause WP X Run st

/-- Standalone D2(c) `NoMatch` `main`-level specification (`MainOkNoMatch`). -/
def MainOkNoMatch (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpec E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st → MainOkNoMatchClause WP X Run st

/-- Canonical-path (`ObservedExceptNorm`) counterpart to `MainOkOverTight`. -/
def MainOkOverNormTight (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState E2E.Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            ObservedExceptNorm WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

/-- Canonical-path (`ObservedExceptNorm`) counterpart to `CliPqBinaryProof.MainOkOver`. -/
def MainOkOverNorm (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpec E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState E2E.Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            ObservedExceptNorm WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

theorem MainOkPqAllTight.toMainOkPqAll {img : Obj.Image} (h : MainOkPqAllTight img) :
    MainOkPqAll img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  exact ⟨Run, subroutine_ok_mainSpec_of_tight hmain, hcl⟩

theorem MainOkPqAllTight.toMainOkCliPqTight {img : Obj.Image} (h : MainOkPqAllTight img) :
    MainOkCliPqTight img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  exact ⟨Run, hmain, fun st hst =>
    let ⟨c1, c2, c3, c4, c5, _⟩ := hcl st hst
    ⟨c1, c2, c3, c4, c5⟩⟩

theorem MainOkPqAllTight.toMainOkNoMatchTight {img : Obj.Image} (h : MainOkPqAllTight img) :
    MainOkNoMatchTight img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  exact ⟨Run, hmain, fun st hst => (hcl st hst).2.2.2.2.2⟩

theorem MainOkPqAllTight.toMainOkOverNormTight {img : Obj.Image} (h : MainOkPqAllTight img) :
    MainOkOverNormTight img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  refine ⟨Run, hmain, fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem MainOkPqAll.toMainOkCliPq {img : Obj.Image} (h : MainOkPqAll img) : MainOkCliPq img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  exact ⟨Run, hmain, fun st hst =>
    let ⟨c1, c2, c3, c4, c5, _⟩ := hcl st hst
    ⟨c1, c2, c3, c4, c5⟩⟩

theorem MainOkPqAll.toMainOkNoMatch {img : Obj.Image} (h : MainOkPqAll img) :
    MainOkNoMatch img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  exact ⟨Run, hmain, fun st hst => (hcl st hst).2.2.2.2.2⟩

theorem MainOkPqAll.toMainOkOverNorm {img : Obj.Image} (h : MainOkPqAll img) :
    MainOkOverNorm img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  refine ⟨Run, hmain, fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem MainOkOverNormTight.toMainOkOverNorm {img : Obj.Image} (h : MainOkOverNormTight img) :
    MainOkOverNorm img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X W
  exact ⟨Run, subroutine_ok_mainSpec_of_tight hmain, hcl⟩

/-! ## 2. Proof of `MainOkPqAllTight` & `MainOkOverNormTight` from `DecPkD2cSlotOk` -/

private theorem main_ok_cli_pq_all_tight_of_runSem {img : Obj.Image}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (S : RunSem)
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) (runRel S)))
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
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
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
        MainOkNoMatchClause WP X Run st := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hcovPq := ratchetScopeCoversPq_scopeIn WP
  have hagInit : PqInitiateAgrees S X WP := InitS0.pqInitiateAgrees_initDef_proof S X WP hS_init
  have hagEnc : PqEncryptAgrees S WP :=
    pqEncryptAgrees_encDef S WP Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovPq
  have hagDec : PqDecryptSignalAgrees S WP :=
    pqDecryptSignalAgrees_decSigDef S WP Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovPq
  have hagPksm : PksmParseAgrees S := pksmParseAgrees_S0 hS_pksm
  have hpksmT : PksmTyped S := pksmTyped_S0 hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X WP :=
    pqDecryptPrekeyAgrees_decPkDefD2c S X WP Slots.scopeIn hS_decPk hpksmT encodeInjOn_scopeIn hcovPq
  refine ⟨runRel S, hmain, fun st hst => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
        runHsOk_pqRecvPrekey_d2c hS_decPkOk hS_pksm st m rc hst hm, rfl⟩,
      RunRefine.runAns_pqRecvPrekey S X WP hagPksm hagDecPk st m rc hst hm hmatch,
      commitOk_pqRecvPrekey_decPkDefD2c hS_decPk st m.bytes rc⟩
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
  · intro x₀ g₀ m rc hs hm hnot
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
        Slots.runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_d2c hS_decPkOk hS_pksm st m rc hst hm, rfl⟩,
      runAns_pqRecvPrekey_noMatch_exact S X WP Slots.scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn hcovPq st x₀ g₀ m rc hst hs hm hnot,
      runAns_pqRecvPrekey_noMatch_exceptNorm S X WP Slots.scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn hcovPq st x₀ g₀ m rc hst hs hm hnot,
      commitOk_pqRecvPrekey_decPkDefD2c hS_decPk st m.bytes rc⟩

set_option maxHeartbeats 800000 in
/-- Discharges `MainOkPqAllTight cliImg` (all 5 `CliSpecPqxdh` clauses + Clause 6 `NoMatch` under
`mainSpecTight` at `runRel (cliRunSemD2c X W)`) from `Obj.Loads libsignalSessionImage cliImg` and
`DecPkD2cSlotOk cliImg`. -/
theorem main_ok_cli_pq_all_tight
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hslot : DecPkD2cSlotOk cliImg) :
    MainOkPqAllTight cliImg :=
  fun X W =>
    main_ok_cli_pq_all_tight_of_runSem X W (cliRunSemD2c X W)
      (main_ok_cli_d2c_tight X W himg hslot)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem main_ok_cli_pq_all
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hslot : DecPkD2cSlotOk cliImg) :
    MainOkPqAll cliImg :=
  (main_ok_cli_pq_all_tight himg hslot).toMainOkPqAll

/-- `MainOkOverNormTight cliImg` discharged from `Obj.Loads libsignalSessionImage cliImg` and
`DecPkD2cSlotOk cliImg`. -/
theorem main_ok_over_norm_tight_of_slot
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hslot : DecPkD2cSlotOk cliImg) :
    MainOkOverNormTight cliImg :=
  (main_ok_cli_pq_all_tight himg hslot).toMainOkOverNormTight

theorem main_ok_over_norm_tight_cli_of_slot (hslot : DecPkD2cSlotOk cliImg) :
    MainOkOverNormTight cliImg :=
  main_ok_over_norm_tight_of_slot loads_cliImg hslot

theorem main_ok_over_norm_tight_of_pollAt
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hpoll : CliDpPollOkD2cStateAt cliImg) :
    MainOkOverNormTight cliImg :=
  main_ok_over_norm_tight_of_slot himg (decPkD2cSlotOk_of_pollAt himg hpoll)

theorem main_ok_over_norm_tight_cli_of_poll (hpoll : CliDpPollOkD2cStateStmt) :
    MainOkOverNormTight cliImg :=
  main_ok_over_norm_tight_of_slot loads_cliImg (decPkD2cSlotOk_of_poll loads_cliImg hpoll)

theorem main_ok_cli_pq_no_match_tight (hslot : DecPkD2cSlotOk cliImg) :
    MainOkPqAllTight cliImg :=
  main_ok_cli_pq_all_tight loads_cliImg hslot

theorem main_ok_cli_pq_no_match (hslot : DecPkD2cSlotOk cliImg) :
    MainOkPqAll cliImg :=
  main_ok_cli_pq_all loads_cliImg hslot

theorem main_ok_cli_pq_all_tight_of_poll (hpoll : CliDpPollOkD2cStateStmt) :
    MainOkPqAllTight cliImg :=
  main_ok_cli_pq_all_tight loads_cliImg (decPkD2cSlotOk_of_poll loads_cliImg hpoll)

theorem main_ok_cli_pq_all_of_poll (hpoll : CliDpPollOkD2cStateStmt) :
    MainOkPqAll cliImg :=
  main_ok_cli_pq_all loads_cliImg (decPkD2cSlotOk_of_poll loads_cliImg hpoll)

/-! ## 3. Whole-Process D2(c) `RunAllocOk` Bridges -/

private theorem cliSpecPq_recvPrekeyNoMatch_exact_of_parts
    {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hover : MainOkPqAll img)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8)))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hs : st.session = some (x₀, g₀))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnot : ¬ PqSessionMatches x₀ g₀ m)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
      if (wirePrekey :: m.bytes).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
      else
        some (d2cObserve ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          st.party.other x₀ g₀
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ { st with session := none } m rc)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
  obtain ⟨_, hmainW, hcl⟩ := hover X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch inp)
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
      halloc
  · simp only [hstin, ↓reduceIte]
    obtain ⟨_, hrun, hobs, _, hcommit⟩ := (hcl st hst).2.2.2.2.2 x₀ g₀ m rc hs hm hnot
    exact cliRunSig_of_main_call_obs himg hbase hE hH hmainW (hpatch inp)
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      hrun
      (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs
      (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      hcommit halloc

/-- Per-input ELF-level D2(c) `NoMatch` theorem with **exact** 2-session `d2cObserve` outcome under
`RunAllocOk`. -/
theorem cliSpecPq_recvPrekeyNoMatch_exact_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hover : MainOkPqAll cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8)))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hs : st.session = some (x₀, g₀))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnot : ¬ PqSessionMatches x₀ g₀ m)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
      if (wirePrekey :: m.bytes).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
      else
        some (d2cObserve ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          st.party.other x₀ g₀
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ { st with session := none } m rc)) :=
  cliSpecPq_recvPrekeyNoMatch_exact_of_parts loads_cliImg cliImg_base
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE)
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat W)
    hover hst x₀ g₀ m rc hs hm hnot halloc

private theorem cliSpecPq_recvPrekeyNoMatch_exceptNorm_of_parts
    {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hover : MainOkPqAll img)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8)))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hs : st.session = some (x₀, g₀))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnot : ¬ PqSessionMatches x₀ g₀ m)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    if (wirePrekey :: m.bytes).length > stdinCapBytes then
      cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
    else
      ∃ o, cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) = some o ∧
        ObservedExceptNorm ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ { st with session := none } m rc) o := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
  obtain ⟨_, hmainW, hcl⟩ := hover X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch inp)
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
      halloc
  · simp only [hstin, ↓reduceIte]
    obtain ⟨_, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2.2.2.2.2 x₀ g₀ m rc hs hm hnot
    exact cliRunSig_of_main_call_pred himg hbase hE hH hmainW (hpatch inp)
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      hrun
      (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hexcept
      (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      hcommit halloc

/-- Per-input ELF-level D2(c) `NoMatch` theorem in canonical-path `ObservedExceptNorm` form under
`RunAllocOk`. -/
theorem cliSpecPq_recvPrekeyNoMatch_exceptNorm_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hover : MainOkPqAll cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8)))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hs : st.session = some (x₀, g₀))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnot : ¬ PqSessionMatches x₀ g₀ m)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    if (wirePrekey :: m.bytes).length > stdinCapBytes then
      cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
    else
      ∃ o, cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) = some o ∧
        ObservedExceptNorm ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ { st with session := none } m rc) o :=
  cliSpecPq_recvPrekeyNoMatch_exceptNorm_of_parts loads_cliImg cliImg_base
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE)
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat W)
    hover hst x₀ g₀ m rc hs hm hnot halloc

/-! ## 4. Unconditional CLI Instantiations (`MainOkPqAllTight`, `MainOkOverTight`, `MainOkOver`) -/

theorem decPkD2cSlotOk_cliImg : DecPkD2cSlotOk cliImg :=
  Cli.RunProofs.decPkD2cSlotOk_cli loads_cliImg

/-- Unconditional `MainOkPqAllTight cliImg` (all 5 `CliSpecPqxdh` clauses + Clause 6 `NoMatch` under
`mainSpecTight`). -/
theorem main_ok_pq_all_tight_cli
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkPqAllTight cliImg :=
  main_ok_cli_pq_all_tight himg (Cli.RunProofs.decPkD2cSlotOk_cli himg)

theorem main_ok_pq_all_cli
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkPqAll cliImg :=
  (main_ok_pq_all_tight_cli himg).toMainOkPqAll

theorem main_ok_over_tight_cli
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkOverTight cliImg :=
  (main_ok_pq_all_tight_cli himg).toMainOkOverNormTight

theorem main_ok_over_tight_cliImg : MainOkOverTight cliImg :=
  main_ok_over_tight_cli loads_cliImg

theorem main_ok_over_cliImg : MainOkOver cliImg :=
  main_ok_over_tight_cliImg.toMainOkOver

/-! ## 5. Parameterized `Ext` 6-Clause & `NoMatch` Assembly -/

open CryptoVerification.SignalSession.Cli.RunSkeleton

/-- `PEParams`-parameterized D2(c) `RunSem` (`cliRunSemD2c` without `CliHooks`). -/
noncomputable def Cli.MainHops.cliRunSemD2cExt (X : UnreachedPqxdhPrimitives) (P : PEParams) : RunSem where
  encrypt := encDef P Cli.Slots.scopeIn
  decryptSignal := decSigDef P Cli.Slots.scopeIn
  initiate := initDef X P
  decryptPrekey := decPkDefD2c X P Cli.Slots.scopeIn
  pksmParse := Pksm.pksmParse
  filesOk := Cli.Slots.filesOk₀ Cli.Slots.scopeIn (fun _ => True)
  encOk := Cli.Slots.encOk₀ Cli.Slots.scopeIn
  initOk := InitOk₀ P
  decPkOk := DecPkOkD2c P Cli.Slots.scopeIn

theorem Cli.MainHops.cliRunSemD2c_eq (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    cliRunSemD2c X W = Cli.MainHops.cliRunSemD2cExt X ⟨W.C, W.Q⟩ := rfl

/-- `Ext` D2(c) `wrapDecryptPrekey` slot contract under `CliExternsOk P A ext`. -/
def Cli.MainHops.DecPkD2cSlotOkExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
    (ext : String → Option (State → State)), CliExternsOk P A ext →
    ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Cli.Slots.filesOk₀ Cli.Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPkDefD2c X P Cli.Slots.scopeIn →
      S.decPkOk = DecPkOkD2c P Cli.Slots.scopeIn →
      needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
      (slotsOf A img S needs).decryptPrekey.Ok img (cliExternsWith ext) wrapDecryptPrekeyName

theorem Cli.MainHops.DecPkD2cSlotOkExt.toDecPkD2cSlotOk {img : Obj.Image}
    (h : Cli.MainHops.DecPkD2cSlotOkExt img) : DecPkD2cSlotOk img :=
  fun X W => h X ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) (cliExterns_ok W)

/-- 5-clause PQXDH body (`abbrev` so `Cli.MainOkCliPqTightExt` is `rfl`-equal to
`ProcessOomExt.MainOkCliPqTightExt`). -/
abbrev Cli.MainHops.PqFiveClausesD2cExt (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (Run : Inputs → Cli.RunAnswer → Prop) (st : PqParty) : Prop :=
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
        pqxdhExpectedOutcome P (pqRecvInputs P st (wireWhisper :: c) rc) (pqRecvWhisperModel P st c rc) ∧
      Cli.CommitOk (pqRecvInputs P st (wireWhisper :: c) rc) (Cli.MainResult.ofAnswer a)) ∧
  (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    ∃ a, Run (pqRecvInputs P st (wirePrekey :: m.bytes) rc) a ∧
      observe (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files a =
        pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
          (pqRecvPrekeyModel X P st m rc) ∧
      Cli.CommitOk (pqRecvInputs P st (wirePrekey :: m.bytes) rc) (Cli.MainResult.ofAnswer a)) ∧
  (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
    c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
    ∃ a, Run (pqRecvInputs P st c rc) a ∧
      observe (pqRecvInputs P st c rc).files a =
        .exited 1 [] (filesOf (pqRecvInputs P st c rc).files) ∧
      Cli.CommitOk (pqRecvInputs P st c rc) (Cli.MainResult.ofAnswer a))

/-- Tightened `Ext` 5-clause PQXDH `main` spec (`rfl`-equal to `ProcessOomExt.MainOkCliPqTightExt`). -/
def Cli.MainOkCliPqTightExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
    (ext : String → Option (State → State)), CliExternsOk P A ext →
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain P st → Cli.MainHops.PqFiveClausesD2cExt X P Run st

/-- Tightened `Ext` 6-clause PQXDH + D2(c) `NoMatch` `main` spec under `CliExternsOk P A ext`. -/
def MainOkPqAllTightExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
    (ext : String → Option (State → State)), CliExternsOk P A ext →
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain P st →
        Cli.MainHops.PqFiveClausesD2cExt X P Run st ∧ MainOkNoMatchClause P X Run st

/-- Tightened `Ext` Clause-6 `NoMatch` `main` spec (`rfl`-equal to `ProcessOomExt.MainOkOverTightExt`). -/
def MainOkOverNormTightExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
    (ext : String → Option (State → State)), CliExternsOk P A ext →
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain P st →
        ∀ (x : RecordExtras) (g : GhostState E2E.Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs P st (wirePrekey :: m.bytes) rc) a ∧
            ObservedExceptNorm P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X P { st with session := none } m rc)
              (observe (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs P st (wirePrekey :: m.bytes) rc) (Cli.MainResult.ofAnswer a)

theorem MainOkPqAllTightExt.toMainOkCliPqTightExt {img : Obj.Image}
    (h : MainOkPqAllTightExt img) : Cli.MainOkCliPqTightExt img := by
  intro X P A ext hOk; obtain ⟨Run, hmain, hcl⟩ := h X P A ext hOk
  exact ⟨Run, hmain, fun st hst => (hcl st hst).1⟩

theorem MainOkPqAllTightExt.toMainOkOverNormTightExt {img : Obj.Image}
    (h : MainOkPqAllTightExt img) : MainOkOverNormTightExt img := by
  intro X P A ext hOk; obtain ⟨Run, hmain, hcl⟩ := h X P A ext hOk
  refine ⟨Run, hmain, fun st hst x g hs m rc hm hnot => ?_⟩
  obtain ⟨a, hrun, _, hexcept, hcommit⟩ := (hcl st hst).2 x g m rc hs hm hnot
  exact ⟨a, hrun, hexcept, hcommit⟩

theorem Cli.MainOkCliPqTightExt.toMainOkCliPqTight {img : Obj.Image}
    (h : Cli.MainOkCliPqTightExt img) : MainOkCliPqTight img :=
  fun X W => h X ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) (cliExterns_ok W)

theorem MainOkOverNormTightExt.toMainOkOverTight {img : Obj.Image}
    (h : MainOkOverNormTightExt img) : MainOkOverTight img :=
  fun X W => h X ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) (cliExterns_ok W)

theorem MainOkPqAllTightExt.toMainOkPqAllTight {img : Obj.Image}
    (h : MainOkPqAllTightExt img) : MainOkPqAllTight img := by
  intro X W
  obtain ⟨Run, hmain, hcl⟩ := h X ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliHookExterns W) (cliExterns_ok W)
  exact ⟨Run, hmain, fun st hst =>
    let ⟨⟨c1, c2, c3, c4, c5⟩, c6⟩ := hcl st hst; ⟨c1, c2, c3, c4, c5, c6⟩⟩

/-- Parameterized 6-clause PQXDH + D2(c) `NoMatch` engine over `{prog : Program}`,
`{A : RustHeap.RustAlloc}`, and `(P : PEParams)`. -/
theorem main_ok_cli_pq_all_tight_of_runSem_ext {img : Obj.Image} {prog : Program}
    {A : RustHeap.RustAlloc} (X : UnreachedPqxdhPrimitives) (P : PEParams) (S : RunSem)
    (hmain : subroutine_ok prog (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) (runRel S)))
    (hS_enc : S.encrypt = encDef P Cli.Slots.scopeIn)
    (hS_dec : S.decryptSignal = decSigDef P Cli.Slots.scopeIn)
    (hS_init : S.initiate = initDef X P)
    (hS_decPk : S.decryptPrekey = decPkDefD2c X P Cli.Slots.scopeIn)
    (hS_pksm : S.pksmParse = Pksm.pksmParse)
    (hS_files : S.filesOk = Cli.Slots.filesOk₀ Cli.Slots.scopeIn (fun _ => True))
    (hS_encOk : S.encOk = Cli.Slots.encOk₀ Cli.Slots.scopeIn)
    (hS_initOk : S.initOk = InitOk₀ P)
    (hS_decPkOk : S.decPkOk = DecPkOkD2c P Cli.Slots.scopeIn) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok prog (entryOf img Cli.mainName)
        (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain P st →
        Cli.MainHops.PqFiveClausesD2cExt X P Run st ∧ MainOkNoMatchClause P X Run st := by
  have hcovPq := ratchetScopeCoversPq_scopeIn P
  have hagInit : PqInitiateAgrees S X P := InitS0.pqInitiateAgrees_initDef_proof S X P hS_init
  have hagEnc : PqEncryptAgrees S P :=
    pqEncryptAgrees_encDef S P Cli.Slots.scopeIn hS_enc encodeInjOn_scopeIn hcovPq
  have hagDec : PqDecryptSignalAgrees S P :=
    pqDecryptSignalAgrees_decSigDef S P Cli.Slots.scopeIn hS_dec encodeInjOn_scopeIn hcovPq
  have hagPksm : PksmParseAgrees S := pksmParseAgrees_S0 hS_pksm
  have hpksmT : PksmTyped S := pksmTyped_S0 hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X P :=
    pqDecryptPrekeyAgrees_decPkDefD2c S X P Cli.Slots.scopeIn hS_decPk hpksmT
      encodeInjOn_scopeIn hcovPq
  refine ⟨runRel S, hmain, fun st hst => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · intro b t hnone
    exact ⟨runAns S (pqInitInputs P st b t),
      ⟨domainArgv_pqInit P st b t, runBounds_pqInit P st b t,
        runFilesOk_pqInit_cli (S := S) hS_files P st b t hst,
        Cli.Slots.runEncOk_pqInit S P st b t,
        runHsOk_pqInit_cli (S := S) (W := P) hS_initOk st b t hst hnone, rfl⟩,
      RunRefine.runAns_pqInit S X P hagInit st b t hst hnone,
      commitOk_pqInit_initDef (S := S) (X := X) (W := P) hS_init st b t⟩
  · intro m r hm
    exact ⟨runAns S (pqSendInputs P st m r),
      ⟨domainArgv_pqSend P st m r, runBounds_pqSend P st m r hm,
        runFilesOk_pqSend_cli (S := S) hS_files P st m r hst,
        Cli.Slots.runEncOk_pqSend (S := S) hS_encOk P st m r,
        runHsOk_pqSend_cli S P st m r, rfl⟩,
      RunRefine.runAns_pqSend S P hagEnc st m r hst hm,
      commitOk_pqSend_encDef (S := S) (W := P) hS_enc st m r⟩
  · intro c rc hc
    have hnot3 : (wireWhisper :: c).head? ≠ some wirePrekey := by simp [wireWhisper, wirePrekey]
    exact ⟨runAns S (pqRecvInputs P st (wireWhisper :: c) rc),
      ⟨domainArgv_pqRecv P st (wireWhisper :: c) rc,
        runBounds_pqRecv P st (wireWhisper :: c) rc (Nat.succ_le_of_lt hc),
        runFilesOk_pqRecv_cli (S := S) hS_files P st (wireWhisper :: c) rc hst,
        Cli.Slots.runEncOk_pqRecv S P st (wireWhisper :: c) rc,
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
        Cli.Slots.runEncOk_pqRecv S P st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_d2c hS_decPkOk hS_pksm st m rc hst hm, rfl⟩,
      RunRefine.runAns_pqRecvPrekey S X P hagPksm hagDecPk st m rc hst hm hmatch,
      commitOk_pqRecvPrekey_decPkDefD2c hS_decPk st m.bytes rc⟩
  · intro c rc hc h2 h3
    refine ⟨runAns S (pqRecvInputs P st c rc),
      ⟨domainArgv_pqRecv P st c rc, runBounds_pqRecv P st c rc (Nat.le_of_lt hc),
        runFilesOk_pqRecv_cli (S := S) hS_files P st c rc hst,
        Cli.Slots.runEncOk_pqRecv S P st c rc, runHsOk_pqRecvOther_cli S P st c rc h3, rfl⟩,
      ?_, commitOk_pqRecvBad S P st c rc h2 h3⟩
    rw [runAns_pqRecvBad S P st c rc h2 h3]; rfl
  · intro x₀ g₀ m rc hs hm hnot
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm)
    exact ⟨runAns S (pqRecvInputs P st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv P st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv P st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli (S := S) hS_files P st (wirePrekey :: m.bytes) rc hst,
        Cli.Slots.runEncOk_pqRecv S P st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_d2c hS_decPkOk hS_pksm st m rc hst hm, rfl⟩,
      runAns_pqRecvPrekey_noMatch_exact S X P Cli.Slots.scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn hcovPq st x₀ g₀ m rc hst hs hm hnot,
      runAns_pqRecvPrekey_noMatch_exceptNorm S X P Cli.Slots.scopeIn hS_decPk hagPksm hpksmT
        encodeInjOn_scopeIn hcovPq st x₀ g₀ m rc hst hs hm hnot,
      commitOk_pqRecvPrekey_decPkDefD2c hS_decPk st m.bytes rc⟩

/-- Parameterized `Ext` D2(c) `mainSpecTight` dependency bundle. -/
abbrev Cli.MainHops.MainD2cTightExt (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustHeap.RustAlloc)
    (ext : String → Option (State → State)), CliExternsOk P A ext →
    subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img)
        (runRel (Cli.MainHops.cliRunSemD2cExt X P)))

/-- Parameterized `Ext` 6-clause PQXDH + `NoMatch` assembly from `MainD2cTightExt`. -/
theorem main_ok_pq_all_tight_ext_of_deps {img : Obj.Image}
    (hd2c : Cli.MainHops.MainD2cTightExt img) : MainOkPqAllTightExt img :=
  fun X P A ext hOk =>
    main_ok_cli_pq_all_tight_of_runSem_ext X P (Cli.MainHops.cliRunSemD2cExt X P)
      (hd2c X P A ext hOk) rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Parameterized `Ext` 5-clause PQXDH projection from `MainD2cTightExt` (definitionally equal to
`ProcessOomExt.MainOkCliPqTightExt img`). -/
theorem Cli.main_ok_cli_pq_tight_ext_of_deps {img : Obj.Image}
    (hd2c : Cli.MainHops.MainD2cTightExt img) : Cli.MainOkCliPqTightExt img :=
  (main_ok_pq_all_tight_ext_of_deps hd2c).toMainOkCliPqTightExt

theorem main_ok_cli_pq_tight_ext_of_d2c {img : Obj.Image}
    (hd2c : Cli.MainHops.MainD2cTightExt img) : Cli.MainOkCliPqTightExt img :=
  (main_ok_pq_all_tight_ext_of_deps hd2c).toMainOkCliPqTightExt

/-- Parameterized `Ext` Clause-6 `NoMatch` projection from `MainD2cTightExt` (definitionally equal
to `ProcessOomExt.MainOkOverTightExt img`). -/
theorem main_ok_over_tight_ext_of_deps {img : Obj.Image}
    (hd2c : Cli.MainHops.MainD2cTightExt img) : MainOkOverNormTightExt img :=
  (main_ok_pq_all_tight_ext_of_deps hd2c).toMainOkOverNormTightExt

end CryptoVerification.SignalSession
