/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.Placed.Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchPathAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFrozen
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Non-Canonical Valid Pre-Key Message Specs & Canonical `runAns` Equivalence

Defines `MainOkValidMatchD3TightPlaced` and `MainOkValidMatchD3TightFrozenPlaced` over
`cliExternsPlaced mmpl W`, and proves canonical `runAns` equivalence on arbitrary wire
payloads `body` satisfying `Pksm.pksmParse body = some pm` and `pkToE? pm = some m`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.ElfFrozen
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Tight `main`-Level Specifications & Canonical `runAns` Equivalence -/

/-- Tight `main`-level specification for empty-or-matching session pre-key `recv` on arbitrary
valid wire payloads `body` under `[LibsignalPlacement]` (`LibsignalCodeRoLoaded lsmpl`). -/
def MainOkValidMatchD3TightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (cliProgPlaced mmpl W) (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256),
          body.length < 2 ^ 32 →
          Pksm.pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk inp (Cli.MainResult.ofAnswer a)

/-- Tight `main`-level specification (`LibsignalFrozen lsmpl`) for empty-or-matching session
pre-key `recv` on arbitrary valid wire payloads `body` under `[LibsignalPlacement]`. -/
def MainOkValidMatchD3TightFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (cliProgPlaced mmpl W) (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256),
          body.length < 2 ^ 32 →
          Pksm.pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk inp (Cli.MainResult.ofAnswer a)

/-- Canonical `Pksm.pksmParse m.bytes` evaluates to `some (pmOfE m pm.message)` whenever
`Pksm.pksmParse body = some pm` and `pkToE? pm = some m` with `m.inner.length + 2048 < 2 ^ 32`. -/
theorem pksmParse_bytes_of_parse_pkToE {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} (hparse : Pksm.pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    Pksm.pksmParse m.bytes = some (pmOfE m pm.message) := by
  have hi := tryFrom_inner_of_pksmParse_pkToE hparse hpk
  have h := Pksm.pksmParse_bytes (RunRefine.argsOf m) hm
  change Pksm.pksmParse m.bytes =
    (match SignalMessage.tryFrom protoSignalCodec m.inner with
     | .ok i => some (pmOfE m i)
     | .error _ => none) at h
  rw [h, hi]

/-- `runAns S` on `pqRecvInputs WP st (wirePrekey :: body) rc` equals `runAns S` on canonical
`pqRecvInputs WP st (wirePrekey :: m.bytes) rc` whenever `S.pksmParse = Pksm.pksmParse`,
`S.decryptPrekey = decPkDef X WP Scope`, `Pksm.pksmParse body = some pm`, `pkToE? pm = some m`,
and `m.inner.length + 2048 < 2 ^ 32`. -/
theorem runAns_pqRecvPrekey_eq_canonical (S : RunSem) (X : UnreachedPqxdhPrimitives) (WP : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hS_pksm : S.pksmParse = Pksm.pksmParse) (hS_decPk : S.decryptPrekey = decPkDef X WP Scope)
    (st : PqParty) (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256) (hparse : Pksm.pksmParse body = some pm) (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    runAns S (pqRecvInputs WP st (wirePrekey :: body) rc) =
      runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) := by
  have hcanon := pksmParse_bytes_of_parse_pkToE hparse hpk hm
  have hfiles_eq :
      (initFsState (Cli.cliInputs (pqRecvInputs WP st (wirePrekey :: body) rc))).files =
      (initFsState (Cli.cliInputs (pqRecvInputs WP st (wirePrekey :: m.bytes) rc))).files := rfl
  rw [runAns_pqRecvPrekey_eq, runAns_pqRecvPrekey_eq, hS_pksm, hparse, hcanon, hS_decPk]
  dsimp only [runFiles]
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk, hfiles_eq]

end LibsignalBinary.Proofs.SignalSession.Cli.D3
