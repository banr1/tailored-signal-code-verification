/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Specifications.Security.AsmSecure

/-!
# Binary Security Statement for `libsignal-cli`

**Trusted: the statement.**

States the top-level security theorem `SignalSessionSecurePlaced bytes` (and placement-indexed
`SignalSessionSecurePlacedAt mpl mmpl bytes`) for the ARM64 ELF binary implementing PQXDH, SPQR,
and the Triple Ratchet, via the run-parametric property `SignalSessionSecureFor Agree R`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Security

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Composed.Refinement
  (AllSecurityQueriesHoldOnHwTrace Explains OpaqueSymbolSemantics
   ProtocolSetup ProtocolSetupWF)
open DY.Libsignal.Composed.Refinement.Cli
  (CliElfProgressPlaced CliTraces CliTurn CoinsFresh ExternContractsHoldCli
   HooksMatchInterpretation InvertsGuarded NextEventCollides elfRelPlaced initDirs)
open CryptoVerification.SignalSession (Inputs Outcome libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (CliElfCodeMatchesPlaced)

/-- Protocol security over run relation `R` and primitive-agreement predicate `Agree` from
`initDirs`: for every valid `interp`, agreeing `W`, and well-formed `r`, there exist opaque
semantics `S` such that every guarded, coin-fresh trace `evs` is either explained (`Explains`) and
satisfies `AllSecurityQueriesHoldOnHwTrace`, or has an explained prefix `evs₁` satisfying
`AllSecurityQueriesHoldOnHwTrace` whose next run event hits `NextEventCollides`. -/
def SignalSessionSecureFor {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : ω, Agree interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∃ S : OpaqueSymbolSemantics,
  ∀ evs : List CliEvent,
    CliTraces (R interp W) interp r (CliTurn.init (initDirs interp r)) evs →
    InvertsGuarded interp r evs →
    CoinsFresh r evs →
    (
      (∃ g ss vis, Explains interp r S g ss vis evs) ∧
      AllSecurityQueriesHoldOnHwTrace interp r S evs)
    ∨ (∃ (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent),
        evs = evs₁ ++ .run ev :: evs₂ ∧
        (∃ g ss vis,
          Explains interp r S g ss vis evs₁ ∧
          NextEventCollides interp r S g ss vis evs₁ ev) ∧
        AllSecurityQueriesHoldOnHwTrace interp r S evs₁)

/-- Security and no-fault progress of ELF image `bytes` at placements `(mpl, mmpl)`: parses `bytes`,
verifies `CliElfCodeMatchesPlaced mpl mmpl elf` and `CliElfProgressPlaced mpl mmpl elf`, and asserts
`SignalSessionSecureFor HooksMatchInterpretation (elfRelPlaced mpl mmpl elf)`. -/
def SignalSessionSecurePlacedAt (mpl mmpl : MultiPlacement) (bytes : List (BitVec 8)) : Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatchesPlaced mpl mmpl elf ∧
    CliElfProgressPlaced mpl mmpl elf ∧
    SignalSessionSecureFor HooksMatchInterpretation (elfRelPlaced mpl mmpl elf)

/-- Relocatable binary security quantified over all valid placements `(mpl, mmpl)` of
`libsignalSessionLib` and `mallocngLib` in `bytes`. -/
def SignalSessionSecurePlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    SignalSessionSecurePlacedAt mpl mmpl bytes

end DY.Libsignal.Composed.Security
