/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqFixed

@[expose] public section

set_option autoImplicit false

/-!
# The `signal-session` binary is correct under every extern table that meets its contracts

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file:
they state the fixed hook table. It is the statement of the `…Ext` corollaries of `CliElfLib`
(`Computational/docs/TRUSTED_BASE.md` §2); a reader who trusts them reads it in full.

This file restates the CLI binary statements (`CliBinary.lean`, `CliBinaryPq.lean`,
`CliBinaryPqProofDefs.lean`) with the fixed hook table `cliHookTable W` (`CliRun.lean`)
replaced by any extern table `ext` that meets the separation-logic contracts
`CliExternsOk P A ext` (`CliExterns.lean`):

* `CliBinaryCorrectExt elf`: `CliBinaryCorrect elf` with `∀ W, … cliRunAbortOnPanic elf W …` replaced by
  `∀ P A ext, CliExternsOk P A ext → … cliRunAbortOnPanicUnderExterns elf ext …`, the crypto `W.C` by `P.C`;
* `CliPqBinaryCorrectExt elf`: `CliPqxdhElfCorrectUnderAllocOk elf` changed the same way, the model
  primitives `⟨W.C, W.Q⟩` by `P` (since an arbitrary `RustAlloc` `A` has an arbitrary heap budget).

`LibsignalCli…Ext bytes` says that `bytes` parse as an ELF that meets the statement. The closed
statements at `cliElfBytes` are proved as `libsignalCliBinaryCorrectExt_cliElf` and
`libsignalCliPqBinaryCorrectExt_cliElf`
(`LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfSlicesExt.lean`).

**The fixed-table statements are special cases.** The fixed table meets the contracts at
`P := ⟨W.C, W.Q⟩` and `A := E2E.HooksE.A0` (`cliExterns_ok`), and `cliRunAbortOnPanic elf W` is
`cliRunAbortOnPanicUnderExterns elf (cliHookExterns W)` by `rfl` (`cliRunSig_eq`, `CliExterns.lean`). So each
`…Ext` statement implies its fixed-table counterpart
(`LibsignalBinary/Proofs/SignalSession/Cli/CliExternsWitness.lean`).

**What an extern table may choose** (`CliExterns.lean`): the allocator (any `RustAlloc`;
`__rust_dealloc` consumes its block, so a use-after-free is not provable, DEV-E6), the registers
a hook leaves (only the callee-saved ones survive a call, DEV-E1), the stack a hook uses (up to its
budget), the result bits the ABI leaves free, and every precondition (a caller proves it).
`CliHooks`' `bcmp` and `utf8Err` fields play no role here: those behaviours are fixed at contract
level (`CliExt.bcmpSpec`, `CliExt.fromUtf8Spec`).

## Main definitions

* `CliAllocNeverFailsWith`, `CliAllocNeverFailsPqWith`: the no-failed-allocation hypotheses
  (DEV-CLI9 in SM mode; proof-side in PQXDH mode) for the run under `ext`.
* `CliRunAllocFailsWith`: some allocation of the run under `ext` fails.
* `CliBinaryCorrectExt`, `LibsignalCliBinaryCorrectExt`: the SM-mode statement over all
  contract-meeting extern tables.
* `CliPqBinaryCorrectExt`, `LibsignalCliPqBinaryCorrectExt`: the PQXDH-mode statement under
  `CliAllocNeverFailsPqWith`, likewise.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## No allocation fails (per extern table) -/

/-- DEV-CLI9 for the run under `ext`: `CliAllocNeverFails elf W` (`CliBinary.lean`) with
`cliProgAbortOnPanicUnderExterns ext` in place of `cliProgAbortOnPanic W` and the crypto `C` in place of `W.C`. -/
def CliAllocNeverFailsWith (elf : ElfImage) (C : Crypto) (ext : String → Option (State → State)) :
    Prop :=
  (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams C) g → m.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smSendInputs g m)) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace) ∧
  (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams C) g →
    c.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smRecvInputs g c rc)) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace)

/-- No allocation fails on any PQXDH-mode input in `CliPqxdhInputs P` under
`cliProgAbortOnPanicUnderExterns ext`. -/
def CliAllocNeverFailsPqWith (elf : ElfImage) (P : PEParams)
    (ext : String → Option (State → State)) : Prop :=
  ∀ i : Inputs, CliPqxdhInputs P i →
    ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace

/-- Some allocation of the run under `ext` fails (`cliRunHitsAllocFailure` with
`cliProgAbortOnPanicUnderExterns ext`). -/
def CliRunAllocFailsWith (elf : ElfImage) (ext : String → Option (State → State)) (i : Inputs) :
    Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgAbortOnPanicUnderExterns ext) (cliTokenPatch s0) s ∧ RustHeap.allocFailedEvent ∈ s.trace

/-! ## The statements -/

/-- The CLI's ELF `elf` meets `CliSpecE` under every extern table that meets its contracts.
`CliBinaryCorrect elf` (`CliBinary.lean`) with its `∀ W` replaced by: for all primitives `P`,
allocators `A` and extern tables `ext` with `CliExternsOk P A ext`, under which no allocation of
the run fails (`CliAllocNeverFailsWith elf P.C ext`), the run under `ext` meets the clauses at
`P.C`. -/
def CliBinaryCorrectExt (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
    CliExternsOk P A ext → CliAllocNeverFailsWith elf P.C ext →
    (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
      CliRunsToUnderExterns elf ext (smSendInputs g m)
        (if m.length > stdinCapBytes then
          .exited 2 [] (filesOf (smSendInputs g m).files)
        else if m.length > maxPlaintextBytes then
          .exited 1 [] (filesOf (smSendInputs g m).files)
        else
          observe (smSendInputs g m).files (smSendModel P.C g m))) ∧
    (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams P.C) g →
      c.length < 2 ^ 32 →
      CliRunsToUnderExterns elf ext (smRecvInputs g c rc)
        (if (msgTypeWhisper :: c).length > stdinCapBytes then
          .exited 2 [] (filesOf (smRecvInputs g c rc).files)
        else
          observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc)))

/-- The SM-mode statement under every extern table that meets its contracts: `bytes` parse as
an ELF that meets `CliBinaryCorrectExt`. -/
def LibsignalCliBinaryCorrectExt (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliBinaryCorrectExt elf

/-- The CLI's ELF `elf` meets the PQXDH-mode specs under every extern table that meets its
contracts and `CliAllocNeverFailsPqWith`. -/
def CliPqBinaryCorrectExt (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
    CliExternsOk P A ext → CliAllocNeverFailsPqWith elf P ext →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunAbortOnPanicUnderExterns elf ext) X P ∧ CliSpecPqxdhNoMatch (cliRunAbortOnPanicUnderExterns elf ext) X P

/-- The PQXDH-mode statement under every extern table that meets its contracts: `bytes` parse
as an ELF that meets `CliPqBinaryCorrectExt`. -/
def LibsignalCliPqBinaryCorrectExt (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqBinaryCorrectExt elf

end CryptoVerification.SignalSession
