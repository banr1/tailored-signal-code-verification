/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionObj
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import LibsignalBinary.Specifications.SignalSession.SmDir

@[expose] public section

set_option autoImplicit false

/-!
# Fixed-Image Session-Management CLI Specification

**Checked by Lean.** Fixed-image binary-level correctness predicates for the `signal-session`
ARM64 ELF in session-management (SM) mode against `CliSpecE` (`SmDir.lean`), together with the
ELF-to-image code match `CliElfCodeMatches` at `cliBase`.

Execution runs `cliProgAbortOnPanic W` from `cliTokenPatch s0` (post-CPU-probe state, DEV-CLI10)
under `CliAllocNeverFails` (DEV-CLI9) and trusted extern hooks (including the bump allocator,
DEV-E6). Machine-model and extern-boundary deviations (`DEV-M6`, `DEV-M7`, `DEV-M11`, `DEV-E1`,
`DEV-E7`) are catalogued in `LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E

/-! ## Allocation Hypothesis -/

/-- **DEV-CLI9 (machine model): no allocation of the CLI's run fails.** On every SM-mode `send` and
`recv` input in `CliSpecE`'s domain, no state reached by `elf` under `cliProgAbortOnPanic W` from
`cliTokenPatch s0` (DEV-CLI10) logs `allocFailedEvent` (emitted on `E2E.allocFail` and
`E2E.allocPanicHook`). Assumed per `(elf, W)` because an end-to-end heap bound from `loadState` to
`exit_group` is not proved (DEV-CLI9). -/
def CliAllocNeverFails (elf : ElfImage) (W : CliHooks) : Prop :=
  (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smSendInputs g m)) = .ok s0 →
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace) ∧
  (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams W.C) g →
    c.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smRecvInputs g c rc)) = .ok s0 →
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace)

/-! ## ELF-to-Image Code Match -/

/-- The five libc extern stubs excused from `CliElfCodeMatches` so a `--branch-stubs` link to musl
requires no specification change. Under `--stubs zero` these words are `0` (matching
`libsignalSessionImage`); four are hooked in `cliHookTable`, while unhooked `memcmp` decodes to
`udf #0` and halts if reached. -/
def cliBranchStubNames : List String := ["memcpy", "memset", "memmove", "memcmp", "bcmp"]

/-- Byte offset `k` falls within the 4-byte stub slot of a symbol in `cliBranchStubNames`. -/
def InCliBranchStub (k : Nat) : Prop :=
  ∃ n ∈ cliBranchStubNames, ∃ off, libsignalSessionImage.toProgram.stubs.lookup n = some off ∧
    off ≤ k ∧ k < off + 4

/-- Loaded memory of `elf` maps every byte of `libsignalSessionImage.toProgram.code` read-execute at
`cliBase + k` with identical byte values outside `InCliBranchStub`. -/
def CliElfCodeMatches (elf : ElfImage) : Prop :=
  ∀ (i : Inputs) (s0 : State), elf.loadState (cliProcessInputs i) = .ok s0 →
    ∀ (k : Nat) (hk : k < libsignalSessionImage.toProgram.code.length),
      s0.mem.perm (cliBase + BitVec.ofNat 64 k) = some Perm.rx ∧
      (¬ InCliBranchStub k →
        s0.mem.read8 (cliBase + BitVec.ofNat 64 k) = libsignalSessionImage.toProgram.code[k])

/-! ## Whole-Process Specification -/

/-- Whole-process SM-mode correctness of `elf`: `CliElfCodeMatches elf` holds, and for every `W`
satisfying `CliAllocNeverFails elf W` (DEV-CLI9), every `send` and `recv` input in `CliSpecE`'s
domain terminates under `CliRunsTo` with the `CliSpecE` outcome. -/
def CliBinaryCorrect (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ W : CliHooks, CliAllocNeverFails elf W →
    (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
      CliRunsTo elf W (smSendInputs g m)
        (if m.length > stdinCapBytes then
          .exited 2 [] (filesOf (smSendInputs g m).files)
        else if m.length > maxPlaintextBytes then
          .exited 1 [] (filesOf (smSendInputs g m).files)
        else
          observe (smSendInputs g m).files (smSendModel W.C g m))) ∧
    (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams W.C) g →
      c.length < 2 ^ 32 →
      CliRunsTo elf W (smRecvInputs g c rc)
        (if (msgTypeWhisper :: c).length > stdinCapBytes then
          .exited 2 [] (filesOf (smRecvInputs g c rc).files)
        else
          observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc)))

/-- Bytes `bytes` parse via `ElfImage.parse` into an ELF image satisfying `CliBinaryCorrect`. -/
def LibsignalCliBinaryCorrect (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliBinaryCorrect elf

end CryptoVerification.SignalSession
