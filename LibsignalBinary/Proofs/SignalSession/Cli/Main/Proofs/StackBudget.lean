/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Stack Budget Constants for `main`

Concrete stack-budget witnesses discharging `hstk` and `hstk64` for `main_ok`:
* `cliMainStk = 8,371,776` B: zeroed RW stack below `sm.sp` at `main` entry (8,371,824 B below
  `sp0` on the 8 MiB stack under `ArgvFitsInitialStack` (DEV-CLI7), minus musl's 48 B entry frame).
* `cliHookStack = extHookStack` (16,384 B): stack budget for hook-modeled callees.
* `cliResStack = cliMainStk - mainFrameSize` (8,370,528 B): stack available below `main`'s
  1,248 B frame for `run` and in-image callees (which require at most `16,560` B).
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.MainHops

open CryptoVerification.LibsignalTripleRatchet

/-- Zeroed RW stack bytes below `sm.sp` at `main` entry (`8,371,824` B below `sp0` minus musl's 48 B entry frame). -/
abbrev cliMainStk : Nat := 8371824 - 48

/-- Stack budget for `main`'s hook-modeled callees (`strlen`, `from_utf8`, and `MainIo`). -/
abbrev cliHookStack : Nat := extHookStack

/-- Stack budget below `main`'s 1,248 B frame for `run` and in-image callees. -/
abbrev cliResStack : Nat := cliMainStk - mainFrameSize

theorem cliMainStk_eq : cliMainStk = 8371776 := rfl

theorem mainFrameSize_eq : mainFrameSize = 1248 := rfl

theorem cliHookStack_eq : cliHookStack = 16384 := rfl

theorem cliResStack_eq : cliResStack = 8370528 := rfl

theorem cli_hstk :
    mainFrameSize + max (max extHookStack cliHookStack) cliResStack ≤ cliMainStk := by
  decide

theorem cli_hstk64 : cliMainStk ≤ 2 ^ 63 := by
  decide

theorem cli_stk_outcome : 48 ≤ cliMainStk ∧ cliMainStk ≤ 2 ^ 64 := by
  decide

/-- Discharges the stack-budget side conditions of `tryAllocateIn3` (`16,432` B), `reserve1`/`reserve16` (`16,496` B), and `ProtocolAddress::new` (`16,560` B) at `cliResStack`. -/
theorem cli_resStack_callees :
    finishGrowStackX ≤ cliResStack ∧ doReserveStackX ≤ cliResStack ∧
      0xB0 + extHookStack ≤ cliResStack ∧ cliResStack ≤ 2 ^ 63 := by
  decide

end CryptoVerification.SignalSession.Cli.MainHops
