/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable I/O Call-Site Helpers for `main` (Block `617`)

Projects relocatable `subroutine_ok` contracts for `read_stdin`, `read_file`, `write_file`, and
`write_stdout` on Block `617` (`mProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

theorem main_readStdin_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlaced A H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced io A hookStack)) :=
  hio.readStdin

theorem main_readFile_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlaced A H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced io A hookStack)) :=
  hio.readFile

theorem main_writeFile_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlaced A H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlaced io hookStack)) :=
  hio.writeFile

theorem main_writeStdout_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {io : IoModel} {hookStack : Nat}
    (hio : MainIoPlaced A H io hookStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced hookStack)) :=
  hio.writeStdout

end CryptoVerification.SignalSession.Cli.MainHops
