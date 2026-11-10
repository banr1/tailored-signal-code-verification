/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `ChainClone3OkPlaced` Wrappers (Block `524`)

Defines `ChainClone3OkPlaced` and `SenderChainClone3OkPlaced` on Block `524` (`blkPC_524` /
`blkPl_524`, `lsmpl.base 524`) and discharges them from `HookSat` hypotheses.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.Cli.LibsignalE2E.Pqxdh.Reloc.ChainClone4

/-- `[LibsignalPlacement]` counterpart of `ChainClone3OkExt` at Block `524`
(`<SessionStructure_Chain as Clone>::clone [local#5]`). -/
def ChainClone3OkPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsmpl.base 524) (chainCloneSpec A)

/-- `[LibsignalPlacement]` counterpart of `SenderChainClone3OkExt` at Block `524`
(`<SessionStructure_Chain as Clone>::clone [local#5]`). -/
def SenderChainClone3OkPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsmpl.base 524) (senderChainCloneSpec A)

theorem chainClone3_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ChainClone3OkPlaced A H :=
  chain_clone_placed_ok hshim halloc hmemcpy hpanic

theorem senderChainClone3_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    SenderChainClone3OkPlaced A H :=
  senderChain_clone_placed_ok hshim halloc hmemcpy hpanic

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
