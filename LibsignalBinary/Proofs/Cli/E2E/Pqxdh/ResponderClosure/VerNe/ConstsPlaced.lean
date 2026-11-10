/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Version-Mismatch Closure Constants

Relocatable (`[LibsignalPlacement]`) program, entry address (Block `518`), and `.bss` log-filter
cell for `message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Program of Block `518` (`message_decrypt_prekey::<Coins>::{closure#0}`). -/
abbrev verNeProgPlaced [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  lsProg_518 ext

abbrev verNeEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  (blkPl_518).base

theorem verNeEntryPlaced_eq_lsmpl_base [LibsignalPlacement] :
    verNeEntryPlaced = lsmpl.base 518 := rfl

/-- Relocatable `.bss` `MAX_LOG_LEVEL_FILTER` 8-byte zero cell (`lsLogFilterAddr ↦₆₄ 0#64`). -/
def pqLogLevelCellPlaced [LibsignalPlacement] : SepProp :=
  lsLogFilterAddr ↦₆₄ 0#64

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
end
