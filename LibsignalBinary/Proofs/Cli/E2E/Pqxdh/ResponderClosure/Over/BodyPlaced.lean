/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon

/-!
# Relocatable Overwrite Responder Closure Body

Relocatable `[LibsignalPlacement]` counterpart of `ClosureOver` on the `get_NoMatch` overwrite
path of `decrypt_prekey`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record.Serialization (CanonSession encSessionMem_eq_of_canon)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession

theorem encSessionMem_clearPending_eq_placed [LibsignalPlacement]
    {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : CanonSession G s) :
    CryptoVerification.E2E.Record.Serialization.encSessionMem
      (clearPendingGhost G) (clearPending s) =
      CryptoVerification.E2E.Record.encSession (clearPending s) :=
  encSessionMem_clearPending_eq h

theorem scopeIn_clearPending_placed [LibsignalPlacement]
    {s : Session (List (BitVec 8))} (h : Cli.Slots.scopeIn ⟨some s⟩) :
    Cli.Slots.scopeIn ⟨some (clearPending s)⟩ :=
  scopeIn_clearPending h

theorem overPrevEncOK_clearPending_of_scopeIn_placed [LibsignalPlacement]
    {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) (hver : s.state.sessionVersion = 4#32) :
    OverPrevEncOK (CryptoVerification.E2E.Record.encSession (clearPending s)) :=
  overPrevEncOK_clearPending_of_scopeIn h hver

theorem lenField2_clearPending_length_lt_placed [LibsignalPlacement]
    {s : Session (List (BitVec 8))} (h : Cli.Slots.scopeIn ⟨some s⟩) :
    (CryptoVerification.E2E.Record.lenField 2
      (CryptoVerification.E2E.Record.encSession (clearPending s))).length <
      2 ^ 31 + 2 ^ 21 + 40 :=
  lenField2_clearPending_length_lt h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
end
