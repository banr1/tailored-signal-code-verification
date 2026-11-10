/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# Weak SPQR hypotheses: send totality and salt binding

**Checked by Lean.**

Reachable-invariant hypotheses on SPQR (`SpqrWeakCorrect`: send totality and salt binding)
weakening `Corr.SpqrOffCorrect` (DEV-LS24) for the H1 session refinement.
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSM.Corr

open LibsignalSession

variable {PQ PQC : Type}

/-- Closure of an SPQR state predicate `Inv` under `init`, successful `send`, and successful `recv`. -/
structure SpqrInvClosed (S : Spqr PQ PQC) (Inv : PQ → Prop) : Prop where
  init : ∀ dir k, Inv (S.init dir k)
  send : ∀ st r st' salt msg, Inv st → S.send st r = some (st', salt, msg) → Inv st'
  recv : ∀ st msg st' salt, Inv st → S.recv st msg = .ok (st', salt) → Inv st'

/-- `S.send` succeeds on every `Inv`-state and coin value (needed for adapter send recording,
DEV-LS17, under adversary-chosen coins, DEV-LS1, and 64-byte SPQR tapes, DEV-SPQR5). -/
def SpqrSendTotalOn (S : Spqr PQ PQC) (Inv : PQ → Prop) : Prop :=
  ∀ st r, Inv st → (S.send st r).isSome

/-- Any `Inv`-state accepting an honest message produced from an `Inv`-state returns the sender's
salt. -/
def SpqrSaltBindingOn (S : Spqr PQ PQC) (Inv : PQ → Prop) : Prop :=
  ∀ st r st' salt msg, Inv st → S.send st r = some (st', salt, msg) →
    ∀ st₂ st₂' salt₂, Inv st₂ → S.recv st₂ msg = .ok (st₂', salt₂) → salt₂ = salt

/-- Existence of a closed invariant `Inv` satisfying `SpqrSendTotalOn` and `SpqrSaltBindingOn`. -/
def SpqrWeakCorrect (S : Spqr PQ PQC) : Prop :=
  ∃ Inv : PQ → Prop, SpqrInvClosed S Inv ∧ SpqrSendTotalOn S Inv ∧ SpqrSaltBindingOn S Inv

end LibsignalSM.Corr
end CryptoGames
