/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.Hooks
public import LibsignalBinary.Proofs.E2E.V1.Scope
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements

/-!
# In-memory public entry specifications and invariants for SPQR V1

Defines the generic post-quantum state invariant `PqInv`, store record invariant `InMemRecOkP`,
hook/environment bundles `BinHooksV1` and `BinEnvV1`, and public entry specs `inMemEncryptSpecV1`
and `inMemDecryptSignalSpecV1`.

Because the 32-bit length ceiling `< 2 ^ 32` required by the triple-ratchet contracts (DEV-SPQR3:
`otrEncryptSpecT`, `tryDecryptSpecT`) is not by itself closed under `spqrV1` send/receive steps,
these specifications parameterize over an arbitrary predicate `Pq : List (BitVec 8) → Prop`
satisfying `PqInv S Pq` (implying `< 2 ^ 32`, closed under `S.send` and `S.recv`, and bounding
emitted PQ ratchet messages to `≤ 2 ^ 30` bytes).
-/

@[expose] public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Bin
open CryptoVerification.LibsignalSpqrV1 (TokenInit otrEncryptSpecT tryDecryptSpecT)

/-! ## Post-quantum state invariant `PqInv` -/

/-- `Pq` is closed under `S.send`. -/
def SendClosed (S : SpqrModel) (Pq : List (BitVec 8) → Prop) : Prop :=
  ∀ st rest st' salt pm, Pq st → S.send st rest = some (st', salt, pm) → Pq st'

/-- `Pq` is closed under `S.recv` (on `Ok`). -/
def RecvClosed (S : SpqrModel) (Pq : List (BitVec 8) → Prop) : Prop :=
  ∀ st msg st' salt, Pq st → S.recv st msg = .ok (st', salt) → Pq st'

/-- On a `Pq` state, `S.send` emits a PQ ratchet message of at most `2 ^ 30` bytes. -/
def SendMsgBoundOn (S : SpqrModel) (Pq : List (BitVec 8) → Prop) : Prop :=
  ∀ st rest st' salt pm, Pq st → S.send st rest = some (st', salt, pm) → pm.length ≤ 2 ^ 30

/-- Closure and length-bound conditions on a post-quantum state invariant `Pq` under `S`. -/
structure PqInv (S : SpqrModel) (Pq : List (BitVec 8) → Prop) : Prop where
  bound : ∀ st, Pq st → st.length < 2 ^ 32
  send : SendClosed S Pq
  recv : RecvClosed S Pq
  msg : SendMsgBoundOn S Pq

/-- Every current session in `r` has its `pqRatchetState` satisfying `Pq`. -/
def RecordPqP (Pq : List (BitVec 8) → Prop) (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → Pq s.state.pqRatchetState

/-- Store-side record invariant replacing `RecordPqStateLengthBelow2Pow32` in `InMemRecOkV1` with `RecordPqP Pq`. -/
def InMemRecOkP (Pq : List (BitVec 8) → Prop) (r : SessionRecord (List (BitVec 8))) : Prop :=
  Record.RecordInScope r ∧ RecordPqP Pq r ∧ r.currentSession.isSome

/-- At `Pq := (·.length < 2 ^ 32)`, `InMemRecOkP Pq` coincides with `InMemRecOkV1`. -/
theorem inMemRecOkP_lt_eq : InMemRecOkP (fun st => st.length < 2 ^ 32) = InMemRecOkV1 := rfl

/-- Projects `InMemRecOkP Pq` to `InMemRecOkV1` given `∀ st, Pq st → st.length < 2 ^ 32`. -/
theorem InMemRecOkP.toV1 {Pq : List (BitVec 8) → Prop} {r : SessionRecord (List (BitVec 8))}
    (h : InMemRecOkP Pq r) (hB : ∀ st, Pq st → st.length < 2 ^ 32) : InMemRecOkV1 r :=
  ⟨h.1, fun s hs => hB _ (h.2.1 s hs), h.2.2⟩

theorem recordPqP_some {Pq : List (BitVec 8) → Prop} {s : Session (List (BitVec 8))} :
    RecordPqP Pq ⟨some s⟩ ↔ Pq s.state.pqRatchetState := by
  constructor
  · intro h
    exact h s rfl
  · intro h s' hs'
    cases hs'
    exact h

/-! ## Hooks and environment -/

/-- Hook bundle for the wrapper binary at SPQR V1 (`BinHooks` without `emptyOk`). -/
structure BinHooksV1 (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop extends PublicApiHooksNoStores C A S abs where
  bcmp : HookSat abs bcmpName e2eBcmpSpec
  randomKeys : HookSat abs randomKeysName randomKeysSpec
  hashbrownBin : ∀ ctl,
    CryptoVerification.E2E.InMem.HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))
  alloc_eq : A = CryptoVerification.E2E.Record.A0
  tpidrSafe : ∀ n f, abs n = some f → ∀ s,
    (f s).tpidrEl0 = s.tpidrEl0 ∧ ∀ a, ((f s).mem.perm a).x → (s.mem.perm a).x

theorem _root_.CryptoVerification.E2E.Bin.BinHooks.toV1 {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)} (h : BinHooks C A S abs) : BinHooksV1 C A S abs where
  toPublicApiHooksNoStores := h.toPublicApiHooksNoStores
  bcmp := h.bcmp
  randomKeys := h.randomKeys
  hashbrownBin := h.hashbrownBin
  alloc_eq := h.alloc_eq
  tpidrSafe := h.tpidrSafe

/-- Binary execution environment at SPQR V1, combining `BinHooksV1` with the `OTR::encrypt`
(`otrEncryptSpecT`) and `try_decrypt_with_state` (`tryDecryptSpecT`) contracts. -/
structure BinEnvV1 (C : Crypto) (A : RustAlloc) (S : SpqrModel) (img : Obj.Image)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : BinHooksV1 C A S abs
  otrEnc : subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrEncryptName)
    (otrEncryptSpecT C A ctl uuidTryParse S img)
  tryDec : subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
    (tryDecryptSpecT C A ctl uuidTryParse S img)

/-! ## V1 in-memory public entry specifications -/

end CryptoVerification.E2E.V1
