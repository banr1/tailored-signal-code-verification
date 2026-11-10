/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.Record
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP

/-!
# `Q`-Generalized Session Record Scopes and `recordDeserializeOpenSpec_Q`

Generalizes `RecordPqEmpty`, `InScopeP`, `DeserializeScopeP`, `RecordCanonical`, and
`recordDeserializeOpenSpec` to an arbitrary SPQR state predicate `Q : List (BitVec 8) → Prop`,
together with `NonEmptyV1Q` (`st.length < 2 ^ 32`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3Defs

open Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.RecordX

/-! ## Non-empty SPQR V1 state predicate -/

/-- Non-empty SPQR V1 state predicate: `Q st ↔ st.length < 2^32`. -/
abbrev NonEmptyV1Q : List (BitVec 8) → Prop :=
  fun st => st.length < 2 ^ 32

/-! ## `Q`-generalized session record scopes and deserialize contract -/

/-- `RecordPqEmpty` generalized to an arbitrary SPQR state predicate `Q`. -/
abbrev RecordScopeP (Q : List (BitVec 8) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → Q s.state.pqRatchetState

/-- `RecordX.InScopeP` generalized from `RecordPqEmpty` to `RecordScopeP Q`. -/
def InScopeP_Q (Q : List (BitVec 8) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  RecordInScopeP r ∧ RecordScopeP Q r ∧ RecordRepr r

/-- `RecordX.DeserializeScopeP` generalized from `RecordPqEmpty` to `RecordScopeP Q`. -/
def DeserializeScopeP_Q (Q : List (BitVec 8) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  InScopeP_Q Q r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeP s

/-- `WireEntries.RecordCanonical` generalized from `DeserializeScopeP` (`RecordPqEmpty`)
to `DeserializeScopeP_Q Q` (`RecordScopeP Q`). -/
def RecordCanonical_Q (Q : List (BitVec 8) → Prop)
    (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = Record.encodeRecord ⟨some s⟩ ∧
  DeserializeScopeP_Q Q ⟨some s⟩ ∧
  ∃ G : SessionGhost, BinCanonSession G s

/-- `WireEntries.recordDeserializeOpenSpec` generalized from `RecordCanonical`
to `RecordCanonical_Q Q`. -/
def recordDeserializeOpenSpec_Q (Q : List (BitVec 8) → Prop) (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) where
  pre := fun (ptr, bs, out, sess) st =>
    ⌜st.readReg64 .x0 = ptr ∧ (st.readReg64 .x1).toNat = bs.length ∧
      st.readReg64 .x8 = out ∧ RecordCanonical_Q Q bs sess⌝ ∗
      (ptr ↦ₛ bs) ∗ memRegion out 0x170 ∗ A.pool ∗ stackAt st.sp recordDeserializeStack
  post := fun (ptr, bs, out, sess) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ bs) ∗
      (∃∗ G : SessionGhost, ⌜BinCanonSession G sess⌝ ∗
        sessionRecordAt A out ⟨0#64, 8#64, some G⟩ ⟨some sess⟩) ∗
      A.pool ∗ stackAt s0.sp recordDeserializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end Symbolic.Swarm.TRREF.B3Defs
