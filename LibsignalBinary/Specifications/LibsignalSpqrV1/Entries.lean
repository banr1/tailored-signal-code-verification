/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks

/-!
# SPQR V1: store load contract with bounded post-quantum state

**Checked by Lean.** No theorem of `Computational/Theorems/` uses anything from this file (see
`Computational/docs/TRUSTED_BASE.md`). Defines `loadSessionSpecPqStateLengthBound` (strengthening
`loadSessionSpec` with `RecordPqStateLengthBelow2Pow32`), which supplies the `< 2^32`-byte
post-quantum state bound (DEV-SPQR3) at the session-store boundary.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi

/-- The loaded record's current session, if any, has a post-quantum state shorter than `2^32` bytes
(DEV-SPQR3; the SPQR-off analogue is `RecordPqEmpty`). -/
def RecordPqStateLengthBelow2Pow32 (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → s.state.pqRatchetState.length < 2 ^ 32

/-- `load_session` contract of an SPQR V1 store: `loadSessionSpec` strengthened with
`RecordPqStateLengthBelow2Pow32` on `Ok(Some r)`. -/
def loadSessionSpecPqStateLengthBound (A : RustAlloc)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec LoadCall where
  pre := (loadSessionSpec A encRecord).pre
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
      ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (loadClass ans) ∧
        sf.trace = s0.trace ++ [loadEvent encRecord x.addr.val ans]⌝ ∗
      (match ans with
       | .ok (some r) =>
         ⌜RecordInScope r ∧ RecordPqStateLengthBelow2Pow32 r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A x.out g r
       | _ => memRegion x.out 368) ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp storeHookStack

end CryptoVerification.LibsignalSpqrV1
