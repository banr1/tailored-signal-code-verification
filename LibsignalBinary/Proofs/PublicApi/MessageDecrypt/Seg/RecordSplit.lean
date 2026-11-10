/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs

/-!
# `MessageDecrypt` Record-Split Bridge (`RecordSplit`)

Pure separation-logic bridge splitting `sessionRecordAt A r g rec` with `rec.currentSession = some s`
and `g.cur = some G` into the `previous_sessions` header cells, `prevBufAt`, `⌜sessionModelRel G s⌝`,
and `sessionStateAt A (r + 0x18) G s.state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.RecordSplit

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

theorem sessionRecordAt_eq_of_some (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))) (G : SessionGhost)
    (hrec : rec.currentSession = some s) (hg : g.cur = some G) :
    sessionRecordAt A r g rec =
      (⌜sessionModelRel G s⌝ ∗ (r ↦₆₄ g.prevCap) ∗ prevBufAt A g.prevCap g.prevPtr ∗
        ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (r + 0x18#64) G s.state) := by
  unfold sessionRecordAt
  rw [hrec, hg]
  dsimp only
  rw [sessionAt_eq]
  unfold vecAt vecHeader prevBufAt
  simp only [List.length_nil]
  ac_rfl

theorem recordSplit_ok : RecordSplit := by
  intro A r g rec s G hrec hg
  rw [sessionRecordAt_eq_of_some A r g rec s G hrec hg]
  exact Entails.refl _

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

theorem recordSplit_placed_ok [LibsignalPlacement] : RecordSplit :=
  recordSplit_ok

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.RecordSplit
