/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs

/-!
# `MessageDecrypt` Record-Join Bridge (`RecordJoin`)

Pure separation-logic bridge reassembling `sessionRecordAt` after `G.AfterRecordDecrypt G'` with
`pendingPreKey := none` and `pendingKyberPreKey := none`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.RecordJoin

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

theorem sessionModelRel_of_recordOkRel {G G' : SessionGhost} {s : Session (List (BitVec 8))}
    {st' : SessionState (List (BitVec 8))}
    (hw0 : sessionModelRel G s) (hok : G.AfterRecordDecrypt G') :
    sessionModelRel G' { s with state := st', pendingPreKey := none, pendingKyberPreKey := none } := by
  rcases hw0 with ⟨_, _, halice, hrem, hloc⟩
  rcases hok with ⟨_, _, halice', hreg', hpend', hkyb'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hpend', PendingRel]
  · simp [hkyb', KyberRel]
  · exact halice'.trans halice
  · rw [hreg']
    exact hrem
  · rw [hreg']
    exact hloc

theorem sessionRecordAt_join_eq (A : RustAlloc) (r cap ptr : BitVec 64) (G' : SessionGhost)
    (s' : Session (List (BitVec 8))) :
    sessionRecordAt A r { prevCap := cap, prevPtr := ptr, cur := some G' }
        { currentSession := some s' } =
      (⌜sessionModelRel G' s'⌝ ∗ (r ↦₆₄ cap) ∗ prevBufAt A cap ptr ∗
        ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (r + 0x18#64) G' s'.state) := by
  unfold sessionRecordAt
  dsimp only
  rw [sessionAt_eq]
  unfold vecAt vecHeader prevBufAt
  simp only [List.length_nil]
  ac_rfl

theorem recordJoin_ok : RecordJoin := by
  intro A r cap ptr G G' s st' hw0 hok
  let s' : Session (List (BitVec 8)) :=
    { s with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hw0' : sessionModelRel G' s' := sessionModelRel_of_recordOkRel hw0 hok
  refine Entails.sepExists_right { prevCap := cap, prevPtr := ptr, cur := some G' } ?_
  rw [sessionRecordAt_join_eq A r cap ptr G' s']
  exact Entails.pure_right hw0' (Entails.refl _)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

theorem recordJoin_placed_ok [LibsignalPlacement] : RecordJoin :=
  recordJoin_ok

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.RecordJoin
