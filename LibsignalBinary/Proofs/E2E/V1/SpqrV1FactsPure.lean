/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure

/-!
# Pure SPQR V1 send-message length bounds

**Checked by Lean.** Machine-free bounds on serialized SPQR V1 messages: every message produced by
`(spqrV1 F K).send` has length `≤ 64` bytes (`spqrV1Send_msg_len_le`), and hence `≤ 2 ^ 30` bytes
under `spqrV1SessionUniformCoins` (`spqrV1Send_pqRatchet_len_le`).
-/

@[expose] public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Top.Send

/-- Every message of a successful `sendAfterStates` is `D.msgSerialize msg index` for some index. -/
theorem sendAfterStates_msg_eq (D : SpqrApiDeps) (hkdf : HkdfFn)
    (statePb : PqRatchetStatePB D.V1StatePB) (msg : D.MessageV1) (key : Option EpochSecret)
    (state : D.States) {s : Send} (h : sendAfterStates D hkdf statePb msg key state = .ok s) :
    ∃ index, s.msg = D.msgSerialize msg index := by
  rw [sendAfterStates_eq_bind_sendChainPhase] at h
  rcases hc : sendChainPhase hkdf statePb.chain statePb.versionNegotiation key (D.msgEpoch msg) with
    e | ⟨index, msgKey, chainPb⟩
  · rw [hc] at h
    cases h
  · rw [hc] at h
    dsimp only at h
    refine ⟨index, ?_⟩
    rcases hser : D.msgSerialize msg index with _ | ⟨b0, tl⟩
    · rw [hser] at h
      cases h
    · rw [hser] at h
      dsimp only at h
      split at h
      · cases h
      · cases h
        rfl

/-- Every PQ ratchet message returned by `(spqrV1 F K).send` has length at most 64 bytes. -/
theorem spqrV1Send_msg_len_le (F : ShaCompress) (K : MlKem) (st tape : List (BitVec 8))
    (st' : List (BitVec 8)) (salt : Salt) (pm : List (BitVec 8))
    (h : (spqrV1 F K).send st tape = some (st', salt, pm)) : pm.length ≤ 64 := by
  rw [spqrV1_send_eq] at h
  simp only [toSpqrModel] at h
  rcases hs : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) st tape).1 with e | s
  · rw [hs] at h
    cases h
  · rw [hs] at h
    dsimp only at h
    rcases hk : messageKeyToSalt? s.key with _ | salt'
    · rw [hk] at h
      cases h
    · rw [hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      unfold LibsignalSpqrV1.send at hs
      split at hs
      · cases hs
      · split at hs
        · simp only [Except.ok.injEq] at hs
          subst hs
          simp
        · split at hs
          · cases hs
          · split at hs
            split at hs
            · simp at hs
            · dsimp only at hs
              obtain ⟨index, hidx⟩ := sendAfterStates_msg_eq _ _ _ _ _ _ hs
              rw [hidx]
              exact message_serialize_length_le _ index

/-- Every PQ ratchet message returned by `(spqrV1SessionUniformCoins F K).send` has length `≤ 2 ^ 30` bytes. -/
theorem spqrV1Send_pqRatchet_len_le (F : ShaCompress) (K : MlKem) (st : List (BitVec 8))
    (r : BitVec 512) (pq' : List (BitVec 8)) (key : Salt) (pm : List (BitVec 8))
    (h : (spqrV1SessionUniformCoins F K).send st r = some (pq', key, pm)) : pm.length ≤ 2 ^ 30 := by
  have := spqrV1Send_msg_len_le F K st (coinBytes r) pq' key pm h
  omega


end CryptoVerification.E2E.V1
