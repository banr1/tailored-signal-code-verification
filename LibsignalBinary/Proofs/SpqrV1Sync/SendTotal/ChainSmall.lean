/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

set_option autoImplicit false

/-!
# Receive-History Size Preservation Under Chain Constructors

Proves that `chainFromVersionNegotiation`, `Chain.addEpoch`, and `Chain.sendKey` preserve
`RecvSmall`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoGames.LibsignalSession (ShaCompress)

private theorem clearSendNextPrefix_recvSmall :
    ∀ (n : ℕ) (xs : List ChainEpoch),
      (∀ l ∈ xs, l.recv.prev.data.length < 2 ^ 20) →
      ∀ l ∈ Chain.clearSendNextPrefix n xs, l.recv.prev.data.length < 2 ^ 20
  | 0, _, hxs => hxs
  | _ + 1, [], hxs => hxs
  | n + 1, x :: xs, hxs => by
    intro l hl
    simp only [Chain.clearSendNextPrefix, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hxs x (List.mem_cons.mpr (Or.inl rfl))
    · exact clearSendNextPrefix_recvSmall n xs
        (fun y hy => hxs y (List.mem_cons.mpr (Or.inr hy))) l hl

/-- `Chain.addEpoch` preserves `RecvSmall`. -/
theorem st_recvSmallAdd : RecvSmallAddStmt := by
  intro hkdf ch ch' es hsmall hadd
  unfold Chain.addEpoch at hadd
  split at hadd
  · nomatch hadd
  · split at hadd
    · nomatch hadd
    · cases hadd
      intro l hl
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact hsmall l hl
      · simp [Chain.cedForDirection, ChainEpochDirection.new, KeyHistory.new]

/-- `Chain.sendKey` preserves `RecvSmall`. -/
theorem st_recvSmallSend : RecvSmallSendStmt := by
  intro hkdf ch ch' e out hsmall hsend
  unfold Chain.sendKey at hsend
  split at hsend
  · nomatch hsend
  · cases hep : ch.epochIdx e with
    | error _ => rw [hep] at hsend; nomatch hsend
    | ok epochIndex0 =>
      rw [hep] at hsend
      dsimp only [ChainResult.ofError, Bind.bind, Except.bind, Pure.pure, Except.pure] at hsend
      by_cases hne : (ch.sendEpoch != e) = true
      · simp only [hne, ↓reduceIte] at hsend
        have hsmall2 : ∀ l ∈ Chain.clearSendNextPrefix
            (epochIndex0 - (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
            (ch.links.drop (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH)),
            l.recv.prev.data.length < 2 ^ 20 :=
          clearSendNextPrefix_recvSmall _ _ (fun y hy => hsmall y (List.mem_of_mem_drop hy))
        split at hsend
        · nomatch hsend
        · rename_i link hget
          split at hsend
          · nomatch hsend
          · cases hsend
            intro l hl
            rcases List.mem_or_eq_of_mem_set hl with hl_old | rfl
            · exact hsmall2 l hl_old
            · exact hsmall2 link (List.mem_of_getElem? hget)
      · simp only [Bool.not_eq_true] at hne
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hsend
        split at hsend
        · nomatch hsend
        · rename_i link hget
          split at hsend
          · nomatch hsend
          · cases hsend
            intro l hl
            rcases List.mem_or_eq_of_mem_set hl with hl_old | rfl
            · exact hsmall l hl_old
            · exact hsmall link (List.mem_of_getElem? hget)

end CryptoVerification.SpqrV1Sync.SendTotal
