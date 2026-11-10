/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelDefs
public import ProofLib.Lemmas
import LibsignalBinary.Proofs.ConsumeMessageKey.ModelProofs.AdvanceAndFrame
import LibsignalBinary.Proofs.ConsumeMessageKey.ModelProofs.PastAndTooFar

/-!
# Closed-Form Equations for `RatchetState.consumeMessageKey`

Relates the monadic session-model `RatchetState.consumeMessageKey` to closed-form expressions over
`chainStepN`, `skippedKeys`, and `ChainsOk` for the past-counter, too-far, advance, and panic paths.
-/

@[expose] public section

namespace CryptoVerification.SessionModel

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

/-- Past-counter case (`c < ck.index`): removes and returns the matching stored key, or returns
`DuplicatedMessage` with unchanged state if absent. -/
theorem consumeMessageKey_past (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (h : c < ck.index) :
    (RatchetState.consumeMessageKey F their ck c t).exec st =
      match st.findReceiverChainIndex their with
      | none => (.error (.duplicatedMessage ck.index c), st)
      | some ci =>
        match (st.receiverChains[ci]?.map fun ch =>
            (ch, ch.messageKeys.findIdx? (fun k => k.counter == c))) with
        | some (ch, some p) =>
          match ch.messageKeys[p]? with
          | some k =>
            (.ok k, { st with
              receiverChains := st.receiverChains.set ci { ch with messageKeys := ch.messageKeys.eraseIdx p } })
          | none => (.error .panic, st)
        | _ => (.error (.duplicatedMessage ck.index c), st) := by
  exact PastAndTooFar.consumeMessageKey_past_aux F st their ck c t h

/-- Too-far case (`st.maxForwardJumps < (c - ck.index).toNat`): returns `InvalidMessage` with unchanged state. -/
theorem consumeMessageKey_tooFar (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (h : ck.index ≤ c)
    (hj : st.maxForwardJumps < (c - ck.index).toNat) :
    (RatchetState.consumeMessageKey F their ck c t).exec st =
      (.error (.invalidMessage t .tooFarInFuture), st) := by
  exact PastAndTooFar.consumeMessageKey_tooFar_aux F st their ck c t h hj

/-- Advance case (`ck.index ≤ c ≤ ck.index + st.maxForwardJumps`, `c ≠ u32::MAX`, chain present):
prepends `c - ck.index` skipped keys (truncated to 2000), advances the chain key past `c`, and
returns the message key at `c`. -/
theorem consumeMessageKey_advance (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (hc : c ≠ BitVec.allOnes 32)
    (h : ck.index ≤ c) (hj : (c - ck.index).toNat ≤ st.maxForwardJumps)
    (ci : ℕ) (hci : st.findReceiverChainIndex their = some ci) (hok : ChainsOk st) :
    ∃ ch, st.receiverChains[ci]? = some ch ∧
    (RatchetState.consumeMessageKey F their ck c t).exec st =
      let n := (c - ck.index).toNat
      let ckc := chainStepN F n ck
      (.ok (ckc.messageKeys F),
        { st with
          receiverChains := st.receiverChains.set ci
            ({ ch with
                messageKeys := (skippedKeys F n ck ++ ch.messageKeys).take maxMessageKeys
                chainKey := some (chainStepN F 1 ckc) }) }) := by
  exact AdvanceAndFrame.consumeMessageKey_advance_thm F st their ck c t hc h hj ci hci hok

/-- `consumeMessageKey` panics (when `ck.index ≤ c` within `maxForwardJumps`) iff `c = u32::MAX` or
no matching receiver chain exists. -/
theorem consumeMessageKey_panic_iff (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) :
    ((RatchetState.consumeMessageKey F their ck c t).exec st).1 = .error .panic ↔
      ck.index ≤ c ∧ (c - ck.index).toNat ≤ st.maxForwardJumps ∧
        (c = BitVec.allOnes 32 ∨ st.findReceiverChainIndex their = none) := by
  exact AdvanceAndFrame.consumeMessageKey_panic_iff_thm F st their ck c t

/-- Frame property: `consumeMessageKey` modifies only `receiverChains`, preserving chain count,
each chain's `senderRatchetKey`, and `ChainsOk`. -/
theorem consumeMessageKey_frame (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (hok : ChainsOk st) :
    let st' := ((RatchetState.consumeMessageKey F their ck c t).exec st).2
    ((RatchetState.consumeMessageKey F their ck c t).exec st).1 ≠ .error .panic →
      st'.rootKey = st.rootKey ∧ st'.senderChain = st.senderChain ∧
      st'.previousCounter = st.previousCounter ∧ st'.maxForwardJumps = st.maxForwardJumps ∧
      st'.receiverChains.map (·.senderRatchetKey) = st.receiverChains.map (·.senderRatchetKey) ∧
      ChainsOk st' := by
  exact AdvanceAndFrame.consumeMessageKey_frame_thm F st their ck c t hok

/-- `findReceiverChainIndex` is invariant under updating a chain while preserving its `senderRatchetKey`. -/
theorem findReceiverChainIndex_set (st : RatchetState) (their : PublicKey) (i : ℕ)
    (ch : ReceiverChain) (h : ∃ ch₀ ∈ st.receiverChains[i]?, ch₀.senderRatchetKey = ch.senderRatchetKey) :
    RatchetState.findReceiverChainIndex { st with receiverChains := st.receiverChains.set i ch } their =
      st.findReceiverChainIndex their := by
  exact AdvanceAndFrame.findReceiverChainIndex_set_thm st their i ch h

/-- Message-key seeds derived by `ChainKey.messageKeys` have length 32. -/
theorem messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  exact PastAndTooFar.messageKeys_seed_length_aux F ck

end CryptoVerification.SessionModel
