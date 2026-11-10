/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
import ProofLib.Lemmas

@[expose] public section

namespace CryptoVerification.SessionModel.PastAndTooFar

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

theorem length_flatMap_toBEBytes :
    ∀ l : List (BitVec 32), (l.flatMap (toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: xs => by
    simp [List.flatMap_cons, toBEBytes, length_flatMap_toBEBytes xs]
    omega

theorem length_sha256With (F : ShaCompress) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  rw [length_flatMap_toBEBytes]
  simp

theorem length_hmacWith (F : ShaCompress) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith
  exact length_sha256With F _

theorem messageKeys_seed_length_aux (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  unfold ChainKey.messageKeys Ratchet.chainHmac
  exact length_hmacWith F _ _

set_option linter.unusedSimpArgs false in
theorem consumeMessageKey_tooFar_aux (F : ShaCompress) (st : RatchetState) (their : PublicKey)
    (ck : ChainKey) (c : BitVec 32) (t : MessageType) (h : ck.index ≤ c)
    (hj : st.maxForwardJumps < (c - ck.index).toNat) :
    (RatchetState.consumeMessageKey F their ck c t).exec st =
      (.error (.invalidMessage t .tooFarInFuture), st) := by
  have hlt : ¬ c < ck.index := BitVec.not_lt.mpr h
  unfold RatchetState.consumeMessageKey Mut.exec
  simp only [hlt, hj, ↓reduceIte, ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad, MonadState.get,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, StateT.pure, StateT.bind,
    Functor.map, StateT.map, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.pure,
    throwThe]

set_option linter.unusedSimpArgs false in
theorem consumeMessageKey_past_aux (F : ShaCompress) (st : RatchetState) (their : PublicKey)
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
  unfold RatchetState.consumeMessageKey RatchetState.takeSkippedKey Mut.exec
  simp [h, ExceptT.run, StateT.run, pure, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, MonadExcept.throw, MonadExceptOf.throw, ExceptT.instMonad, MonadState.get,
    get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, StateT.pure, StateT.bind,
    Functor.map, StateT.map, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.pure,
    throwThe]
  cases hci : st.findReceiverChainIndex their with
  | none =>
    rfl
  | some ci =>
    have hci' : ci < st.receiverChains.length := by
      unfold RatchetState.findReceiverChainIndex at hci
      exact (List.findIdx?_eq_some_iff_findIdx_eq.mp hci).1
    dsimp only
    rw [List.getElem?_eq_getElem hci']
    dsimp only [Option.map_some]
    cases hp : st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == c) with
    | none =>
      rfl
    | some p =>
      dsimp only
      cases hk : st.receiverChains[ci].messageKeys[p]? with
      | none =>
        rfl
      | some k =>
        rfl

end CryptoVerification.SessionModel.PastAndTooFar
