/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqStatement
import LibsignalBinary.Proofs.SignalSession.Closure.Version

/-!
# Steady-State CLI Refinement to `pqxdhSessionParams`

Proves `PqCliSteadyRefinesSM W`: once `pendingPreKey` is cleared, `pqSendModel` and
`pqRecvWhisperModel` refine `Params.send` and `Params.receive` at `pqxdhSessionParams W` and agree
with `sendModelPq` and `recvModelPq` when `st.trusts k = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec

theorem pqCliSteadyRefinesSM_proof (W : PEParams) : PqCliSteadyRefinesSM W := by
  intro st x g hsess hp
  have hC : (pqxdhSessionParams W).C = W.C := rfl
  have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
  have hspqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro m r st' out hsend
    unfold pqSendModel at hsend
    rw [hsess] at hsend
    dsimp only at hsend
    rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with ⟨err | msg, s⟩
    · rw [henc] at hsend
      cases err <;> cases hsend
    · rw [henc] at hsend
      dsimp only at hsend
      cases hk : g.session.remoteIdentity with
      | none => rw [hk] at hsend; cases hsend
      | some k =>
        rw [hk] at hsend
        dsimp only at hsend
        cases ht : st.trusts k
        · rw [ht] at hsend; cases hsend
        · rw [ht] at hsend
          rw [hp] at hsend
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hsend
          rcases hsend with ⟨rfl, rfl⟩
          refine ⟨k, rfl, ?_, ?_⟩
          · unfold Params.send
            rw [hC, hcodec, hspqr, henc]
          · unfold Params.send
            rw [hC, hcodec, hspqr, henc]
  · intro c rc st' pt hrecv
    unfold pqRecvWhisperModel at hrecv
    rw [hsess] at hrecv
    dsimp only at hrecv
    cases htry : SignalMessage.tryFrom protoSignalCodec c with
    | error _ => rw [htry] at hrecv; cases hrecv
    | ok msg =>
      rw [htry] at hrecv
      dsimp only at hrecv
      unfold pqxdhSessionDecryptModel at hrecv
      rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt', s⟩
      · rw [hdec] at hrecv
        cases err <;> cases hrecv
      · rw [hdec] at hrecv
        dsimp only at hrecv
        cases hk : s.remoteIdentity with
        | none => rw [hk] at hrecv; cases hrecv
        | some k =>
          rw [hk] at hrecv
          dsimp only at hrecv
          cases ht : st.trusts k
          · rw [ht] at hrecv; cases hrecv
          · rw [ht] at hrecv
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at hrecv
            rcases hrecv with ⟨rfl, rfl⟩
            unfold Params.receive
            rw [hcodec, htry, hC, hspqr]
            dsimp only
            rw [hdec]
            exact ⟨_, _, _, k, rfl, hk, rfl⟩
  · intro k hk htrust
    refine ⟨?_, ?_⟩
    · intro m r
      unfold pqSendModel sendModelPq
      rw [hsess, hC, hcodec, hspqr]
      dsimp only
      rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with ⟨err | msg, s⟩
      · cases err <;> rfl
      · dsimp only
        rw [hk]
        dsimp only
        rw [htrust, hp]
        rfl
    · intro c rc
      unfold pqRecvWhisperModel recvModelPq
      rw [hsess, hC, hcodec, hspqr]
      dsimp only
      cases htry : SignalMessage.tryFrom protoSignalCodec c with
      | error _ => rfl
      | ok msg =>
        dsimp only
        unfold pqxdhSessionDecryptModel
        rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt, s⟩
        · cases err <;> rfl
        · dsimp only
          have hsrem : s.remoteIdentity = some k := by
            have hpres := Closure.Version.tryDecryptFromRecord_remoteIdentity W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session
            rw [hdec] at hpres
            exact hpres.trans hk
          rw [hsrem]
          dsimp only
          rw [htrust]
          rfl

end CryptoVerification.SignalSession
