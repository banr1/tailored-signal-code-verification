/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse

/-!
# Clean Prefix Steps and Honest Representations

Defines the `.network`-free 24-step party schedule `ssClean cls spqrIdxs k`, parameterized by
send-coin lengths `cls : Nat → Nat` (`ValidCoinLens`) and SPQR receive indices
`spqrIdxs : Nat → UInt32`, along with the honest pre-key and message representations
(`cleanPreKeyRep`, `cleanRecvTerm`) at each `.recv` call of `trace0`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs

open DY (Bytes)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step PreKeyRep runTrace)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (bh1 kh1)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (trace0)

/-- Each of the 12 `.send` calls (`j < 12`) draws `0`, `32`, or `64` SPQR send-coin bytes. -/
def ValidCoinLens (cls : Nat → Nat) : Prop :=
  ∀ j, j < 12 → cls j = 0 ∨ cls j = 32 ∨ cls j = 64

/-- Indices of all 12 `.recv` events in `trace0`. -/
def recvCallIndices : List Nat :=
  [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 24]

/-- Indices of the 11 post-handshake `.recv` events in `trace0` checked via `RecvCollisionOn`. -/
def whisperOrReplayIndices : List Nat :=
  [5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 24]

/-- Four party steps of ping-pong round `rd` (`0 ≤ rd < 5`) from trace length `curLen` with Alice
and Bob states at `aSt` and `bSt` (Bob encrypt, Alice decrypt, Alice encrypt, Bob decrypt; `+7`
trace entries each). Returns `(steps, aSt', bSt', curLen + 28)`. -/
def cleanPingPongRound (cls : Nat → Nat) (spqrIdxs : Nat → UInt32)
    (rd aSt bSt curLen : Nat) : List Step × Nat × Nat × Nat :=
  let baseCall := 4 + 4 * rd
  let sBase := 2 + 2 * rd
  let pqB := curLen + 2
  let bSt1 := curLen + 5
  let msgB := curLen + 6
  let sBobSend := Step.messageEncrypt "bob" bSt (cls sBase) pqB
  let len1 := curLen + 7
  let aSt1 := len1 + 6
  let sAliceRecv := Step.messageDecrypt "alice" aSt msgB pqB (spqrIdxs (baseCall + 1))
  let len2 := len1 + 7
  let pqA := len2 + 2
  let aSt2 := len2 + 5
  let msgA := len2 + 6
  let sAliceSend := Step.messageEncrypt "alice" aSt1 (cls (sBase + 1)) pqA
  let len3 := len2 + 7
  let bSt2 := len3 + 6
  let sBobRecv := Step.messageDecrypt "bob" bSt1 msgA pqA (spqrIdxs (baseCall + 3))
  let len4 := len3 + 7
  ([sBobSend, sAliceRecv, sAliceSend, sBobRecv], aSt2, bSt2, len4)

/-- The 24-step `.network`-free party schedule for Calls `0..23` of `trace0`, starting after the
22-entry setup trace: `aliceStart` (`22..30`, `ek = 25`, `ct = 26`, `aSt = 30`), two Alice encrypts
(`aSt = 36, 43`, `pq = 33, 40`, `msg = 37, 44`), `bobStart` on Call 2 skipping counter `0`
(`bSt = 54`, length `55`), and five ping-pong rounds (`+28` entries each). -/
def cleanCallSteps (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) : List Step :=
  let s0 := Step.aliceStart "alice" "bob" 4 6 bh1
  let s1 := Step.messageEncrypt "alice" 30 (cls 0) 33
  let s2 := Step.messageEncrypt "alice" 36 (cls 1) 40
  let s3 := Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)
  let (r0s, a0, b0, l0) := cleanPingPongRound cls spqrIdxs 0 43 54 55
  let (r1s, a1, b1, l1) := cleanPingPongRound cls spqrIdxs 1 a0 b0 l0
  let (r2s, a2, b2, l2) := cleanPingPongRound cls spqrIdxs 2 a1 b1 l1
  let (r3s, a3, b3, l3) := cleanPingPongRound cls spqrIdxs 3 a2 b2 l2
  let (r4s, _, _, _) := cleanPingPongRound cls spqrIdxs 4 a3 b3 l3
  [s0, s1, s2, s3] ++ r0s ++ r1s ++ r2s ++ r3s ++ r4s

/-- Prefix of `k` clean party steps explaining `trace0.take k` (`k ≤ 24`). -/
def ssClean (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (k : Nat) : List Step :=
  (cleanCallSteps cls spqrIdxs).take k

theorem cleanCallSteps_length (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    (cleanCallSteps cls spqrIdxs).length = 24 := rfl

/-- `ExecTrace` index of the honest `TRSignalMsg` received at `.recv` call `k`: `44` at Call 3
(Alice's Call 2 message), `37` at Call 24 (replayed Call 1 message), and `55 + 7 * (k - 4) - 1`
at odd whisper calls `5..23` (sent in Call `k - 1`). -/
def cleanMsgIdx (k : Nat) : Nat :=
  if k = 3 then 44
  else if k = 24 then 37
  else 55 + 7 * (k - 4) - 1

/-- Unreachable `Option.getD` fallback term for `cleanRecvTerm` and `cleanPreKeyRep`. -/
def emptyLit : Bytes := DY.Spqr.zeroKey

/-- Honest `TRSignalMsg` term on `runTrace r (ssClean cls spqrIdxs k)` at `.recv` call `k`. -/
def cleanRecvTerm (r : ProtocolSetup) (cls : Nat → Nat) (spqrIdxs : Nat → UInt32)
    (k : Nat) : Bytes :=
  ((runTrace r (ssClean cls spqrIdxs k)).getMessageSentAt (cleanMsgIdx k)).getD emptyLit

/-- Honest `PreKeyRep` on `runTrace r (ssClean cls spqrIdxs 3)` at Bob's Call 3 `bobStart`. -/
def cleanPreKeyRep (r : ProtocolSetup) (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) : PreKeyRep where
  ek := ((runTrace r (ssClean cls spqrIdxs 3)).getMessageSentAt 25).getD emptyLit
  ct := ((runTrace r (ssClean cls spqrIdxs 3)).getMessageSentAt 26).getD emptyLit
  msg := cleanRecvTerm r cls spqrIdxs 3

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
