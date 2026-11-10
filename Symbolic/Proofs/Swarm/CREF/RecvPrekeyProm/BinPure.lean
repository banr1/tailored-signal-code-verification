/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
import Symbolic.Proofs.Refinement.RecordBytesBridge
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Promote-Call Bookkeeping State and Output Witness

Defines `PromTurn` and `PromBinAcceptOut` for accepting `session_recv_prekey` calls on the
session-promotion path, and proves `prom_recordBytes_ne_nil`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)

/-- Per-turn bookkeeping state for promote calls. -/
structure PromTurn where
  records : Participant → Option HwBytes
  sent : List HwBytes
  accepted : List HwBytes
  opkUsed : Bool

/-- Structured witness of an accepting promote-call output. -/
structure PromBinAcceptOut (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (rec b : HwBytes) (mid : List MachineEvent) (sm : StateAndMessage)
    (pf : PreKeyFields) (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)) : Prop where
  hpf : parsePreKeyWire b = some pf
  hcan_in : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec sess
  hcoins : (coins = 0#256 ∧ mid = []) ∨
    (∃ rb : List (BitVec 8), mid = [.rng rb] ∧ rb.length = 32 ∧
      coins = Symbolic.Swarm.CREF.CliPure.RpkCli.pinCoins (some rb) ∧
      pureDrawsCoins (Proofs.libsignal.Hooks2.cryptoOf' interpretation) sess.state
        pf.inner.senderRatchetKey = true)
  hdecOk : PureDecryptCoinsOk
    (Proofs.libsignal.Hooks2.cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey coins
  hexec : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
      (Proofs.libsignal.Hooks2.cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (pureSpqrOf interpretation)
      expected pf.inner .preKey coins) sess.state = (Except.ok pt, sess'.state)
  halice : sess'.aliceBaseKey = sess.aliceBaseKey
  hpend : sess'.pendingPreKey = none
  hkyb : sess'.pendingKyberPreKey = sess.pendingKyberPreKey
  hstate : sm.state = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩
  hmsg : sm.message = List.replicate 47 0#8 ++ pt
  hwrc : TR.Pure.WireRecCanon sm.state
  hcanon_out : sm.state.length < 2 ^ 32 - 2 ^ 20 → TR.PureTRRecordCanon r r.bob sm.state

theorem prom_recordBytes_ne_nil (rr : RecordRec) : recordBytes rr ≠ [] := by
  intro h
  dsimp only [recordBytes, msgField,
    DY.Libsignal.Refinement.encodeField] at h
  rw [Swarm.Phase0WholeFunctionBridge.paddedVarint_zero_of_lt_128 (by decide : 1 * 8 + 2 < 128)] at h
  nomatch h

end Symbolic.Swarm.CREF.CliPure
