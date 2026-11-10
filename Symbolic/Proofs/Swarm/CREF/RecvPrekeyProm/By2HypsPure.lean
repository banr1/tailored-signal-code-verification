/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Tie.BlockReadPure
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2Pure -- shake: keep

/-!
# `CleanBy` Read Extraction on `promAccBlk`

Proves `prom_not_recvCollision_of_not_dirtyAt₂` and `prom_currentRead_of_not_dirtyAt₂`, extracting
`¬ RecvCollision` and `RcvCurrentRead` from `CleanBy` on an accepting promote block.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey chainKeyAt kdfCk kdfRk computeMac
  createChain x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding kdfRk createChain x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm

variable (interpretation : ExternInterpretation)

theorem prom_not_recvCollision_of_not_dirtyAt₂ {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {acc mid : List MachineEvent}
    {b pt : HwBytes} {pf : PreKeyFields} {t : DY.Bytes}
    (hpf : parsePreKeyWire b = some pf)
    (hc : CleanBy interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ promAccBlk b mid pt))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hmid : mid = [] ∨ ∃ rb : List (BitVec 8), mid = [.rng rb] ∧ rb.length = 32)
    (ht : rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t) :
    ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t :=
  prom_not_recvCollision_of_clean hpf hc hB hpre hmid ht

theorem prom_currentRead_of_not_dirtyAt₂ {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc mid : List MachineEvent} {b pt : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire b = some pf)
    (hc : CleanBy interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ promAccBlk b mid pt))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post)
    (_hmid : mid = [] ∨ ∃ rb : List (BitVec 8), mid = [.rng rb] ∧ rb.length = 32) :
    RcvCurrentRead interpretation r S g (ms₀ ++ pre) pf.message m := by
  have h := prom_currentRead_of_clean hpf hc hB hpre hpost
  cases m <;> exact h

end Symbolic.Swarm.CREF.CliPure
