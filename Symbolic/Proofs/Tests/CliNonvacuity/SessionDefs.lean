/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Witness
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
public import Symbolic.Proofs.Swarm.CREF.Cli.DirBridge
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Tests.Nonvacuity.ExposedSession
public import Symbolic.Tests.Nonvacuity.HonestSession
import Symbolic.Proofs.Tests.Nonvacuity
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Shared Session Definitions and Step Traces for CLI Non-Vacuity

Defines the concrete setup (`r0`), opaque byte semantics (`S0`), coin tapes, `Step` sequences
(`msHonest`, `msLeaks`, `msTail`, `msExposed`), concretization ghost (`myGhost`, `myGhost_compat`),
and `runTrace` equations shared by the multi-turn session non-vacuity proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs

open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed (reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost GhostAndSemMatchSetup Step stepIn
   pubBytes secretBytes setupPublic setupTrace runSteps runTrace)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.E2E (PreKeyBundleFields initiateTapeLen pqxdhSessionParams)
open CryptoVerification.SignalSession (PqParty)
open Symbolic.Tests.Nonvacuity (honestSessionTrace exposedSessionTrace)
open Symbolic.Proofs.Tests.Nonvacuity (honestSessionTrace_eq exposedSessionTrace_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myParams myInterp freshBytes pt0 pt1 ptReply0 pt2 mkRecords padSendCoins mySem mySem_compat)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (bh1 kh1 mh1 spkB stA0 coins0 key0 m0 stA1 coins1 key1 m1
   t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 wTr
   t5_runs t6_runs t7_runs t8_runs t9_runs t10_runs t11_runs
   t12_runs t13_runs t14_runs t15_runs)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (Runs encSig)
open Symbolic.Swarm.CREF.Cli (initPqParty)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-! ## Provisioned Setup, Semantics, and Coin Tapes -/

abbrev r0 : ProtocolSetup := mkRecords false
abbrev S0 : OpaqueSymbolSemantics := mySem false

def stA_init : PqParty := initPqParty myInterp r0 "alice"
def stB_init : PqParty := initPqParty myInterp r0 "bob"

def bE : PreKeyBundleFields where
  regId := r0.regIdB
  spkId := r0.spkId
  spkPub := bytesToVec 32 (pubBytes myInterp (secretBytes r0 2))
  spkSig := bytesToVec 64 (r0.opaqueBytes (setupPublic r0 5))
  kpkId := r0.kpkId
  kpkPub := bytesToVec 1568 (r0.opaqueBytes (setupPublic r0 6))
  kpkSig := bytesToVec 64 (r0.opaqueBytes (setupPublic r0 7))
  idPub := bytesToVec 32 (pubBytes myInterp (secretBytes r0 1))
  opk := none

def tapeInitBytes : HwBytes :=
  freshBytes 22 32 ++ List.replicate 128 24#8 ++ freshBytes 24 32

def tapeInit : List.Vector (BitVec 8) initiateTapeLen :=
  bytesToVec initiateTapeLen tapeInitBytes

def cSend0 : HwBytes := List.replicate 64 0x31#8
def cSend1 : HwBytes := List.replicate 64 0x32#8
def cSendReply0 : HwBytes := List.replicate 64 0x33#8
def cSend2 : HwBytes := List.replicate 64 0x34#8

def cSend0Vec : List.Vector (BitVec 8) 64 := ⟨cSend0, rfl⟩
def cSend1Vec : List.Vector (BitVec 8) 64 := ⟨cSend1, rfl⟩
def cSendReply0Vec : List.Vector (BitVec 8) 64 := ⟨cSendReply0, rfl⟩
def cSend2Vec : List.Vector (BitVec 8) 64 := ⟨cSend2, rfl⟩

def rc3Bytes : HwBytes := freshBytes 45 32
def rc4Bytes : HwBytes := List.replicate 32 0x56#8
def rc6Bytes : HwBytes := freshBytes 65 32
def rc8Bytes : HwBytes := freshBytes 83 32

def rc3 : BitVec 256 := bytesToKey32 rc3Bytes
def rc4 : BitVec 256 := bytesToKey32 rc4Bytes
def rc6 : BitVec 256 := bytesToKey32 rc6Bytes
def rc8 : BitVec 256 := bytesToKey32 rc8Bytes

/-! ## Concrete `Ghost` Witness -/

def myGhostSigma (ts n : Nat) : HwBytes :=
  if n == 32 then
    if ts == 31 then pt0
    else if ts == 32 then cSend0.take 32
    else if ts == 38 then pt1
    else if ts == 39 then cSend1.take 32
    else if ts == 58 then ptReply0
    else if ts == 59 then cSendReply0.take 32
    else if ts == 76 then pt2
    else if ts == 77 then cSend2.take 32
    else freshBytes ts n
  else freshBytes ts n

def msg0WireTerm : DY.Bytes := (encSig stA0 coins0 key0 m0).wire
def msg1WireTerm : DY.Bytes := (encSig stA1 coins1 key1 m1).wire

def myGhostAddr (t : DY.Bytes) : HwBytes :=
  if t == msg0WireTerm then
    ((pqxdhSessionParams myParams).sendAddrs .A).getD []
  else if t == msg1WireTerm then
    ((pqxdhSessionParams myParams).sendAddrs .A).getD []
  else
    []

def myGhost : Ghost where
  σ := myGhostSigma
  addr := myGhostAddr

theorem myGhost_compat : GhostAndSemMatchSetup myInterp r0 S0 myGhost := by
  apply mySem_compat
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r0
    (Symbolic.Proofs.Tests.CliNonvacuity.Witness.mkRecords_wf false).1]
  decide

/-! ## Concrete `Step` Sequences and `runTrace` Equations -/

def move0_init : Step := .aliceStart "alice" "bob" 4 6 bh1
def move1_enc0 : Step := .messageEncrypt "alice" 30 32 33
def move2_enc1 : Step := .messageEncrypt "alice" 36 32 40
def move3_bobStart : Step := .bobStart "bob" "alice" kh1 1 mh1 33 1
def move4_dec1 : Step := .messageDecrypt "bob" 53 44 40 2
def move5_encReply0 : Step := .messageEncrypt "bob" 57 32 60
def move6_decReply0 : Step := .messageDecrypt "alice" 43 64 60 1
def move7_leakCkr : Step := .exposeKey "alice" 71 (.ckr (DY.DiffieHellman.dhPk spkB))
def move8_leakCks : Step := .exposeKey "alice" 71 .cks
def move9_enc2 : Step := .messageEncrypt "alice" 71 32 78
def move10_dec2 : Step := .messageDecrypt "bob" 63 82 78 3

def msHonest : List Step :=
  [move0_init, move1_enc0, move2_enc1, move3_bobStart, move4_dec1, move5_encReply0, move6_decReply0]

def msLeaks : List Step := [move7_leakCkr, move8_leakCks]

def msTail : List Step := [move9_enc2, move10_dec2]

def msExposed : List Step := msHonest ++ msLeaks ++ msTail

private theorem stepIn_next (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

private theorem stepIn_isSome (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (inst.pf_step x).symm

theorem setupTrace_r0_eq : setupTrace r0 = t4 :=
  Symbolic.Proofs.Tests.Nonvacuity.keySetupTrace_eq
theorem move0_next : move0_init.next t4 = t5 :=
  (stepIn_next DY.Libsignal.Composed.aliceStart.reachability _ t4).trans t5_runs.2
theorem move1_next : move1_enc0.next t5 = t6 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5).trans t6_runs.2
theorem move2_next : move2_enc1.next t6 = t7 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t6).trans t7_runs.2
theorem move3_next : move3_bobStart.next t7 = t8 :=
  (stepIn_next DY.Libsignal.Composed.bobStart.reachability _ t7).trans t8_runs.2
theorem move4_next : move4_dec1.next t8 = t9 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ t8).trans t9_runs.2
theorem move5_next : move5_encReply0.next t9 = t10 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t9).trans t10_runs.2
theorem move6_next : move6_decReply0.next t10 = t11 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ t10).trans t11_runs.2
theorem move7_next : move7_leakCkr.next t11 = t12 :=
  (stepIn_next DY.Libsignal.TripleRatchet.exposeKey.reachability _ t11).trans t12_runs.2
theorem move8_next : move8_leakCks.next t12 = t13 :=
  (stepIn_next DY.Libsignal.TripleRatchet.exposeKey.reachability _ t12).trans t13_runs.2
theorem move9_next : move9_enc2.next t13 = t14 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t13).trans t14_runs.2
theorem move10_next : move10_dec2.next t14 = t15 :=
  (stepIn_next DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ t14).trans t15_runs.2

theorem move0_ok : move0_init.ok t4 = true :=
  (stepIn_isSome DY.Libsignal.Composed.aliceStart.reachability _ t4).trans
    (congrArg Option.isSome t5_runs.1)
theorem move1_ok : move1_enc0.ok t5 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5).trans
    (congrArg Option.isSome t6_runs.1)
theorem move2_ok : move2_enc1.ok t6 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t6).trans
    (congrArg Option.isSome t7_runs.1)
theorem move3_ok : move3_bobStart.ok t7 = true :=
  (stepIn_isSome DY.Libsignal.Composed.bobStart.reachability _ t7).trans
    (congrArg Option.isSome t8_runs.1)
theorem move4_ok : move4_dec1.ok t8 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ t8).trans
    (congrArg Option.isSome t9_runs.1)
theorem move5_ok : move5_encReply0.ok t9 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t9).trans
    (congrArg Option.isSome t10_runs.1)
theorem move6_ok : move6_decReply0.ok t10 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ t10).trans
    (congrArg Option.isSome t11_runs.1)
theorem move7_ok : move7_leakCkr.ok t11 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.exposeKey.reachability _ t11).trans
    (congrArg Option.isSome t12_runs.1)
theorem move8_ok : move8_leakCks.ok t12 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.exposeKey.reachability _ t12).trans
    (congrArg Option.isSome t13_runs.1)
theorem move9_ok : move9_enc2.ok t13 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t13).trans
    (congrArg Option.isSome t14_runs.1)
theorem move10_ok : move10_dec2.ok t14 = true :=
  (stepIn_isSome DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ t14).trans
    (congrArg Option.isSome t15_runs.1)

theorem runTrace_msHonest : runTrace r0 msHonest = honestSessionTrace := by
  rw [honestSessionTrace_eq, runTrace, setupTrace_r0_eq]
  dsimp only [msHonest, runSteps]
  rw [move0_next, move1_next, move2_next,
    move3_next, move4_next, move5_next, move6_next]

theorem runTrace_msExposed : runTrace r0 msExposed = exposedSessionTrace := by
  rw [exposedSessionTrace_eq, wTr, runTrace, setupTrace_r0_eq]
  dsimp only [msExposed, msHonest, msLeaks, msTail,
    List.cons_append, List.nil_append, runSteps]
  rw [move0_next, move1_next, move2_next,
    move3_next, move4_next, move5_next, move6_next, move7_next, move8_next,
    move9_next, move10_next]

end Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
