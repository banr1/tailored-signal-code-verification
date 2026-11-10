/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import all DY.Bytes.Basic
import all DY.ALaCarte.Basic
import all DY.ALaCarte.DecidableEq
import all DY.ALaCarte.Ordering
import all DY.Misc.Instances
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.Concat
import all DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.KdfExtract
import all DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.PQXDH
import Symbolic.Specifications.Model.TripleRatchet
import Symbolic.Specifications.Model.Instance
import all Init.Data.Array.Attach
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Ord.Array
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli

/-!
# Call-4 Receiver Whisper Collision Refutation

Discharges `noRecvCollision_call4` from the pre-certified `Table.Cli.cliTable` and `cliGamma`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv4

set_option maxRecDepth 200000

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY
open DY.Libsignal.Composed.Refinement
  (runTrace honestSaltsOf availableStates ownKeys trialTerms whisperTrials)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (decide_nvVec3168_self decide_nvEk1152_self decide_nvDk2400_self
   decide_nvEk1152_nvDk2400 decide_nvDk2400_nvEk1152)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (trStateProxyRoots macTerms
   r0Comp r0_eq_comp S0Comp S0_eq_comp myGhostComp myGhost_eq_comp)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (extractMacSeed? noRecvCollisionBool)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 S0 myGhost)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (msPre4 trAt visAt saltsAt
   runTrace_take_eq honestSalts_take_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (msg1Term msg1Sig parse_msg1Term
   kemDecap_eq_fast symDec_eq_fast
   ite_sessionInfo_eq_fast ite_bytes_composed_eq_fast ite_bytes_tr_eq_fast)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (decide_bytes_composed_eq_fast decide_bytes_tr_eq_fast decide_bytes_pq_eq_fast
   saltsAt_4_eq sendTerms_visAt_4 plaintextTerms_visAt_4
   pqSecretsList storedStates_trAt_4 storedSecrets_trAt_4
   whisperTrialsNoSkipped whisperTrials_trAt_4)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (noMemoCollisionHsTableBool noMemoCollisionTableBool noMacForgeryTableBool
   noRecvCollisionBool_of_table)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli
  (cliTable cliTable_sound cliGamma gamma_comp_eq_cliGamma)

-- Keep `cliGamma`, `cliTable`, `cliIdTree`, and `tableGamma` OUT of `dsimp`/`unfold`.
local macro "close_eval_table" : tactic =>
  `(tactic| (
    try simp (config := { zeta := false }) only [gamma_comp_eq_cliGamma]
    try unfold trialTerms
    try dsimp (config := { zeta := false }) only [
      noMemoCollisionTableBool, noMemoCollisionHsTableBool, noMacForgeryTableBool,
      trStateProxyRoots, pqSecretsList, macTerms,
      extractMacSeed?, ownKeys,
      DY.Libsignal.TripleRatchet.recvChainFor,
      DY.Libsignal.TripleRatchet.findRecvChain,
      DY.Spqr.spqrRecv, DY.Spqr.spqrEmptyMsg, DY.Spqr.spqrParamsDir?,
      List.contains, List.elem, BEq.beq, instBEqOfDecidableEq,
      Option.instBEq, Option.instBEq.beq]
    try simp (config := { zeta := false }) only [kemDecap_eq_fast]
    try simp (config := { zeta := false }) only [symDec_eq_fast]
    try simp (config := { zeta := false }) only [ite_sessionInfo_eq_fast]
    try simp (config := { zeta := false }) only [ite_bytes_composed_eq_fast]
    try simp (config := { zeta := false }) only [ite_bytes_tr_eq_fast]
    try simp (config := { zeta := false }) only [decide_bytes_composed_eq_fast]
    try simp (config := { zeta := false }) only [decide_bytes_tr_eq_fast]
    try simp (config := { zeta := false }) only [decide_bytes_pq_eq_fast]
    try simp (config := { zeta := false }) only [
      decide_nvVec3168_self, decide_nvEk1152_self, decide_nvDk2400_self,
      decide_nvEk1152_nvDk2400, decide_nvDk2400_nvEk1152]))

private theorem noRecvMemo_call4 :
    noMemoCollisionTableBool cliTable cliGamma r0Comp (trAt 4) (visAt 4)
      (msg1Term ::
        (whisperTrials myInterp r0Comp S0Comp myGhostComp (trAt 4) msg1Sig).flatMap
          (trialTerms (saltsAt 4) msg1Sig)) [] = true := by
  dsimp (config := { zeta := false }) only [noMemoCollisionTableBool]
  simp (config := { zeta := false }) only [
    whisperTrials_trAt_4, whisperTrialsNoSkipped, ownKeys, availableStates,
    storedStates_trAt_4, storedSecrets_trAt_4,
    sendTerms_visAt_4, plaintextTerms_visAt_4, saltsAt_4_eq]
  close_eval_table; decide +kernel

private theorem noRecvMac_call4 :
    noMacForgeryTableBool cliGamma (saltsAt 4) msg1Sig
      (whisperTrials myInterp r0Comp S0Comp myGhostComp (trAt 4) msg1Sig) = true := by
  simp (config := { zeta := false }) only [
    whisperTrials_trAt_4, whisperTrialsNoSkipped, ownKeys, availableStates,
    storedStates_trAt_4, saltsAt_4_eq]
  close_eval_table; decide +kernel

theorem noRecvCollision_call4 :
    noRecvCollisionBool myInterp r0 S0 myGhost
      (runTrace r0 msPre4) (visAt 4) (honestSaltsOf r0 msPre4) msg1Term = true := by
  have htr : runTrace r0 msPre4 = trAt 4 := runTrace_take_eq 4
  have hs : honestSaltsOf r0 msPre4 = saltsAt 4 := honestSalts_take_eq 4
  rw [htr, hs, r0_eq_comp, S0_eq_comp, myGhost_eq_comp]
  exact noRecvCollisionBool_of_table cliTable_sound gamma_comp_eq_cliGamma
    rfl rfl rfl parse_msg1Term noRecvMemo_call4 noRecvMac_call4

end Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv4
