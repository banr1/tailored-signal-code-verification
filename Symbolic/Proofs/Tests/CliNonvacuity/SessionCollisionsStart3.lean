/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
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
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli

/-!
# Call-3 Pre-Key Session-Start Collision Refutation

Discharges `not_bobStartCollides_call3` from the pre-certified `Table.Cli.cliTable` and
`cliGamma`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart3

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
open DY.Libsignal.PQXDH (errToOption)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (setupPublic setupSecret runTrace honestSaltsOf
   PreKeyFields parsePreKeyWire preKeySpqrIndex
   BobSessionStartCollidesOrImplicitRejectsOn
   ownKeys bobTrials trialTerms)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (decide_nvVec3168_self decide_nvEk1152_self decide_nvDk2400_self
   decide_nvEk1152_nvDk2400 decide_nvDk2400_nvEk1152)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (trStateProxyRoots macTerms
   r0Comp r0_eq_comp S0_eq_comp myGhost_eq_comp)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (extractMacSeed? not_bobSessionStartCollidesOrImplicitRejectsOn_check)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs (r0 S0 myGhost)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04 (pkMsg0)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (msPre3 trAt visAt saltsAt runTrace_take_eq honestSalts_take_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (msg0Sig x3Rep parse_msg0Term
   kemDecap_eq_fast symDec_eq_fast
   ite_sessionInfo_eq_fast ite_bytes_composed_eq_fast ite_bytes_tr_eq_fast)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (decide_bytes_composed_eq_fast decide_bytes_tr_eq_fast decide_bytes_pq_eq_fast
   setupPublic_r0Comp_0 setupPublic_r0Comp_2
   setupSecret_r0Comp_1 setupSecret_r0Comp_2 setupSecret_r0Comp_4
   saltsAt_3_eq sendTerms_visAt_3 plaintextTerms_visAt_3
   pqSecretsList storedStates_trAt_3 storedSecrets_trAt_3)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (noMemoCollisionHsTableBool noMemoCollisionTableBool noMacForgeryTableBool
   noBobStartCollisionBool_of_table)
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

private theorem bobTrials_call3_or_nil {p : PreKeyFields} (hp_id : p.preKeyId = none) :
    bobTrials r0Comp (trAt 3) p x3Rep msg0Sig = [] ∨
    bobTrials r0Comp (trAt 3) p x3Rep msg0Sig =
      (let keys :=
        let pqsk := setupSecret r0Comp 4
        let ss := (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk x3Rep.ct)).getD
          (DY.PQKem.kemRejKey pqsk x3Rep.ct)
        DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
          (DY.Libsignal.PQXDH.agree (setupPublic r0Comp 0) (setupSecret r0Comp 2))
          (DY.Libsignal.PQXDH.agree x3Rep.ek (setupSecret r0Comp 1))
          (DY.Libsignal.PQXDH.agree x3Rep.ek (setupSecret r0Comp 2))
          none ss)
      let c : DY.Libsignal.TripleRatchet.RecvChain :=
        { ratchetKey := msg0Sig.ratchetKey
          chainKey := (DY.Libsignal.TripleRatchet.createChain keys.rk msg0Sig.ratchetKey (setupSecret r0Comp 2)).2
          index := 0, rIdx := 2 }
      let peerIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r0Comp 0)
      let myIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r0Comp 2)
      match DY.Libsignal.TripleRatchet.consumeMessageKey c msg0Sig.counter with
      | none =>
        [{ peerIk, myIk, extra := [keys.rk, keys.ck, keys.pqr, c.chainKey], ownSalts := [], seed? := none }]
      | some (seed, c') =>
        let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A)
          msg0Sig.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList
        [{ peerIk, myIk
           extra := [keys.rk, keys.ck, keys.pqr, c.chainKey, c'.chainKey] ++
             DY.Libsignal.TripleRatchet.skippedSeeds c msg0Sig.counter
           ownSalts := own, seed? := some seed }]) := by
  unfold bobTrials
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikAPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqskSecTerm
  rw [hp_id]
  dsimp only
  split
  · exact .inl rfl
  · exact .inr rfl
private theorem noBobStartMemo_call3 {p : PreKeyFields}
    (hp_id : p.preKeyId = none) (hp_idx : preKeySpqrIndex p = 1) :
    noMemoCollisionTableBool cliTable cliGamma r0Comp (trAt 3) (visAt 3)
      ([x3Rep.ek, x3Rep.ct, x3Rep.msg] ++
        (bobTrials r0Comp (trAt 3) p x3Rep msg0Sig).flatMap (trialTerms (saltsAt 3) msg0Sig)) [] = true := by
  rcases bobTrials_call3_or_nil hp_id with h | h <;> rw [h]
  · dsimp (config := { zeta := false }) only [noMemoCollisionTableBool]
    simp (config := { zeta := false }) only [
      storedStates_trAt_3, storedSecrets_trAt_3,
      sendTerms_visAt_3, plaintextTerms_visAt_3]
    close_eval_table; decide +kernel
  · dsimp (config := { zeta := false }) only [noMemoCollisionTableBool]
    simp (config := { zeta := false }) only [
      hp_idx,
      setupPublic_r0Comp_0, setupPublic_r0Comp_2,
      setupSecret_r0Comp_1, setupSecret_r0Comp_2, setupSecret_r0Comp_4,
      storedStates_trAt_3, storedSecrets_trAt_3,
      sendTerms_visAt_3, plaintextTerms_visAt_3, saltsAt_3_eq]
    close_eval_table; decide +kernel

private theorem noBobStartMac_call3 {p : PreKeyFields}
    (hp_id : p.preKeyId = none) (hp_idx : preKeySpqrIndex p = 1) :
    noMacForgeryTableBool cliGamma (saltsAt 3) msg0Sig
      (bobTrials r0Comp (trAt 3) p x3Rep msg0Sig) = true := by
  rcases bobTrials_call3_or_nil hp_id with h | h <;> rw [h]
  · decide +kernel
  · simp (config := { zeta := false }) only [
      hp_idx,
      setupPublic_r0Comp_0, setupPublic_r0Comp_2,
      setupSecret_r0Comp_1, setupSecret_r0Comp_2, setupSecret_r0Comp_4,
      saltsAt_3_eq]
    close_eval_table; decide +kernel

theorem not_bobStartCollides_call3 {p : PreKeyFields}
    (hp : parsePreKeyWire (wirePrekeyTag :: pkMsg0.bytes) = some p) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn myInterp r0 S0 myGhost
        (runTrace r0 msPre3) (visAt 3) (honestSaltsOf r0 msPre3) p x3Rep := by
  have hp_id : p.preKeyId = none := by
    have h : (parsePreKeyWire (wirePrekeyTag :: pkMsg0.bytes)).map (·.preKeyId) = some none := by
      decide +kernel
    rw [hp] at h; exact Option.some.inj h
  have hp_idx : preKeySpqrIndex p = 1 := by
    have h : (parsePreKeyWire (wirePrekeyTag :: pkMsg0.bytes)).map preKeySpqrIndex = some 1 := by
      decide +kernel
    rw [hp] at h; exact Option.some.inj h
  refine not_bobSessionStartCollidesOrImplicitRejectsOn_check ?_
  have htr : runTrace r0 msPre3 = trAt 3 := runTrace_take_eq 3
  have hs : honestSaltsOf r0 msPre3 = saltsAt 3 := honestSalts_take_eq 3
  rw [htr, hs, r0_eq_comp, S0_eq_comp, myGhost_eq_comp]
  exact noBobStartCollisionBool_of_table cliTable_sound gamma_comp_eq_cliGamma
    rfl rfl rfl parse_msg0Term (noBobStartMemo_call3 hp_id hp_idx) (noBobStartMac_call3 hp_id hp_idx)

end Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart3
