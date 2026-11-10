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
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli

/-!
# Call-4 Session-Start and Reselect Collision Refutations

Discharges `noBobStartCollision_call4`, `bobDoneBaseKey_call4`, `noReselectCollision_call4`,
`noReselectCollision_call6`, and `noReselectCollision_call8` from the pre-certified
`Table.Cli.cliTable` and `cliGamma`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart4

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
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (setupPublic setupSecret runTrace honestSaltsOf
   PreKeyFields parsePreKeyWire preKeySpqrIndex
   bobDoneBaseKeys availableStates ownKeys
   bobTrials trialTerms gamma)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (decide_nvVec3168_self decide_nvEk1152_self decide_nvDk2400_self
   decide_nvEk1152_nvDk2400 decide_nvDk2400_nvEk1152)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (trStateProxyRoots macTerms
   r0Comp r0_eq_comp S0_eq_comp myGhost_eq_comp)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (extractMacSeed? noBobStartCollisionBool noReselectCollisionBool)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 S0 myGhost msExposed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04 (pkMsg1)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (msPre4 msPre6 msPre8 trAt visAt saltsAt
   runTrace_take_eq honestSalts_take_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (msg1Term msg1Sig msgReply0Term msg2Term x4Rep
   parse_msg1Term parse_msgReply0Term parse_msg2Term
   kemDecap_eq_fast symDec_eq_fast
   ite_sessionInfo_eq_fast ite_bytes_composed_eq_fast ite_bytes_tr_eq_fast)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (decide_bytes_composed_eq_fast decide_bytes_tr_eq_fast decide_bytes_pq_eq_fast
   setupPublic_r0Comp_0 setupPublic_r0Comp_2
   setupSecret_r0Comp_1 setupSecret_r0Comp_2 setupSecret_r0Comp_4
   saltsAt_4_eq sendTerms_visAt_4 plaintextTerms_visAt_4
   pqSecretsList storedStates_trAt_4 storedStates_trAt_6 storedStates_trAt_10
   storedSecrets_trAt_4 bobDoneBaseKeys_trAt_4
   storedRatchetKeysNoSkipped
   storedRatchetKeys_trAt_4 storedRatchetKeys_trAt_6 storedRatchetKeys_trAt_10)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (noMemoCollisionHsTableBool noMemoCollisionTableBool noMacForgeryTableBool
   noBobStartCollisionBool_of_table
   noReselectCollisionTableBool noReselectCollisionBool_of_table)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli
  (cliTable cliTable_sound cliGamma gamma_comp_eq_cliGamma)

-- Keep `cliGamma`, `cliTable`, `cliIdTree`, and `tableGamma` OUT of `dsimp`/`unfold`.
local macro "close_eval_table" : tactic =>
  `(tactic| (
    try simp (config := { zeta := false }) only [gamma_comp_eq_cliGamma]
    try unfold trialTerms
    try dsimp (config := { zeta := false }) only [
      noMemoCollisionTableBool, noMemoCollisionHsTableBool, noMacForgeryTableBool,
      noReselectCollisionTableBool,
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

private theorem bobTrials_call4_or_nil {p : PreKeyFields} (hp_id : p.preKeyId = none) :
    bobTrials r0Comp (trAt 4) p x4Rep msg1Sig = [] ∨
    bobTrials r0Comp (trAt 4) p x4Rep msg1Sig =
      (let keys :=
        let pqsk := setupSecret r0Comp 4
        let ss := (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk x4Rep.ct)).getD
          (DY.PQKem.kemRejKey pqsk x4Rep.ct)
        DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
          (DY.Libsignal.PQXDH.agree (setupPublic r0Comp 0) (setupSecret r0Comp 2))
          (DY.Libsignal.PQXDH.agree x4Rep.ek (setupSecret r0Comp 1))
          (DY.Libsignal.PQXDH.agree x4Rep.ek (setupSecret r0Comp 2))
          none ss)
      let c : DY.Libsignal.TripleRatchet.RecvChain :=
        { ratchetKey := msg1Sig.ratchetKey
          chainKey := (DY.Libsignal.TripleRatchet.createChain keys.rk msg1Sig.ratchetKey (setupSecret r0Comp 2)).2
          index := 0, rIdx := 2 }
      let peerIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r0Comp 0)
      let myIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r0Comp 2)
      match DY.Libsignal.TripleRatchet.consumeMessageKey c msg1Sig.counter with
      | none =>
        [{ peerIk, myIk, extra := [keys.rk, keys.ck, keys.pqr, c.chainKey], ownSalts := [], seed? := none }]
      | some (seed, c') =>
        let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A)
          msg1Sig.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList
        [{ peerIk, myIk
           extra := [keys.rk, keys.ck, keys.pqr, c.chainKey, c'.chainKey] ++
             DY.Libsignal.TripleRatchet.skippedSeeds c msg1Sig.counter
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

private theorem noBobStartMemo_call4 {p : PreKeyFields}
    (hp_id : p.preKeyId = none) (hp_idx : preKeySpqrIndex p = 2) :
    noMemoCollisionTableBool cliTable cliGamma r0Comp (trAt 4) (visAt 4)
      ([x4Rep.ek, x4Rep.ct, x4Rep.msg] ++
        (bobTrials r0Comp (trAt 4) p x4Rep msg1Sig).flatMap (trialTerms (saltsAt 4) msg1Sig)) [] = true := by
  rcases bobTrials_call4_or_nil hp_id with h | h <;> rw [h]
  · dsimp (config := { zeta := false }) only [noMemoCollisionTableBool]
    simp (config := { zeta := false }) only [
      storedStates_trAt_4, storedSecrets_trAt_4,
      sendTerms_visAt_4, plaintextTerms_visAt_4]
    close_eval_table; decide +kernel
  · dsimp (config := { zeta := false }) only [noMemoCollisionTableBool]
    simp (config := { zeta := false }) only [
      hp_idx,
      setupPublic_r0Comp_0, setupPublic_r0Comp_2,
      setupSecret_r0Comp_1, setupSecret_r0Comp_2, setupSecret_r0Comp_4,
      storedStates_trAt_4, storedSecrets_trAt_4,
      sendTerms_visAt_4, plaintextTerms_visAt_4, saltsAt_4_eq]
    close_eval_table; decide +kernel

private theorem noBobStartMac_call4 {p : PreKeyFields}
    (hp_id : p.preKeyId = none) (hp_idx : preKeySpqrIndex p = 2) :
    noMacForgeryTableBool cliGamma (saltsAt 4) msg1Sig
      (bobTrials r0Comp (trAt 4) p x4Rep msg1Sig) = true := by
  rcases bobTrials_call4_or_nil hp_id with h | h <;> rw [h]
  · decide +kernel
  · simp (config := { zeta := false }) only [
      hp_idx,
      setupPublic_r0Comp_0, setupPublic_r0Comp_2,
      setupSecret_r0Comp_1, setupSecret_r0Comp_2, setupSecret_r0Comp_4,
      saltsAt_4_eq]
    close_eval_table; decide +kernel

theorem noBobStartCollision_call4 {p : PreKeyFields}
    (hp : parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes) = some p) :
    noBobStartCollisionBool myInterp r0 S0 myGhost
      (runTrace r0 msPre4) (visAt 4) (honestSaltsOf r0 msPre4) p x4Rep = true := by
  have hp_id : p.preKeyId = none := by
    have h : (parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes)).map (·.preKeyId) = some none := by
      decide +kernel
    rw [hp] at h; exact Option.some.inj h
  have hp_idx : preKeySpqrIndex p = 2 := by
    have h : (parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes)).map preKeySpqrIndex = some 2 := by
      decide +kernel
    rw [hp] at h; exact Option.some.inj h
  have htr : runTrace r0 msPre4 = trAt 4 := runTrace_take_eq 4
  have hs : honestSaltsOf r0 msPre4 = saltsAt 4 := honestSalts_take_eq 4
  rw [htr, hs, r0_eq_comp, S0_eq_comp, myGhost_eq_comp]
  exact noBobStartCollisionBool_of_table cliTable_sound gamma_comp_eq_cliGamma
    rfl rfl rfl parse_msg1Term (noBobStartMemo_call4 hp_id hp_idx) (noBobStartMac_call4 hp_id hp_idx)

theorem noReselectCollision_call4 :
    noReselectCollisionBool myInterp r0 S0 myGhost (runTrace r0 msPre4) msg1Term = true := by
  have htr : runTrace r0 msPre4 = trAt 4 := runTrace_take_eq 4
  rw [htr, r0_eq_comp, S0_eq_comp, myGhost_eq_comp]
  refine noReselectCollisionBool_of_table gamma_comp_eq_cliGamma rfl parse_msg1Term ?_
  dsimp (config := { zeta := false }) only [noReselectCollisionTableBool]
  simp (config := { zeta := false }) only [
    storedRatchetKeys_trAt_4, storedRatchetKeysNoSkipped, availableStates, storedStates_trAt_4]
  close_eval_table; decide +kernel

theorem bobDoneBaseKey_call4 :
    ((bobDoneBaseKeys (runTrace r0 msPre4)).any fun ek =>
      gamma myInterp S0 myGhost ek == gamma myInterp S0 myGhost x4Rep.ek) = true := by
  rw [show msPre4 = msExposed.take 4 from rfl, runTrace_take_eq 4, bobDoneBaseKeys_trAt_4]
  simp

theorem noReselectCollision_call6 :
    noReselectCollisionBool myInterp r0 S0 myGhost (runTrace r0 msPre6) msgReply0Term = true := by
  have htr : runTrace r0 msPre6 = trAt 6 := runTrace_take_eq 6
  rw [htr, r0_eq_comp, S0_eq_comp, myGhost_eq_comp]
  refine noReselectCollisionBool_of_table gamma_comp_eq_cliGamma rfl parse_msgReply0Term ?_
  dsimp (config := { zeta := false }) only [noReselectCollisionTableBool]
  simp (config := { zeta := false }) only [
    storedRatchetKeys_trAt_6, storedRatchetKeysNoSkipped, availableStates, storedStates_trAt_6]
  close_eval_table; decide +kernel

theorem noReselectCollision_call8 :
    noReselectCollisionBool myInterp r0 S0 myGhost (runTrace r0 msPre8) msg2Term = true := by
  have htr : runTrace r0 msPre8 = trAt 10 := runTrace_take_eq 10
  rw [htr, r0_eq_comp, S0_eq_comp, myGhost_eq_comp]
  refine noReselectCollisionBool_of_table gamma_comp_eq_cliGamma rfl parse_msg2Term ?_
  dsimp (config := { zeta := false }) only [noReselectCollisionTableBool]
  simp (config := { zeta := false }) only [
    storedRatchetKeys_trAt_10, storedRatchetKeysNoSkipped, availableStates, storedStates_trAt_10]
  close_eval_table; decide +kernel

end Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart4
