/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe

/-!
# Call 3 (`bobStart`) Non-Collision on Clean Prefixes

Proves `not_bobStartCollides_clean`: for any valid send-coin schedule `cls` (`ValidCoinLens`) and
SPQR receive indices `spqrIdxs` explaining `trace0.take 3` under `evictedCompFitsPinned`, Bob's
session start at Call 3 satisfies `¬ BobSessionStartCollidesOrImplicitRejectsOn` on
`cleanPreKeyRep r cls spqrIdxs`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoBobStart

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

open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk kemEncap kemDecap kemRejKey)
open DY.Libsignal.PQXDH (errToOption agree serializedIk pqxdhIkm pqxdhKdf)
open DY.Libsignal.TripleRatchet
  (TRState createChain kdfCk parseTrSignalMsg spqrB2A)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry PreKeyFields PreKeyRep TrialCtx
   parsePreKeyWire preKeySpqrIndex setupPublic setupSecret runTrace honestSaltsOf
   principalTerms plaintextTerms prefixTerms
   bobTrials trialTerms Explains BobSessionStartCollidesOrImplicitRejectsOn randTerm)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (kemDecap_kemEncap)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encMsg encSig parse_encMsg agree_comm createChain_comm)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB o1 keys1 dhsA stA0)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
  (setupPublic_0 setupPublic_2 setupSecret_1 setupSecret_2)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0 trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens ssClean cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (ev3_full_fields)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes honestSaltIds)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt safeMemo_plaintext safeMemo_lit_short)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
  (safeMemo_spqrInit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials
  (allSeedTuples safeMemo_of_seedTrialOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
  (runTrace_eq_r0 honestSaltsOf_eq_r0 cleanPreKeyRep_eq_r0 bobSessionStartCollides_eq_r0
   setupSecret_r0_4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf pqMsgOf sendStOf sendMsgOf stA1c stA2c pqKey0 pqKey1 allStates24 allSalts13 cleanSendMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop (summary_at_3)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0
  (sendPtTs sendPtBytes_len_lt8)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins
  (PrefixPinned explains_at_3)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
  (termAt_lit_b HandshakeAt handshake_termAt pqSecrets_safeMemo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (SendStepOut send_step_at)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe
  (SafeMemo2 safeMemo_toSafeMemo2 not_memoCollisionOn_of_safeMemo2
   safeMemo2_trState_of_dr not_macTagForgery_of_sendStep)

private def bobCtx3 (cls : Nat → Nat) (p : PreKeyFields) : TrialCtx :=
  let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys1.pqr spqrB2A)
    (pqMsgOf (stA1c cls) (cls 1) 38) (preKeySpqrIndex p)).map (·.2)).toList
  { peerIk := serializedIk (dhPk ikA)
    myIk := serializedIk (dhPk ikB)
    extra := [keys1.rk, keys1.ck, keys1.pqr, stA0.cks, (stA2c cls).cks, (kdfCk stA0.cks).2]
    ownSalts := own
    seed? := some (kdfCk (stA1c cls).cks).2 }

private theorem bobTrials_at_3_or_nil (cls : Nat → Nat) (tr : ExecTrace) (p : PreKeyFields)
    (hpId : p.preKeyId = none) :
    let x : PreKeyRep := ⟨o1.ek, o1.ct, cleanSendMsg cls 1⟩
    let msg1 := encSig (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32)
    bobTrials r0 tr p x msg1 = [] ∨ bobTrials r0 tr p x msg1 = [bobCtx3 cls p] := by
  dsimp only
  unfold bobTrials ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm ProtocolSetup.spkSecTerm ProtocolSetup.ikBSecTerm ProtocolSetup.pqskSecTerm
  rw [hpId]
  dsimp only
  split
  · exact .inl rfl
  · right
    have hp0 : setupPublic r0 0 = dhPk ikA := setupPublic_0 (r := r0) (by decide)
    have hp2 : setupPublic r0 2 = dhPk ikB := setupPublic_2 (r := r0) (by decide)
    have hs1 : setupSecret r0 1 = ikB := setupSecret_1 (r := r0) (by decide)
    have hs2 : setupSecret r0 2 = spkB := setupSecret_2 (r := r0) (by decide)
    have hs4 : setupSecret r0 4 = pqskB := setupSecret_r0_4
    rw [hp0, hp2, hs1, hs2, hs4]
    have hct_eq : o1.ct = (kemEncap (kemPk pqskB) (rnd 23 32)).1 := by
      dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
        DY.Libsignal.PQXDH.aliceAgreement]
      rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; rfl
    have hek_eq : o1.ek = dhPk (rnd 22 32) := by
      dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
      rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; rfl
    have hss : (errToOption (kemDecap pqskB o1.ct)).getD (kemRejKey pqskB o1.ct) =
        (kemEncap (kemPk pqskB) (rnd 23 32)).2 := by
      rw [hct_eq, kemDecap_kemEncap]; rfl
    rw [hss]
    have hkeys : pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree o1.ek ikB)
        (agree o1.ek spkB) (Option.map (agree o1.ek) none)
        (kemEncap (kemPk pqskB) (rnd 23 32)).2) = keys1 := by
      rw [hek_eq]
      dsimp only [Option.map, keys1, o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
        DY.Libsignal.PQXDH.aliceAgreement]
      rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
      rw [agree_comm ikA spkB, agree_comm (rnd 22 32) ikB, agree_comm (rnd 22 32) spkB]
      rfl
    rw [hkeys]
    have hrk : (encSig (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32)).ratchetKey =
        dhPk dhsA := rfl
    have hcnt : (encSig (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32)).counter = 1 := rfl
    have hpqm : (encSig (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32)).pqRatchet =
        pqMsgOf (stA1c cls) (cls 1) 38 := rfl
    rw [hrk, hcnt, hpqm]
    have hcc : (createChain keys1.rk (dhPk dhsA) spkB).2 = stA0.cks := by
      change (createChain keys1.rk (dhPk dhsA) spkB).2 = (createChain keys1.rk (dhPk spkB) dhsA).2
      rw [createChain_comm keys1.rk dhsA spkB]
    rw [hcc]
    rfl

private theorem safeMemo2_alice_init_state
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {st : TRState}
    (hh : HandshakeAt S g pts)
    (hpart_peer : st.peer = "bob")
    (hcore_eq : st.myIk = serializedIk (dhPk ikA) ∧
                st.peerIk = serializedIk (dhPk ikB) ∧
                st.rk = stA0.rk ∧
                st.dhs = dhsA ∧
                st.sid = stA0.sid)
    (hrecv_eq : st.recv = [{ ratchetKey := dhPk spkB, chainKey := keys1.ck, index := 0, rIdx := 1 }])
    (hspqr : SafeMemo dagSize dagOp dagBytes S g pts st.spqr)
    (hcks : SafeMemo dagSize dagOp dagBytes S g pts st.cks) :
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", st⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  refine safeMemo2_trState_of_dr (ls₀ := ⟨"alice", st⟩)
    (cLast := { ratchetKey := dhPk spkB, chainKey := keys1.ck, index := 0, rIdx := 1 })
    rfl rfl (Or.inl rfl) (Or.inr hpart_peer) hspqr ?_ ?_ ?_ (by decide)
  · intro u hu
    dsimp only at hu
    rw [hcore_eq.1, hcore_eq.2.1, hcore_eq.2.2.1, hcore_eq.2.2.2.1, hcore_eq.2.2.2.2] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hh.ik0s.safeMemo
    · exact hh.ik1s.safeMemo
    · exact hh.stA0_rk.safeMemo
    · exact hh.t_dhsA.safeMemo
    · exact hcks
    · exact hh.stA0_sid.safeMemo
  · intro c hc
    dsimp only at hc
    rw [hrecv_eq, List.mem_singleton] at hc
    subst hc
    exact ⟨hh.pk2.safeMemo, hh.ck_init.safeMemo⟩
  · dsimp only; rw [hrecv_eq]; rfl

/-- At Call 3 (`bobStart`), `cleanPreKeyRep r cls spqrIdxs` triggers no implicit rejection,
`MemoCollisionOn`, or `MacTagForgeryOrCollision` on `ssClean cls spqrIdxs 3`. -/
theorem not_bobStartCollides_clean
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (vis' : List VisEntry)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (p : PreKeyFields)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hcls : ValidCoinLens cls)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs 3) vis' (trace0.take 3))
    (hp : parsePreKeyWire (ev 3).input = some p) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn evictedI0 r S g'
        (runTrace r (ssClean cls spqrIdxs 3)) vis'
        (honestSaltsOf r (ssClean cls spqrIdxs 3)) p
        (cleanPreKeyRep r cls spqrIdxs) := by
  rw [bobSessionStartCollides_eq_r0 hfit, runTrace_eq_r0 hfit,
      honestSaltsOf_eq_r0 hfit, cleanPreKeyRep_eq_r0 hfit]
  have hpinned := explains_at_3 hfit hExp
  obtain ⟨hst_sum, hsec_sum, hsalts_sum, hrep_eq⟩ := summary_at_3 cls spqrIdxs
  set tr := runTrace r0 (ssClean cls spqrIdxs 3)
  set salts := honestSaltsOf r0 (ssClean cls spqrIdxs 3)
  set pts := plaintextTerms vis'
  have hpts_eq : pts = [randTerm (sendPtTs 0) 32, randTerm (sendPtTs 1) 32] := by
    change plaintextTerms vis' = _
    rw [hpinned.vis_pts]; rfl
  have hpt0_mem : randTerm (sendPtTs 0) 32 ∈ pts := by rw [hpts_eq]; simp
  have hpt1_mem : randTerm (sendPtTs 1) 32 ∈ pts := by rw [hpts_eq]; simp
  have hh := handshake_termAt (pts := pts) hpinned.base
  have hspqr_stA0 : SafeMemo dagSize dagOp dagBytes S g' pts stA0.spqr :=
    safeMemo_spqrInit hh.pqr.safeMemo (safeMemo_lit_short (by decide))
  have hs0 : SendStepOut (cls := cls) S g' pts stA0 0 :=
    send_step_at hpinned hcls (by decide) (by decide) hpt0_mem rfl
      hspqr_stA0 hh.pk4 hh.ik0s hh.ik1s hh.stA0_cks rfl rfl
  have hs1 : SendStepOut (cls := cls) S g' pts (stA1c cls) 1 :=
    send_step_at hpinned hcls (by decide) (by decide) hpt1_mem rfl
      hs0.spqr_sm hh.pk4 hh.ik0s hh.ik1s hs0.cks_next rfl rfl
  have hclean1 : cleanSendMsg cls 1 =
      encMsg (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32) := rfl
  have hparse1 : parseTrSignalMsg (cleanSendMsg cls 1) =
      some (encSig (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32)) := by
    rw [hclean1]; exact parse_encMsg _ _ _ _
  have hpId : p.preKeyId = none := (ev3_full_fields hp).2.2.1
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  rw [hrep_eq]
  dsimp only
  rw [hparse1]
  dsimp only
  rintro (hmemo | hmac_forg)
  · have hbt3 := bobTrials_at_3_or_nil cls tr p hpId
    refine not_memoCollisionOn_of_safeMemo2 ?_ ?_ hmemo
    · intro t ht
      rw [List.append_nil]
      change SafeMemo2 S g' pts t
      unfold prefixTerms principalTerms at ht
      simp only [List.mem_append] at ht
      rcases ht with ((hsend | hstate) | hsec) | hpt
      · rcases hpinned.vis_sends t hsend with rfl | rfl | ⟨j, hj, rfl⟩
        · exact safeMemo_toSafeMemo2 hh.ek.safeMemo
        · exact safeMemo_toSafeMemo2 hh.ct.safeMemo
        · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
          · exact safeMemo_toSafeMemo2 hs0.wmac.safeMemo
          · exact safeMemo_toSafeMemo2 hs1.wmac.safeMemo
      · rw [hst_sum] at hstate
        have htake3 : (allStates24 cls).take 3 =
            [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩] := rfl
        rw [htake3] at hstate
        simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hstate
        rcases hstate with rfl | rfl | rfl
        · exact safeMemo2_alice_init_state hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            hspqr_stA0 hh.stA0_cks.safeMemo
        · exact safeMemo2_alice_init_state hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            hs0.spqr_sm hs0.cks_next.safeMemo
        · exact safeMemo2_alice_init_state hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            hs1.spqr_sm hs1.cks_next.safeMemo
      · rw [hsec_sum] at hsec
        exact safeMemo_toSafeMemo2 (pqSecrets_safeMemo hh t hsec)
      · have hpt' : t ∈ [randTerm (sendPtTs 0) 32, randTerm (sendPtTs 1) 32] := by
          rw [← hpts_eq]; exact hpt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt'
        rcases hpt' with rfl | rfl
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext hpt0_mem
            (by rw [hpinned.send_pt 0 (by decide)]; exact sendPtBytes_len_lt8 (by decide)))
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext hpt1_mem
            (by rw [hpinned.send_pt 1 (by decide)]; exact sendPtBytes_len_lt8 (by decide)))
    · intro t ht
      rw [List.append_nil]
      change SafeMemo2 S g' pts t
      have ht_full : t ∈ [o1.ek, o1.ct, cleanSendMsg cls 1] ++
          ([bobCtx3 cls p]).flatMap (trialTerms salts
            (encSig (stA1c cls) (rnd 39 (cls 1)) (pqKey1 cls) (rnd 38 32))) := by
        rcases hbt3 with hbt | hbt <;> rw [hbt] at ht
        · simp only [List.flatMap_nil, List.append_nil] at ht
          exact List.mem_append_left _ ht
        · exact ht
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.flatMap_cons, List.flatMap_nil] at ht_full
      rcases ht_full with (rfl | rfl | rfl) | htrial
      · exact safeMemo_toSafeMemo2 hh.ek.safeMemo
      · exact safeMemo_toSafeMemo2 hh.ct.safeMemo
      · exact safeMemo_toSafeMemo2 hs1.wmac.safeMemo
      · refine safeMemo_toSafeMemo2 (safeMemo_of_seedTrialOk
          (salts := salts) (ctx := bobCtx3 cls p)
          (nSalts := 3) (seed_id := 124) (pIk_id := 30) (mIk_id := 31) (wire_id := 133)
          (by decide) ?_ ?_ hs1.ct.safeMemo hh.ik0s hh.ik1s hs1.wire ?_ t htrial)
        · intro salt hsalt
          rw [hsalts_sum] at hsalt
          have hs3 : (allSalts13 cls).take 3 = [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] := rfl
          rw [hs3] at hsalt
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
          rcases hsalt with rfl | rfl | rfl
          · exact ⟨8, by decide, termAt_lit_b (by decide +kernel)⟩
          · exact ⟨100, by decide, hs0.pqKey⟩
          · exact ⟨120, by decide, hs1.pqKey⟩
        · intro u hu
          dsimp only [bobCtx3] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hh.rk_init.safeMemo
          · exact hh.ck_init.safeMemo
          · exact hh.pqr.safeMemo
          · exact hh.stA0_cks.safeMemo
          · exact hs1.cks_next.safeMemo
          · exact hs0.seed.safeMemo
        · intro seed hseed
          dsimp only [bobCtx3] at hseed
          cases hseed
          exact hs1.seed
  · have hsalt1_mem : pqKeyOf (stA1c cls) (cls 1) (sendPtTs 1) ∈ salts := by
      rw [hsalts_sum]
      have hs3 : (allSalts13 cls).take 3 = [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] := rfl
      rw [hs3]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    exact not_macTagForgery_of_sendStep (j := 1) (by decide) hsalt1_mem hs1 hmac_forg

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoBobStart
