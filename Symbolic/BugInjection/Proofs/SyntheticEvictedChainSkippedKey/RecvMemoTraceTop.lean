/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace

/-!
# Closed-Form Prefix Summaries at Receiver Calls

Proves closed-form equations for `storedStates`, `storedSecrets`, `skippedStoredEvents`,
`honestSaltsOf`, `cleanPreKeyRep`, and `cleanRecvTerm` at `k = 3` (`summary_at_3`) and at every
`k ∈ whisperOrReplayIndices` (`summary_at_whisperOrReplay`), and rewrites `whisperTrials` in terms
of `skippedStoredEvents`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop

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

open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Bytes Participant Trace ExecTrace)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg TREvent messageVersion findRecvChain recvChainFor consumeMessageKey
   skippedSeeds)
open DY.Libsignal.Composed.Refinement
  (Step Ghost OpaqueSymbolSemantics
   setupTrace runTrace runSteps storedStates availableStates storedSecrets
   honestKeysOf honestSaltsOf TrialCtx ownKeys whisperTrials gamma)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (NetE StT rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (bh1 kh1 o1 stA0 t1 t2 t3 t4 t5 t4_length t5_length)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (pqSecretsList t1Pure t2Pure t3Pure t4Pure t1_eq_pure t2_eq_pure t3_eq_pure t4_eq_pure)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (whisperOrReplayIndices cleanCallSteps ssClean cleanMsgIdx cleanRecvTerm cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
  (setupTrace_r0_eq_t4 step0_next_t4 cleanPreKeyRep_ek_ct)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
  (length_append le_append_of_le at?_append_self at?_mono getMessageSentAt_mono
   encTrGen_getMessageSentAt_pq encTrGen_getMessageSentAt_msg
   skippedStoredEvents skippedStoredEvents_nil skippedStoredEvents_append_non
   skippedStoredEvents_append_skipped skippedStoredEvents_encTrGen
   storedSecrets_append_pub storedSecrets_encTrGen
   storedStates_append_pub storedStates_encTrGen honestKeysOf_append)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf pqMsgOf sendStOf sendMsgOf recvStOf
   stA1c stA2c pqKey0 pqKey1 stB1c bobSkipEntry
   hrConfig hrStates allStates24 allSalts13 cleanSendMsg
   at?_append_at trClean1 trClean2 trClean3 t5_at?_30 step1_enc_next step2_enc_next
   trClean2_eq step3_bobStart_next
   SyncPair syncPair_initial halfRound_send_spec halfRound_full_spec)

private theorem storedSecrets_nil : storedSecrets Trace.nil = [] := by
  unfold storedSecrets
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem runSteps_append :
    ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
      runSteps (ss₁ ++ ss₂) tr = runSteps ss₂ (runSteps ss₁ tr)
  | [], _, _ => rfl
  | s :: ss₁, ss₂, tr => runSteps_append ss₁ ss₂ (s.next tr)

private theorem foldl_next_eq_runSteps :
    ∀ (ss : List Step) (tr : ExecTrace),
      ss.foldl (fun t s => s.next t) tr = runSteps ss tr
  | [], _ => rfl
  | s :: ss, tr => foldl_next_eq_runSteps ss (s.next tr)

theorem storedSecrets_t5 : storedSecrets t5 = pqSecretsList := by
  have ht4 : storedSecrets t4 = pqSecretsList := by
    rw [t4_eq_pure]
    simp only [t4Pure, t3Pure, t2Pure, t1Pure,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr,
      storedSecrets_append_pub, storedSecrets_nil, length_append,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  repeat rw [storedSecrets_append_pub]
  rw [ht4]
  repeat erw [List.append_nil]

theorem storedStates_t5 : storedStates r0 t5 = [⟨"alice", stA0⟩] := by
  have h0 : storedStates r0 t4 = [] := by
    rw [← setupTrace_r0_eq_t4]
    simp [storedStates, DY.Libsignal.Composed.Refinement.newIndices]
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  have hdhs : rnd (t4.length + 2) 32 = rnd 24 32 := by rw [t4_length]
  rw [hdhs]
  repeat rw [storedStates_append_pub _ r0 _
    (by simp -failIfUnchanged only [setupTrace_r0_eq_t4, length_append, t4_length]; omega)]
  rw [h0]
  repeat erw [List.append_nil]
  rfl

theorem skippedStoredEvents_t5 : skippedStoredEvents t5 = [] := by
  have ht1 : skippedStoredEvents t1Pure = [] := by
    unfold t1Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact skippedStoredEvents_nil
  have ht2 : skippedStoredEvents t2Pure = [] := by
    unfold t2Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact ht1
  have ht3 : skippedStoredEvents t3Pure = [] := by
    unfold t3Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact ht2
  have ht4 : skippedStoredEvents t4 = [] := by
    rw [t4_eq_pure]
    unfold t4Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact ht3
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  repeat rw [skippedStoredEvents_append_non _ _ rfl]
  exact ht4

theorem summary_at_3 (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    let tr := runTrace r0 (ssClean cls spqrIdxs 3)
    storedStates r0 tr = (allStates24 cls).take 3 ∧
    storedSecrets tr = pqSecretsList ∧
    honestSaltsOf r0 (ssClean cls spqrIdxs 3) = (allSalts13 cls).take 3 ∧
    cleanPreKeyRep r0 cls spqrIdxs = ⟨o1.ek, o1.ct, cleanSendMsg cls 1⟩ := by
  obtain ⟨htr, _, _, _⟩ := trClean2_eq cls spqrIdxs
  have hlen1 : (trClean1 cls).length = 38 := by unfold trClean1; rw [RecvMemoTrace0.length_encTrGen, t5_length]
  have hmin0 : (setupTrace r0).length ≤ t5.length := by
    rw [setupTrace_r0_eq_t4, t4_length, t5_length]; omega
  have hmin1 : (setupTrace r0).length ≤ (trClean1 cls).length := by
    rw [setupTrace_r0_eq_t4, t4_length, hlen1]; omega
  have hst1 : storedStates r0 (trClean1 cls) = [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩] := by
    unfold trClean1
    rw [storedStates_encTrGen r0 t5 "alice" 30 stA0 (cls 0) _ hmin0, storedStates_t5, t5_length]
    rfl
  have hst2 : storedStates r0 (trClean2 cls) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩] := by
    unfold trClean2
    rw [storedStates_encTrGen r0 (trClean1 cls) "alice" 36 (stA1c cls) (cls 1) _ hmin1,
        hst1, hlen1]
    rfl
  have hsec2 : storedSecrets (trClean2 cls) = pqSecretsList := by
    unfold trClean2 trClean1
    rw [storedSecrets_encTrGen, storedSecrets_encTrGen, storedSecrets_t5]
  have hsalts : honestSaltsOf r0 (ssClean cls spqrIdxs 3) =
      [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] := by
    have hss : ssClean cls spqrIdxs 3 =
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
    have hs1 := step1_enc_next cls
    have hs2 := step2_enc_next cls
    rw [hss]; unfold honestSaltsOf
    simp only [honestKeysOf, Step.publishedSpqrKey?,
      DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx,
      DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx,
      setupTrace_r0_eq_t4, step0_next_t4, hs1, hs2]
    have hne1 : ¬ (33 = t5.length + 3) := by rw [t5_length]; omega
    have hne2 : ¬ (40 = (trClean1 cls).length + 3) := by rw [hlen1]; omega
    simp only [hne1, hne2, ↓reduceIte]
    have hpq0 := encTrGen_getMessageSentAt_pq t5 "alice" 30 stA0 (cls 0) (pqKey0 cls)
    rw [t5_length] at hpq0
    have hpq1 := encTrGen_getMessageSentAt_pq (trClean1 cls) "alice" 36 (stA1c cls) (cls 1) (pqKey1 cls)
    rw [hlen1] at hpq1
    rw [t5_length, hlen1]
    unfold trClean2; rw [hpq1]
    unfold trClean1; rw [hpq0]; rfl
  have hrep : cleanPreKeyRep r0 cls spqrIdxs = ⟨o1.ek, o1.ct, cleanSendMsg cls 1⟩ := by
    obtain ⟨hek, hct⟩ := cleanPreKeyRep_ek_ct cls spqrIdxs
    have hmsg : cleanRecvTerm r0 cls spqrIdxs 3 = cleanSendMsg cls 1 := by
      unfold cleanRecvTerm cleanMsgIdx
      simp only [↓reduceIte, htr]
      unfold trClean2 cleanSendMsg sendMsgOf
      have hm44 := encTrGen_getMessageSentAt_msg (trClean1 cls) "alice" 36 (stA1c cls) (cls 1)
        (pqKey1 cls) (i := 44) (by rw [hlen1])
      rw [hlen1] at hm44
      rw [hm44]; rfl
    cases h : cleanPreKeyRep r0 cls spqrIdxs
    rw [h] at hek hct
    dsimp only at hek hct
    have hm_eq : (cleanPreKeyRep r0 cls spqrIdxs).msg = cleanRecvTerm r0 cls spqrIdxs 3 := rfl
    rw [h] at hm_eq
    dsimp only at hm_eq
    rw [hek, hct, hm_eq, hmsg]
  exact ⟨by rw [htr, hst2]; rfl, by rw [htr, hsec2], by rw [hsalts]; rfl, hrep⟩

def hrSStH (h : Nat) : Nat := 54 + 14 * h
def hrRStH (h : Nat) : Nat := if h = 0 then 43 else 46 + 14 * h

def hrSteps (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (h : Nat) : List Step :=
  let (me, peer, _, _) := hrConfig cls h
  let curLen := 55 + 14 * h
  [Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (curLen + 2),
   Step.messageDecrypt peer (hrRStH h) (curLen + 6) (curLen + 2) (spqrIdxs (5 + 2 * h))]

private theorem hrConfig_parties :
    ∀ h (cls : Nat → Nat),
      (hrConfig cls h).1 = (if h % 2 = 0 then "bob" else "alice") ∧
      (hrConfig cls h).2.1 = (if h % 2 = 0 then "alice" else "bob")
  | 0, _ => ⟨rfl, rfl⟩
  | h + 1, cls => by
    obtain ⟨h1, h2⟩ := hrConfig_parties h cls
    unfold hrConfig
    cases hrc : hrConfig cls h with
    | mk me rest =>
      rcases rest with ⟨peer, sSt, rSt⟩
      rw [hrc] at h1 h2
      dsimp only at h1 h2 ⊢
      by_cases he : h % 2 = 0
      · have hne : (h + 1) % 2 ≠ 0 := by omega
        simp only [he, hne, ↓reduceIte] at h1 h2 ⊢
        exact ⟨h2, h1⟩
      · have he1 : (h + 1) % 2 = 0 := by omega
        simp only [he, he1, ↓reduceIte] at h1 h2 ⊢
        exact ⟨h2, h1⟩

theorem cleanCallSteps_eq_hr (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    cleanCallSteps cls spqrIdxs =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33,
       Step.messageEncrypt "alice" 36 (cls 1) 40,
       Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
      (List.range 10).flatMap (hrSteps cls spqrIdxs) := by
  have hp : ∀ h, h < 10 →
      (hrSteps cls spqrIdxs h) =
        let me := if h % 2 = 0 then "bob" else "alice"
        let peer := if h % 2 = 0 then "alice" else "bob"
        let curLen := 55 + 14 * h
        [Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (curLen + 2),
         Step.messageDecrypt peer (hrRStH h) (curLen + 6) (curLen + 2) (spqrIdxs (5 + 2 * h))] := by
    intro h _
    obtain ⟨h1, h2⟩ := hrConfig_parties h cls
    unfold hrSteps
    cases hrc : hrConfig cls h with
    | mk me rest =>
      rcases rest with ⟨peer, sSt, rSt⟩
      rw [hrc] at h1 h2
      dsimp only at h1 h2 ⊢
      rw [h1, h2]
  have hr10 : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [hr10]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hp 0 (by omega), hp 1 (by omega), hp 2 (by omega), hp 3 (by omega), hp 4 (by omega),
      hp 5 (by omega), hp 6 (by omega), hp 7 (by omega), hp 8 (by omega), hp 9 (by omega)]
  rfl

theorem trClean3_props (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    let tr3 := runSteps
      [Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)]
      (trClean2 cls)
    tr3 = trClean3 cls (spqrIdxs 3) ∧
    tr3.length = 55 ∧
    trClean1 cls ≤ tr3 ∧
    tr3.at? 54 = some (StT "bob" (stB1c cls)) ∧
    tr3.at? 43 = some (StT "alice" (stA2c cls)) ∧
    storedStates r0 tr3 = [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩,
      ⟨"bob", stB1c cls⟩] ∧
    storedSecrets tr3 = pqSecretsList ∧
    skippedStoredEvents tr3 = [bobSkipEntry] := by
  have hs3 := step3_bobStart_next cls (spqrIdxs 3)
  obtain ⟨htr2, hlen2, _, hle12⟩ := trClean2_eq cls spqrIdxs
  obtain ⟨hst_2, hsec_2, _, _⟩ := summary_at_3 cls spqrIdxs
  rw [htr2] at hst_2 hsec_2
  have hlen1 : (trClean1 cls).length = 38 := by
    unfold trClean1; rw [RecvMemoTrace0.length_encTrGen, t5_length]
  have hle23 : trClean2 cls ≤ trClean3 cls (spqrIdxs 3) := by
    unfold trClean3; dsimp only
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
        (Trace.append_le _ _) _) _) _) _) _) _) _) _) _
  have hlen3 : (trClean3 cls (spqrIdxs 3)).length = 55 := by
    unfold trClean3; simp only [length_append, hlen2]
  have hat43_2 : (trClean2 cls).at? 43 = some (StT "alice" (stA2c cls)) := by
    unfold trClean2 stA2c sendStOf
    have hc : rnd ((trClean1 cls).length + 1) (cls 1) = rnd 39 (cls 1) := by rw [hlen1]
    rw [← hc]
    exact RecvMemoTrace0.encTrGen_at?_st (trClean1 cls) "alice" 36 (stA1c cls) (cls 1) (pqKey1 cls)
      (by rw [hlen1])
  have hat54 : (trClean3 cls (spqrIdxs 3)).at? 54 = some (StT "bob" (stB1c cls)) := by
    unfold trClean3; dsimp only
    exact at?_append_at _ _ (by simp only [length_append, hlen2])
  have hskip2 : skippedStoredEvents (trClean2 cls) = [] := by
    unfold trClean2 trClean1
    rw [skippedStoredEvents_encTrGen, skippedStoredEvents_encTrGen, skippedStoredEvents_t5]
  have hskip3 : skippedStoredEvents (trClean3 cls (spqrIdxs 3)) = [bobSkipEntry] := by
    unfold trClean3; dsimp only
    rw [skippedStoredEvents_append_non _ _ rfl, skippedStoredEvents_append_non _ _ rfl,
        skippedStoredEvents_append_non _ _ rfl, skippedStoredEvents_append_skipped,
        skippedStoredEvents_append_non _ _ rfl, skippedStoredEvents_append_non _ _ rfl,
        skippedStoredEvents_append_non _ _ rfl, skippedStoredEvents_append_non _ _ rfl,
        skippedStoredEvents_append_non _ _ rfl, skippedStoredEvents_append_non _ _ rfl, hskip2]
    rfl
  have hst3 : storedStates r0 (trClean3 cls (spqrIdxs 3)) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩, ⟨"bob", stB1c cls⟩] := by
    unfold trClean3; dsimp only
    repeat rw [storedStates_append_pub _ r0 _
      (by simp -failIfUnchanged only [setupTrace_r0_eq_t4, length_append, hlen2, t4_length]; omega)]
    rw [hst_2]
    repeat erw [List.append_nil]
    rfl
  have hsec3 : storedSecrets (trClean3 cls (spqrIdxs 3)) = pqSecretsList := by
    unfold trClean3; dsimp only
    repeat rw [storedSecrets_append_pub]
    rw [hsec_2]
    repeat erw [List.append_nil]
  dsimp only [runSteps]
  rw [hs3]
  exact ⟨rfl, hlen3, Trace.le_trans _ _ _ hle12 hle23, hat54, at?_mono hle23 hat43_2,
    hst3, hsec3, hskip3⟩

/-- Closed-form trace, state, and salt summary after `h` completed half-rounds (`0 ≤ h ≤ 10`). -/
theorem hrPrefix_props (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    ∀ h, h ≤ 10 →
      let steps := [Step.aliceStart "alice" "bob" 4 6 bh1,
        Step.messageEncrypt "alice" 30 (cls 0) 33,
        Step.messageEncrypt "alice" 36 (cls 1) 40,
        Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
        (List.range h).flatMap (hrSteps cls spqrIdxs)
      let tr := runTrace r0 steps
      let (me, peer, sSt, rSt) := hrConfig cls h
      tr.length = 55 + 14 * h ∧
      trClean1 cls ≤ tr ∧
      tr.at? (hrSStH h) = some (StT me sSt) ∧
      tr.at? (hrRStH h) = some (StT peer rSt) ∧
      (∃ ts, SyncPair me peer sSt rSt ts (55 + 14 * h)) ∧
      storedStates r0 tr = [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩,
        ⟨"bob", stB1c cls⟩] ++ (List.range h).flatMap (hrStates cls) ∧
      storedSecrets tr = pqSecretsList ∧
      skippedStoredEvents tr = [bobSkipEntry] ∧
      honestSaltsOf r0 steps = [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] ++
        (List.range h).map (fun i =>
          let (_, _, st_i, _) := hrConfig cls i
          pqKeyOf st_i (cls (2 + i)) (55 + 14 * i)) := by
  intro h hh
  induction h with
  | zero =>
    simp only [List.range_zero, List.flatMap_nil, List.map_nil, List.append_nil, Nat.mul_zero,
      Nat.add_zero]
    obtain ⟨htr2, _, _, _⟩ := trClean2_eq cls spqrIdxs
    obtain ⟨_, _, hsalts3, _⟩ := summary_at_3 cls spqrIdxs
    obtain ⟨htr3_eq, hlen3, hle13, hat54, hat43, hst3, hsec3, hskip3⟩ := trClean3_props cls spqrIdxs
    have hrun4 : runTrace r0
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] =
        trClean3 cls (spqrIdxs 3) := by
      have hsplit : [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] =
        ssClean cls spqrIdxs 3 ++
        [Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] := rfl
      rw [hsplit]; unfold runTrace
      rw [runSteps_append]
      change runSteps _ (runTrace r0 (ssClean cls spqrIdxs 3)) = _
      rw [htr2]; exact htr3_eq
    have hsalts4 : honestSaltsOf r0
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] =
        [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] := by
      have hsplit : [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] =
        ssClean cls spqrIdxs 3 ++
        [Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] := rfl
      rw [hsplit]; unfold honestSaltsOf at hsalts3 ⊢
      rw [honestKeysOf_append]
      have hk3 : honestKeysOf (setupTrace r0) (ssClean cls spqrIdxs 3) =
          [pqKey0 cls, pqKey1 cls] := by
        have hcons : DY.Spqr.zeroKey :: honestKeysOf (setupTrace r0) (ssClean cls spqrIdxs 3) =
            [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] := hsalts3
        exact List.cons.inj hcons |>.2
      rw [hk3]; simp [honestKeysOf, Step.publishedSpqrKey?]
    rw [htr3_eq] at hlen3 hle13 hat54 hat43 hst3 hsec3 hskip3
    rw [hrun4]
    exact ⟨hlen3, hle13, hat54, hat43, ⟨45, syncPair_initial cls⟩, hst3, hsec3, hskip3, hsalts4⟩
  | succ h ih =>
    obtain ⟨hlen, hle1, hsSt, hrSt, ⟨tsS, hsync⟩, hstates, hsec, hskip, hsalts⟩ :=
      ih (by omega)
    have hsteps_eq :
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
        (List.range (h + 1)).flatMap (hrSteps cls spqrIdxs) =
        ([Step.aliceStart "alice" "bob" 4 6 bh1,
          Step.messageEncrypt "alice" 30 (cls 0) 33,
          Step.messageEncrypt "alice" 36 (cls 1) 40,
          Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
         (List.range h).flatMap (hrSteps cls spqrIdxs)) ++
        hrSteps cls spqrIdxs h := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
    dsimp only
    rw [hsteps_eq]
    revert hsSt hrSt hsync
    cases hrc : hrConfig cls h with
    | mk me rest =>
      rcases rest with ⟨peer, sSt, rSt⟩
      intro hsSt hrSt hsync
      have hhrs : hrSteps cls spqrIdxs h =
          [Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2),
           Step.messageDecrypt peer (hrRStH h) (55 + 14 * h + 6) (55 + 14 * h + 2)
             (spqrIdxs (5 + 2 * h))] := by
        unfold hrSteps; rw [hrc]
      have hrc1 : hrConfig cls (h + 1) =
          (peer, me, recvStOf rSt sSt (cls (2 + h)) (55 + 14 * h),
            sendStOf sSt (cls (2 + h)) (55 + 14 * h)) := by
        unfold hrConfig; rw [hrc]
      obtain ⟨hlen2, hle_step, hat_s1, hat_r1, hkeys_hr, hstates2, hsec2, hskip2, hsync2⟩ :=
        halfRound_full_spec (idx := spqrIdxs (5 + 2 * h)) (cl := cls (2 + h))
          hlen (by omega) hsSt hrSt hsync
      have hrun_eq : runTrace r0
          (([Step.aliceStart "alice" "bob" 4 6 bh1,
             Step.messageEncrypt "alice" 30 (cls 0) 33,
             Step.messageEncrypt "alice" 36 (cls 1) 40,
             Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
            (List.range h).flatMap (hrSteps cls spqrIdxs)) ++
           hrSteps cls spqrIdxs h) =
          (Step.messageDecrypt peer (hrRStH h) (55 + 14 * h + 6) (55 + 14 * h + 2)
            (spqrIdxs (5 + 2 * h))).next
            ((Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2)).next
              (runTrace r0 ([Step.aliceStart "alice" "bob" 4 6 bh1,
                Step.messageEncrypt "alice" 30 (cls 0) 33,
                Step.messageEncrypt "alice" 36 (cls 1) 40,
                Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
               (List.range h).flatMap (hrSteps cls spqrIdxs)))) := by
        rw [hhrs]; unfold runTrace; rw [runSteps_append]; rfl
      rw [hrc1, hrun_eq]
      have harith14 : 55 + 14 * h + 14 = 55 + 14 * (h + 1) := by omega
      have hsH1 : hrSStH (h + 1) = 55 + 14 * h + 13 := by unfold hrSStH; omega
      have hrH1 : hrRStH (h + 1) = 55 + 14 * h + 5 := by unfold hrRStH; simp; omega
      refine ⟨by rw [hlen2, harith14], Trace.le_trans _ _ _ hle1 hle_step,
        by rw [hsH1]; exact hat_r1, by rw [hrH1]; exact hat_s1,
        ⟨55 + 14 * h + 7, by rw [← harith14]; exact hsync2⟩,
        ?_, hsec2.trans hsec, hskip2.trans hskip, ?_⟩
      · rw [hstates2, hstates, List.range_succ, List.flatMap_append, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, List.append_assoc]
        unfold hrStates; simp only [hrc]
      · unfold honestSaltsOf at hsalts ⊢
        rw [honestKeysOf_append, foldl_next_eq_runSteps]
        have hk_prev : honestKeysOf (setupTrace r0)
            ([Step.aliceStart "alice" "bob" 4 6 bh1,
              Step.messageEncrypt "alice" 30 (cls 0) 33,
              Step.messageEncrypt "alice" 36 (cls 1) 40,
              Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
             (List.range h).flatMap (hrSteps cls spqrIdxs)) =
            [pqKey0 cls, pqKey1 cls] ++
              (List.range h).map (fun i =>
                let (_, _, st_i, _) := hrConfig cls i
                pqKeyOf st_i (cls (2 + i)) (55 + 14 * i)) :=
          (List.cons.inj hsalts).2
        rw [hk_prev, hhrs]
        change DY.Spqr.zeroKey :: (_ ++ honestKeysOf (runTrace r0 _) _) = _
        rw [hkeys_hr, List.range_succ, List.map_append, List.map_cons, List.map_nil]
        simp only [hrc, List.cons_append, List.append_assoc]

/-- Closed-form trace, state, salt, and message summary for `k ∈ whisperOrReplayIndices`. -/
theorem summary_at_whisperOrReplay (cls : Nat → Nat) (spqrIdxs : Nat → UInt32)
    {k : Nat} (hk : k ∈ whisperOrReplayIndices) :
    let tr := runTrace r0 (ssClean cls spqrIdxs k)
    let j := if k = 24 then 0 else (k - 5) / 2 + 2
    let nSalts := if k = 24 then 13 else (k - 5) / 2 + 4
    storedStates r0 tr = (allStates24 cls).take k ∧
    storedSecrets tr = pqSecretsList ∧
    skippedStoredEvents tr = [bobSkipEntry] ∧
    honestSaltsOf r0 (ssClean cls spqrIdxs k) = (allSalts13 cls).take nSalts ∧
    cleanRecvTerm r0 cls spqrIdxs k = cleanSendMsg cls j := by
  by_cases hk24 : k = 24
  · subst hk24
    have hss24 : ssClean cls spqrIdxs 24 =
        [Step.aliceStart "alice" "bob" 4 6 bh1,
         Step.messageEncrypt "alice" 30 (cls 0) 33,
         Step.messageEncrypt "alice" 36 (cls 1) 40,
         Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
        (List.range 10).flatMap (hrSteps cls spqrIdxs) := by
      unfold ssClean
      rw [List.take_of_length_le (by rw [RecvDefs.cleanCallSteps_length]),
          cleanCallSteps_eq_hr]
    obtain ⟨_, hle1, _, _, _, hstates, hsec, hskip, hsalts⟩ := hrPrefix_props cls spqrIdxs 10 (by omega)
    simp only [↓reduceIte, hss24]
    have hlen_st : (allStates24 cls).length = 24 := by
      unfold allStates24 hrStates
      have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
      rw [hr]; rfl
    have hlen_sa : (allSalts13 cls).length = 13 := rfl
    refine ⟨?_, hsec, hskip, ?_, ?_⟩
    · rw [hstates, List.take_of_length_le (by rw [hlen_st])]; rfl
    · rw [hsalts, List.take_of_length_le (by rw [hlen_sa])]; rfl
    · have hcm24 : cleanMsgIdx 24 = 37 := rfl
      unfold cleanRecvTerm
      rw [hcm24, hss24]
      have hm37 := encTrGen_getMessageSentAt_msg t5 "alice" 30 stA0 (cls 0) (pqKey0 cls)
        (i := 37) (by rw [t5_length])
      rw [t5_length] at hm37
      rw [getMessageSentAt_mono hle1 hm37]; rfl
  · have hodd : ∃ h, h < 10 ∧ k = 5 + 2 * h := by
      simp only [whisperOrReplayIndices, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
      · exact ⟨4, by omega, rfl⟩
      · exact ⟨5, by omega, rfl⟩
      · exact ⟨6, by omega, rfl⟩
      · exact ⟨7, by omega, rfl⟩
      · exact ⟨8, by omega, rfl⟩
      · exact ⟨9, by omega, rfl⟩
      · exact absurd rfl hk24
    obtain ⟨h, hh, rfl⟩ := hodd
    have hss_odd : ssClean cls spqrIdxs (5 + 2 * h) =
        ([Step.aliceStart "alice" "bob" 4 6 bh1,
          Step.messageEncrypt "alice" 30 (cls 0) 33,
          Step.messageEncrypt "alice" 36 (cls 1) 40,
          Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
         (List.range h).flatMap (hrSteps cls spqrIdxs)) ++
        [let (me, _, _, _) := hrConfig cls h
         Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2)] := by
      unfold ssClean
      rw [cleanCallSteps_eq_hr]
      rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨hlen, _, hsSt, _, ⟨tsS, hsync⟩, hstates, hsec, hskip, hsalts⟩ :=
      hrPrefix_props cls spqrIdxs h (by omega)
    revert hsSt hsync
    cases hrc : hrConfig cls h with
    | mk me rest =>
      rcases rest with ⟨peer, sSt, rSt⟩
      intro hsSt hsync
      obtain ⟨_, _, _, _, _, hget_msg, hkeys1, hstates1, hsec1, hskip1⟩ :=
        halfRound_send_spec (cl := cls (2 + h)) hlen (by omega) hsSt hsync
      have hrun_odd : runTrace r0 (ssClean cls spqrIdxs (5 + 2 * h)) =
          (Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2)).next
            (runTrace r0 ([Step.aliceStart "alice" "bob" 4 6 bh1,
              Step.messageEncrypt "alice" 30 (cls 0) 33,
              Step.messageEncrypt "alice" 36 (cls 1) 40,
              Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
             (List.range h).flatMap (hrSteps cls spqrIdxs))) := by
        rw [hss_odd]; unfold runTrace
        rw [runSteps_append]; simp only [hrc, runSteps]
      have hne24 : ¬ (5 + 2 * h = 24) := by omega
      have hdiv : (5 + 2 * h - 5) / 2 = h := by omega
      simp only [hne24, ↓reduceIte, hdiv]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hrun_odd, hstates1, hstates]
        unfold allStates24 hrStates
        rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil,
            List.cons_append, List.nil_append, List.append_nil, List.take, hrc]
      · rw [hrun_odd, hsec1, hsec]
      · rw [hrun_odd, hskip1, hskip]
      · rw [hss_odd]; unfold honestSaltsOf at hsalts ⊢
        rw [honestKeysOf_append, foldl_next_eq_runSteps]
        have hk_prev := (List.cons.inj hsalts).2
        rw [hk_prev]
        simp only [hrc, List.append_eq] at hkeys1 ⊢
        change DY.Spqr.zeroKey :: (_ ++ honestKeysOf (runTrace r0 _) _) = _
        rw [hkeys1]
        unfold allSalts13
        rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.range, List.range.loop, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append, List.append_nil, List.take, hrc]
      · unfold cleanRecvTerm cleanMsgIdx
        have hne3 : ¬ (5 + 2 * h = 3) := by omega
        have hidx : 55 + 7 * (5 + 2 * h - 4) - 1 = 55 + 14 * h + 6 := by omega
        simp only [hne3, hne24, ↓reduceIte, hidx, hrun_odd, hget_msg]
        unfold cleanSendMsg
        have hne0 : ¬ (h + 2 = 0) := by omega
        have hne1 : ¬ (h + 2 = 1) := by omega
        have hsub : h + 2 - 2 = h := by omega
        simp only [hne0, hne1, ↓reduceIte, hsub, hrc]; rfl

/-- Expresses `whisperTrials` over `availableStates` and `skippedStoredEvents` without raw trace indices. -/
theorem whisperTrials_eq_of_skipped (i : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (msg : TRSignalMsg) :
    whisperTrials i r0 S g tr msg =
      if msg.version = messageVersion then
        let γ := gamma i S g
        (availableStates r0 tr).flatMap fun st =>
          let own := ownKeys r0 tr st msg
          let chains :=
            (st.toDRState.recv.filter fun c => decide (γ c.ratchetKey = γ msg.ratchetKey)) ++
            match recvChainFor st.toDRState msg.ratchetKey with
            | some (c, true) => [c]
            | _ => []
          (chains.map fun c =>
            match consumeMessageKey c msg.counter with
            | none =>
              { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
                ownSalts := [], seed? := none }
            | some (seed, c') =>
              { peerIk := st.peerIk, myIk := st.myIk,
                extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
                ownSalts := own, seed? := some seed }) ++
          (skippedStoredEvents tr).filterMap fun (s, pk, n, seed) =>
            if (findRecvChain st.toDRState.recv pk).isSome ∧
                γ pk = γ msg.ratchetKey ∧ n = msg.counter then
              some { peerIk := st.peerIk, myIk := st.myIk, extra := [],
                     ownSalts := if st.sessionInfo s.me = s then own else [],
                     seed? := some seed }
            else none
      else [] := by
  unfold whisperTrials skippedStoredEvents
  split
  · refine List.flatMap_congr fun st _ => congrArg₂ (· ++ ·) ?_ ?_
    · congr 1; congr 1
      unfold recvChainFor DY.Libsignal.TripleRatchet.recvHalfStep
      dsimp only [TRState.toDRState]
      cases h1 : findRecvChain st.recv msg.ratchetKey <;>
        cases h2 : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey <;>
        rfl
    · rw [List.filterMap_filterMap]
      apply List.filterMap_congr
      intro idx _
      cases tr.getEventAt TREvent idx with
      | none => rfl
      | some ev => cases ev <;> rfl
  · rfl

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
