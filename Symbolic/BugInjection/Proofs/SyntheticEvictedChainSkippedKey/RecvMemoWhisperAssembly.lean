/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsA
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup

/-!
# Whisper and Replay Collision Refutation Assembly

Combines `prefix_safe_at_whisper`, `safeMemo_existing_and_skipped_trials`, and a
`NewChainTrialsProp` hypothesis to prove `not_recvCollisionOn_of_new_chain_trials` for every
`k ∈ whisperOrReplayIndices`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperAssembly

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

open DY.Libsignal.TripleRatchet
  (TRState messageVersion parseTrSignalMsg consumeMessageKey recvChainFor skippedSeeds)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry TrialCtx trialTerms
   runTrace availableStates honestSaltsOf ownKeys plaintextTerms
   whisperTrials Explains RecvCollisionOn)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSig parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (stA0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0 trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens whisperOrReplayIndices ssClean cleanRecvTerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators (SafeMemo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
  (runTrace_eq_r0 honestSaltsOf_eq_r0 cleanRecvTerm_eq_r0 recvCollisionOn_eq_r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace (pqKeyOf)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
  (summary_at_whisperOrReplay whisperTrials_eq_of_skipped)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0 (sendPtTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (SendStepOut)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe
  (safeMemo_toSafeMemo2 not_memoCollisionOn_of_safeMemo2 not_macTagForgery_of_sendStep)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1
  (meta0 stateMetas StateWitness)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2
  (whisperMsgMeta WhisperPrefixBundle prefix_safe_at_whisper)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsA
  (safeMemo_existing_and_skipped_trials)

private theorem exists_idx_of_mem {α : Type} {x : α} {l : List α} (d : α) (hx : x ∈ l) :
    ∃ i < l.length, l.getD i d = x := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact ⟨0, Nat.zero_lt_succ _, rfl⟩
    · obtain ⟨i, hi, hget⟩ := ih hrest
      exact ⟨i + 1, Nat.succ_lt_succ hi, hget⟩

private theorem getD_take_of_lt {α : Type} :
    ∀ (k : Nat) (l : List α) (i : Nat) (d : α), i < k → (l.take k).getD i d = l.getD i d
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ + 1, [], _, _, _ => rfl
  | _ + 1, _ :: _, 0, _, _ => rfl
  | k + 1, _ :: xs, i + 1, d, hi => getD_take_of_lt k xs i d (Nat.lt_of_succ_lt_succ hi)

abbrev NewChainTrialsProp : Prop :=
  ∀ {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k i : Nat}
    {S : OpaqueSymbolSemantics} {g : Ghost} {vis : List VisEntry}
    {ls ls₀ : DY.PersistentLocalState.LocalState TRState}
    {sSt : TRState},
    k ∈ whisperOrReplayIndices →
    WhisperPrefixBundle cls spqrIdxs k S g vis →
    i < k →
    StateWitness S g (plaintextTerms vis) ls ls₀ (stateMetas.getD i meta0) →
    sSt.dhs = rnd (whisperMsgMeta k).1 32 →
    sSt.ns = 0 →
    SendStepOut (cls := cls) S g (plaintextTerms vis) sSt
      (if k = 24 then 0 else (k - 5) / 2 + 2) →
    let j := if k = 24 then 0 else (k - 5) / 2 + 2
    let msg := encSig sSt (rnd (sendPtTs j + 1) (cls j))
      (pqKeyOf sSt (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)
    let st := ls.state
    let tr := runTrace r0 (ssClean cls spqrIdxs k)
    let salts := honestSaltsOf r0 (ssClean cls spqrIdxs k)
    let own := ownKeys r0 tr st msg
    let newCtxs :=
      (match recvChainFor st.toDRState msg.ratchetKey with
       | some (c, true) => [c]
       | _ => []).map fun c =>
        match consumeMessageKey c msg.counter with
        | none =>
          ({ peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
             ownSalts := [], seed? := none } : TrialCtx)
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := own, seed? := some seed }
    ∀ ctx ∈ newCtxs,
      ∀ t ∈ trialTerms salts msg ctx,
        SafeMemo dagSize dagOp dagBytes S g (plaintextTerms vis) t

theorem not_recvCollisionOn_of_new_chain_trials
    (hNew : NewChainTrialsProp)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g' : Ghost) (vis' : List VisEntry)
    (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (k : Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hcls : ValidCoinLens cls)
    (hk : k ∈ whisperOrReplayIndices)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs k) vis' (trace0.take k)) :
    ¬ RecvCollisionOn evictedI0 r S g'
        (runTrace r (ssClean cls spqrIdxs k)) vis'
        (honestSaltsOf r (ssClean cls spqrIdxs k))
        (cleanRecvTerm r cls spqrIdxs k) := by
  rw [recvCollisionOn_eq_r0 hfit, runTrace_eq_r0 hfit,
      honestSaltsOf_eq_r0 hfit, cleanRecvTerm_eq_r0 hfit]
  have wb := prefix_safe_at_whisper hfit hcls hk hExp
  obtain ⟨sSt, hrecv_eq, hsalt_mem, hsSt_dhs, hsSt_ns, hout⟩ := wb.sender
  set j := if k = 24 then 0 else (k - 5) / 2 + 2
  set tr := runTrace r0 (ssClean cls spqrIdxs k)
  set salts := honestSaltsOf r0 (ssClean cls spqrIdxs k)
  set msg := encSig sSt (rnd (sendPtTs j + 1) (cls j))
    (pqKeyOf sSt (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)
  have hparse : parseTrSignalMsg (cleanRecvTerm r0 cls spqrIdxs k) = some msg := by
    rw [hrecv_eq]
    exact parse_encMsg _ _ _ _
  have hclean_eq := (summary_at_whisperOrReplay cls spqrIdxs hk).2.2.2.2
  unfold RecvCollisionOn
  dsimp only
  rw [hparse]
  dsimp only
  rintro (hmemo | hmac_forg)
  · refine not_memoCollisionOn_of_safeMemo2 ?_ ?_ hmemo
    · intro t ht
      rw [List.append_nil]
      exact wb.hPref t ht
    · intro t ht
      rw [List.append_nil]
      rcases List.mem_cons.mp ht with rfl | hflat
      · rw [hclean_eq]
        exact safeMemo_toSafeMemo2 hout.wmac.safeMemo
      · obtain ⟨ctx, hctx, ht_trial⟩ := List.mem_flatMap.mp hflat
        rw [whisperTrials_eq_of_skipped] at hctx
        have hver : msg.version = messageVersion := rfl
        simp only [hver, ↓reduceIte] at hctx
        obtain ⟨st, hst_avail, hctx_st⟩ := List.mem_flatMap.mp hctx
        unfold availableStates at hst_avail
        obtain ⟨ls, hls_mem, rfl⟩ := List.mem_map.mp hst_avail
        obtain ⟨i, hi_l, hls_get⟩ := exists_idx_of_mem ⟨"alice", stA0⟩ hls_mem
        have htk_len : (stateMetas.take k).length = k := by
          rw [List.length_take, show stateMetas.length = 24 from rfl]
          have := wb.hk_le
          omega
        have hi_tk : i < (stateMetas.take k).length := wb.hstates.1 ▸ hi_l
        have hi : i < k := htk_len ▸ hi_tk
        have sw := wb.hstates.2.2 i hi_tk
        rw [hls_get, getD_take_of_lt k stateMetas i meta0 hi] at sw
        rw [List.map_append] at hctx_st
        refine safeMemo_toSafeMemo2 ?_
        rcases List.mem_append.mp hctx_st with hchains | hskip_c
        · rcases List.mem_append.mp hchains with hexist | hnew
          · exact safeMemo_existing_and_skipped_trials hk wb hi sw hsSt_dhs hsSt_ns hout
              ctx (List.mem_append_left _ hexist) t ht_trial
          · exact hNew hk wb hi sw hsSt_dhs hsSt_ns hout ctx hnew t ht_trial
        · exact safeMemo_existing_and_skipped_trials hk wb hi sw hsSt_dhs hsSt_ns hout
            ctx (List.mem_append_right _ hskip_c) t ht_trial
  · exact not_macTagForgery_of_sendStep wb.hj_lt hsalt_mem hout hmac_forg

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperAssembly
