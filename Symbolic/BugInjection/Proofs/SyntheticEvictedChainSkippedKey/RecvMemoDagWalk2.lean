/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1

/-!
# Clean Prefix Bundle at Whisper and Replay Calls

Combines the half-round DAG walk (`walk_hr_prefix`, `walk_hr_send`), ghost pinning
(`explains_at_whisperOrReplay`), and trace summaries (`summary_at_whisperOrReplay`) into
`WhisperPrefixBundle` for every `k ∈ whisperOrReplayIndices`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet (TRState)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry
   runTrace storedStates honestSaltsOf storedSecrets
   principalTerms plaintextTerms prefixTerms randTerm Explains)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (stA0 seedB0)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux (pqSecretsList)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0 trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens whisperOrReplayIndices ssClean cleanRecvTerm)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes honestSaltIds)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt safeMemo_plaintext)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
  (skippedStoredEvents)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf pqKey0 sendStOf sendMsgOf bobSkipEntry
   hrConfig hrStates allStates24 allSalts13 cleanSendMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
  (summary_at_whisperOrReplay)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0
  (sendPtTs sendPtBytes_len_lt8)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins
  (PrefixPinned explains_at_whisperOrReplay)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
  (handshake_termAt pqSecrets_safeMemo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (getSendRow SendStepOut cls0 hrConfig_toDRState)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe
  (SafeMemo2 safeMemo_toSafeMemo2)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1
  (StateMeta meta0 meta1 meta2 meta3 stepSendMeta hrConfigMeta hrMetas stateMetas
   getStateMeta hrStepCheck all_hr_steps_ok all_stateMetas_chains_ok
   StateTripleList stateTripleList_append
   walk_calls_0_to_2 walk_hr_send initStates4 prefixSaltsOf walk_hr_prefix)

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

private theorem getD_mem_of_lt {α : Type} :
    ∀ (l : List α) (i : Nat) (d : α), i < l.length → l.getD i d ∈ l
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => List.mem_cons_self
  | _ :: xs, i + 1, d, hi =>
    List.mem_cons_of_mem _ (getD_mem_of_lt xs i d (Nat.lt_of_succ_lt_succ hi))

theorem safeMemo2_of_stateTripleList {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {l l₀ : List (DY.PersistentLocalState.LocalState TRState)} {k : Nat}
    (hk_le : k ≤ 24)
    (hsts : StateTripleList S g pts l l₀ (stateMetas.take k)) :
    ∀ ls ∈ l, SafeMemo2 S g pts (DY.Comparse.serialize ls) := by
  obtain ⟨hl_len, _, hw⟩ := hsts
  have hsm_len : stateMetas.length = 24 := rfl
  have htk_len : (stateMetas.take k).length = k := by
    rw [List.length_take, hsm_len]; omega
  intro ls hls
  obtain ⟨i, hi_l, hget⟩ := exists_idx_of_mem ⟨"alice", stA0⟩ hls
  have hi_tk : i < (stateMetas.take k).length := hl_len ▸ hi_l
  have hi_k : i < k := htk_len ▸ hi_tk
  have hi_24 : i < 24 := Nat.lt_of_lt_of_le hi_k hk_le
  have sw := hw i hi_tk
  rw [hget, getD_take_of_lt k stateMetas i meta0 hi_k] at sw
  have hm_ok := List.all_eq_true.mp all_stateMetas_chains_ok
    (stateMetas.getD i meta0) (getD_mem_of_lt stateMetas i meta0 (hsm_len ▸ hi_24))
  exact sw.safeMemo2 hm_ok

private theorem forall₂_mem_salts {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salts : List Bytes} {ids : List Nat}
    (h : List.Forall₂ (TermAt dagSize dagOp dagBytes S g pts) salts ids) :
    ∀ salt ∈ salts, ∃ s_id ∈ ids, TermAt dagSize dagOp dagBytes S g pts salt s_id := by
  induction h with
  | nil => intro _ hm; cases hm
  | @cons _ s_id _ _ ht _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact ⟨s_id, List.mem_cons_self, ht⟩
    · obtain ⟨id', hid', ht'⟩ := ih x hrest
      exact ⟨id', List.mem_cons_of_mem _ hid', ht'⟩

theorem safeMemo2_prefixTerms_of_parts {cls : Nat → Nat} {S : OpaqueSymbolSemantics}
    {g : Ghost} {vis : List VisEntry} {tr : ExecTrace}
    {l₀ : List (DY.PersistentLocalState.LocalState TRState)} {nSends nRecvs k : Nat}
    (hp : PrefixPinned cls S g vis nSends nRecvs)
    (hnSends_le : nSends ≤ 12)
    (hk_le : k ≤ 24)
    (hsts : StateTripleList S g (plaintextTerms vis) (storedStates r0 tr) l₀ (stateMetas.take k))
    (hsec_eq : storedSecrets tr = pqSecretsList)
    (hsends_sm : ∀ j < nSends,
      SafeMemo dagSize dagOp dagBytes S g (plaintextTerms vis) (cleanSendMsg cls j)) :
    ∀ t ∈ prefixTerms r0 tr vis, SafeMemo2 S g (plaintextTerms vis) t := by
  set pts := plaintextTerms vis
  have hh := handshake_termAt (pts := pts) hp.base
  intro t ht
  unfold prefixTerms principalTerms at ht
  simp only [List.mem_append] at ht
  rcases ht with ((hsend | hstate) | hsec) | hpt
  · rcases hp.vis_sends t hsend with rfl | rfl | ⟨j, hj, rfl⟩
    · exact safeMemo_toSafeMemo2 hh.ek.safeMemo
    · exact safeMemo_toSafeMemo2 hh.ct.safeMemo
    · exact safeMemo_toSafeMemo2 (hsends_sm j hj)
  · obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hstate
    exact safeMemo2_of_stateTripleList hk_le hsts ls hls
  · rw [hsec_eq] at hsec
    exact safeMemo_toSafeMemo2 (pqSecrets_safeMemo hh t hsec)
  · have hpt_map : t ∈ (List.range nSends).map (fun j => randTerm (sendPtTs j) 32) := by
      rw [← hp.vis_pts]; exact hpt
    obtain ⟨j, hj_mem, rfl⟩ := List.mem_map.mp hpt_map
    have hj : j < nSends := List.mem_range.mp hj_mem
    exact safeMemo_toSafeMemo2 (safeMemo_plaintext hpt
      (by rw [hp.send_pt j hj]; exact sendPtBytes_len_lt8 (by omega)))

/-- `(msg_ts, msg_sk_id)` of the sender's ephemeral DH key for `.recv` call `k`. -/
def whisperMsgMeta (k : Nat) : Nat × Nat :=
  if k = 24 then (24, 67)
  else
    let mS := (hrConfigMeta ((k - 5) / 2)).1
    (mS.dhs_ts, mS.sk_id)

/-- Certified prefix invariants at `.recv` call `k ∈ whisperOrReplayIndices`: `SafeMemo2` on
`prefixTerms`, `TermAt` witnesses on states and salts, and `SendStepOut` for the incoming message. -/
structure WhisperPrefixBundle (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (k : Nat)
    (S : OpaqueSymbolSemantics) (g : Ghost) (vis : List VisEntry) : Prop where
  hk_le : k ≤ 24
  hj_lt : (if k = 24 then 0 else (k - 5) / 2 + 2) < 12
  hstates : StateTripleList S g (plaintextTerms vis)
    (storedStates r0 (runTrace r0 (ssClean cls spqrIdxs k)))
    ((allStates24 cls0).take k)
    (stateMetas.take k)
  hsalts : ∀ salt ∈ honestSaltsOf r0 (ssClean cls spqrIdxs k),
    ∃ s_id ∈ honestSaltIds.take (if k = 24 then 13 else (k - 5) / 2 + 4),
      TermAt dagSize dagOp dagBytes S g (plaintextTerms vis) salt s_id
  hskip : skippedStoredEvents (runTrace r0 (ssClean cls spqrIdxs k)) = [bobSkipEntry]
  t_seedB0 : TermAt dagSize dagOp dagBytes S g (plaintextTerms vis) seedB0 104
  hPref : ∀ t ∈ prefixTerms r0 (runTrace r0 (ssClean cls spqrIdxs k)) vis,
    SafeMemo2 S g (plaintextTerms vis) t
  t_msg_sk : TermAt dagSize dagOp dagBytes S g (plaintextTerms vis)
    (rnd (whisperMsgMeta k).1 32) (whisperMsgMeta k).2
  t_msg_pk : TermAt dagSize dagOp dagBytes S g (plaintextTerms vis)
    (dhPk (rnd (whisperMsgMeta k).1 32))
    (getSendRow (if k = 24 then 0 else (k - 5) / 2 + 2)).pk_id
  sender : ∃ sSt : TRState,
    cleanRecvTerm r0 cls spqrIdxs k =
      sendMsgOf sSt (cls (if k = 24 then 0 else (k - 5) / 2 + 2))
        (sendPtTs (if k = 24 then 0 else (k - 5) / 2 + 2)) ∧
    pqKeyOf sSt (cls (if k = 24 then 0 else (k - 5) / 2 + 2))
        (sendPtTs (if k = 24 then 0 else (k - 5) / 2 + 2)) ∈
      honestSaltsOf r0 (ssClean cls spqrIdxs k) ∧
    sSt.dhs = rnd (whisperMsgMeta k).1 32 ∧
    sSt.ns = 0 ∧
    SendStepOut (cls := cls) S g (plaintextTerms vis) sSt
      (if k = 24 then 0 else (k - 5) / 2 + 2)

private theorem sendRows_ctr_zero_hr :
    (List.range 10).all (fun h => (getSendRow (2 + h)).ctr == 0) = true := by
  decide

/-- Constructs `WhisperPrefixBundle` from `Explains` at any `k ∈ whisperOrReplayIndices`. -/
theorem prefix_safe_at_whisper {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g' : Ghost} {vis' : List VisEntry} {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hcls : ValidCoinLens cls)
    (hk : k ∈ whisperOrReplayIndices)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs k) vis' (trace0.take k)) :
    WhisperPrefixBundle cls spqrIdxs k S g' vis' := by
  have hp := explains_at_whisperOrReplay hfit hk hExp
  obtain ⟨hst_sum, hsec_sum, hskip_sum, hsalts_sum, hrecv_sum⟩ :=
    summary_at_whisperOrReplay cls spqrIdxs hk
  set pts := plaintextTerms vis'
  by_cases hk24 : k = 24
  · subst hk24
    simp only [↓reduceIte] at hp hst_sum hsalts_sum hrecv_sum
    obtain ⟨hsts10, hsalts10, hsends10, t_seed, _, _, _⟩ :=
      walk_hr_prefix hp hcls 10 (by omega) (by omega) (by omega)
    obtain ⟨_, _, _, out0, _, _, _⟩ := walk_calls_0_to_2 hp hcls (by omega)
    have hh := handshake_termAt (pts := pts) hp.base
    have hlen_st : ∀ c, (allStates24 c).length = 24 := fun c => by
      unfold allStates24 hrStates
      have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
      rw [hr]; rfl
    have hlen_sm : stateMetas.length = 24 := rfl
    have hsts24 : StateTripleList S g' pts
        (storedStates r0 (runTrace r0 (ssClean cls spqrIdxs 24)))
        ((allStates24 cls0).take 24) (stateMetas.take 24) := by
      rw [hst_sum, List.take_of_length_le (by rw [hlen_st]),
          List.take_of_length_le (by rw [hlen_st]),
          List.take_of_length_le (by rw [hlen_sm])]
      exact hsts10
    have hsalts24 : List.Forall₂ (TermAt dagSize dagOp dagBytes S g' pts)
        (honestSaltsOf r0 (ssClean cls spqrIdxs 24)) (honestSaltIds.take 13) := by
      rw [hsalts_sum]
      have hlen_sa : (allSalts13 cls).length = 13 := rfl
      rw [List.take_of_length_le (by rw [hlen_sa])]
      exact hsalts10
    have hPref24 := safeMemo2_prefixTerms_of_parts (k := 24) hp (by omega) (by omega) hsts24 hsec_sum
      (fun j hj => by obtain ⟨_, _, _, hout⟩ := hsends10 j hj; exact hout.wmac.safeMemo)
    have hsalt0_mem : pqKeyOf stA0 (cls 0) (sendPtTs 0) ∈
        honestSaltsOf r0 (ssClean cls spqrIdxs 24) := by
      rw [hsalts_sum]
      have hlen_sa : (allSalts13 cls).length = 13 := rfl
      rw [List.take_of_length_le (by rw [hlen_sa])]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    refine ⟨by omega, by decide, hsts24, forall₂_mem_salts hsalts24, hskip_sum, t_seed, hPref24,
      hh.t_dhsA, hh.pk4, ⟨stA0, ?_, hsalt0_mem, rfl, rfl, out0⟩⟩
    simp only [↓reduceIte, hrecv_sum]; rfl
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
    obtain ⟨h, hh_lt, rfl⟩ := hodd
    have hne24 : ¬ (5 + 2 * h = 24) := by omega
    have hdiv : (5 + 2 * h - 5) / 2 = h := by omega
    have hj_eq : (if 5 + 2 * h = 24 then 0 else (5 + 2 * h - 5) / 2 + 2) = 2 + h := by
      simp only [hne24, ↓reduceIte, hdiv]; omega
    have hns_eq : (if 5 + 2 * h = 24 then 13 else (5 + 2 * h - 5) / 2 + 4) = 4 + h := by
      simp only [hne24, ↓reduceIte, hdiv]; omega
    simp only [hne24, ↓reduceIte, hdiv] at hp hst_sum hsalts_sum hrecv_sum
    have hwalk := walk_hr_prefix hp hcls h (by omega) (by omega) (by omega)
    rcases hrc : hrConfig cls h with ⟨me, peer, sSt, rSt⟩
    rcases hrc0 : hrConfig cls0 h with ⟨me0, peer0, sSt₀, rSt₀⟩
    rcases hm : hrConfigMeta h with ⟨mS, mR⟩
    rw [hrc, hrc0, hm] at hwalk; dsimp only at hwalk
    obtain ⟨hsts_prev, hsalts_prev, hsends_prev, t_seed, swS, _, _⟩ := hwalk
    have ⟨hm_eq, _, _, _⟩ := hrConfig_toDRState cls h
    rw [hrc, hrc0] at hm_eq; dsimp only at hm_eq; subst hm_eq
    obtain ⟨outS, swSendOut⟩ := walk_hr_send hp hcls hh_lt (by omega) ⟨peer, rSt, hrc⟩ hm swS
    have hchk := List.all_eq_true.mp all_hr_steps_ok h (List.mem_range.mpr hh_lt)
    unfold hrStepCheck at hchk; rw [hm] at hchk; dsimp only at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpk_id, _⟩, _⟩, _⟩, hctr⟩, _⟩, hsalt_id⟩, hpt_ts⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hchk
    have hsts_odd : StateTripleList S g' pts
        (storedStates r0 (runTrace r0 (ssClean cls spqrIdxs (5 + 2 * h))))
        ((allStates24 cls0).take (5 + 2 * h))
        (stateMetas.take (5 + 2 * h)) := by
      rw [hst_sum]
      have h1 : (allStates24 cls).take (5 + 2 * h) =
          (initStates4 cls ++ (List.range h).flatMap (hrStates cls)) ++
            [⟨me, sendStOf sSt (cls (2 + h)) (55 + 14 * h)⟩] := by
        unfold allStates24 initStates4 hrStates
        rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil,
            List.cons_append, List.nil_append, List.append_nil, List.take, hrc]
      have h2 : (allStates24 cls0).take (5 + 2 * h) =
          (initStates4 cls0 ++ (List.range h).flatMap (hrStates cls0)) ++
            [⟨me, sendStOf sSt₀ 0 (55 + 14 * h)⟩] := by
        unfold allStates24 initStates4 hrStates
        rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil,
            List.cons_append, List.nil_append, List.append_nil, List.take, hrc0]
      have h3 : stateMetas.take (5 + 2 * h) =
          ([meta0, meta1, meta2, meta3] ++ (List.range h).flatMap hrMetas) ++
            [stepSendMeta mS (2 + h)] := by
        unfold stateMetas hrMetas
        rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil,
            List.cons_append, List.nil_append, List.append_nil, List.take, hm]
      rw [h1, h2, h3]
      refine stateTripleList_append hsts_prev ⟨rfl, rfl, fun i hi => ?_⟩
      have hi0 : i = 0 := by dsimp at hi; omega
      subst hi0; exact swSendOut
    have hsalts_list_eq : honestSaltsOf r0 (ssClean cls spqrIdxs (5 + 2 * h)) =
        prefixSaltsOf cls h ++ [pqKeyOf sSt (cls (2 + h)) (55 + 14 * h)] := by
      rw [hsalts_sum]
      unfold allSalts13 prefixSaltsOf
      rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [List.range, List.range.loop, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, List.append_nil, List.take, hrc]
    have hsalts_odd : List.Forall₂ (TermAt dagSize dagOp dagBytes S g' pts)
        (honestSaltsOf r0 (ssClean cls spqrIdxs (5 + 2 * h))) (honestSaltIds.take (4 + h)) := by
      rw [hsalts_list_eq]
      have htake_ids : honestSaltIds.take (4 + h) =
          honestSaltIds.take (3 + h) ++ [honestSaltIds.getD (3 + h) 0] := by
        rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      rw [htake_ids]
      exact Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1.forall₂_append_one
        hsalts_prev (hsalt_id ▸ (hpt_ts ▸ outS.pqKey))
    have hsends_sm : ∀ j < h + 3, SafeMemo dagSize dagOp dagBytes S g' pts (cleanSendMsg cls j) := by
      intro j hj
      by_cases hj_last : j = 2 + h
      · subst hj_last; exact outS.wmac.safeMemo
      · obtain ⟨_, _, _, hout⟩ := hsends_prev j (by omega)
        exact hout.wmac.safeMemo
    have hPref_odd := safeMemo2_prefixTerms_of_parts (k := 5 + 2 * h) hp (by omega) (by omega)
      hsts_odd hsec_sum hsends_sm
    have hwmeta : whisperMsgMeta (5 + 2 * h) = (mS.dhs_ts, mS.sk_id) := by
      unfold whisperMsgMeta; simp only [hne24, ↓reduceIte, hdiv, hm]
    have hclean_sSt : cleanSendMsg cls (h + 2) = sendMsgOf sSt (cls (2 + h)) (sendPtTs (2 + h)) := by
      have hcomm : h + 2 = 2 + h := by omega
      rw [hcomm]; unfold cleanSendMsg
      have h0 : ¬ (2 + h = 0) := by omega
      have h1 : ¬ (2 + h = 1) := by omega
      have hsub : 2 + h - 2 = h := by omega
      simp only [h0, h1, ↓reduceIte, hsub, hrc, hpt_ts]
    have hctr0 : (getSendRow (2 + h)).ctr = 0 :=
      beq_iff_eq.mp (List.all_eq_true.mp sendRows_ctr_zero_hr h (List.mem_range.mpr hh_lt))
    refine ⟨by omega, by rw [hj_eq]; omega, hsts_odd, ?_, hskip_sum, t_seed, hPref_odd,
      ?_, ?_, ⟨sSt, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hns_eq]; exact forall₂_mem_salts hsalts_odd
    · rw [hwmeta]; exact swS.hdhs_eq ▸ swS.t_dhs
    · rw [hwmeta, hj_eq, hpk_id]; exact swS.hdhs_eq ▸ swS.t_pk
    · rw [hj_eq, hrecv_sum, hclean_sSt]
    · rw [hj_eq, hsalts_list_eq, hpt_ts]
      exact List.mem_append_right _ List.mem_cons_self
    · rw [hwmeta]; exact (congrArg (·.dhs) swS.hdr).trans swS.hdhs_eq
    · rw [congrArg (·.ns) swS.hdr, swS.hns, ← hctr, hctr0]
    · rw [hj_eq]; exact outS

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2
