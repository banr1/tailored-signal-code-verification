/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2

/-!
# Existing-Chain and Skipped-Seed `whisperTrials` Safety

Proves `safeMemo_existing_and_skipped_trials`: for every `k ∈ whisperOrReplayIndices` and every
prefix state `i < k`, all `trialTerms` from existing receiver chains (`existCtxs`) and from
`skippedStoredEvents` (`skipCtxs`) satisfy `SafeMemo`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsA

open scoped DY.Libsignal.Composed
open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain consumeMessageKey skippedSeeds findRecvChain)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry TrialCtx trialTerms
   gamma runTrace honestSaltsOf ownKeys plaintextTerms)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSig dhPk_rnd_ne)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (dhsA stB0' seedB0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (whisperOrReplayIndices ssClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets
  (dag_no_collision)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
  (safeMemo_trialTerms)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials
  (allSeedTuples safeMemo_of_seedTrialOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
  (skippedStoredEvents)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf bobSkipEntry)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0 (sendPtTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (getSendRow SendStepOut)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1
  (meta0 stateMetas StateWitness forall₂_mem_left)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2
  (whisperMsgMeta WhisperPrefixBundle)

private theorem stateMetas_chains_pk_ai :
    stateMetas.all (fun m =>
      m.chains.all (fun cm => decide (cm.pk_id < dagSize) && (dagOp cm.pk_id).isAI)) = true := by
  decide +kernel

private theorem exist_chains_idx_or_ne :
    whisperOrReplayIndices.all (fun k =>
      let j := if k = 24 then 0 else (k - 5) / 2 + 2
      (List.range k).all (fun i =>
        (stateMetas.getD i meta0).chains.all (fun cm =>
          decide (cm.pk_id ≠ (getSendRow j).pk_id) || decide ((0 : UInt32) < cm.index)))) = true := by
  decide

private theorem alice_chains_ts_ne_24 :
    stateMetas.all (fun m => m.isBob || m.chains.all (fun cm => decide (cm.ts ≠ 24))) = true := by
  decide

private theorem pk69_only_at_24 :
    whisperOrReplayIndices.all (fun k =>
      decide ((getSendRow (if k = 24 then 0 else (k - 5) / 2 + 2)).pk_id ≠ 69) ||
        decide (k = 24)) = true := by
  decide

private theorem sendRows_pk_lt :
    (List.range 12).all (fun j => decide ((getSendRow j).pk_id < dagSize)) = true := by
  decide

private theorem pk69_ai : 69 < dagSize ∧ (dagOp 69).isAI = true :=
  ⟨by decide, by decide +kernel⟩

private theorem skip24_seedTuple_mem : (13, 104, 30, 31, 113) ∈ allSeedTuples := by
  decide

private theorem getD_mem_of_lt {α : Type} :
    ∀ (l : List α) (i : Nat) (d : α), i < l.length → l.getD i d ∈ l
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => List.mem_cons_self
  | _ :: xs, i + 1, d, hi =>
    List.mem_cons_of_mem _ (getD_mem_of_lt xs i d (Nat.lt_of_succ_lt_succ hi))

private theorem termAt_pk69_of_bundle {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k : Nat}
    {S : OpaqueSymbolSemantics} {g : Ghost} {vis : List VisEntry}
    (hk : k ∈ whisperOrReplayIndices)
    (wb : WhisperPrefixBundle cls spqrIdxs k S g vis) :
    TermAt dagSize dagOp dagBytes S g (plaintextTerms vis) (dhPk dhsA) 69 := by
  have hk_pos : 0 < k := by
    simp only [whisperOrReplayIndices, List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have htk_len : (stateMetas.take k).length = k := by
    rw [List.length_take, show stateMetas.length = 24 from rfl]
    have := wb.hk_le
    omega
  have sw0 := wb.hstates.2.2 0 (by omega)
  have hm0 : (stateMetas.take k).getD 0 meta0 = meta0 := by
    cases k with
    | zero => omega
    | succ _ => rfl
  rw [hm0] at sw0
  have hdhsA_eq : dhsA = rnd meta0.dhs_ts 32 := rfl
  rw [hdhsA_eq, ← sw0.hdhs_eq]
  exact sw0.t_pk

private theorem consumeMessageKey_zero_of_pos {c : RecvChain} (h : (0 : UInt32) < c.index) :
    consumeMessageKey c 0 = none := by
  unfold consumeMessageKey
  simp only [h, ↓reduceIte]

theorem safeMemo_existing_and_skipped_trials
    {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k i : Nat}
    {S : OpaqueSymbolSemantics} {g : Ghost} {vis : List VisEntry}
    {ls ls₀ : DY.PersistentLocalState.LocalState TRState}
    {sSt : TRState}
    (hk : k ∈ whisperOrReplayIndices)
    (wb : WhisperPrefixBundle cls spqrIdxs k S g vis)
    (hi : i < k)
    (sw : StateWitness S g (plaintextTerms vis) ls ls₀ (stateMetas.getD i meta0))
    (hsSt_dhs : sSt.dhs = rnd (whisperMsgMeta k).1 32)
    (hsSt_ns : sSt.ns = 0)
    (hout : SendStepOut (cls := cls) S g (plaintextTerms vis) sSt
      (if k = 24 then 0 else (k - 5) / 2 + 2)) :
    let j := if k = 24 then 0 else (k - 5) / 2 + 2
    let msg := encSig sSt (rnd (sendPtTs j + 1) (cls j))
      (pqKeyOf sSt (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)
    let st := ls.state
    let tr := runTrace r0 (ssClean cls spqrIdxs k)
    let salts := honestSaltsOf r0 (ssClean cls spqrIdxs k)
    let γ := gamma evictedI0 S g
    let own := ownKeys r0 tr st msg
    let existCtxs :=
      (st.toDRState.recv.filter fun c => decide (γ c.ratchetKey = γ msg.ratchetKey)).map fun c =>
        match consumeMessageKey c msg.counter with
        | none =>
          ({ peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
             ownSalts := [], seed? := none } : TrialCtx)
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := own, seed? := some seed }
    let skipCtxs :=
      (skippedStoredEvents tr).filterMap fun (s, pk, n, seed) =>
        if (findRecvChain st.toDRState.recv pk).isSome ∧
            γ pk = γ msg.ratchetKey ∧ n = msg.counter then
          some ({ peerIk := st.peerIk, myIk := st.myIk, extra := [],
                  ownSalts := if st.sessionInfo s.me = s then own else [],
                  seed? := some seed } : TrialCtx)
        else none
    ∀ ctx ∈ existCtxs ++ skipCtxs,
      ∀ t ∈ trialTerms salts msg ctx,
        SafeMemo dagSize dagOp dagBytes S g (plaintextTerms vis) t := by
  intro j msg st tr salts γ own existCtxs skipCtxs ctx hctx t ht
  have hi24 : i < 24 := Nat.lt_of_lt_of_le hi wb.hk_le
  have hm_mem : stateMetas.getD i meta0 ∈ stateMetas :=
    getD_mem_of_lt stateMetas i meta0 (by rw [show stateMetas.length = 24 from rfl]; exact hi24)
  have hrpk_lt : (getSendRow j).pk_id < dagSize :=
    of_decide_eq_true (List.all_eq_true.mp sendRows_pk_lt j (List.mem_range.mpr wb.hj_lt))
  have t_mpk : TermAt dagSize dagOp dagBytes S g (plaintextTerms vis) msg.ratchetKey
      (getSendRow j).pk_id := by
    show TermAt _ _ _ _ _ _ (dhPk sSt.dhs) (getSendRow j).pk_id
    rw [hsSt_dhs]
    exact wb.t_msg_pk
  rcases List.mem_append.mp hctx with hctx_ex | hctx_sk
  · obtain ⟨c, hc_filt, hctx_eq⟩ := List.mem_map.mp hctx_ex
    obtain ⟨hc_mem, hgamma_dec⟩ := List.mem_filter.mp hc_filt
    have hgamma_eq : γ c.ratchetKey = γ msg.ratchetKey := of_decide_eq_true hgamma_dec
    have hc_mem0 : c ∈ ls₀.state.recv := (congrArg (·.recv) sw.hdr) ▸ hc_mem
    obtain ⟨cm, hcm_mem, hcr⟩ := forall₂_mem_left sw.hchains hc_mem0
    have hcm_ai_both :=
      List.all_eq_true.mp (List.all_eq_true.mp stateMetas_chains_pk_ai _ hm_mem) cm hcm_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcm_ai_both
    have hex_chk := List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp exist_chains_idx_or_ne k hk)
        i (List.mem_range.mpr hi))
      cm hcm_mem
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hex_chk
    rcases hex_chk with hne | hpos
    · have hbytes_eq : dagBytes cm.pk_id = dagBytes (getSendRow j).pk_id :=
        hcr.2.2.2.1.gamma_eq.symm.trans (hgamma_eq.trans t_mpk.gamma_eq)
      exact absurd
        (dag_no_collision cm.pk_id hcm_ai_both.1 (getSendRow j).pk_id hrpk_lt
          (Or.inl hcm_ai_both.2) hbytes_eq)
        hne
    · have hc_pos : (0 : UInt32) < c.index := hcr.2.1 ▸ hpos
      have hcmk : consumeMessageKey c msg.counter = none := by
        change consumeMessageKey c sSt.ns = none
        rw [hsSt_ns]
        exact consumeMessageKey_zero_of_pos hc_pos
      rw [hcmk] at hctx_eq
      subst hctx_eq
      refine safeMemo_trialTerms ?_ hout.ct.safeMemo (fun _ hs => by cases hs) t ht
      intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact hcr.2.2.2.2.safeMemo
  · change ctx ∈ (skippedStoredEvents tr).filterMap _ at hctx_sk
    rw [wb.hskip] at hctx_sk
    obtain ⟨entry, hentry, hsome⟩ := List.mem_filterMap.mp hctx_sk
    rw [List.mem_singleton] at hentry
    subst hentry
    unfold bobSkipEntry at hsome
    dsimp only at hsome
    split at hsome
    · next hcond =>
      obtain ⟨hfind_some, hgamma69, _⟩ := hcond
      injection hsome with hctx_sk
      have t_pk69 := termAt_pk69_of_bundle hk wb
      have hbytes69 : dagBytes 69 = dagBytes (getSendRow j).pk_id :=
        t_pk69.gamma_eq.symm.trans (hgamma69.trans t_mpk.gamma_eq)
      have hid69 : 69 = (getSendRow j).pk_id :=
        dag_no_collision 69 pk69_ai.1 (getSendRow j).pk_id hrpk_lt (Or.inl pk69_ai.2) hbytes69
      have hk24_or := List.all_eq_true.mp pk69_only_at_24 k hk
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk24_or
      have hk24 : k = 24 := hk24_or.resolve_left (not_not.mpr hid69.symm)
      unfold findRecvChain at hfind_some
      obtain ⟨c, hfind_eq⟩ := Option.isSome_iff_exists.mp hfind_some
      have hc_mem0 : c ∈ ls₀.state.recv :=
        (congrArg (·.recv) sw.hdr) ▸ List.mem_of_find?_eq_some hfind_eq
      have hc_pk : c.ratchetKey = dhPk dhsA :=
        beq_iff_eq.mp (List.find?_some (p := fun x : RecvChain => x.ratchetKey == dhPk dhsA) hfind_eq)
      obtain ⟨cm, hcm_mem, hcr⟩ := forall₂_mem_left sw.hchains hc_mem0
      have halice_chk := List.all_eq_true.mp alice_chains_ts_ne_24 _ hm_mem
      simp only [Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq] at halice_chk
      have hbob : (stateMetas.getD i meta0).isBob = true := by
        rcases halice_chk with hb | hts_ne
        · exact hb
        · exact absurd (hcr.1.symm.trans hc_pk) (dhPk_rnd_ne (hts_ne cm hcm_mem))
      subst hctx_sk
      refine safeMemo_of_seedTrialOk
        (salts := salts) (msg := msg)
        (nSalts := 13) (seed_id := 104) (pIk_id := 30) (mIk_id := 31) (wire_id := 113)
        skip24_seedTuple_mem ?_ ?_ hout.ct.safeMemo ?_ ?_ ?_ ?_ t ht
      · intro salt hsalt
        have hs := wb.hsalts salt hsalt
        simp only [hk24, ↓reduceIte] at hs
        exact hs
      · intro u hu
        cases hu
      · dsimp only
        rw [congrArg (·.peerIk) sw.hdr]
        have tp := sw.t_peerIk
        rw [hbob] at tp
        exact tp
      · dsimp only
        rw [congrArg (·.myIk) sw.hdr]
        have tm := sw.t_myIk
        rw [hbob] at tm
        exact tm
      · have hw := hout.wire
        have hj0 : j = 0 := by simp [j, hk24]
        have hwid : (getSendRow j).wire_id = 113 := by rw [hj0]; rfl
        rw [← hwid]
        exact hw
      · intro seed hseed
        dsimp only at hseed
        cases hseed
        exact wb.t_seedB0
    · nomatch hsome

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsA
