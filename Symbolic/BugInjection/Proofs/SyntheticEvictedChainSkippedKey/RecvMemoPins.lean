/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins2
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv

/-!
# Clean Prefix `Explains` Peeling

Peels `Explains evictedI0 r S g' (ssClean cls spqrIdxs k) vis' (trace0.take k)` at `k = 3` and
every `k ∈ whisperOrReplayIndices` into `PrefixPinned cls S g' vis' nSends nRecvs`, which pins
`g'.σ`, `g'.addr`, sent message bytes, and `vis'` send and plaintext entries.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins

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

open DY (Bytes Participant ExecTrace)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet (TRState parseTrSignalMsg findRecvChain)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry Step BundlePreKeyIds
   setupTrace runTrace runSteps randTerm bundlePreKeyIds nextBundleIds plaintextTerms
   GhostWF RunMatches RunRejected MatchesEventsAt Explains gamma)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (NetE StT rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (bh1 kh1 o1 stA0 t4 t5 t5_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0 trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ssClean whisperOrReplayIndices)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev trace_eq_evs ev_not_rejected)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData (dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
  (setupTrace_eq_r0 setupTrace_r0_eq_t4 step0_next_t4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
  (at?_mono length_encTrGen encTrGen_at?_pq decTr0 step_messageDecrypt0_next)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf pqMsgOf sendMsgOf stA1c hrConfig cleanSendMsg
   trClean1 trClean2 step1_enc_next step2_enc_next
   SyncPair findRecvChain_eq_none_of_lt halfRound_send_spec)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
  (hrSStH hrRStH hrSteps cleanCallSteps_eq_hr hrPrefix_props)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins1
  (SetupAndCall0Pinned aliceDonePairs_t5 aliceDonePairs_trClean1
   matchesEventsAt_nil_vis matchesEventsAt_party_cons peel_setup_and_call0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins2
  (peel_encrypt_preKey peel_encrypt_whisper peel_bobStart peel_decrypt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv
  (aliceBobAddrBytes serializeAddresses_alice_bob_eq sendPtTs sendPtBytes sendC32Id sendC64Id
   sendWmacId recvDhsTs recvSkId ev1_preKeySend_facts ev2_preKeySend_facts
   ev_whisperSend_facts ev_recv_facts)

/-- Ghost randomness, address, wire-byte, and visible-entry equations extracted from `Explains`
after `nSends` clean sends and `nRecvs` clean receives. -/
structure PrefixPinned (cls : Nat → Nat) (S : OpaqueSymbolSemantics) (g : Ghost)
    (vis : List VisEntry) (nSends nRecvs : Nat) : Prop where
  base : SetupAndCall0Pinned S g
  send_pt : ∀ j < nSends, g.σ (sendPtTs j) 32 = sendPtBytes j
  send_c32 : ∀ j < nSends, cls j = 32 → g.σ (sendPtTs j + 1) 32 = dagBytes (sendC32Id j)
  send_c64 : ∀ j < nSends, cls j = 64 → g.σ (sendPtTs j + 1) 64 = dagBytes (sendC64Id j)
  send_msg : ∀ j < nSends, gamma evictedI0 S g (cleanSendMsg cls j) = dagBytes (sendWmacId j)
  send_addr : ∀ j < nSends, ∀ pm, parseTrSignalMsg (cleanSendMsg cls j) = some pm →
    g.addr pm.wire = (if j < 2 then aliceBobAddrBytes else [])
  recv_dhs : ∀ m < nRecvs, g.σ (recvDhsTs m) 32 = dagBytes (recvSkId m)
  vis_sends : ∀ t ∈ (vis.filter (·.kind == .send)).flatMap (·.terms),
    t = o1.ek ∨ t = o1.ct ∨ ∃ j < nSends, t = cleanSendMsg cls j
  vis_pts : plaintextTerms vis = (List.range nSends).map (fun j => randTerm (sendPtTs j) 32)

private theorem filter_flatMap_append {α β : Type} (p : α → Bool) (f : α → List β)
    (xs ys : List α) :
    ((xs ++ ys).filter p).flatMap f = (xs.filter p).flatMap f ++ (ys.filter p).flatMap f := by
  rw [List.filter_append, List.flatMap_append]

private theorem plaintextTerms_append (v₁ v₂ : List VisEntry) :
    plaintextTerms (v₁ ++ v₂) = plaintextTerms v₁ ++ plaintextTerms v₂ := by
  unfold plaintextTerms
  exact filter_flatMap_append _ _ v₁ v₂

theorem matchesEventsAt_party_append
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss₁ ss₂ : List Step} {es₁ : List RunEvent} {evs₂ : List CliEvent}
    {vis visAll : List VisEntry}
    (hlen : ss₁.length = es₁.length)
    (hparty : ∀ s ∈ ss₁, s.cls = .party)
    (hnotRej : ∀ e ∈ es₁, ¬ RunRejected e)
    (hm : MatchesEventsAt evictedI0 r S g initIds tr (ss₁ ++ ss₂)
            (es₁.map CliEvent.run ++ evs₂) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll) :
    ∃ v₁ v₂,
      vis = v₁ ++ v₂ ∧
      MatchesEventsAt evictedI0 r S g initIds tr ss₁ (es₁.map CliEvent.run) v₁ ∧
      (∀ w ∈ v₁, w ∈ visAll) ∧
      (∀ w ∈ v₂, w ∈ visAll) ∧
      MatchesEventsAt evictedI0 r S g (es₁.foldl nextBundleIds initIds)
        (runSteps ss₁ tr) ss₂ evs₂ v₂ := by
  induction ss₁ generalizing es₁ initIds tr vis with
  | nil =>
    cases es₁ with
    | nil =>
      exact ⟨[], vis, rfl, MatchesEventsAt.nil (by simp),
        by simp, hsub, hm⟩
    | cons _ _ => cases hlen
  | cons s ss₁' ih =>
    cases es₁ with
    | nil => cases hlen
    | cons e es₁' =>
      simp only [List.cons_append, List.map_cons] at hm
      obtain ⟨v, vs, rfl, hrm, hv_sub, hvs_sub, hm'⟩ :=
        matchesEventsAt_party_cons
          (hparty s List.mem_cons_self)
          (hnotRej e List.mem_cons_self) hm hsub
      obtain ⟨v₁', v₂, rfl, hm₁', hv₁'_sub, hv₂_sub, hm₂⟩ :=
        ih (Nat.succ.inj hlen)
          (fun x hx => hparty x (List.mem_cons_of_mem _ hx))
          (fun x hx => hnotRej x (List.mem_cons_of_mem _ hx))
          hm' hvs_sub
      refine ⟨v ++ v₁', v₂, (List.append_assoc v v₁' v₂).symm,
        MatchesEventsAt.run1 (pre := []) (by simp) hrm hm₁',
        fun w hw => ?_, hv₂_sub, hm₂⟩
      rcases List.mem_append.mp hw with hw | hw
      · exact hv_sub w hw
      · exact hv₁'_sub w hw

private theorem extend_no_send_pt {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {v₁ v₂ : List VisEntry} {nSends nRecvs : Nat}
    (hp : PrefixPinned cls S g v₁ nSends nRecvs)
    (hsend₂ : (v₂.filter (·.kind == .send)).flatMap (·.terms) = [])
    (hpt₂ : plaintextTerms v₂ = []) :
    PrefixPinned cls S g (v₁ ++ v₂) nSends nRecvs := by
  refine ⟨hp.base, hp.send_pt, hp.send_c32, hp.send_c64, hp.send_msg, hp.send_addr,
    hp.recv_dhs, ?_, ?_⟩
  · intro t ht
    rw [filter_flatMap_append, hsend₂, List.append_nil] at ht
    exact hp.vis_sends t ht
  · rw [plaintextTerms_append, hpt₂, List.append_nil]
    exact hp.vis_pts

def initSteps3 (cls : Nat → Nat) : List Step :=
  [Step.aliceStart "alice" "bob" 4 6 bh1,
   Step.messageEncrypt "alice" 30 (cls 0) 33,
   Step.messageEncrypt "alice" 36 (cls 1) 40]

theorem peel_calls_0_to_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {cls : Nat → Nat} {v02 visAll : List VisEntry}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hsetup : DY.Libsignal.Composed.Refinement.GhostAndSemMatchSetup evictedI0 r S g)
    (hgwf : GhostWF g visAll)
    (hm : MatchesEventsAt evictedI0 r S g none t4 (initSteps3 cls)
            [CliEvent.run (ev 0), CliEvent.run (ev 1), CliEvent.run (ev 2)] v02)
    (hsub : ∀ w ∈ v02, w ∈ visAll) :
    PrefixPinned cls S g v02 2 0 := by
  unfold initSteps3 at hm
  obtain ⟨v0, vs1, rfl, hrm0, hv0, hvs1, hm1⟩ :=
    matchesEventsAt_party_cons rfl (ev_not_rejected 0 (by decide)) hm hsub
  obtain ⟨hbase, hsend0, hpt0, hids0⟩ := peel_setup_and_call0 hfit hsetup hgwf hrm0 hv0
  rw [hids0, step0_next_t4] at hm1
  obtain ⟨v1, vs2, rfl, hrm1, hv1, hvs2, hm2⟩ :=
    matchesEventsAt_party_cons rfl (ev_not_rejected 1 (by decide)) hm1 hvs1
  obtain ⟨hcmd1, hex1, hwrap1, hwire1, hin1, hc32_1, hc64_1, hids1⟩ := ev1_preKeySend_facts
  have hnext1 : (Step.messageEncrypt "alice" 30 (cls 0) 33).next t5 =
      RecvMemoTrace0.encTrGen t5 "alice" 30 stA0 (cls 0) (pqKeyOf stA0 (cls 0) t5.length) := by
    rw [t5_length]; exact step1_enc_next cls
  obtain ⟨hpt_pin1, hcl_pin1, hmsg_pin1, haddr_pin1, hsend1, hpt1⟩ :=
    peel_encrypt_preKey hfit hbase hgwf hv1 hnext1 aliceDonePairs_t5 hcmd1 hex1 hwrap1 hwire1 hrm1
  rw [t5_length] at hpt_pin1 hcl_pin1 hmsg_pin1 haddr_pin1 hsend1 hpt1
  rw [hids1, step1_enc_next cls] at hm2
  obtain ⟨v2, vs3, rfl, hrm2, hv2, _, hm3⟩ :=
    matchesEventsAt_party_cons rfl (ev_not_rejected 2 (by decide)) hm2 hvs2
  have hvs3_nil := matchesEventsAt_nil_vis hm3
  subst hvs3_nil
  have hlen1 : (trClean1 cls).length = 38 := by
    unfold trClean1; rw [length_encTrGen, t5_length]
  obtain ⟨hcmd2, hex2, hwrap2, hwire2, hin2, hc32_2, hc64_2, _⟩ := ev2_preKeySend_facts
  have hnext2 : (Step.messageEncrypt "alice" 36 (cls 1) 40).next (trClean1 cls) =
      RecvMemoTrace0.encTrGen (trClean1 cls) "alice" 36 (stA1c cls) (cls 1)
        (pqKeyOf (stA1c cls) (cls 1) (trClean1 cls).length) := by
    rw [hlen1]; exact step2_enc_next cls
  obtain ⟨hpt_pin2, hcl_pin2, hmsg_pin2, haddr_pin2, hsend2, hpt2⟩ :=
    peel_encrypt_preKey hfit hbase hgwf hv2 hnext2 (aliceDonePairs_trClean1 cls)
      hcmd2 hex2 hwrap2 hwire2 hrm2
  rw [hlen1] at hpt_pin2 hcl_pin2 hmsg_pin2 haddr_pin2 hsend2 hpt2
  refine ⟨hbase, ?_, ?_, ?_, ?_, ?_, fun m hm_lt => by omega, ?_, ?_⟩
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact hpt_pin1.trans hin1
    · exact hpt_pin2.trans hin2
  · intro j hj hcl
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · dsimp only [sendPtTs]; rw [hcl] at hcl_pin1; exact (hcl_pin1 (by decide)).trans hc32_1
    · dsimp only [sendPtTs]; rw [hcl] at hcl_pin2; exact (hcl_pin2 (by decide)).trans hc32_2
  · intro j hj hcl
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · dsimp only [sendPtTs]; rw [hcl] at hcl_pin1; exact (hcl_pin1 (by decide)).trans hc64_1
    · dsimp only [sendPtTs]; rw [hcl] at hcl_pin2; exact (hcl_pin2 (by decide)).trans hc64_2
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact hmsg_pin1
    · exact hmsg_pin2
  · intro j hj pm hpm
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simp only [show (0 : Nat) < 2 by decide, ↓reduceIte]
      exact (haddr_pin1 pm hpm).trans serializeAddresses_alice_bob_eq
    · simp only [show (1 : Nat) < 2 by decide, ↓reduceIte]
      exact (haddr_pin2 pm hpm).trans serializeAddresses_alice_bob_eq
  · intro t ht
    rw [List.append_nil, filter_flatMap_append, filter_flatMap_append,
        hsend0, hsend1, hsend2, List.nil_append] at ht
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0, by decide, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨1, by decide, rfl⟩)
  · rw [List.append_nil, plaintextTerms_append, plaintextTerms_append,
        hpt0, hpt1, hpt2]
    rfl

/-- Extracts `PrefixPinned cls S g' vis' 2 0` from `Explains` on the 3-step prefix before Call 3 (`bobStart`). -/
theorem explains_at_3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g' : Ghost}
    {vis' : List VisEntry} {cls : Nat → Nat} {spqrIdxs : Nat → UInt32}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs 3) vis' (trace0.take 3)) :
    PrefixPinned cls S g' vis' 2 0 := by
  obtain ⟨hsetup, hgwf, _, hm⟩ := hExp
  unfold DY.Libsignal.Composed.Refinement.MatchesEvents at hm
  rw [setupTrace_eq_r0 hfit, setupTrace_r0_eq_t4] at hm
  have htr3 : trace0.take 3 = [CliEvent.run (ev 0), CliEvent.run (ev 1), CliEvent.run (ev 2)] := by
    change Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.cliTrace.take 3 = _
    rw [trace_eq_evs]; rfl
  have hss3 : ssClean cls spqrIdxs 3 = initSteps3 cls := rfl
  rw [htr3, hss3] at hm
  exact peel_calls_0_to_2 hfit hsetup hgwf hm (fun _ hw => hw)

private theorem extend_whisper_send {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {cls : Nat → Nat} {h nRecvs : Nat} {tr : ExecTrace} {me peer : Participant}
    {sSt rSt : TRState} {tsS : Nat} {initIds : Option BundlePreKeyIds}
    {v_prev v_send visAll : List VisEntry}
    (hh : h < 10)
    (hgwf : GhostWF g visAll)
    (hp : PrefixPinned cls S g v_prev (2 + h) nRecvs)
    (hv_send : ∀ w ∈ v_send, w ∈ visAll)
    (hlen : tr.length = 55 + 14 * h)
    (hsSt : tr.at? (hrSStH h) = some (StT me sSt))
    (hsync : SyncPair me peer sSt rSt tsS (55 + 14 * h))
    (hrc : hrConfig cls h = (me, peer, sSt, rSt))
    (hrm : RunMatches evictedI0 r S g tr
      (Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2))
      (ev (4 + 2 * h)) v_send initIds) :
    PrefixPinned cls S g (v_prev ++ v_send) (3 + h) nRecvs := by
  obtain ⟨hnext, _, _, _, _, _, _, _, _, _⟩ :=
    halfRound_send_spec (cl := cls (2 + h)) hlen (by omega) hsSt hsync
  obtain ⟨hcmd, hex, hwrap, htail, hin, hc32, hc64, _⟩ := ev_whisperSend_facts hh
  have hnext' : (Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2)).next tr =
      RecvMemoTrace0.encTrGen tr me (hrSStH h) sSt (cls (2 + h))
        (pqKeyOf sSt (cls (2 + h)) tr.length) := by
    rw [hlen]; exact hnext
  obtain ⟨hpt_pin, hcl_pin, hmsg_pin, haddr_pin, hsend_v, hpt_v⟩ :=
    peel_encrypt_whisper hgwf hv_send hnext' hcmd hex hwrap hrm
  rw [hlen] at hpt_pin hcl_pin hmsg_pin haddr_pin hsend_v hpt_v
  have hcsm : cleanSendMsg cls (2 + h) = sendMsgOf sSt (cls (2 + h)) (55 + 14 * h) := by
    unfold cleanSendMsg
    simp only [show ¬ (2 + h = 0) by omega, show ¬ (2 + h = 1) by omega, ↓reduceIte,
      show 2 + h - 2 = h by omega, hrc]
  have hpt_ts : sendPtTs (2 + h) = 55 + 14 * h := by
    unfold sendPtTs
    simp only [show ¬ (2 + h = 0) by omega, show ¬ (2 + h = 1) by omega, ↓reduceIte,
      show 2 + h - 2 = h by omega]
  refine ⟨hp.base, ?_, ?_, ?_, ?_, ?_, hp.recv_dhs, ?_, ?_⟩
  · intro j hj
    by_cases hlt : j < 2 + h
    · exact hp.send_pt j hlt
    · have hj_eq : j = 2 + h := by omega
      subst hj_eq; rw [hpt_ts]; exact hpt_pin.trans hin
  · intro j hj hcl
    by_cases hlt : j < 2 + h
    · exact hp.send_c32 j hlt hcl
    · have hj_eq : j = 2 + h := by omega
      subst hj_eq; rw [hpt_ts]; rw [hcl] at hcl_pin; exact (hcl_pin (by decide)).trans hc32
  · intro j hj hcl
    by_cases hlt : j < 2 + h
    · exact hp.send_c64 j hlt hcl
    · have hj_eq : j = 2 + h := by omega
      subst hj_eq; rw [hpt_ts]; rw [hcl] at hcl_pin; exact (hcl_pin (by decide)).trans hc64
  · intro j hj
    by_cases hlt : j < 2 + h
    · exact hp.send_msg j hlt
    · have hj_eq : j = 2 + h := by omega
      subst hj_eq; rw [hcsm]; exact hmsg_pin.trans htail
  · intro j hj pm hpm
    by_cases hlt : j < 2 + h
    · exact hp.send_addr j hlt pm hpm
    · have hj_eq : j = 2 + h := by omega
      subst hj_eq
      simp only [show ¬ (2 + h < 2) by omega, ↓reduceIte]
      rw [hcsm] at hpm
      exact haddr_pin pm hpm
  · intro t ht
    rw [filter_flatMap_append, hsend_v] at ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases hp.vis_sends t ht with rfl | rfl | ⟨j, hj, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨j, by omega, rfl⟩)
    · rw [List.mem_singleton.mp ht, ← hcsm]
      exact Or.inr (Or.inr ⟨2 + h, by omega, rfl⟩)
  · rw [plaintextTerms_append, hp.vis_pts, hpt_v, ← hpt_ts,
        show 3 + h = (2 + h) + 1 by omega, List.range_succ, List.map_append, List.map_cons,
        List.map_nil]

private theorem halfRound_recv_next {tr : ExecTrace} {me peer : Participant} {sStH rStH : Nat}
    {sSt rSt : TRState} {tsS curLen cl : Nat} {idx : UInt32}
    (hlen : tr.length = curLen) (hmin : 22 ≤ curLen)
    (hsSt : tr.at? sStH = some (StT me sSt))
    (hrSt : tr.at? rStH = some (StT peer rSt))
    (hsync : SyncPair me peer sSt rSt tsS curLen) :
    let tr1 := (Step.messageEncrypt me sStH cl (curLen + 2)).next tr
    (Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx).next tr1 =
      decTr0 tr1 peer rStH rSt sSt.dhs (pqKeyOf sSt cl curLen)
        (pqMsgOf sSt cl curLen) (rnd curLen 32) ∧
    tr1.length = curLen + 7 ∧
    (∃ b, tr1.getMessageSentAt (curLen + 6) = some b) := by
  have hts_lt : tsS < curLen := hsync.tsS_lt
  obtain ⟨hnext1, hlen1, hle1, _, hmsg1, hget1, _, _, _, _⟩ :=
    halfRound_send_spec (cl := cl) hlen hmin hsSt hsync
  set tr1 := (Step.messageEncrypt me sStH cl (curLen + 2)).next tr
  have hrSt1 : tr1.at? rStH = some (StT peer rSt) := at?_mono hle1 hrSt
  have hpq1 : tr1.at? (curLen + 2) = some (NetE (pqKeyOf sSt cl curLen)) := by
    rw [hnext1]; unfold pqKeyOf; rw [← hlen]
    exact encTrGen_at?_pq tr me sStH sSt cl _ rfl
  have hfind : findRecvChain rSt.recv (dhPk sSt.dhs) = none := by
    rw [hsync.dhs_s]
    exact findRecvChain_eq_none_of_lt hsync.recv_r (Nat.le_refl tsS)
  exact ⟨step_messageDecrypt0_next hrSt1 hmsg1 hpq1 (by omega) hsync.ns_zero
    hsync.spqr_r hfind hsync.cks_eq hsync.ik_my.symm hsync.ik_peer.symm, hlen1, ⟨_, hget1⟩⟩

private def hrStepsPrefix (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (h : Nat) : List Step :=
  [Step.aliceStart "alice" "bob" 4 6 bh1,
   Step.messageEncrypt "alice" 30 (cls 0) 33,
   Step.messageEncrypt "alice" 36 (cls 1) 40,
   Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] ++
  (List.range h).flatMap (hrSteps cls spqrIdxs)

private theorem hrStepsPrefix_party (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) (h : Nat) :
    ∀ s ∈ hrStepsPrefix cls spqrIdxs h, s.cls = .party := by
  intro s hs
  unfold hrStepsPrefix at hs
  rcases List.mem_append.mp hs with hs | hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hs
    unfold hrSteps at hi
    rcases hrc : hrConfig cls i with ⟨me, peer, _, _⟩
    rw [hrc] at hi
    dsimp only at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

private theorem hrStepsPrefix_length (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    ∀ h, (hrStepsPrefix cls spqrIdxs h).length = 4 + 2 * h
  | 0 => rfl
  | h + 1 => by
    have ih := hrStepsPrefix_length cls spqrIdxs h
    unfold hrStepsPrefix at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc,
        List.length_append, ih]
    unfold hrSteps
    rcases hrc : hrConfig cls h with ⟨me, peer, _, _⟩
    dsimp only
    simp only [List.length_cons, List.length_nil]
    omega

private theorem peel_hr_prefix {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {visAll : List VisEntry}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hsetup : DY.Libsignal.Composed.Refinement.GhostAndSemMatchSetup evictedI0 r S g)
    (hgwf : GhostWF g visAll) :
    ∀ h, h ≤ 10 → ∀ v_h,
      MatchesEventsAt evictedI0 r S g none t4 (hrStepsPrefix cls spqrIdxs h)
        (((List.range (4 + 2 * h)).map ev).map CliEvent.run) v_h →
      (∀ w ∈ v_h, w ∈ visAll) →
      PrefixPinned cls S g v_h (2 + h) (1 + h)
  | 0, _, v_0, hm, hsub => by
    have hss : hrStepsPrefix cls spqrIdxs 0 =
        initSteps3 cls ++ [Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 (spqrIdxs 3)] := rfl
    have hevs : ((List.range 4).map ev).map CliEvent.run =
        [ev 0, ev 1, ev 2].map CliEvent.run ++ [CliEvent.run (ev 3)] := rfl
    rw [hss, hevs] at hm
    obtain ⟨v02, v3, rfl, hm02, hv02, hv3, hm3⟩ :=
      matchesEventsAt_party_append rfl
        (by intro s hs; simp only [initSteps3, List.mem_cons, List.not_mem_nil, or_false] at hs;
            rcases hs with rfl | rfl | rfl <;> rfl)
        (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he;
            rcases he with rfl | rfl | rfl
            · exact ev_not_rejected 0 (by decide)
            · exact ev_not_rejected 1 (by decide)
            · exact ev_not_rejected 2 (by decide))
        hm hsub
    have hp02 := peel_calls_0_to_2 hfit hsetup hgwf hm02 hv02
    have hrun02 : runSteps (initSteps3 cls) t4 = trClean2 cls := by
      dsimp only [initSteps3, runSteps]
      rw [step0_next_t4, step1_enc_next cls, step2_enc_next cls]
    rw [hrun02] at hm3
    obtain ⟨v3a, v3b, rfl, hrm3, hv3a, _, hm3_nil⟩ :=
      matchesEventsAt_party_cons rfl (ev_not_rejected 3 (by decide)) hm3 hv3
    have hv3b_nil := matchesEventsAt_nil_vis hm3_nil
    subst hv3b_nil; rw [List.append_nil]
    obtain ⟨h45, hsend3, hpt3⟩ := peel_bobStart hgwf hv3a hrm3
    obtain ⟨_, hc3, _⟩ := ev_recv_facts (m := 0) (by decide)
    have hp3 := extend_no_send_pt hp02 hsend3 hpt3
    refine ⟨hp3.base, hp3.send_pt, hp3.send_c32, hp3.send_c64, hp3.send_msg, hp3.send_addr,
      ?_, hp3.vis_sends, hp3.vis_pts⟩
    intro m hm_lt
    have hm0 : m = 0 := by omega
    subst hm0
    exact h45.trans hc3
  | h + 1, hh, v_next, hm, hsub => by
    have hss : hrStepsPrefix cls spqrIdxs (h + 1) =
        hrStepsPrefix cls spqrIdxs h ++ hrSteps cls spqrIdxs h := by
      unfold hrStepsPrefix
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    have hevs : ((List.range (4 + 2 * (h + 1))).map ev).map CliEvent.run =
        ((List.range (4 + 2 * h)).map ev).map CliEvent.run ++
        [CliEvent.run (ev (4 + 2 * h)), CliEvent.run (ev (5 + 2 * h))] := by
      rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hss, hevs] at hm
    obtain ⟨v_h, v_step, rfl, hm_h, hv_h, hv_step, hm_step⟩ :=
      matchesEventsAt_party_append
        (by rw [List.length_map, List.length_range, hrStepsPrefix_length])
        (hrStepsPrefix_party cls spqrIdxs h)
        (by intro e he; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he;
            exact ev_not_rejected i (by have := List.mem_range.mp hi; omega))
        hm hsub
    have hp_h := peel_hr_prefix hfit hsetup hgwf h (by omega) v_h hm_h hv_h
    obtain ⟨hlen, _, hsSt, hrSt, ⟨tsS, hsync⟩, _, _, _, _⟩ :=
      hrPrefix_props cls spqrIdxs h (by omega)
    have hrun_eq : runSteps (hrStepsPrefix cls spqrIdxs h) t4 =
        runTrace r0 (hrStepsPrefix cls spqrIdxs h) := by
      unfold runTrace; rw [setupTrace_r0_eq_t4]
    rw [hrun_eq] at hm_step
    rcases hrc : hrConfig cls h with ⟨me, peer, sSt, rSt⟩
    rw [hrc] at hsSt hrSt hsync
    dsimp only at hsSt hrSt hsync
    unfold hrSteps at hm_step
    rw [hrc] at hm_step
    dsimp only at hm_step
    obtain ⟨v_s, vs_r, rfl, hrm_s, hv_s, hvs_r, hm_r⟩ :=
      matchesEventsAt_party_cons rfl (ev_not_rejected (4 + 2 * h) (by omega)) hm_step hv_step
    have hp_mid := extend_whisper_send (by omega) hgwf hp_h hv_s hlen hsSt hsync hrc hrm_s
    obtain ⟨v_r, v_end, rfl, hrm_r, hv_r, _, hm_end⟩ :=
      matchesEventsAt_party_cons rfl (ev_not_rejected (5 + 2 * h) (by omega)) hm_r hvs_r
    have hv_end_nil := matchesEventsAt_nil_vis hm_end
    subst hv_end_nil; rw [List.append_nil, ← List.append_assoc]
    obtain ⟨hnext_r, hlen1, hmsg_at⟩ :=
      halfRound_recv_next (cl := cls (2 + h)) (idx := spqrIdxs (5 + 2 * h))
        hlen (by omega) hsSt hrSt hsync
    obtain ⟨hcmd_r, hc_r, _⟩ := ev_recv_facts (m := 1 + h) (by omega)
    have hk_eq : 3 + 2 * (1 + h) = 5 + 2 * h := by omega
    rw [hk_eq] at hcmd_r hc_r
    obtain ⟨hdhs_pin, hsend_r, hpt_r⟩ :=
      peel_decrypt hgwf hv_r hnext_r hmsg_at hcmd_r hrm_r
    rw [hlen1] at hdhs_pin
    have hp_full := extend_no_send_pt hp_mid hsend_r hpt_r
    refine ⟨hp_full.base,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.send_pt,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.send_c32,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.send_c64,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.send_msg,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.send_addr,
      ?_,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.vis_sends,
      by rw [show 2 + (h + 1) = 3 + h by omega]; exact hp_full.vis_pts⟩
    intro m hm_lt
    by_cases hlt : m < 1 + h
    · exact hp_full.recv_dhs m hlt
    · have hm_eq : m = 1 + h := by omega
      subst hm_eq
      unfold recvDhsTs
      simp only [show ¬ (1 + h = 0) by omega, ↓reduceIte, show 1 + h - 1 = h by omega,
        show 62 + 14 * h = 55 + 14 * h + 7 by omega]
      exact hdhs_pin.trans hc_r

/-- Extracts `PrefixPinned` from `Explains` at any `k ∈ whisperOrReplayIndices`. -/
theorem explains_at_whisperOrReplay {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g' : Ghost}
    {vis' : List VisEntry} {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hk : k ∈ whisperOrReplayIndices)
    (hExp : Explains evictedI0 r S g' (ssClean cls spqrIdxs k) vis' (trace0.take k)) :
    let nSends := if k = 24 then 12 else (k - 5) / 2 + 3
    let nRecvs := if k = 24 then 11 else (k - 5) / 2 + 1
    PrefixPinned cls S g' vis' nSends nRecvs := by
  obtain ⟨hsetup, hgwf, _, hm⟩ := hExp
  unfold DY.Libsignal.Composed.Refinement.MatchesEvents at hm
  rw [setupTrace_eq_r0 hfit, setupTrace_r0_eq_t4] at hm
  by_cases hk24 : k = 24
  · subst hk24
    simp only [↓reduceIte]
    have hss24 : ssClean cls spqrIdxs 24 = hrStepsPrefix cls spqrIdxs 10 := by
      unfold ssClean hrStepsPrefix
      rw [List.take_of_length_le (by rw [RecvDefs.cleanCallSteps_length]), cleanCallSteps_eq_hr]
    have hevs24 : trace0.take 24 = (((List.range 24).map ev).map CliEvent.run) := by
      change Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.cliTrace.take 24 = _
      rw [trace_eq_evs]; rfl
    rw [hss24, hevs24] at hm
    exact peel_hr_prefix hfit hsetup hgwf 10 (by omega) vis' hm (fun _ hw => hw)
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
    simp only [show ¬ (5 + 2 * h = 24) by omega, ↓reduceIte,
      show (5 + 2 * h - 5) / 2 + 3 = 3 + h by omega,
      show (5 + 2 * h - 5) / 2 + 1 = 1 + h by omega]
    have hss_odd : ssClean cls spqrIdxs (5 + 2 * h) =
        hrStepsPrefix cls spqrIdxs h ++
        [let (me, _, _, _) := hrConfig cls h
         Step.messageEncrypt me (hrSStH h) (cls (2 + h)) (55 + 14 * h + 2)] := by
      unfold ssClean hrStepsPrefix
      rw [cleanCallSteps_eq_hr]
      rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hevs_odd : trace0.take (5 + 2 * h) =
        (((List.range (4 + 2 * h)).map ev).map CliEvent.run) ++ [CliEvent.run (ev (4 + 2 * h))] := by
      change Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.cliTrace.take (5 + 2 * h) = _
      rw [trace_eq_evs]
      rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hss_odd, hevs_odd] at hm
    obtain ⟨v_h, v_last, rfl, hm_h, hv_h, hv_last, hm_last⟩ :=
      matchesEventsAt_party_append
        (by rw [List.length_map, List.length_range, hrStepsPrefix_length])
        (hrStepsPrefix_party cls spqrIdxs h)
        (by intro e he; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he;
            exact ev_not_rejected i (by have := List.mem_range.mp hi; omega))
        hm (fun _ hw => hw)
    have hp_h := peel_hr_prefix hfit hsetup hgwf h (by omega) v_h hm_h hv_h
    obtain ⟨hlen, _, hsSt, _, ⟨tsS, hsync⟩, _, _, _, _⟩ :=
      hrPrefix_props cls spqrIdxs h (by omega)
    have hrun_eq : runSteps (hrStepsPrefix cls spqrIdxs h) t4 =
        runTrace r0 (hrStepsPrefix cls spqrIdxs h) := by
      unfold runTrace; rw [setupTrace_r0_eq_t4]
    rw [hrun_eq] at hm_last
    rcases hrc : hrConfig cls h with ⟨me, peer, sSt, rSt⟩
    rw [hrc] at hsSt hsync hm_last
    dsimp only at hsSt hsync hm_last
    obtain ⟨v_s, v_end, rfl, hrm_s, hv_s, _, hm_end⟩ :=
      matchesEventsAt_party_cons rfl (ev_not_rejected (4 + 2 * h) (by omega)) hm_last hv_last
    have hv_end_nil := matchesEventsAt_nil_vis hm_end
    subst hv_end_nil; rw [List.append_nil]
    exact extend_whisper_send hh hgwf hp_h hv_s hlen hsSt hsync hrc hrm_s

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins
