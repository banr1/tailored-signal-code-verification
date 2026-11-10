/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.ALaCarte.DecidableEq
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

@[expose] public section

set_option autoImplicit false

open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (TestTracePredicates mkTestTracePredicates FSQueryP PCSQueryP fsQuery_iff_test pcsQuery_iff_test)

/-!
# Triple Ratchet Forward-Secrecy Tightness Traces

Constructs six reachable witness traces (`trCK`, `trCK2`, `trRKPost`, `trRKP2`, `trDC`, `trMK`)
built on `HonestSession.lean` together with reachability, compromise-reduction, `saltDepth`, and
attacker-knowledge lemmas for Triple Ratchet forward-secrecy and post-compromise-security
specification-tightness tests.
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRTraces

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (ak_chain_ck_comm ak_chain_rk ak_dhPk ak_hmac
  ak_lit ak_net ak_seed exposeCks_reach exposeDhs_reach exposeRk_reach exposeSkipped_reach
  isAnyTRExposure mem_trEvIdx not_tr_logged trEvIdx)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (cB cB' coins0 coins1 coins2 dhsA dhsA2
  dhsB1 evIdx ikA ikB isCompromise key0 key1 key2 keys1 m0 m1 m2 mem_evIdx noCompromise_idx
  noCompromise_of_evIdx o1 pqm0 pqm1 pqm2 pqskB seedA1 seedB0 seedB1 seedB1_eq spkB stA0 stA1 stA2
  stA3' stA4 stB0' stB00 stB1 stB2 stB3 t1 t1_length t2 t2_length t3 t3_length t4 t4_length t5
  t5_length t5_stA0_at t6 t6_length t6_reach t7 t7_length t7_reach t8 t8_length t8_reach t8_stB1_at
  t9 t9_length t10 t10_length t10_reach t11 t11_length t11_reach t11_stA4_at wTr)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_not_init)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs
  Runs.messageDecrypt_noRatchet Runs.messageEncrypt StP StT aliceSt aliceTr aliceTrOpt
  createChain_comm dec_ok encMsg encSig encSt encTr exposeCksTr exposeDhsTr exposeRkTr
  exposeSkippedTr genPQPrekeyTr genSignedPrekeyTr mac_ok messageDecrypt_reachable
  messageEncrypt_reachable notInit_recv parse_encMsg ratchetState reach_of_runs recvKey recvSt
  registerIdentityTr rnd skipTr)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (ExposedKey IsChainRoot
  compromised_iff_exposedKey_of_noCompromise exposedKey_append_expose exposedKey_encTr
  isChainRoot_createChain_snd not_exposedKey_of_trEvIdx saltDepth)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem DY.KdfExtract DY.Concat DY.Literal
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm pqxdhLabel agree
  AliceHandshakeWasCompromised BobHandshakeWasCompromised NoCompromise HandshakeKeysAt HandshakeWasCompromisedAt)

/-! ## Key-derivation and wire-header knowledge helpers -/

theorem knows_encMsg_ratchetKey {tr : ExecTrace} {st : TRState} {coins pq m : Bytes}
    {i : Nat} (h : tr.MessageSentAt (encMsg st coins pq m) i) :
    (dhPk st.dhs).AttackerKnows tr := by
  have henc := Trace.MessageSentAt_implies_AttackerKnows _ _ _ h
  let keys := trMsgKeys pq (kdfCk st.cks).2
  let wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc keys.cipherKey keys.iv m) (Spqr.spqrSend st.spqr coins).2.2
  let mac := computeMac keys.macKey st.myIk st.peerIk wire
  have hsp := Concat.attacker_knows_split (Concat.concat wire mac) wire.length tr henc
  rw [Concat.split_concat] at hsp
  exact (DY.TrWire.attacker_knows_trWireMsg_args _ _ _ _ _ _ _ tr hsp.1).1

theorem ak_kdfCk_fst {tr : ExecTrace} {ck : Bytes} (hck : ck.AttackerKnows tr) :
    (kdfCk ck).1.AttackerKnows tr :=
  ak_hmac hck (ak_lit _)

/-! ## Local trace, snapshot, and event-index helpers -/

private theorem nil_len_loc : (Trace.nil : ExecTrace).length = 0 :=
  Symbolic.DYBridge.DY.Trace.length_eq_1

private theorem append_len_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem le_append_loc {E : Type} [ExecTraceTypes.Has E] {ta tb : ExecTrace}
    (h : ta ≤ tb) (e : E) : ta ≤ tb.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le tb e)

private theorem append2_le_loc {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) : tr ≤ (tr.append e1).append e2 :=
  le_append_loc (Trace.append_le tr e1) e2

private theorem append2_len_loc {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) :
    ((tr.append e1).append e2).length = tr.length + 2 := by
  simp only [append_len_loc]

private theorem at?_mono_loc {E : Type} [ExecTraceTypes.Has E] {ta tb : ExecTrace} {i : Nat}
    {x : E} (hle : ta ≤ tb) (h : ta.at? i = some x) : tb.at? i = some x := by
  have := Trace.at?_le (EntryT := E) ta tb i hle
  rwa [h] at this

private theorem at?_append_at_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    {i : Nat} (hi : tr.length = i) : (tr.append x).at? i = some x := by
  subst hi; exact Trace.at?_append tr x

private theorem append2_snd_at_loc {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) {i : Nat} (hi : tr.length + 1 = i) :
    ((tr.append e1).append e2).at? i = some e2 :=
  at?_append_at_loc _ _ (by rw [append_len_loc]; exact hi)

private theorem hat_snoc_loc {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : ExecTrace.Entry) (i : Nat) :
    ((tr.snoc e).at? i : Option E) =
      (if i = tr.length then TraceEntryHas.proj e
       else if i < tr.length then tr.at? i else none) := by
  simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_2]
  by_cases h1 : i = tr.length
  · subst h1
    have hlt : tr.length < tr.length + 1 := Nat.lt_succ_self _
    simp only [hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
  · by_cases h2 : i < tr.length
    · have hlt : i < tr.length + 1 := by omega
      simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
    · have hlt : ¬ i < tr.length + 1 := by omega
      simp only [h1, h2, hlt, ↓reduceDIte, ↓reduceIte]

private theorem at?_append_self_proj_loc {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc, ↓reduceIte]

private theorem at?_append_of_lt_loc {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  have hne : i ≠ tr.length := Nat.ne_of_lt hi
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc, hne, hi, ↓reduceIte]

private theorem eventLoggedAt_of_at?_loc {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact h

private theorem eventLoggedAt_mono_loc {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {ta tb : ExecTrace} {ev : Ev} {i : Nat}
    (hle : ta ≤ tb) (h : ta.EventLoggedAt ev i) : tb.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono_loc hle h

private theorem messageSentAt_of_at?_loc {tr : ExecTrace} {m : Bytes} {i : Nat}
    (h : tr.at? i = some (NetE m)) : tr.MessageSentAt m i := by
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact h

private theorem runs_cast_loc {α : Type} {x : Traceful α} {tr ta tb : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 ta) (ha : a1 = a2) (ht : ta = tb) : Runs x tr a2 tb := by
  subst ha; subst ht; exact h

private theorem bytesToLiteral_spqrSendMsg_loc (st coins : Bytes) :
    Literal.bytesToLiteral (Spqr.spqrSend st coins).2.2 = none := by
  have hl0 : ((Spqr.spqrSend st coins).2.2).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes)
  dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

private theorem skipTr_one_loc (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (h1 : n.toNat - c.index.toNat = 1) :
    skipTr tr s pk c src n =
      tr.append (EvT (.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)) := by
  dsimp only [skipTr]; rw [h1]
  unfold TripleRatchet.logSkippedKeys
  have ⟨hs1, hs2⟩ :=
    Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.logEvent tr
      (TREvent.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)
  rw [Traceful.run_bind]
  rcases hrun :
      (ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)).run tr with
    ⟨opt_x, tr_1⟩
  rw [hrun] at hs1 hs2
  subst hs1; dsimp only; rw [hs2]
  unfold TripleRatchet.logSkippedKeys
  erw [Traceful.run_pure]

private theorem isCurrentSnapshot_append_self_loc (tr : ExecTrace) (me : Participant)
    (st : TRState) {k : Nat} (hk : tr.length = k) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [Trace.at?_append tr (StT me st), append_len_loc, Nat.sub_self]; rfl

private theorem isCurrentSnapshot_append_non_st_loc {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {k : Nat} (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))) =
      none)
    (hcur : TripleRatchet.isCurrentSnapshot tr k = true) :
    TripleRatchet.isCurrentSnapshot (tr.append e) k = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  cases hst : (tr.at? k :
      Option (PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))) with
  | none => rw [hst] at hcur; cases hcur
  | some es =>
    have hk : k < tr.length := by
      have := Trace.at?_eq_some_implies_length_le
        (EntryT := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))
        tr k
      rwa [hst] at this
    rw [hst] at hcur
    rw [at?_mono_loc (Trace.append_le tr e) hst]
    dsimp only at hcur ⊢
    have hsub : (tr.append e).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
      rw [append_len_loc]; omega
    rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at hcur ⊢
      intro j hj
      rw [at?_append_of_lt_loc tr e (by rw [List.mem_range'_1] at hj; omega)]
      exact hcur j hj
    · rw [at?_append_self_proj_loc, hnone]

private theorem isCurrentSnapshot_append_st_ne_loc {tr : ExecTrace} {me me' : Participant}
    {st st' : TRState} {k : Nat}
    (hst : tr.at? k = some (StT me st)) (hne : (me' != me) = true)
    (hcur : TripleRatchet.isCurrentSnapshot tr k = true) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me' st')) k = true := by
  have hk : k < tr.length := by
    have := Trace.at?_eq_some_implies_length_le
      (EntryT := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))
      tr k
    rwa [hst] at this
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [hst] at hcur
  rw [at?_mono_loc (Trace.append_le tr (StT me' st')) hst]
  dsimp only at hcur ⊢
  have hsub : (tr.append (StT me' st')).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
    rw [append_len_loc]; omega
  rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
    List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hcur ⊢
    intro j hj
    rw [at?_append_of_lt_loc tr (StT me' st') (by rw [List.mem_range'_1] at hj; omega)]
    exact hcur j hj
  · rw [Trace.at?_append]; simp [hne]

private theorem isCurrentSnapshot_encTr_self_loc (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : Bytes) {n5 : Nat} (h5 : tr.length + 5 = n5) :
    TripleRatchet.isCurrentSnapshot (encTr tr me stH st pq) n5 = true := by
  subst h5; dsimp only [encTr]
  refine isCurrentSnapshot_append_non_st_loc _ rfl (isCurrentSnapshot_append_self_loc _ _ _ ?_)
  simp only [append_len_loc]

private theorem isCurrentSnapshot_encTr_ne_loc {tr : ExecTrace} {me me' : Participant}
    {st st' : TRState} {stH k : Nat} {pq : Bytes}
    (hst : tr.at? k = some (StT me st)) (hne : (me' != me) = true)
    (hcur : TripleRatchet.isCurrentSnapshot tr k = true) :
    TripleRatchet.isCurrentSnapshot (encTr tr me' stH st' pq) k = true := by
  dsimp only [encTr]
  have h5le : tr ≤ ((((tr.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend st'.spqr (rnd (tr.length + 1) 32)).2.1)).append
      (EvT (.Sent me' st'.peer (dhPk st'.dhs) st'.ns (rnd tr.length 32)))).append
      (EvT (.MessageKey (st'.sessionInfo me') .sender (kdfCk st'.cks).2 pq st'.ns
        st'.rIdx stH)) :=
    le_append_loc (le_append_loc (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _) _
  refine isCurrentSnapshot_append_non_st_loc _ rfl
    (isCurrentSnapshot_append_st_ne_loc (at?_mono_loc h5le hst) hne ?_)
  exact isCurrentSnapshot_append_non_st_loc _ rfl (isCurrentSnapshot_append_non_st_loc _ rfl
    (isCurrentSnapshot_append_non_st_loc _ rfl (isCurrentSnapshot_append_non_st_loc _ rfl
      (isCurrentSnapshot_append_non_st_loc _ rfl hcur))))

private theorem encTr_le_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_loc (le_append_loc (le_append_loc (le_append_loc (le_append_loc
    (le_append_loc (Trace.append_le _ _) _) _) _) _) _) _

private theorem encTr_len_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : (encTr tr me stH st pq).length = tr.length + 7 := by
  dsimp only [encTr]; simp only [append_len_loc]

private theorem encTr_pq_at_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) {coins : Bytes} {i : Nat}
    (hc : rnd (tr.length + 1) 32 = coins) (hi : tr.length + 2 = i) :
    (encTr tr me stH st pq).at? i = some (NetE (Spqr.spqrSend st.spqr coins).2.1) := by
  dsimp only [encTr]; rw [hc]
  exact at?_mono_loc
    (le_append_loc (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _)
    (at?_append_at_loc _ _ (by simp only [append_len_loc]; exact hi))

private theorem encTr_mk_at_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) {i : Nat} (hi : tr.length + 4 = i) :
    (encTr tr me stH st pq).EventLoggedAt
      (TREvent.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns st.rIdx stH) i := by
  refine eventLoggedAt_of_at?_loc ?_
  dsimp only [encTr]
  exact at?_mono_loc (append2_le_loc _ _ _)
    (at?_append_at_loc _ _ (by simp only [append_len_loc]; exact hi))

private theorem encTr_st_at_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) {coins : Bytes} {i : Nat}
    (hc : rnd (tr.length + 1) 32 = coins) (hi : tr.length + 5 = i) :
    (encTr tr me stH st pq).at? i = some (StT me (encSt st coins)) := by
  dsimp only [encTr]; rw [hc]
  exact at?_mono_loc (Trace.append_le _ _)
    (at?_append_at_loc _ _ (by simp only [append_len_loc]; exact hi))

private theorem encTr_msg_at_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) {m coins : Bytes} {i : Nat}
    (hm : rnd tr.length 32 = m) (hc : rnd (tr.length + 1) 32 = coins) (hi : tr.length + 6 = i) :
    (encTr tr me stH st pq).at? i = some (NetE (encMsg st coins pq m)) := by
  dsimp only [encTr]; rw [hm, hc]
  exact at?_append_at_loc _ _ (by simp only [append_len_loc]; exact hi)

private theorem runs_messageEncrypt_loc {tr : ExecTrace} {me : Participant} {stH pqH outH : Nat}
    {st : TRState} {coins pq : Bytes}
    (hst : tr.at? stH = some (StT me st)) (hns : st.ns ≠ u32Max)
    (hc : rnd (tr.length + 1) 32 = coins)
    (hpqEq : (Spqr.spqrSend st.spqr coins).2.1 = pq)
    (hpqH : tr.length + 2 = pqH) (houtH : tr.length + 6 = outH) :
    Runs (TripleRatchet.messageEncrypt me stH 32 pqH) tr outH (encTr tr me stH st pq) := by
  have hpq : (((tr.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1)).at? pqH = some (NetE pq) := by
    rw [hc, hpqEq]
    exact at?_append_at_loc _ _ (by simp only [append_len_loc]; exact hpqH)
  exact runs_cast_loc (Runs.messageEncrypt hst hns hpq) houtH rfl

private theorem evIdx_nil_loc (p : PQXDHEvent → Bool) : evIdx Trace.nil p = [] := by
  unfold evIdx; rw [nil_len_loc]; rfl

private theorem evIdx_append_non_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    evIdx (tr.append x) p = evIdx tr p := by
  unfold evIdx
  rw [append_len_loc, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj_loc, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt_loc tr x (List.mem_range.mp hi)]

private theorem evIdx_append_ev_loc (tr : ExecTrace) (ev : PQXDHEvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvP ev)) p = cond (p ev) (evIdx tr p ++ [tr.length]) (evIdx tr p) := by
  unfold evIdx
  rw [append_len_loc, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
        decide),
      List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt_loc tr (EvP ev) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]),
      List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt_loc tr (EvP ev) (List.mem_range.mp hi)])

private theorem evIdx_encTr_loc (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) (p : PQXDHEvent → Bool) :
    evIdx (encTr tr me stH st pq) p = evIdx tr p := by
  dsimp only [encTr]
  rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
    evIdx_append_non_loc _ _ _ rfl]

private theorem evIdx_eq_nil_of_le_loc {ta tb : ExecTrace} {p : PQXDHEvent → Bool}
    (hle : ta ≤ tb) (h2 : evIdx tb p = []) : evIdx ta p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  simp only [evIdx, List.mem_filter, List.mem_range,
    Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hi
  cases hat : (ta.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => rw [hat] at hi; exact Bool.noConfusion hi.2
  | some ev =>
    rw [hat] at hi
    have hmem : i ∈ evIdx tb p :=
      mem_evIdx (eventLoggedAt_of_at?_loc (at?_mono_loc hle hat)) hi.2
    rw [h2] at hmem
    exact List.not_mem_nil hmem

private theorem someEventB_of_evIdx_nil_loc {tr : ExecTrace} {p : PQXDHEvent → Bool}
    (h : evIdx tr p = []) : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  intro i _
  cases hat : (tr.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => dsimp only; exact Bool.false_ne_true
  | some ev =>
    dsimp only
    cases hp : p ev.ev
    · exact Bool.false_ne_true
    · intro _
      have hmem : i ∈ evIdx tr p := mem_evIdx (eventLoggedAt_of_at?_loc hat) hp
      rw [h] at hmem
      exact List.not_mem_nil hmem

private theorem t1_eq_loc : t1 = registerIdentityTr Trace.nil "alice" :=
  (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.registerIdentity (by
    simp only [Bool.not_eq_true']
    exact someEventB_of_evIdx_nil_loc (evIdx_nil_loc _))).2

private theorem t2_eq_loc : t2 = registerIdentityTr t1 "bob" :=
  (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.registerIdentity (by
    simp only [Bool.not_eq_true']
    refine someEventB_of_evIdx_nil_loc ?_
    rw [t1_eq_loc]; dsimp only [registerIdentityTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_ev_loc]
    dsimp only
    rw [show ("alice" == "bob") = false by decide,
      Bool.cond_false, evIdx_append_non_loc _ _ _ rfl, evIdx_nil_loc])).2

private theorem t3_eq_loc : t3 = genSignedPrekeyTr t2 "bob" ikB :=
  (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.genSignedPrekey (by
    rw [t2_eq_loc]
    simp only [registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc_loc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t1_length, ↓reduceIte]
    rfl)).2

private theorem t4_eq_loc : t4 = genPQPrekeyTr t3 "bob" ikB :=
  (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.genPQPrekey (by
    rw [t3_eq_loc, t2_eq_loc]
    simp only [genSignedPrekeyTr, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      hat_snoc_loc, Symbolic.DYBridge.DY.Trace.length_eq_2, t1_length, ↓reduceIte]
    rfl)).2

private theorem trEvIdx_nil_loc (p : TREvent → Bool) : trEvIdx Trace.nil p = [] := by
  unfold trEvIdx; rw [nil_len_loc]; rfl

private theorem trEvIdx_append_non_loc {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : TREvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    trEvIdx (tr.append x) p = trEvIdx tr p := by
  unfold trEvIdx
  rw [append_len_loc, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj_loc, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt_loc tr x (List.mem_range.mp hi)]

private theorem trEvIdx_append_ev_false_loc (tr : ExecTrace) (ev : TREvent) (p : TREvent → Bool)
    (hp : p ev = false) :
    trEvIdx (tr.append (EvT ev)) p = trEvIdx tr p := by
  unfold trEvIdx
  rw [append_len_loc, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt_loc tr (EvT ev) (List.mem_range.mp hi)]

private theorem trEvIdx_encTr_false_loc (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : Bytes) (p : TREvent → Bool)
    (hSent : ∀ m, p (.Sent me st.peer (dhPk st.dhs) st.ns m) = false)
    (hMk :
      p (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
        st.rIdx stH) = false) :
    trEvIdx (encTr tr me stH st pq) p = trEvIdx tr p := by
  dsimp only [encTr]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_ev_false_loc _ _ _ hMk, trEvIdx_append_ev_false_loc _ _ _ (hSent _),
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl]

private theorem trEvIdx_eq_nil_of_le_loc {ta tb : ExecTrace} {p : TREvent → Bool}
    (hle : ta ≤ tb) (h2 : trEvIdx tb p = []) : trEvIdx ta p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  simp only [trEvIdx, List.mem_filter, List.mem_range,
    Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hi
  cases hat : (ta.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) with
  | none => rw [hat] at hi; exact Bool.noConfusion hi.2
  | some ev =>
    rw [hat] at hi
    have hmem : i ∈ trEvIdx tb p :=
      mem_trEvIdx (eventLoggedAt_of_at?_loc (at?_mono_loc hle hat)) hi.2
    rw [h2] at hmem
    exact List.not_mem_nil hmem

private theorem trEvIdx_t4_loc (p : TREvent → Bool) : trEvIdx t4 p = [] := by
  rw [t4_eq_loc]; dsimp only [genPQPrekeyTr]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl]
  rw [t3_eq_loc]; dsimp only [genSignedPrekeyTr]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl]
  rw [t2_eq_loc]; dsimp only [registerIdentityTr]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl]
  rw [t1_eq_loc]; dsimp only [registerIdentityTr]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_nil_loc]

private theorem t7_le_t8_loc : t7 ≤ t8 := by
  dsimp only [t8]
  exact le_append_loc (le_append_loc (le_append_loc (le_append_loc (le_append_loc
    (le_append_loc (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _) _) _) _) _) _

private theorem t8_le_t9_loc : t8 ≤ t9 := by
  dsimp only [t9]
  exact le_append_loc (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _

private theorem t10_le_t11_loc : t10 ≤ t11 := by
  dsimp only [t11]
  exact le_append_loc (le_append_loc (le_append_loc (le_append_loc
    (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _) _) _) _

private theorem t5_le_t10_loc : t5 ≤ t10 :=
  Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _)
    (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _)
      (Trace.le_trans _ _ _ t7_le_t8_loc
        (Trace.le_trans _ _ _ t8_le_t9_loc (encTr_le_loc _ _ _ _ _))))

private theorem evIdx_t11_isCompromise_loc : evIdx t11 isCompromise = [] := by
  have h11_12 : t11 ≤ Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t12 :=
    append2_le_loc _ _ _
  have h12_13 :
      Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t12 ≤
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13 :=
    append2_le_loc _ _ _
  have h13_14 :
      Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13 ≤
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14 :=
    encTr_le_loc _ _ _ _ _
  have h14_w : Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14 ≤ wTr := by
    dsimp only [wTr, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t15]
    exact le_append_loc (le_append_loc (le_append_loc (le_append_loc
      (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _) _) _) _
  exact evIdx_eq_nil_of_le_loc
    (Trace.le_trans _ _ _ h11_12
      (Trace.le_trans _ _ _ h12_13 (Trace.le_trans _ _ _ h13_14 h14_w)))
    noCompromise_idx

private theorem trEvIdx_t8_false_loc (p : TREvent → Bool)
    (hInit : ∀ a b k1 k2, p (.InitSession a b k1 k2) = false)
    (hSent : ∀ a b pk n m, p (.Sent a b pk n m) = false)
    (hMkS : ∀ s seed pq n r pa, p (.MessageKey s .sender seed pq n r pa) = false)
    (hRat : ∀ a b pk1 pk2, p (.DHRatchet a b pk1 pk2) = false)
    (hHon : ∀ s dhs r, p (.HonestDH s dhs r) = false)
    (hRec : ∀ a b pk n m, p (.Received a b pk n m) = false)
    (hMkR0 : ∀ s seed pq r pa, p (.MessageKey s .receiver seed pq 0 r pa) = false) :
    trEvIdx t8 p = [] := by
  dsimp only [t8]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ (hMkR0 ..),
    trEvIdx_append_ev_false_loc _ _ _ (hRec ..), trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_ev_false_loc _ _ _ (hHon ..), trEvIdx_append_ev_false_loc _ _ _ (hRat ..),
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl]
  dsimp only [t7]
  rw [trEvIdx_encTr_false_loc _ _ _ _ _ _ (fun _ => hSent ..) (hMkS ..)]
  dsimp only [t6]
  rw [trEvIdx_encTr_false_loc _ _ _ _ _ _ (fun _ => hSent ..) (hMkS ..)]
  dsimp only [t5, aliceTr, aliceTrOpt]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_ev_false_loc _ _ _ (hInit ..), trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_t4_loc]

private theorem trEvIdx_t11_noExposure_loc : trEvIdx t11 isAnyTRExposure = [] := by
  dsimp only [t11]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
    trEvIdx_append_ev_false_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
    trEvIdx_append_ev_false_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl,
    trEvIdx_append_non_loc _ _ _ rfl]
  dsimp only [t10]
  rw [trEvIdx_encTr_false_loc _ _ _ _ _ _ (fun _ => rfl) rfl]
  dsimp only [t9]
  rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
    trEvIdx_append_ev_false_loc _ _ _ rfl, trEvIdx_append_non_loc _ _ _ rfl]
  exact trEvIdx_t8_false_loc isAnyTRExposure
    (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

private theorem t6_stA0_loc : t6.at? 30 = some (StT "alice" stA0) :=
  at?_mono_loc (encTr_le_loc _ _ _ _ _) t5_stA0_at

private theorem t7_stA0_loc : t7.at? 30 = some (StT "alice" stA0) :=
  at?_mono_loc (encTr_le_loc _ _ _ _ _) t6_stA0_loc

private theorem t10_stA0_loc : t10.at? 30 = some (StT "alice" stA0) :=
  at?_mono_loc t5_le_t10_loc t5_stA0_at

private theorem t11_stA0_loc : t11.at? 30 = some (StT "alice" stA0) :=
  at?_mono_loc t10_le_t11_loc t10_stA0_loc

private theorem t10_stB3_loc : t10.at? 63 = some (StT "bob" stB3) :=
  encTr_st_at_loc t9 "bob" 57 stB2 key2 (by rw [t9_length]) (by rw [t9_length])

private theorem t7_stA2_loc : t7.at? 43 = some (StT "alice" stA2) :=
  encTr_st_at_loc t6 "alice" 36 stA1 key1 (by rw [t6_length]) (by rw [t6_length])

private theorem t8_stA2_loc : t8.at? 43 = some (StT "alice" stA2) :=
  at?_mono_loc t7_le_t8_loc t7_stA2_loc

private theorem t6_mkA0_at_loc :
    t6.EventLoggedAt
      (TREvent.MessageKey (stA0.sessionInfo "alice") .sender (kdfCk stA0.cks).2 key0 0 1 30)
      35 :=
  encTr_mk_at_loc t5 "alice" 30 stA0 key0 (by rw [t5_length])

private theorem t7_mkA1_at_loc :
    t7.EventLoggedAt
      (TREvent.MessageKey (stA1.sessionInfo "alice") .sender (kdfCk stA1.cks).2 key1 1 1 36)
      42 :=
  encTr_mk_at_loc t6 "alice" 36 stA1 key1 (by rw [t6_length])

private theorem t10_mkB0_at_loc :
    t10.EventLoggedAt
      (TREvent.MessageKey (stB2.sessionInfo "bob") .sender (kdfCk stB2.cks).2 key2 0 2 57)
      62 :=
  encTr_mk_at_loc t9 "bob" 57 stB2 key2 (by rw [t9_length])

private theorem t10_msg2_at_loc :
    t10.at? 64 = some (NetE (encMsg stB2 coins2 key2 m2)) :=
  encTr_msg_at_loc t9 "bob" 57 stB2 key2 (by rw [t9_length]) (by rw [t9_length])
    (by rw [t9_length])

/-! ## Witness trace `trCK` -/

/-- `t6` extended by exposing `stA0.cks`. -/
def trCK : ExecTrace := exposeCksTr t6 "alice" stA0

abbrev mkA0 : Bytes := (kdfCk stA0.cks).2

@[simp] theorem saltDepth_mkA0 : saltDepth mkA0 = 5 := by
  change saltDepth (kdfCk stA0.cks).2 = 5
  simp

theorem trCK_reach : trCK.Reachable reachability :=
  exposeCks_reach t6_reach (stH := 30) t6_stA0_loc

theorem trCK_noCompromise : NoCompromise trCK :=
  noCompromise_of_evIdx (by
    dsimp only [trCK, exposeCksTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]
    exact evIdx_eq_nil_of_le_loc
      (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _)
        (Trace.le_trans _ _ _ t7_le_t8_loc
          (Trace.le_trans _ _ _ t8_le_t9_loc
            (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) t10_le_t11_loc))))
      evIdx_t11_isCompromise_loc)

theorem not_exposedKey_t6 {k : Bytes} : ¬ ExposedKey t6 k :=
  not_exposedKey_of_trEvIdx
    (trEvIdx_eq_nil_of_le_loc
      (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _)
        (Trace.le_trans _ _ _ t7_le_t8_loc
          (Trace.le_trans _ _ _ t8_le_t9_loc
            (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) t10_le_t11_loc))))
      trEvIdx_t11_noExposure_loc)

theorem trCK_compromised {k : Bytes}
    (h : (mkTestTracePredicates trCK).Compromised k) : k = stA0.cks := by
  have hexp := (compromised_iff_exposedKey_of_noCompromise trCK_noCompromise).mp h
  rcases exposedKey_append_expose hexp with h6 | rfl
  · exact False.elim (not_exposedKey_t6 h6)
  · rfl

theorem trCK_messageKey : (mkTestTracePredicates trCK).MessageKey mkA0 :=
  ⟨key0, stA0.sessionInfo "alice", .sender, 0, 1, 30,
    ⟨35, eventLoggedAt_mono_loc (append2_le_loc _ _ _) t6_mkA0_at_loc⟩⟩

theorem trCK_knows : (mkTestTracePredicates trCK).AttackerKnows mkA0 :=
  ⟨key0, ⟨stA0.sessionInfo "alice", .sender, 0, 1, 30,
    ⟨35, eventLoggedAt_mono_loc (append2_le_loc _ _ _) t6_mkA0_at_loc⟩⟩,
    .inl (ak_seed (ak_net (i := 39) (append2_snd_at_loc _ _ _ (by rw [t6_length]))))⟩

/-! ## Witness trace `trCK2` -/

/-- `t7` extended by exposing `stA0.cks`. -/
def trCK2 : ExecTrace := exposeCksTr t7 "alice" stA0

abbrev mkA1 : Bytes := (kdfCk stA1.cks).2

@[simp] theorem saltDepth_mkA1 : saltDepth mkA1 = 6 := by
  change saltDepth (kdfCk stA1.cks).2 = 6
  simp

theorem trCK2_reach : trCK2.Reachable reachability :=
  exposeCks_reach t7_reach (stH := 30) t7_stA0_loc

theorem trCK2_noCompromise : NoCompromise trCK2 :=
  noCompromise_of_evIdx (by
    dsimp only [trCK2, exposeCksTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]
    exact evIdx_eq_nil_of_le_loc
      (Trace.le_trans _ _ _ t7_le_t8_loc
        (Trace.le_trans _ _ _ t8_le_t9_loc
          (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) t10_le_t11_loc)))
      evIdx_t11_isCompromise_loc)

theorem not_exposedKey_t7 {k : Bytes} : ¬ ExposedKey t7 k :=
  not_exposedKey_of_trEvIdx
    (trEvIdx_eq_nil_of_le_loc
      (Trace.le_trans _ _ _ t7_le_t8_loc
        (Trace.le_trans _ _ _ t8_le_t9_loc
          (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) t10_le_t11_loc)))
      trEvIdx_t11_noExposure_loc)

theorem trCK2_compromised {k : Bytes}
    (h : (mkTestTracePredicates trCK2).Compromised k) : k = stA0.cks := by
  have hexp := (compromised_iff_exposedKey_of_noCompromise trCK2_noCompromise).mp h
  rcases exposedKey_append_expose hexp with h7 | rfl
  · exact False.elim (not_exposedKey_t7 h7)
  · rfl

theorem trCK2_messageKey : (mkTestTracePredicates trCK2).MessageKey mkA1 :=
  ⟨key1, stA1.sessionInfo "alice", .sender, 1, 1, 36,
    ⟨42, eventLoggedAt_mono_loc (append2_le_loc _ _ _) t7_mkA1_at_loc⟩⟩

theorem trCK2_knows : (mkTestTracePredicates trCK2).AttackerKnows mkA1 :=
  ⟨key1, ⟨stA1.sessionInfo "alice", .sender, 1, 1, 36,
    ⟨42, eventLoggedAt_mono_loc (append2_le_loc _ _ _) t7_mkA1_at_loc⟩⟩,
    .inl (ak_seed (ak_kdfCk_fst (ak_net (i := 46)
      (append2_snd_at_loc _ _ _ (by rw [t7_length])))))⟩

/-! ## Witness trace `trRKPost` -/

def tRKP1 : ExecTrace := exposeRkTr t10 "alice" stA0

/-- `t10` extended by exposing `stA0.rk` and `dhsA`. -/
def trRKPost : ExecTrace := exposeDhsTr tRKP1 "alice" stA0

abbrev mkB0 : Bytes := (kdfCk stB2.cks).2

@[simp] theorem saltDepth_mkB0 : saltDepth mkB0 = 7 := by
  change saltDepth (kdfCk stB2.cks).2 = 7
  simp

theorem stB2_cks_eq : stB2.cks = (createChain stA0.rk (dhPk dhsA) dhsB1).2 := by
  show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2 =
    (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsA) dhsB1).2
  rw [createChain_comm keys1.rk dhsA spkB]

theorem trRKPost_reach : trRKPost.Reachable reachability :=
  exposeDhs_reach (exposeRk_reach t10_reach (stH := 30) t10_stA0_loc) (stH := 30)
    (at?_mono_loc (append2_le_loc _ _ _) t10_stA0_loc)

theorem trRKPost_noCompromise : NoCompromise trRKPost :=
  noCompromise_of_evIdx (by
    dsimp only [trRKPost, tRKP1, exposeDhsTr, exposeRkTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl]
    exact evIdx_eq_nil_of_le_loc t10_le_t11_loc evIdx_t11_isCompromise_loc)

theorem not_exposedKey_t10 {k : Bytes} : ¬ ExposedKey t10 k :=
  not_exposedKey_of_trEvIdx (trEvIdx_eq_nil_of_le_loc t10_le_t11_loc trEvIdx_t11_noExposure_loc)

theorem trRKPost_compromised {k : Bytes}
    (h : (mkTestTracePredicates trRKPost).Compromised k) : k = stA0.rk ∨ k = dhsA := by
  have hexp := (compromised_iff_exposedKey_of_noCompromise trRKPost_noCompromise).mp h
  rcases exposedKey_append_expose hexp with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_t10 h0)
    · exact .inl rfl
  · exact .inr rfl

theorem trRKPost_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trRKPost).Compromised k) : saltDepth k ≤ 4 := by
  rcases trRKPost_compromised h with rfl | rfl <;> simp

theorem trRKPost_messageKey : (mkTestTracePredicates trRKPost).MessageKey mkB0 :=
  ⟨key2, stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc (append2_le_loc _ _ _) t10_mkB0_at_loc)⟩⟩

theorem trRKPost_knows_mkB0 : mkB0.AttackerKnows trRKPost := by
  have hrk : stA0.rk.AttackerKnows trRKPost :=
    ak_net (i := 66) (at?_mono_loc (append2_le_loc _ _ _)
      (append2_snd_at_loc _ _ _ (by rw [t10_length])))
  have hsk : dhsA.AttackerKnows trRKPost :=
    ak_net (i := 68) (append2_snd_at_loc _ _ _
      (by dsimp only [tRKP1, exposeRkTr]; rw [append2_len_loc, t10_length]))
  have hpk : (dhPk dhsB1).AttackerKnows trRKPost :=
    knows_encMsg_ratchetKey (tr := trRKPost) (st := stB2) (coins := coins2) (pq := key2)
      (m := m2) (i := 64)
      (messageSentAt_of_at?_loc
        (at?_mono_loc (append2_le_loc _ _ _)
          (at?_mono_loc (append2_le_loc _ _ _) t10_msg2_at_loc)))
  have hcks : (createChain stA0.rk (dhPk dhsA) dhsB1).2.AttackerKnows trRKPost :=
    ak_chain_ck_comm hrk hpk hsk
  rw [← stB2_cks_eq] at hcks
  exact ak_seed hcks

theorem trRKPost_knows : (mkTestTracePredicates trRKPost).AttackerKnows mkB0 :=
  ⟨key2, ⟨stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc (append2_le_loc _ _ _) t10_mkB0_at_loc)⟩⟩,
    .inl trRKPost_knows_mkB0⟩

/-! ## Witness trace `trRKP2` -/

abbrev mRKP2 : Bytes := rnd 65 32
abbrev coinsRKP2 : Bytes := rnd 66 32
def keyRKP2 : Bytes := (Spqr.spqrSend stB3.spqr coinsRKP2).2.1
def tRKP2_0 : ExecTrace := encTr t10 "bob" 63 stB3 keyRKP2
def tRKP2_1 : ExecTrace := exposeRkTr tRKP2_0 "alice" stA0

/-- `t10` extended with Bob encrypting message 1 from `stB3` and exposing `stA0.rk` and `dhsA`. -/
def trRKP2 : ExecTrace := exposeDhsTr tRKP2_1 "alice" stA0

abbrev mkB1 : Bytes := (kdfCk stB3.cks).2

@[simp] theorem saltDepth_mkB1 : saltDepth mkB1 = 8 := by
  change saltDepth (kdfCk stB3.cks).2 = 8
  simp

theorem isChainRoot_stB2_cks : IsChainRoot stB2.cks := by
  rw [stB2_cks_eq]; exact isChainRoot_createChain_snd _ _ _

theorem tRKP2_0_runs : Runs (TripleRatchet.messageEncrypt "bob" 63 32 67) t10 71 tRKP2_0 :=
  runs_messageEncrypt_loc t10_stB3_loc (by decide) (by rw [t10_length]) rfl
    (by rw [t10_length]) (by rw [t10_length])

theorem tRKP2_0_reach : tRKP2_0.Reachable reachability :=
  reach_of_runs tRKP2_0_runs
    (messageEncrypt_reachable t10_reach
      (hcur := isCurrentSnapshot_encTr_self_loc t9 "bob" 57 stB2 key2 (by rw [t9_length])))

theorem trRKP2_reach : trRKP2.Reachable reachability :=
  have hst0 : tRKP2_0.at? 30 = some (StT "alice" stA0) :=
    at?_mono_loc (encTr_le_loc _ _ _ _ _) t10_stA0_loc
  exposeDhs_reach (exposeRk_reach tRKP2_0_reach (stH := 30) hst0) (stH := 30)
    (at?_mono_loc (append2_le_loc _ _ _) hst0)

theorem trRKP2_noCompromise : NoCompromise trRKP2 :=
  noCompromise_of_evIdx (by
    dsimp only [trRKP2, tRKP2_1, tRKP2_0, exposeDhsTr, exposeRkTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl, evIdx_encTr_loc]
    exact evIdx_eq_nil_of_le_loc t10_le_t11_loc evIdx_t11_isCompromise_loc)

theorem trRKP2_compromised {k : Bytes}
    (h : (mkTestTracePredicates trRKP2).Compromised k) : k = stA0.rk ∨ k = dhsA := by
  have hexp := (compromised_iff_exposedKey_of_noCompromise trRKP2_noCompromise).mp h
  rcases exposedKey_append_expose hexp with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_t10 (exposedKey_encTr h0))
    · exact .inl rfl
  · exact .inr rfl

theorem trRKP2_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trRKP2).Compromised k) : saltDepth k ≤ 4 := by
  rcases trRKP2_compromised h with rfl | rfl <;> simp

theorem trRKP2_messageKey : (mkTestTracePredicates trRKP2).MessageKey mkB1 :=
  ⟨keyRKP2, stB3.sessionInfo "bob", .sender, 1, 2, 63,
    ⟨69, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc (append2_le_loc _ _ _)
        (encTr_mk_at_loc t10 "bob" 63 stB3 keyRKP2 (by rw [t10_length])))⟩⟩

theorem trRKP2_knows_mkB1 : mkB1.AttackerKnows trRKP2 := by
  have hrk : stA0.rk.AttackerKnows trRKP2 :=
    ak_net (i := 73) (at?_mono_loc (append2_le_loc _ _ _)
      (append2_snd_at_loc _ _ _ (by dsimp only [tRKP2_0]; rw [encTr_len_loc, t10_length])))
  have hsk : dhsA.AttackerKnows trRKP2 :=
    ak_net (i := 75) (append2_snd_at_loc _ _ _
      (by dsimp only [tRKP2_1, exposeRkTr, tRKP2_0]; rw [append2_len_loc, encTr_len_loc, t10_length]))
  have hpk : (dhPk dhsB1).AttackerKnows trRKP2 :=
    knows_encMsg_ratchetKey (tr := trRKP2) (st := stB2) (coins := coins2) (pq := key2)
      (m := m2) (i := 64)
      (messageSentAt_of_at?_loc
        (at?_mono_loc (append2_le_loc _ _ _)
          (at?_mono_loc (append2_le_loc _ _ _)
            (at?_mono_loc (encTr_le_loc _ _ _ _ _) t10_msg2_at_loc))))
  have hcks : (createChain stA0.rk (dhPk dhsA) dhsB1).2.AttackerKnows trRKP2 :=
    ak_chain_ck_comm hrk hpk hsk
  rw [← stB2_cks_eq] at hcks
  exact ak_seed (ak_kdfCk_fst hcks)

theorem trRKP2_knows : (mkTestTracePredicates trRKP2).AttackerKnows mkB1 :=
  ⟨keyRKP2, ⟨stB3.sessionInfo "bob", .sender, 1, 2, 63,
    ⟨69, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc (append2_le_loc _ _ _)
        (encTr_mk_at_loc t10 "bob" 63 stB3 keyRKP2 (by rw [t10_length])))⟩⟩,
    .inl trRKP2_knows_mkB1⟩

/-! ## Witness trace `trDC` -/

abbrev mDC : Bytes := rnd 72 32
abbrev coinsDC : Bytes := rnd 73 32
def keyDC : Bytes := (Spqr.spqrSend stA4.spqr coinsDC).2.1
def tDC0 : ExecTrace := encTr t11 "alice" 71 stA4 keyDC
def tDC1 : ExecTrace := exposeRkTr tDC0 "alice" stA0
def tDC2 : ExecTrace := exposeDhsTr tDC1 "alice" stA0

/-- `t11` extended with Alice encrypting message 0 from `stA4` and exposing `stA0.rk`, `dhsA`, and
`dhsB1`. -/
def trDC : ExecTrace := exposeDhsTr tDC2 "bob" stB1

abbrev mkDC : Bytes := (kdfCk stA4.cks).2

@[simp] theorem saltDepth_mkDC : saltDepth mkDC = 9 := by
  change saltDepth (kdfCk stA4.cks).2 = 9
  simp

theorem stA4_cks_eq :
    stA4.cks = (createChain (createChain stA0.rk (dhPk dhsB1) dhsA).1 (dhPk dhsB1) dhsA2).2 := rfl

theorem tDC0_runs : Runs (TripleRatchet.messageEncrypt "alice" 71 32 74) t11 78 tDC0 :=
  runs_messageEncrypt_loc t11_stA4_at (by decide) (by rw [t11_length]) rfl
    (by rw [t11_length]) (by rw [t11_length])

theorem tDC0_reach : tDC0.Reachable reachability :=
  reach_of_runs tDC0_runs
    (messageEncrypt_reachable t11_reach
      (hcur := by
        dsimp only [t11]
        exact isCurrentSnapshot_append_self_loc _ _ _ (by simp only [append_len_loc, t10_length])))

theorem trDC_reach : trDC.Reachable reachability :=
  have hstA0 : tDC0.at? 30 = some (StT "alice" stA0) :=
    at?_mono_loc (encTr_le_loc _ _ _ _ _) t11_stA0_loc
  have hstB1 : tDC2.at? 53 = some (StT "bob" stB1) :=
    at?_mono_loc (append2_le_loc _ _ _)
      (at?_mono_loc (append2_le_loc _ _ _)
        (at?_mono_loc (encTr_le_loc _ _ _ _ _)
          (at?_mono_loc t10_le_t11_loc
            (at?_mono_loc (encTr_le_loc _ _ _ _ _)
              (at?_mono_loc t8_le_t9_loc t8_stB1_at)))))
  exposeDhs_reach
    (exposeDhs_reach (exposeRk_reach tDC0_reach (stH := 30) hstA0) (stH := 30)
      (at?_mono_loc (append2_le_loc _ _ _) hstA0))
    (stH := 53) hstB1

theorem trDC_noCompromise : NoCompromise trDC :=
  noCompromise_of_evIdx (by
    dsimp only [trDC, tDC2, tDC1, tDC0, exposeDhsTr, exposeRkTr]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl, evIdx_encTr_loc]
    exact evIdx_t11_isCompromise_loc)

theorem not_exposedKey_t11 {k : Bytes} : ¬ ExposedKey t11 k :=
  not_exposedKey_of_trEvIdx trEvIdx_t11_noExposure_loc

theorem trDC_compromised {k : Bytes}
    (h : (mkTestTracePredicates trDC).Compromised k) : k = stA0.rk ∨ k = dhsA ∨ k = dhsB1 := by
  have hexp := (compromised_iff_exposedKey_of_noCompromise trDC_noCompromise).mp h
  rcases exposedKey_append_expose hexp with h2 | rfl
  · rcases exposedKey_append_expose h2 with h1 | rfl
    · rcases exposedKey_append_expose h1 with h0 | rfl
      · exact False.elim (not_exposedKey_t11 (exposedKey_encTr h0))
      · exact .inl rfl
    · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem trDC_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trDC).Compromised k) : saltDepth k ≤ 4 := by
  rcases trDC_compromised h with rfl | rfl | rfl <;> simp

theorem trDC_messageKey : (mkTestTracePredicates trDC).MessageKey mkDC :=
  ⟨keyDC, stA4.sessionInfo "alice", .sender, 0, 3, 71,
    ⟨76, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc (append2_le_loc _ _ _)
        (eventLoggedAt_mono_loc (append2_le_loc _ _ _)
          (encTr_mk_at_loc t11 "alice" 71 stA4 keyDC (by rw [t11_length]))))⟩⟩

theorem trDC_knows_mkDC : mkDC.AttackerKnows trDC := by
  have hrk0 : stA0.rk.AttackerKnows trDC :=
    ak_net (i := 80) (at?_mono_loc (append2_le_loc _ _ _)
      (at?_mono_loc (append2_le_loc _ _ _)
        (append2_snd_at_loc _ _ _ (by dsimp only [tDC0]; rw [encTr_len_loc, t11_length]))))
  have hdhsA : dhsA.AttackerKnows trDC :=
    ak_net (i := 82) (at?_mono_loc (append2_le_loc _ _ _)
      (append2_snd_at_loc _ _ _
        (by dsimp only [tDC1, exposeRkTr, tDC0]; rw [append2_len_loc, encTr_len_loc, t11_length])))
  have hdhsB1 : dhsB1.AttackerKnows trDC :=
    ak_net (i := 84) (append2_snd_at_loc _ _ _
      (by
        dsimp only [tDC2, tDC1, exposeDhsTr, exposeRkTr, tDC0]
        rw [append2_len_loc, append2_len_loc, encTr_len_loc, t11_length]))
  have hpkA2 : (dhPk dhsA2).AttackerKnows trDC :=
    knows_encMsg_ratchetKey (tr := trDC) (st := stA4) (coins := coinsDC) (pq := keyDC)
      (m := mDC) (i := 78)
      (messageSentAt_of_at?_loc
        (at?_mono_loc (append2_le_loc _ _ _)
          (at?_mono_loc (append2_le_loc _ _ _)
            (at?_mono_loc (append2_le_loc _ _ _)
              (encTr_msg_at_loc t11 "alice" 71 stA4 keyDC (by rw [t11_length])
                (by rw [t11_length]) (by rw [t11_length]))))))
  have hrk1 : (createChain stA0.rk (dhPk dhsB1) dhsA).1.AttackerKnows trDC :=
    ak_chain_rk hrk0 (ak_dhPk hdhsB1) hdhsA
  have hcks :
      (createChain (createChain stA0.rk (dhPk dhsB1) dhsA).1 (dhPk dhsB1) dhsA2).2.AttackerKnows
        trDC :=
    ak_chain_ck_comm hrk1 hpkA2 hdhsB1
  exact ak_seed hcks

theorem trDC_knows : (mkTestTracePredicates trDC).AttackerKnows mkDC :=
  ⟨keyDC, ⟨stA4.sessionInfo "alice", .sender, 0, 3, 71,
    ⟨76, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc (append2_le_loc _ _ _)
        (eventLoggedAt_mono_loc (append2_le_loc _ _ _)
          (encTr_mk_at_loc t11 "alice" 71 stA4 keyDC (by rw [t11_length]))))⟩⟩,
    .inl trDC_knows_mkDC⟩

/-! ## Witness trace `trMK` -/

def isRecvKeyAt (n : UInt32) : TREvent → Bool
  | .MessageKey _ .receiver _ _ n' _ _ => n' == n
  | _ => false

theorem not_receiverKeyUsedB_of_trEvIdx {tr : ExecTrace} {s : SessionInfo}
    {seed : Bytes} {n : UInt32} {r : Nat}
    (hidx : trEvIdx tr (isRecvKeyAt n) = []) :
    (!TripleRatchet.receiverKeyUsedB tr s seed n r) = true := by
  suffices h : TripleRatchet.receiverKeyUsedB tr s seed n r = false by simp [h]
  unfold TripleRatchet.receiverKeyUsedB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  intro i _
  cases hi : (tr.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) with
  | none => simp
  | some e =>
    rcases e with ⟨ev⟩
    cases ev with
    | MessageKey s' dir seed' pq' n' r' pa' =>
      cases dir with
      | receiver =>
        simp only [decide_eq_true_eq]
        rintro ⟨rfl, rfl, rfl, rfl⟩
        exact not_tr_logged hidx (by simp [isRecvKeyAt]) ⟨i, eventLoggedAt_of_at?_loc hi⟩
      | sender => simp
    | _ => simp

abbrev mMK : Bytes := rnd 54 32
abbrev coinsMK : Bytes := rnd 55 32
def keyMK : Bytes := (Spqr.spqrSend stA2.spqr coinsMK).2.1
def pqmMK : Bytes := (Spqr.spqrSend stA2.spqr coinsMK).2.2
def tMK1 : ExecTrace := encTr t8 "alice" 43 stA2 keyMK

def cBMK : RecvChain := { cB' with chainKey := (kdfCk (kdfCk cB'.chainKey).1).1, index := 3 }
def seedMK2 : Bytes := (kdfCk (kdfCk cB'.chainKey).1).2
def stB2_mk : TRState := { stB1 with recv := [cBMK], spqr := recvSt stB1.spqr pqmMK }

theorem recv_tMK2 : Spqr.spqrRecv stB1.spqr pqmMK 2 = some (stB2_mk.spqr, recvKey stB1.spqr pqmMK) :=
  spqrRecv_not_init _ _ _ (notInit_recv _ _) (bytesToLiteral_spqrSendMsg_loc _ _)

def tMK2 : ExecTrace :=
  let tr0 := tMK1.append (NetE (recvKey stB1.spqr pqmMK))
  let trS := tr0.append (EvT (.SkippedKeyStored (stB1.sessionInfo "bob") (dhPk dhsA) 1 seedB1 2 53))
  ((trS.append (EvT (.Received "bob" "alice" (dhPk dhsA) 2 mMK))).append
    (EvT (.MessageKey (stB1.sessionInfo "bob") .receiver seedMK2 keyMK 2 2 53))).append
    (StT "bob" stB2_mk)

theorem seedMK2_eq : (kdfCk stA2.cks).2 = seedMK2 := by
  show (kdfCk (kdfCk (kdfCk (createChain keys1.rk (dhPk spkB) dhsA).2).1).1).2 =
    (kdfCk (kdfCk (kdfCk (createChain keys1.rk (dhPk dhsA) spkB).2).1).1).2
  rw [createChain_comm keys1.rk dhsA spkB]

theorem tMK1_runs : Runs (TripleRatchet.messageEncrypt "alice" 43 32 56) t8 60 tMK1 :=
  runs_messageEncrypt_loc t8_stA2_loc (by decide) (by rw [t8_length]) rfl
    (by rw [t8_length]) (by rw [t8_length])

theorem tMK2_runs : Runs (TripleRatchet.messageDecrypt "bob" 53 60 56 2) tMK1 65 tMK2 := by
  have hst : tMK1.at? 53 = some (StT "bob" stB1) :=
    at?_mono_loc (encTr_le_loc _ _ _ _ _) t8_stB1_at
  have hmsg : tMK1.at? 60 = some (NetE (encMsg stA2 coinsMK keyMK mMK)) :=
    encTr_msg_at_loc t8 "alice" 43 stA2 keyMK (by rw [t8_length]) (by rw [t8_length])
      (by rw [t8_length])
  have hpq : (tMK1.append (NetE (recvKey stB1.spqr pqmMK))).at? 56 = some (NetE keyMK) :=
    at?_mono_loc (Trace.append_le _ _)
      (encTr_pq_at_loc t8 "alice" 43 stA2 keyMK (by rw [t8_length]) (by rw [t8_length]))
  have hset : setRecvChain stB1.recv cBMK = [cBMK] := by
    simp [setRecvChain, stB1, cBMK, cB']
  exact runs_cast_loc (Runs.messageDecrypt_noRatchet (st := stB1)
      (msg := encSig stA2 coinsMK keyMK mMK)
      (t := encMsg stA2 coinsMK keyMK mMK) (c := cB') (c' := cBMK) (pq := keyMK) (seed := seedMK2)
      (m := mMK) hst hmsg (parse_encMsg _ _ _ _) rfl
      (by simp [findRecvChain, stB1, encSig, stA2, stA1, encSt, stA0, aliceSt, cB', cB,
        ratchetState])
      rfl recv_tMK2 hpq (mac_ok seedMK2_eq rfl rfl) (dec_ok seedMK2_eq) (stOut := stB2_mk)
      (by rw [hset]; rfl))
    (by
      rw [skipTr_one_loc _ _ _ _ _ _ rfl]
      dsimp only [tMK1]
      simp only [encTr_len_loc, append_len_loc, t8_length])
    (by
      rw [skipTr_one_loc _ _ _ _ _ _ rfl]
      rfl)

/-- `t8` extended with out-of-order message 2 delivery and `exposeSkipped` leaking `seedB1`. -/
def trMK : ExecTrace := exposeSkippedTr tMK2 (stB1.sessionInfo "bob") seedB1 1 2

theorem tMK1_reach : tMK1.Reachable reachability :=
  reach_of_runs tMK1_runs
    (messageEncrypt_reachable t8_reach
      (hcur := by
        have hcur7 : TripleRatchet.isCurrentSnapshot t7 43 = true :=
          isCurrentSnapshot_encTr_self_loc t6 "alice" 36 stA1 key1 (by rw [t6_length])
        have h78pre : t7 ≤ (((((((t7.append (RndE 32)).append (NetE key0)).append
            (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
              o1.ek o1.ct keys1))).append
            (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
            (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0))).append
            (EvC (.HandshakeSession (stB0'.sessionInfo "bob") 47))).append
            (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
            (EvT (.MessageKey (stB0'.sessionInfo "bob") .receiver seedB0 key0 0 2 53)) :=
          le_append_loc (le_append_loc (le_append_loc (le_append_loc (le_append_loc
            (le_append_loc (le_append_loc (Trace.append_le _ _) _) _) _) _) _) _) _
        dsimp only [t8]
        refine isCurrentSnapshot_append_st_ne_loc (at?_mono_loc h78pre t7_stA2_loc) rfl ?_
        exact isCurrentSnapshot_append_non_st_loc _ rfl
          (isCurrentSnapshot_append_non_st_loc _ rfl
            (isCurrentSnapshot_append_non_st_loc _ rfl
              (isCurrentSnapshot_append_non_st_loc _ rfl
                (isCurrentSnapshot_append_non_st_loc _ rfl
                  (isCurrentSnapshot_append_non_st_loc _ rfl
                    (isCurrentSnapshot_append_non_st_loc _ rfl
                      (isCurrentSnapshot_append_non_st_loc _ rfl hcur7)))))))))

theorem tMK2_reach : tMK2.Reachable reachability :=
  reach_of_runs tMK2_runs
    (messageDecrypt_reachable tMK1_reach
      (hcur := by
        have hcur8 : TripleRatchet.isCurrentSnapshot t8 53 = true := by
          dsimp only [t8]
          exact isCurrentSnapshot_append_self_loc _ _ _ (by simp only [append_len_loc, t7_length])
        exact isCurrentSnapshot_encTr_ne_loc t8_stB1_at rfl hcur8))

theorem trMK_reach : trMK.Reachable reachability :=
  have hsk :
      tMK2.at? 62 =
        some (EvT (.SkippedKeyStored (stB1.sessionInfo "bob") (dhPk dhsA) 1 seedB1 2 53)) := by
    dsimp only [tMK2]
    exact at?_mono_loc
      (le_append_loc (le_append_loc (Trace.append_le _ _) _) _)
      (at?_append_at_loc _ _ (by dsimp only [tMK1]; simp only [append_len_loc, encTr_len_loc, t8_length]))
  exposeSkipped_reach tMK2_reach (skH := 62) hsk
    (not_receiverKeyUsedB_of_trEvIdx (by
      dsimp only [tMK2]
      rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
        trEvIdx_append_ev_false_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
        trEvIdx_append_non_loc _ _ _ rfl]
      dsimp only [tMK1]
      rw [trEvIdx_encTr_false_loc _ _ _ _ _ _ (fun _ => rfl) rfl]
      exact trEvIdx_t8_false_loc (isRecvKeyAt 1)
        (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
        (fun _ _ _ _ _ => rfl)))

theorem trMK_noCompromise : NoCompromise trMK :=
  noCompromise_of_evIdx (by
    dsimp only [trMK, exposeSkippedTr, tMK2, tMK1]
    rw [evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_append_non_loc _ _ _ rfl,
      evIdx_append_non_loc _ _ _ rfl, evIdx_encTr_loc]
    exact evIdx_eq_nil_of_le_loc
      (Trace.le_trans _ _ _ t8_le_t9_loc
        (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) t10_le_t11_loc))
      evIdx_t11_isCompromise_loc)

theorem not_exposedKey_tMK2 {k : Bytes} : ¬ ExposedKey tMK2 k :=
  not_exposedKey_of_trEvIdx (by
    dsimp only [tMK2, tMK1]
    rw [trEvIdx_append_non_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
      trEvIdx_append_ev_false_loc _ _ _ rfl, trEvIdx_append_ev_false_loc _ _ _ rfl,
      trEvIdx_append_non_loc _ _ _ rfl,
      trEvIdx_encTr_false_loc _ _ _ _ _ _ (fun _ => rfl) rfl]
    exact trEvIdx_eq_nil_of_le_loc
      (Trace.le_trans _ _ _ t8_le_t9_loc
        (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) t10_le_t11_loc))
      trEvIdx_t11_noExposure_loc)

theorem trMK_compromised {k : Bytes}
    (h : (mkTestTracePredicates trMK).Compromised k) : k = mkA1 := by
  have hexp := (compromised_iff_exposedKey_of_noCompromise trMK_noCompromise).mp h
  rcases exposedKey_append_expose hexp with h2 | rfl
  · exact False.elim (not_exposedKey_tMK2 h2)
  · exact seedB1_eq.symm

private theorem tMK2_le_loc : t7 ≤ tMK2 := by
  have h12 : tMK1 ≤ tMK2 := by
    dsimp only [tMK2]
    exact le_append_loc (le_append_loc (le_append_loc (le_append_loc
      (Trace.append_le _ _) _) _) _) _
  exact Trace.le_trans _ _ _ t7_le_t8_loc
    (Trace.le_trans _ _ _ (encTr_le_loc _ _ _ _ _) h12)

theorem trMK_messageKey : (mkTestTracePredicates trMK).MessageKey mkA1 :=
  ⟨key1, stA1.sessionInfo "alice", .sender, 1, 1, 36,
    ⟨42, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc tMK2_le_loc t7_mkA1_at_loc)⟩⟩

theorem trMK_knows_mkA1 : mkA1.AttackerKnows trMK := by
  show (kdfCk stA1.cks).2.AttackerKnows trMK
  rw [seedB1_eq]
  exact ak_net (i := 67)
    (append2_snd_at_loc _ _ _
      (by dsimp only [tMK2, tMK1]; simp only [append_len_loc, encTr_len_loc, t8_length]))

theorem trMK_knows : (mkTestTracePredicates trMK).AttackerKnows mkA1 :=
  ⟨key1, ⟨stA1.sessionInfo "alice", .sender, 1, 1, 36,
    ⟨42, eventLoggedAt_mono_loc (append2_le_loc _ _ _)
      (eventLoggedAt_mono_loc tMK2_le_loc t7_mkA1_at_loc)⟩⟩,
    .inl trMK_knows_mkA1⟩

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRTraces
