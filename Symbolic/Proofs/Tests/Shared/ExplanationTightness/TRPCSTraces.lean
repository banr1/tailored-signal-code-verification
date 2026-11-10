/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
import Init.Data.String.Defs
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
# Triple Ratchet Post-Compromise Security Tightness Traces

Constructs eight reachable witness traces (`trCK`, `trCK2`, `trMK`, `trRKPre`, `trRKPost`,
`trRKP2`, `trDC`, `trRP`) together with compromise-reduction, `saltDepth`, and attacker-knowledge
lemmas for Triple Ratchet post-compromise security specification-tightness tests.
-/

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRPCSTraces

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (ak_chain_ck ak_chain_ck_comm
  ak_chain_rk_comm ak_hmac ak_lit ak_net ak_seed exposeCks_reach exposeDhs_reach exposeRk_reach
  exposeSkipped_reach isAnyTRExposure not_tr_logged trEvIdx)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (cA0 cB cB' cB'' cB2 cB2' coins0 coins1
  coins2 coins3 dhsA dhsA2 dhsB1 dhsB2 ikA ikB key0 key1 key2 key3 keys1 m0 m1 m2 m3 o1 pqm0 pqm1
  pqm2 pqm3 pqskB recv15 seedA1 seedB0 seedB1 seedB3 seedB3_eq spkB stA0 stA1 stA2 stA3' stA4 stA5
  stB00 stB0' stB1 stB2 stB3 stB4' stB5 t1 t2 t3 t4 t5 t5_length t5_stA0_at t6 t6_length t7
  t7_length t8 t8_length t8_stB1_at t9 t9_length t10 t10_length t10_reach t11 t11_length
  t11_noCompromise t11_reach t11_stA4_at)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_not_init)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs
  Runs.messageDecrypt_ratchet Runs.messageEncrypt StP StT aliceSt aliceTr aliceTrOpt bobSt0
  createChain_comm dec_ok dhPk_rnd_ne encMsg encSig encSt encTr exposeCksTr exposeDhsTr exposeRkTr
  exposeSkippedTr mac_ok messageDecrypt_reachable messageEncrypt_reachable notInit notInit_send
  parse_encMsg ratchetState reach_of_runs recvKey recvSt rnd skipTr)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (ExposedKey IsChainRoot TREntry
  at?_append_cases at?_append_of_lt compromised_iff_exposedKey_of_noCompromise
  eq_of_rootDescends_keys1_rk eq_or_rootDescends_of_createChain_fst eventLogged_append_ev
  eventLogged_append_other exposedKey_append_ev_nonExpose exposedKey_append_expose
  exposedKey_append_other exposedKey_encTr isChainRoot_createChain_snd kdfCk_snd_inj
  not_chainKeyAt_eq_of_root not_exposedKey_of_trEvIdx saltDepth saltDepth_createChain_snd
  saltDepth_kdfCk_snd saltDepth_keys1_rk saltDepth_rnd saltDepth_stA0_rk saltDepth_stA4_cks
  saltDepth_stA4_rk saltDepth_stB1_rk)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.KdfExtract DY.Concat DY.Literal DY.SymEnc DY.Trunc
open DY.X25519 DY.Spqr DY.TrWire
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm pqxdhLabel agree
  NoCompromise)

/-! ## Key-schedule and ancestry identities -/

theorem stB1_rk_eq : stB1.rk = (createChain stA0.rk (dhPk dhsA) dhsB1).1 := by
  show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).1 =
    (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsA) dhsB1).1
  rw [createChain_comm keys1.rk dhsA spkB]

theorem stB1_cks_eq : stB1.cks = (createChain stA0.rk (dhPk dhsA) dhsB1).2 := by
  show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2 =
    (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsA) dhsB1).2
  rw [createChain_comm keys1.rk dhsA spkB]

private theorem trState_with_recv_spqr_cks (s : TRState) (recv : List RecvChain) (spqr : Bytes) :
    ({ s with recv, spqr } : TRState).cks = s.cks := by rfl

theorem stB2_cks_eq : stB2.cks = (createChain stA0.rk (dhPk dhsA) dhsB1).2 := by
  unfold stB2; rw [trState_with_recv_spqr_cks]; exact stB1_cks_eq

theorem stA4_rk_eq : stA4.rk = (createChain stB1.rk (dhPk dhsB1) dhsA2).1 := by
  show (createChain (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsB1) dhsA).1
      (dhPk dhsB1) dhsA2).1 =
    (createChain (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).1
      (dhPk dhsB1) dhsA2).1
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsB1 dhsA]

theorem stA4_cks_eq : stA4.cks = (createChain stB1.rk (dhPk dhsB1) dhsA2).2 := by
  show (createChain (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsB1) dhsA).1
      (dhPk dhsB1) dhsA2).2 =
    (createChain (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).1
      (dhPk dhsB1) dhsA2).2
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsB1 dhsA]

theorem stB5_cks_eq : stB5.cks = (createChain stA4.rk (dhPk dhsA2) dhsB2).2 := by
  show (createChain (createChain (createChain (createChain keys1.rk (dhPk dhsA) spkB).1
      (dhPk dhsA) dhsB1).1 (dhPk dhsA2) dhsB1).1 (dhPk dhsA2) dhsB2).2 =
    (createChain (createChain (createChain (createChain keys1.rk (dhPk spkB) dhsA).1
      (dhPk dhsB1) dhsA).1 (dhPk dhsB1) dhsA2).1 (dhPk dhsA2) dhsB2).2
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsB1 dhsA,
    createChain_comm _ dhsA2 dhsB1]

@[simp] theorem saltDepth_stA5_cks : saltDepth stA5.cks = 9 := by
  change saltDepth (kdfCk stA4.cks).1 = 9; simp

@[simp] theorem saltDepth_stB5_cks : saltDepth stB5.cks = 10 := by
  rw [stB5_cks_eq, saltDepth_createChain_snd, saltDepth_stA4_rk]

theorem rootDescends_stA0_rk {rk : Bytes} (h : RootDescends rk stA0.rk) :
    rk = stA0.rk ∨ rk = keys1.rk := by
  rcases eq_or_rootDescends_of_createChain_fst h with rfl | h'
  · exact .inl rfl
  · exact .inr (eq_of_rootDescends_keys1_rk h')

theorem saltDepth_of_rootDescends_stA0_rk {rk : Bytes} (h : RootDescends rk stA0.rk) :
    saltDepth rk = 4 ∨ saltDepth rk = 2 := by
  rcases rootDescends_stA0_rk h with rfl | rfl
  · exact .inl saltDepth_stA0_rk
  · exact .inr saltDepth_keys1_rk

theorem knows_encMsg_ratchetKey {tr : ExecTrace} {st : TRState} {coins pq m : Bytes}
    {i : Nat} (h : tr.at? i = some (NetE (encMsg st coins pq m))) :
    (dhPk st.dhs).AttackerKnows tr := by
  have henc : (encMsg st coins pq m).AttackerKnows tr := ak_net h
  let keys := trMsgKeys pq (kdfCk st.cks).2
  let wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc keys.cipherKey keys.iv m) (Spqr.spqrSend st.spqr coins).2.2
  let mac := computeMac keys.macKey st.myIk st.peerIk wire
  have hsp := Concat.attacker_knows_split (Concat.concat wire mac) wire.length tr henc
  rw [Concat.split_concat] at hsp
  exact (DY.TrWire.attacker_knows_trWireMsg_args _ _ _ _ _ _ _ tr hsp.1).1

private theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace}
    (h : t1 ≤ t2) (e : E) : t1 ≤ t2.append e :=
  Trace.le_trans t1 t2 (t2.append e) h (Trace.append_le t2 e)

private theorem at?_mono {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace} {i : Nat} {x : E}
    (hle : t1 ≤ t2) (h : t1.at? i = some x) : t2.at? i = some x := by
  have := Trace.at?_le (EntryT := E) t1 t2 i hle
  rwa [h] at this

private theorem at?_append_at {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

private theorem at?_append_self_st {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length :
      Option (PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  unfold Trace.at?
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

private theorem eventLoggedAt_of_at? {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact h

private theorem encTr_len (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : (encTr tr me stH st pq).length = tr.length + 7 := by
  simp only [encTr, append_len]

private theorem encTr_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (Trace.append_le tr _) _) _) _) _) _) _

private theorem encTr_pq_pre (tr : ExecTrace) (st : TRState) (pq : Bytes) {n2 : Nat}
    (hpq : (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1 = pq)
    (h2 : tr.length + 2 = n2) :
    (((tr.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1)).at? n2 =
      some (NetE pq) := by
  subst hpq; subst h2
  apply at?_append_at
  simp only [append_len]

private theorem encTr_pq_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq pq0 : Bytes) {n2 : Nat}
    (hpq0 : (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1 = pq0)
    (h2 : tr.length + 2 = n2) :
    (encTr tr me stH st pq).at? n2 = some (NetE pq0) := by
  dsimp only [encTr]
  exact at?_mono
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
    (encTr_pq_pre tr st pq0 hpq0 h2)

private theorem encTr_mk_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq mk : Bytes) {n4 : Nat} (hmk : (kdfCk st.cks).2 = mk)
    (h4 : tr.length + 4 = n4) :
    (encTr tr me stH st pq).at? n4 =
      some (EvT (.MessageKey (st.sessionInfo me) .sender mk pq st.ns st.rIdx
        stH)) := by
  subst hmk; subst h4
  dsimp only [encTr]
  apply at?_mono (le_append_of_le (Trace.append_le _ _) _)
  apply at?_append_at
  simp only [append_len]

private theorem encTr_st_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st st' : TRState)
    (pq : Bytes) {n5 : Nat} (hst' : encSt st (rnd (tr.length + 1) 32) = st')
    (h5 : tr.length + 5 = n5) :
    (encTr tr me stH st pq).at? n5 = some (StT me st') := by
  subst hst'; subst h5
  dsimp only [encTr]
  apply at?_mono (Trace.append_le _ _)
  apply at?_append_at
  simp only [append_len]

private theorem encTr_msg_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (coins pq m : Bytes) {n6 : Nat} (hm : rnd tr.length 32 = m)
    (hc : rnd (tr.length + 1) 32 = coins) (h6 : tr.length + 6 = n6) :
    (encTr tr me stH st pq).at? n6 = some (NetE (encMsg st coins pq m)) := by
  subst hm; subst hc; subst h6
  dsimp only [encTr]
  apply at?_append_at
  simp only [append_len]

private theorem expose_le {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) : tr ≤ (tr.append e1).append e2 :=
  le_append_of_le (Trace.append_le tr e1) e2

private theorem expose_len {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) :
    ((tr.append e1).append e2).length = tr.length + 2 := by
  simp only [append_len]

private theorem expose_net_at {E1 : Type} [ExecTraceTypes.Has E1] (tr : ExecTrace) (e1 : E1)
    (k : Bytes) {n1 : Nat} (h1 : tr.length + 1 = n1) :
    ((tr.append e1).append (NetE k)).at? n1 = some (NetE k) := by
  subst h1
  exact at?_append_at (tr.append e1) (NetE k) (append_len tr e1)

private theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  unfold skipTr
  rw [hz]
  unfold TripleRatchet.logSkippedKeys
  rw [Traceful.run_pure]

private theorem skipTr_one (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (h1 : n.toNat - c.index.toNat = 1) :
    skipTr tr s pk c src n =
      tr.append (EvT (.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)) := by
  unfold skipTr
  rw [h1]
  simp only [TripleRatchet.logSkippedKeys, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]

private theorem x25519LowOrder_dhPk (sk : Bytes) :
    TripleRatchet.x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl0 : (dhPk sk).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl : Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
    rw [hl0]
  unfold TripleRatchet.x25519LowOrder X25519.normalizeX25519Key
  rw [hv, hl]

private theorem bytesToLiteral_spqrSendMsg (st coins : Bytes) :
    Literal.bytesToLiteral (Spqr.spqrSend st coins).2.2 = none := by
  have hl0 : ((Spqr.spqrSend st coins).2.2).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes)
  dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

private theorem isCurrentSnapshot_append_self (tr : ExecTrace) (me : Participant) (st : TRState)
    {k : Nat} (hk : tr.length = k) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [Trace.at?_append tr (StT me st), append_len, Nat.sub_self]
  rfl

private theorem isCurrentSnapshot_append_non_st {E : Type} [ExecTraceTypes.Has E]
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
    rw [at?_mono (Trace.append_le tr e) hst]
    dsimp only at hcur ⊢
    have hsub : (tr.append e).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
      rw [append_len]; omega
    rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at hcur ⊢
      intro j hj
      have hjlt : j < tr.length := by rw [List.mem_range'_1] at hj; omega
      rw [at?_append_of_lt tr e hjlt]
      exact hcur j hj
    · rw [at?_append_self_st, hnone]

private theorem isCurrentSnapshot_append_st_ne {tr : ExecTrace} {me me' : Participant}
    {st st' : TRState} {k : Nat}
    (hst : tr.at? k = some (StT me st))
    (hne : (me' != me) = true)
    (hcur : TripleRatchet.isCurrentSnapshot tr k = true) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me' st')) k = true := by
  have hk : k < tr.length := by
    have := Trace.at?_eq_some_implies_length_le
      (EntryT := PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))
      tr k
    rwa [hst] at this
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [hst] at hcur
  rw [at?_mono (Trace.append_le tr (StT me' st')) hst]
  dsimp only at hcur ⊢
  have hsub : (tr.append (StT me' st')).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
    rw [append_len]; omega
  rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
    List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hcur ⊢
    intro j hj
    have hjlt : j < tr.length := by rw [List.mem_range'_1] at hj; omega
    rw [at?_append_of_lt tr (StT me' st') hjlt]
    exact hcur j hj
  · rw [Trace.at?_append]
    simp [hne]

private theorem isCurrentSnapshot_encTr_self (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : Bytes) {n5 : Nat} (h5 : tr.length + 5 = n5) :
    TripleRatchet.isCurrentSnapshot (encTr tr me stH st pq) n5 = true := by
  subst h5
  dsimp only [encTr]
  refine isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_self _ _ _ ?_)
  simp only [append_len]

private theorem isCurrentSnapshot_encTr_other {tr : ExecTrace} {me me' : Participant}
    {st st' : TRState} {k stH' : Nat} {pq' : Bytes}
    (hst : tr.at? k = some (StT me st))
    (hcur : TripleRatchet.isCurrentSnapshot tr k = true)
    (hne : (me' != me) = true) :
    TripleRatchet.isCurrentSnapshot (encTr tr me' stH' st' pq') k = true := by
  dsimp only [encTr]
  refine isCurrentSnapshot_append_non_st _ rfl
    (isCurrentSnapshot_append_st_ne (me := me) (st := st) ?_ hne
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl hcur))))))
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le tr _) _) _) _) _) hst

private theorem noCompromise_of_le {t1 t2 : ExecTrace} (hle : t1 ≤ t2) (hnc : NoCompromise t2) :
    NoCompromise t1 := by
  have lift {ev : PQXDHEvent} (hnot : ¬ t2.EventLogged ev) : ¬ t1.EventLogged ev := by
    rintro ⟨i, hi⟩
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    exact hnot ⟨i, eventLoggedAt_of_at? (at?_mono hle hi)⟩
  exact ⟨fun p k => lift (hnc.1 p k), fun p k => lift (hnc.2.1 p k),
    fun p k => lift (hnc.2.2.1 p k), fun p k => lift (hnc.2.2.2.1 p k),
    lift hnc.2.2.2.2.1, lift hnc.2.2.2.2.2⟩

private theorem noCompromise_append_non_pq {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (e : E) (hnc : NoCompromise tr)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by rfl) :
    NoCompromise (tr.append e) := by
  have step {ev : PQXDHEvent} (hnot : ¬ tr.EventLogged ev) : ¬ (tr.append e).EventLogged ev := by
    rintro ⟨i, hi⟩
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
    rcases at?_append_cases hi with ⟨_, hi'⟩ | ⟨_, hp⟩
    · exact hnot ⟨i, eventLoggedAt_of_at? hi'⟩
    · rw [hnone] at hp; cases hp
  exact ⟨fun p k => step (hnc.1 p k), fun p k => step (hnc.2.1 p k),
    fun p k => step (hnc.2.2.1 p k), fun p k => step (hnc.2.2.2.1 p k),
    step hnc.2.2.2.2.1, step hnc.2.2.2.2.2⟩

private theorem noCompromise_encTr {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st : TRState} {pq : Bytes} (hnc : NoCompromise tr) :
    NoCompromise (encTr tr me stH st pq) := by
  dsimp only [encTr]
  exact noCompromise_append_non_pq _ (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
    (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
      (noCompromise_append_non_pq _ hnc))))))

private theorem noTREventP_nil (p : TREvent → Bool) :
    ∀ e : TREvent, p e = true → ¬ (Trace.nil : ExecTrace).EventLogged e := by
  rintro e _ ⟨i, hi⟩
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
  simp only [Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte,
    reduceCtorEq] at hi

private theorem noTREventP_append_other {E : Type} [ExecTraceTypes.Has E] {p : TREvent → Bool}
    {tr : ExecTrace} (e : E) (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) =
      none := by rfl) :
    ∀ ev, p ev = true → ¬ (tr.append e).EventLogged ev :=
  fun ev hp hev => h ev hp (eventLogged_append_other hnone hev)

private theorem noTREventP_append_ev {p : TREvent → Bool} {tr : ExecTrace} (ev₀ : TREvent)
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) (hp₀ : p ev₀ = false := by decide) :
    ∀ ev, p ev = true → ¬ (tr.append (EvT ev₀)).EventLogged ev := by
  intro ev hp hev
  rcases eventLogged_append_ev hev with h' | rfl
  · exact h ev hp h'
  · rw [hp₀] at hp; cases hp

private theorem noTREventP_encTr {p : TREvent → Bool} {tr : ExecTrace} {me : Participant}
    {stH : Nat} {st : TRState} {pq : Bytes}
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev)
    (hS : p (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32)) = false := by rfl)
    (hM : p (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH) = false := by rfl) :
    ∀ ev, p ev = true → ¬ (encTr tr me stH st pq).EventLogged ev := by
  dsimp only [encTr]
  exact noTREventP_append_other _ (noTREventP_append_other _
    (noTREventP_append_ev _ (noTREventP_append_ev _
      (noTREventP_append_other _ (noTREventP_append_other _ (noTREventP_append_other _ h))) hS) hM))

private theorem noTREventP_bind {α β : Type} {p : TREvent → Bool} {x : Traceful α}
    {f : α → Traceful β} {tr : ExecTrace}
    (hx : (∀ ev, p ev = true → ¬ tr.EventLogged ev) →
      ∀ ev, p ev = true → ¬ (x.run tr).2.val.EventLogged ev)
    (hf : ∀ a t, (∀ ev, p ev = true → ¬ t.EventLogged ev) →
      ∀ ev, p ev = true → ¬ ((f a).run t).2.val.EventLogged ev)
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((x >>= f).run tr).2.val.EventLogged ev := by
  rw [Traceful.run_bind]
  have hx' := hx h
  rcases hrun : x.run tr with ⟨o, t, _⟩
  rw [hrun] at hx'
  cases o with
  | none => exact hx'
  | some a => exact hf a t hx'

private theorem noTREventP_appendEntry {E : Type} [ExecTraceTypes.Has E] {p : TREvent → Bool}
    (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) =
      none := by rfl)
    {tr : ExecTrace} (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((DY.appendEntry e).run tr).2.val.EventLogged ev := by
  rw [Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact noTREventP_append_other e h hnone

private theorem noTREventP_genRand {p : TREvent → Bool} (n : Nat) {tr : ExecTrace}
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((Random.genRand n).run tr).2.val.EventLogged ev := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact noTREventP_bind (noTREventP_appendEntry _)
    (fun _ _ ht => by rw [Traceful.run_pure]; exact ht) h

private theorem noTREventP_logPQ {p : TREvent → Bool} (e : PQXDHEvent) {tr : ExecTrace}
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((ProtocolEvent.logEvent e).run tr).2.val.EventLogged ev := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact noTREventP_bind (noTREventP_appendEntry _)
    (fun _ _ ht => by rw [Traceful.run_pure]; exact ht) h

private theorem noTREventP_send {p : TREvent → Bool} (m : Bytes) {tr : ExecTrace}
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((Network.sendMessage m).run tr).2.val.EventLogged ev := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact noTREventP_appendEntry _ rfl h

private theorem noTREventP_storePQ {p : TREvent → Bool} (me : Participant) (st : PQXDHState)
    {tr : ExecTrace} (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((PersistentLocalState.storeLocalState me st).run tr).2.val.EventLogged ev := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact noTREventP_appendEntry _ rfl h

private theorem noTREventP_getKey {p : TREvent → Bool} (me : Participant) (idx : Nat)
    (k : PQXDH.KeyKind) {tr : ExecTrace} (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((PQXDH.getKey me idx k).run tr).2.val.EventLogged ev := by
  unfold PQXDH.getKey
  rw [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine noTREventP_bind ?_ (fun st t ht => ?_) h
  · refine noTREventP_bind ?_ (fun st0 t0 ht0 => ?_)
    · refine noTREventP_bind ?_ (fun e t1 ht1 => by rw [Traceful.run_pure]; exact ht1)
      intro ht'; rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]; exact ht'
    · refine noTREventP_bind ?_ (fun _ t2 ht2 => by rw [Traceful.run_pure]; exact ht2) ht0
      intro ht'
      by_cases heq : st0.participant = me
      · simp only [_root_.guard, heq, ↓reduceIte, Traceful.run_pure]; exact ht'
      · simp only [_root_.guard, heq, ↓reduceIte, Traceful.run_failure]; exact ht'
  · refine noTREventP_bind ?_ (fun _ t2 ht2 => by rw [Traceful.run_pure]; exact ht2) ht
    intro ht'
    by_cases heq : st.kind = k
    · simp only [_root_.guard, heq, ↓reduceIte, Traceful.run_pure]; exact ht'
    · simp only [_root_.guard, heq, ↓reduceIte, Traceful.run_failure]; exact ht'

private theorem noTREventP_regId {p : TREvent → Bool} (me : Participant) {tr : ExecTrace}
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) :
    ∀ ev, p ev = true → ¬ ((PQXDH.registerIdentity me).run tr).2.val.EventLogged ev := by
  unfold PQXDH.registerIdentity
  refine noTREventP_bind
    (fun ht => by unfold PQXDH.guardTrace; rw [Traceful.run_mk]; exact ht)
    (fun _ _ ht => ?_) h
  refine noTREventP_bind (noTREventP_genRand _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_logPQ _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_send _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_send _) (fun _ _ ht => noTREventP_storePQ _ _ ht) ht

private theorem noTREventP_t4 (p : TREvent → Bool) :
    ∀ ev, p ev = true → ¬ t4.EventLogged ev := by
  have h1 : ∀ ev, p ev = true → ¬ t1.EventLogged ev := noTREventP_regId _ (noTREventP_nil p)
  have h2 : ∀ ev, p ev = true → ¬ t2.EventLogged ev := noTREventP_regId _ h1
  have h3 : ∀ ev, p ev = true → ¬ t3.EventLogged ev := by
    unfold t3 PQXDH.genSignedPrekey
    refine noTREventP_bind (noTREventP_getKey _ _ _) (fun _ _ ht => ?_) h2
    refine noTREventP_bind (noTREventP_genRand _) (fun _ _ ht => ?_) ht
    refine noTREventP_bind (noTREventP_genRand _) (fun _ _ ht => ?_) ht
    refine noTREventP_bind (noTREventP_logPQ _) (fun _ _ ht => ?_) ht
    refine noTREventP_bind (noTREventP_storePQ _ _) (fun _ _ ht => ?_) ht
    refine noTREventP_bind (noTREventP_send _) (fun _ _ ht => ?_) ht
    exact noTREventP_bind (noTREventP_send _) (fun _ _ ht => by rw [Traceful.run_pure]; exact ht) ht
  unfold t4 PQXDH.genPQPrekey
  refine noTREventP_bind (noTREventP_getKey _ _ _) (fun _ _ ht => ?_) h3
  refine noTREventP_bind (noTREventP_genRand _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_genRand _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_logPQ _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_storePQ _ _) (fun _ _ ht => ?_) ht
  refine noTREventP_bind (noTREventP_send _) (fun _ _ ht => ?_) ht
  exact noTREventP_bind (noTREventP_send _) (fun _ _ ht => by rw [Traceful.run_pure]; exact ht) ht

private theorem noTREventP_t10 {p : TREvent → Bool}
    (hInit : ∀ a b pk spk, p (.InitSession a b pk spk) = false)
    (hSent : ∀ me peer pk ns m, p (.Sent me peer pk ns m) = false)
    (hSender : ∀ s seed pq n r pa, p (.MessageKey s .sender seed pq n r pa) = false)
    (hDH : ∀ a b pk1 pk2, p (.DHRatchet a b pk1 pk2) = false)
    (hHDH : ∀ s d i, p (.HonestDH s d i) = false)
    (hRecv : ∀ a b pk n m, p (.Received a b pk n m) = false)
    (hR2 : ∀ s seed pq n pa, p (.MessageKey s .receiver seed pq n 2 pa) = false) :
    ∀ ev, p ev = true → ¬ t10.EventLogged ev := by
  have h5 : ∀ ev, p ev = true → ¬ t5.EventLogged ev := by
    dsimp only [t5, aliceTr, aliceTrOpt]
    exact noTREventP_append_other _ (noTREventP_append_other _
      (noTREventP_append_ev _ (noTREventP_append_other _ (noTREventP_append_other _
        (noTREventP_append_other _ (noTREventP_append_other _ (noTREventP_append_other _
          (noTREventP_append_other _ (noTREventP_t4 p))))))) (hInit _ _ _ _)))
  have h6 : ∀ ev, p ev = true → ¬ t6.EventLogged ev :=
    noTREventP_encTr h5 (hSent _ _ _ _ _) (hSender _ _ _ _ _ _)
  have h7 : ∀ ev, p ev = true → ¬ t7.EventLogged ev :=
    noTREventP_encTr h6 (hSent _ _ _ _ _) (hSender _ _ _ _ _ _)
  have h8 : ∀ ev, p ev = true → ¬ t8.EventLogged ev := by
    dsimp only [t8]
    exact noTREventP_append_other _ (noTREventP_append_ev _ (noTREventP_append_ev _
      (noTREventP_append_other _ (noTREventP_append_ev _ (noTREventP_append_ev _
        (noTREventP_append_other _ (noTREventP_append_other _
          (noTREventP_append_other _ h7))) (hDH _ _ _ _)) (hHDH _ _ _)))
        (hRecv _ _ _ _ _)) (hR2 _ _ _ _ _))
  have h9 : ∀ ev, p ev = true → ¬ t9.EventLogged ev := by
    dsimp only [t9]
    exact noTREventP_append_other _ (noTREventP_append_ev _ (noTREventP_append_ev _
      (noTREventP_append_other _ h8) (hRecv _ _ _ _ _)) (hR2 _ _ _ _ _))
  exact noTREventP_encTr h9 (hSent _ _ _ _ _) (hSender _ _ _ _ _ _)

private theorem trEvIdx_eq_nil_of_noTREventP {tr : ExecTrace} {p : TREvent → Bool}
    (h : ∀ ev, p ev = true → ¬ tr.EventLogged ev) : trEvIdx tr p = [] := by
  unfold trEvIdx
  rw [List.filter_eq_nil_iff]
  intro i _
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases hi : (tr.at? i : Option TREntry) with
  | none => simp
  | some entry =>
    simp only [Bool.not_eq_true]
    cases hp : p entry.ev with
    | false => rfl
    | true => exact False.elim (h entry.ev hp ⟨i, eventLoggedAt_of_at? hi⟩)

private theorem t5_le_t7 : t5 ≤ t7 :=
  Trace.le_trans t5 t6 t7 (encTr_le _ _ _ _ _) (encTr_le _ _ _ _ _)

private theorem t7_le_t8 : t7 ≤ t8 := by
  dsimp only [t8]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le t7 _) _) _) _) _) _) _) _) _

private theorem t8_le_t9 : t8 ≤ t9 := by
  dsimp only [t9]
  exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le t8 _) _) _) _

private theorem t9_le_t10 : t9 ≤ t10 := encTr_le _ _ _ _ _

private theorem t8_le_t10 : t8 ≤ t10 := Trace.le_trans t8 t9 t10 t8_le_t9 t9_le_t10

private theorem t5_le_t10 : t5 ≤ t10 :=
  Trace.le_trans t5 t8 t10 (Trace.le_trans t5 t7 t8 t5_le_t7 t7_le_t8) t8_le_t10

private theorem t10_le_t11 : t10 ≤ t11 := by
  dsimp only [t11]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le t10 _) _) _) _) _) _) _

private theorem t7_stA2_at : t7.at? 43 = some (StT "alice" stA2) :=
  encTr_st_at t6 "alice" 36 stA1 stA2 key1 (by rw [t6_length]; rfl) (by rw [t6_length])

private theorem t10_stA2_at : t10.at? 43 = some (StT "alice" stA2) :=
  at?_mono (Trace.le_trans t7 t8 t10 t7_le_t8 t8_le_t10) t7_stA2_at

private theorem t10_stA0_at : t10.at? 30 = some (StT "alice" stA0) :=
  at?_mono t5_le_t10 t5_stA0_at

private theorem t11_stA0_at : t11.at? 30 = some (StT "alice" stA0) :=
  at?_mono t10_le_t11 t10_stA0_at

private theorem t10_stB1_at : t10.at? 53 = some (StT "bob" stB1) :=
  at?_mono t8_le_t10 t8_stB1_at

private theorem t11_stB1_at : t11.at? 53 = some (StT "bob" stB1) :=
  at?_mono t10_le_t11 t10_stB1_at

private theorem t9_stB2_at : t9.at? 57 = some (StT "bob" stB2) := by
  dsimp only [t9]
  apply at?_append_at
  simp only [append_len, t8_length]

private theorem t10_stB2_at : t10.at? 57 = some (StT "bob" stB2) :=
  at?_mono t9_le_t10 t9_stB2_at

private theorem t10_mkB0_at :
    t10.at? 62 = some (EvT (.MessageKey (stB2.sessionInfo "bob") .sender
      (kdfCk stB2.cks).2 key2 0 2 57)) :=
  encTr_mk_at t9 "bob" 57 stB2 key2 (kdfCk stB2.cks).2 rfl (by rw [t9_length])

private theorem t10_stB3_at : t10.at? 63 = some (StT "bob" stB3) :=
  encTr_st_at t9 "bob" 57 stB2 stB3 key2 (by rw [t9_length]; rfl) (by rw [t9_length])

private theorem t10_msg2_at : t10.at? 64 = some (NetE (encMsg stB2 coins2 key2 m2)) :=
  encTr_msg_at t9 "bob" 57 stB2 coins2 key2 m2 (by rw [t9_length]) (by rw [t9_length])
    (by rw [t9_length])

private theorem t11_msg2_at : t11.at? 64 = some (NetE (encMsg stB2 coins2 key2 m2)) :=
  at?_mono t10_le_t11 t10_msg2_at

private theorem t10_noCompromise : NoCompromise t10 :=
  noCompromise_of_le t10_le_t11 t11_noCompromise

private theorem t10_cur_63 : TripleRatchet.isCurrentSnapshot t10 63 = true :=
  isCurrentSnapshot_encTr_self t9 "bob" 57 stB2 key2 (by rw [t9_length])

private theorem t11_cur_71 : TripleRatchet.isCurrentSnapshot t11 71 = true := by
  dsimp only [t11]
  apply isCurrentSnapshot_append_self
  simp only [append_len, t10_length]

private theorem t10_cur_43 : TripleRatchet.isCurrentSnapshot t10 43 = true := by
  have h7 : TripleRatchet.isCurrentSnapshot t7 43 = true :=
    isCurrentSnapshot_encTr_self t6 "alice" 36 stA1 key1 (by rw [t6_length])
  have h8 : TripleRatchet.isCurrentSnapshot t8 43 = true := by
    dsimp only [t8]
    refine isCurrentSnapshot_append_st_ne (me := "alice") (st := stA2) ?_ (by decide)
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
            (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl h7))))))))
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le t7 _) _) _) _) _) _) _) _)
      t7_stA2_at
  have s8 : t8.at? 43 = some (StT "alice" stA2) := at?_mono t7_le_t8 t7_stA2_at
  have h9 : TripleRatchet.isCurrentSnapshot t9 43 = true := by
    dsimp only [t9]
    refine isCurrentSnapshot_append_st_ne (me := "alice") (st := stA2) ?_ (by decide)
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl h8)))
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le t8 _) _) _) s8
  exact isCurrentSnapshot_encTr_other (at?_mono t8_le_t9 s8) h9 (by decide)

theorem not_exposedKey_t10 {k : Bytes} : ¬ ExposedKey t10 k :=
  not_exposedKey_of_trEvIdx (trEvIdx_eq_nil_of_noTREventP
    (noTREventP_t10 (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)))

theorem not_exposedKey_t11 {k : Bytes} : ¬ ExposedKey t11 k := by
  refine not_exposedKey_of_trEvIdx (trEvIdx_eq_nil_of_noTREventP ?_)
  dsimp only [t11]
  have h0 := noTREventP_t10 (p := isAnyTRExposure)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  exact noTREventP_append_other _ (noTREventP_append_ev _ (noTREventP_append_ev _
    (noTREventP_append_ev _ (noTREventP_append_ev _
      (noTREventP_append_other _ (noTREventP_append_other _ h0)) rfl) rfl) rfl) rfl)

/-! ## Witness trace `trCK` -/

abbrev mkB0 : Bytes := (kdfCk stB2.cks).2

@[simp] theorem saltDepth_mkB0 : saltDepth mkB0 = 7 := by
  change saltDepth (kdfCk stB2.cks).2 = 7; simp

/-- `t10` extended with `exposeKey "bob" 57 .cks`, exposing `stB2.cks`. -/
def trCK : ExecTrace := exposeCksTr t10 "bob" stB2

private theorem t10_le_trCK : t10 ≤ trCK := expose_le _ _ _

private theorem trCK_len : trCK.length = 67 := by
  dsimp only [trCK, exposeCksTr]; rw [expose_len, t10_length]

private theorem trCK_cks_at : trCK.at? 66 = some (NetE stB2.cks) :=
  expose_net_at t10 _ stB2.cks (by rw [t10_length])

theorem trCK_reach : trCK.Reachable reachability :=
  exposeCks_reach (stH := 57) t10_reach t10_stB2_at

theorem trCK_compromised {k : Bytes} (h : (mkTestTracePredicates trCK).Compromised k) :
    k = stB2.cks := by
  have hnc : NoCompromise trCK :=
    noCompromise_append_non_pq _ (noCompromise_append_non_pq _ t10_noCompromise)
  have hexp : ExposedKey trCK k := (compromised_iff_exposedKey_of_noCompromise hnc).mp h
  rcases exposedKey_append_expose hexp with h0 | rfl
  · exact False.elim (not_exposedKey_t10 h0)
  · rfl

theorem trCK_messageKey : (mkTestTracePredicates trCK).MessageKey mkB0 :=
  ⟨key2, stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_of_at? (at?_mono t10_le_trCK t10_mkB0_at)⟩⟩

theorem trCK_knows : (mkTestTracePredicates trCK).AttackerKnows mkB0 :=
  ⟨key2, ⟨stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_of_at? (at?_mono t10_le_trCK t10_mkB0_at)⟩⟩,
    .inl (ak_seed (ak_net (i := 66) trCK_cks_at))⟩

theorem trCK_honestDH_dhsB1 : (mkTestTracePredicates trCK).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t10_le_trCK t10_stB1_at, rfl⟩

theorem trCK_honestDH_dhsA : (mkTestTracePredicates trCK).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t10_le_trCK t10_stA0_at, rfl⟩

/-! ## Witness trace `trCK2` -/

abbrev coinsCK2 : Bytes := rnd 68 32
def pqCK2 : Bytes := (Spqr.spqrSend stB3.spqr coinsCK2).2.1

/-- `trCK` extended with Bob encrypting message 1 from `stB3`. -/
def trCK2 : ExecTrace := encTr trCK "bob" 63 stB3 pqCK2

abbrev mkB1 : Bytes := (kdfCk stB3.cks).2

@[simp] theorem saltDepth_mkB1 : saltDepth mkB1 = 8 := by
  change saltDepth (kdfCk stB3.cks).2 = 8; simp

private theorem t10_le_trCK2 : t10 ≤ trCK2 :=
  Trace.le_trans t10 trCK trCK2 t10_le_trCK (encTr_le _ _ _ _ _)

private theorem trCK_cur_63 : TripleRatchet.isCurrentSnapshot trCK 63 = true :=
  isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t10_cur_63)

theorem trCK2_reach : trCK2.Reachable reachability :=
  reach_of_runs
    (Runs.messageEncrypt (tr := trCK) (stH := 63) (pqH := 69) (st := stB3) (pq := pqCK2)
      (at?_mono t10_le_trCK t10_stB3_at) (by decide)
      (encTr_pq_pre trCK stB3 pqCK2 (by rw [trCK_len]; rfl) (by rw [trCK_len])))
    (messageEncrypt_reachable trCK_reach trCK_cur_63)

theorem trCK2_compromised {k : Bytes} (h : (mkTestTracePredicates trCK2).Compromised k) :
    k = stB2.cks := by
  have hnc : NoCompromise trCK2 :=
    noCompromise_encTr (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ t10_noCompromise))
  have hexp : ExposedKey trCK2 k := (compromised_iff_exposedKey_of_noCompromise hnc).mp h
  rcases exposedKey_append_expose (exposedKey_encTr hexp) with h0 | rfl
  · exact False.elim (not_exposedKey_t10 h0)
  · rfl

private theorem trCK2_mkB1_at :
    trCK2.at? 71 = some (EvT (.MessageKey (stB3.sessionInfo "bob") .sender mkB1 pqCK2
      1 2 63)) :=
  encTr_mk_at trCK "bob" 63 stB3 pqCK2 mkB1 rfl (by rw [trCK_len])

theorem trCK2_messageKey : (mkTestTracePredicates trCK2).MessageKey mkB1 :=
  ⟨pqCK2, stB3.sessionInfo "bob", .sender, 1, 2, 63,
    ⟨71, eventLoggedAt_of_at? trCK2_mkB1_at⟩⟩

theorem trCK2_knows : (mkTestTracePredicates trCK2).AttackerKnows mkB1 :=
  ⟨pqCK2, ⟨stB3.sessionInfo "bob", .sender, 1, 2, 63,
    ⟨71, eventLoggedAt_of_at? trCK2_mkB1_at⟩⟩,
    .inl (ak_seed (ak_hmac (ak_net (i := 66) (at?_mono (encTr_le _ _ _ _ _) trCK_cks_at))
      (ak_lit _)))⟩

theorem trCK2_honestDH_dhsB1 : (mkTestTracePredicates trCK2).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t10_le_trCK2 t10_stB1_at, rfl⟩

theorem trCK2_honestDH_dhsA : (mkTestTracePredicates trCK2).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t10_le_trCK2 t10_stA0_at, rfl⟩

/-! ## Witness trace `trMK` -/

abbrev mMK1 : Bytes := rnd 65 32
abbrev coinsMK1 : Bytes := rnd 66 32
def pqMK1 : Bytes := (Spqr.spqrSend stB3.spqr coinsMK1).2.1
def pqmMK1 : Bytes := (Spqr.spqrSend stB3.spqr coinsMK1).2.2

def tMK1 : ExecTrace := encTr t10 "bob" 63 stB3 pqMK1

private theorem tMK1_len : tMK1.length = 72 := by
  dsimp only [tMK1]; rw [encTr_len, t10_length]

abbrev dhsA_mk : Bytes := rnd 72 32
def stA_mk' : TRState := (ratchetState stA2 (dhPk dhsB1) dhsA_mk).1
def cA_mk : RecvChain := (ratchetState stA2 (dhPk dhsB1) dhsA_mk).2
def cA_mk' : RecvChain :=
  { cA_mk with chainKey := (kdfCk (chainKeyAt cA_mk.chainKey 1)).1, index := 2 }
def stA_mk : TRState := { stA_mk' with recv := [cA0, cA_mk'], spqr := recvSt stA2.spqr pqmMK1 }
def seedA_mk1 : Bytes := (kdfCk (chainKeyAt cA_mk.chainKey 1)).2
def seedA_mk0 : Bytes := (kdfCk cA_mk.chainKey).2

theorem seedA_mk0_eq_mkB0 : seedA_mk0 = mkB0 := by
  show (kdfCk (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsB1) dhsA).2).2 =
    (kdfCk (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2).2
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsB1 dhsA]

theorem seedA_mk1_eq_mkB1 : (kdfCk stB3.cks).2 = seedA_mk1 := by
  show (kdfCk (kdfCk (createChain (createChain keys1.rk (dhPk dhsA) spkB).1
      (dhPk dhsA) dhsB1).2).1).2 =
    (kdfCk (kdfCk (createChain (createChain keys1.rk (dhPk spkB) dhsA).1
      (dhPk dhsB1) dhsA).2).1).2
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsA dhsB1]

theorem recv_tMK2 : Spqr.spqrRecv stA_mk'.spqr pqmMK1 2 =
    some (stA_mk.spqr, recvKey stA2.spqr pqmMK1) :=
  spqrRecv_not_init _ _ _ (notInit_send stA1.spqr coins1)
    (bytesToLiteral_spqrSendMsg stB3.spqr coinsMK1)

def tMK2 : ExecTrace :=
  let tr1 := (((tMK1.append (RndE 32)).append (NetE (recvKey stA2.spqr pqmMK1))).append
    (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1) (dhPk dhsA_mk)))).append
    (EvT (.HonestDH (stA_mk'.sessionInfo "alice") dhsA_mk 1))
  let trS := skipTr tr1 (stA_mk'.sessionInfo "alice") (dhPk dhsB1) cA_mk 43 1
  ((trS.append (EvT (.Received "alice" "bob" (dhPk dhsB1) 1 mMK1))).append
    (EvT (.MessageKey (stA_mk'.sessionInfo "alice") .receiver seedA_mk1 pqMK1 1 3 43))).append
    (StT "alice" stA_mk)

private theorem tMK2_eq :
    tMK2 =
      ((((((((tMK1.append (RndE 32)).append (NetE (recvKey stA2.spqr pqmMK1))).append
        (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1) (dhPk dhsA_mk)))).append
        (EvT (.HonestDH (stA_mk'.sessionInfo "alice") dhsA_mk 1))).append
        (EvT (.SkippedKeyStored (stA_mk'.sessionInfo "alice") (dhPk dhsB1) 0 seedA_mk0 3 43))).append
        (EvT (.Received "alice" "bob" (dhPk dhsB1) 1 mMK1))).append
        (EvT (.MessageKey (stA_mk'.sessionInfo "alice") .receiver seedA_mk1 pqMK1 1 3
          43))).append
        (StT "alice" stA_mk)) := by
  dsimp only [tMK2]
  rw [skipTr_one _ _ _ _ _ _ rfl]
  rfl

private theorem tMK2_len : tMK2.length = 80 := by
  rw [tMK2_eq]; simp only [append_len, tMK1_len]

private theorem t10_le_tMK2 : t10 ≤ tMK2 := by
  rw [tMK2_eq]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (encTr_le _ _ _ _ _) _) _) _) _) _) _) _) _

theorem tMK2_runs : Runs (TripleRatchet.messageDecrypt "alice" 43 71 67 2) tMK1 79 tMK2 := by
  have hne : dhPk spkB ≠ dhPk dhsB1 := dhPk_rnd_ne (by decide)
  have ho1 : o1.spk = dhPk spkB := rfl
  have hrs : ratchetState stA2 (encSig stB3 coinsMK1 pqMK1 mMK1).ratchetKey (rnd tMK1.length 32) =
      (stA_mk', cA_mk) := by
    rw [tMK1_len]; rfl
  have hset : setRecvChain stA_mk'.recv cA_mk' = [cA0, cA_mk'] := by
    simp [setRecvChain, stA_mk', ratchetState, cA_mk', cA_mk, stA2, stA1, encSt, stA0, aliceSt,
      cA0, ho1, hne, maxReceiverChains]
  have hfind : findRecvChain stA2.recv (dhPk dhsB1) = none := by
    simp [findRecvChain, stA2, stA1, encSt, stA0, aliceSt, ho1, hne]
  have hst : tMK1.at? 43 = some (StT "alice" stA2) :=
    at?_mono (encTr_le _ _ _ _ _) t10_stA2_at
  have hmsg : tMK1.at? 71 = some (NetE (encMsg stB3 coinsMK1 pqMK1 mMK1)) :=
    encTr_msg_at t10 "bob" 63 stB3 coinsMK1 pqMK1 mMK1
      (by rw [t10_length]) (by rw [t10_length]) (by rw [t10_length])
  have hpq : ((tMK1.append (RndE 32)).append (NetE (recvKey stA2.spqr pqmMK1))).at? 67 =
      some (NetE pqMK1) :=
    at?_mono (expose_le _ _ _)
      (encTr_pq_at t10 "bob" 63 stB3 pqMK1 pqMK1 (by rw [t10_length]; rfl) (by rw [t10_length]))
  have hrun := Runs.messageDecrypt_ratchet (st := stA2) (st' := stA_mk') (c := cA_mk) (c' := cA_mk')
    (msg := encSig stB3 coinsMK1 pqMK1 mMK1) (t := encMsg stB3 coinsMK1 pqMK1 mMK1) (pq := pqMK1)
    (seed := seedA_mk1) (m := mMK1)
    hst hmsg (parse_encMsg _ _ _ _) rfl hfind (x25519LowOrder_dhPk dhsB1) hrs rfl recv_tMK2 hpq
    (mac_ok seedA_mk1_eq_mkB1 rfl rfl) (dec_ok seedA_mk1_eq_mkB1) (stOut := stA_mk)
    (by rw [hset]; rfl)
  dsimp only at hrun
  have htrS_len : (skipTr
      ((((tMK1.append (RndE 32)).append (NetE (recvKey stA2.spqr pqmMK1))).append
        (EvT (.DHRatchet "alice" stA_mk'.peer (encSig stB3 coinsMK1 pqMK1 mMK1).ratchetKey
          (dhPk stA_mk'.dhs)))).append
        (EvT (.HonestDH (stA_mk'.sessionInfo "alice") stA_mk'.dhs (stA_mk'.rIdx - 2))))
      (stA_mk'.sessionInfo "alice") (encSig stB3 coinsMK1 pqMK1 mMK1).ratchetKey cA_mk 43
      (encSig stB3 coinsMK1 pqMK1 mMK1).counter).length + 2 = 79 := by
    rw [skipTr_one _ _ _ _ _ _ rfl]
    simp only [append_len, tMK1_len]
  rw [htrS_len] at hrun
  exact hrun

private def isRecvKeyAt (n : UInt32) (r : Nat) : TREvent → Bool
  | .MessageKey _ .receiver _ _ n' r' _ => decide (n' = n ∧ r' = r)
  | _ => false

private theorem receiverKeyUsedB_false_of_trEvIdx {tr : ExecTrace} {s : SessionInfo}
    {seed : Bytes} {n : UInt32} {r : Nat} (hno : trEvIdx tr (isRecvKeyAt n r) = []) :
    (!TripleRatchet.receiverKeyUsedB tr s seed n r) = true := by
  suffices h : TripleRatchet.receiverKeyUsedB tr s seed n r = false by simp [h]
  unfold TripleRatchet.receiverKeyUsedB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  intro i _
  cases hi : (tr.at? i : Option TREntry) with
  | none => simp
  | some e =>
    rcases e with ⟨ev⟩
    cases ev with
    | MessageKey s' dir seed' pq' n' r' pa' =>
      cases dir with
      | receiver =>
        simp only [decide_eq_true_eq]
        rintro ⟨rfl, rfl, rfl, rfl⟩
        exact not_tr_logged hno (e := .MessageKey s' .receiver seed' pq' n' r' pa')
          (by simp [isRecvKeyAt]) ⟨i, eventLoggedAt_of_at? hi⟩
      | sender => simp
    | _ => simp

/-- `t10` extended with out-of-order message 1 delivery and `exposeSkipped` leaking `mkB0`. -/
def trMK : ExecTrace := exposeSkippedTr tMK2 (stA_mk'.sessionInfo "alice") seedA_mk0 0 3

private theorem noTREventP_tMK2 {p : TREvent → Bool}
    (hInit : ∀ a b pk spk, p (.InitSession a b pk spk) = false)
    (hSent : ∀ me peer pk ns m, p (.Sent me peer pk ns m) = false)
    (hSender : ∀ s seed pq n r pa, p (.MessageKey s .sender seed pq n r pa) = false)
    (hDH : ∀ a b pk1 pk2, p (.DHRatchet a b pk1 pk2) = false)
    (hHDH : ∀ s d i, p (.HonestDH s d i) = false)
    (hRecv : ∀ a b pk n m, p (.Received a b pk n m) = false)
    (hR2 : ∀ s seed pq n pa, p (.MessageKey s .receiver seed pq n 2 pa) = false)
    (hSk : ∀ s pk n seed r src, p (.SkippedKeyStored s pk n seed r src) = false)
    (hM13 : ∀ s seed pq pa, p (.MessageKey s .receiver seed pq 1 3 pa) = false) :
    ∀ ev, p ev = true → ¬ tMK2.EventLogged ev := by
  have h10 := noTREventP_t10 hInit hSent hSender hDH hHDH hRecv hR2
  have hMK1 : ∀ ev, p ev = true → ¬ tMK1.EventLogged ev :=
    noTREventP_encTr h10 (hSent _ _ _ _ _) (hSender _ _ _ _ _ _)
  rw [tMK2_eq]
  exact noTREventP_append_other _ (noTREventP_append_ev _ (noTREventP_append_ev _
    (noTREventP_append_ev _ (noTREventP_append_ev _ (noTREventP_append_ev _
      (noTREventP_append_other _ (noTREventP_append_other _ hMK1))
      (hDH _ _ _ _)) (hHDH _ _ _)) (hSk _ _ _ _ _ _)) (hRecv _ _ _ _ _)) (hM13 _ _ _ _))

theorem trMK_reach : trMK.Reachable reachability := by
  have r1 : tMK1.Reachable reachability :=
    reach_of_runs
      (Runs.messageEncrypt (tr := t10) (stH := 63) (pqH := 67) (st := stB3) (pq := pqMK1)
        t10_stB3_at (by decide)
        (encTr_pq_pre t10 stB3 pqMK1 (by rw [t10_length]; rfl) (by rw [t10_length])))
      (messageEncrypt_reachable t10_reach t10_cur_63)
  have hcur43 : TripleRatchet.isCurrentSnapshot tMK1 43 = true :=
    isCurrentSnapshot_encTr_other t10_stA2_at t10_cur_43 (by decide)
  have r2 : tMK2.Reachable reachability :=
    reach_of_runs tMK2_runs (messageDecrypt_reachable r1 hcur43)
  have hsk76 : tMK2.at? 76 =
      some (EvT (.SkippedKeyStored (stA_mk'.sessionInfo "alice") (dhPk dhsB1) 0 seedA_mk0 3 43)) := by
    rw [tMK2_eq]
    apply at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    apply at?_append_at
    simp only [append_len, tMK1_len]
  have hno03 : trEvIdx tMK2 (isRecvKeyAt 0 3) = [] :=
    trEvIdx_eq_nil_of_noTREventP (noTREventP_tMK2
      (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ => by simp [isRecvKeyAt])
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl))
  exact exposeSkipped_reach (skH := 76) r2 hsk76 (receiverKeyUsedB_false_of_trEvIdx hno03)

theorem not_exposedKey_tMK2 {k : Bytes} : ¬ ExposedKey tMK2 k :=
  not_exposedKey_of_trEvIdx (trEvIdx_eq_nil_of_noTREventP (noTREventP_tMK2
    (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)))

theorem trMK_compromised {k : Bytes} (h : (mkTestTracePredicates trMK).Compromised k) :
    k = mkB0 := by
  have hnc_mk2 : NoCompromise tMK2 := by
    rw [tMK2_eq]
    exact noCompromise_append_non_pq _ (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
      (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
        (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
          (noCompromise_encTr t10_noCompromise))))))))
  have hnc : NoCompromise trMK :=
    noCompromise_append_non_pq _ (noCompromise_append_non_pq _ hnc_mk2)
  have hexp : ExposedKey trMK k := (compromised_iff_exposedKey_of_noCompromise hnc).mp h
  rcases exposedKey_append_expose hexp with h0 | rfl
  · exact False.elim (not_exposedKey_tMK2 h0)
  · exact seedA_mk0_eq_mkB0

private theorem t10_le_trMK : t10 ≤ trMK :=
  Trace.le_trans t10 tMK2 trMK t10_le_tMK2 (expose_le _ _ _)

theorem trMK_messageKey : (mkTestTracePredicates trMK).MessageKey mkB0 :=
  ⟨key2, stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_of_at? (at?_mono t10_le_trMK t10_mkB0_at)⟩⟩

theorem trMK_knows : (mkTestTracePredicates trMK).AttackerKnows mkB0 := by
  refine ⟨key2, ⟨stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_of_at? (at?_mono t10_le_trMK t10_mkB0_at)⟩⟩, .inl ?_⟩
  rw [← seedA_mk0_eq_mkB0]
  exact ak_net (i := 81) (expose_net_at tMK2 _ seedA_mk0 (by rw [tMK2_len]))

theorem trMK_honestDH_dhsB1 : (mkTestTracePredicates trMK).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t10_le_trMK t10_stB1_at, rfl⟩

theorem trMK_honestDH_dhsA : (mkTestTracePredicates trMK).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t10_le_trMK t10_stA0_at, rfl⟩

/-! ## Witness trace `trRKPre` -/

def trRKPre1 : ExecTrace := exposeRkTr t10 "alice" stA0

/-- `t10` extended by exposing `stA0.rk` and `dhsA`. -/
def trRKPre : ExecTrace := exposeDhsTr trRKPre1 "alice" stA0

private theorem t10_le_trRKPre : t10 ≤ trRKPre :=
  Trace.le_trans t10 trRKPre1 trRKPre (expose_le _ _ _) (expose_le _ _ _)

theorem trRKPre_reach : trRKPre.Reachable reachability :=
  exposeDhs_reach (stH := 30) (exposeRk_reach (stH := 30) t10_reach t10_stA0_at)
    (at?_mono (expose_le _ _ _) t10_stA0_at)

theorem trRKPre_compromised {k : Bytes} (h : (mkTestTracePredicates trRKPre).Compromised k) :
    k = stA0.rk ∨ k = dhsA := by
  have hnc : NoCompromise trRKPre :=
    noCompromise_append_non_pq _ (noCompromise_append_non_pq _
      (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ t10_noCompromise)))
  have hexp : ExposedKey trRKPre k := (compromised_iff_exposedKey_of_noCompromise hnc).mp h
  rcases exposedKey_append_expose hexp with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_t10 h0)
    · exact .inl rfl
  · exact .inr rfl

theorem trRKPre_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trRKPre).Compromised k) : saltDepth k = 4 ∨ saltDepth k = 0 := by
  rcases trRKPre_compromised h with rfl | rfl
  · exact .inl saltDepth_stA0_rk
  · exact .inr (saltDepth_rnd 24 32)

theorem trRKPre_messageKey : (mkTestTracePredicates trRKPre).MessageKey mkB0 :=
  ⟨key2, stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_of_at? (at?_mono t10_le_trRKPre t10_mkB0_at)⟩⟩

theorem trRKPre_knows : (mkTestTracePredicates trRKPre).AttackerKnows mkB0 := by
  have hrk : stA0.rk.AttackerKnows trRKPre :=
    ak_net (i := 66)
      (at?_mono (expose_le _ _ _) (expose_net_at t10 _ stA0.rk (by rw [t10_length])))
  have hdhsA : dhsA.AttackerKnows trRKPre :=
    ak_net (i := 68)
      (expose_net_at trRKPre1 _ dhsA
        (by dsimp only [trRKPre1, exposeRkTr]; rw [expose_len, t10_length]))
  have hpkB1 : (dhPk dhsB1).AttackerKnows trRKPre :=
    knows_encMsg_ratchetKey (tr := trRKPre) (st := stB2) (coins := coins2) (pq := key2)
      (m := m2) (i := 64) (at?_mono t10_le_trRKPre t10_msg2_at)
  have hcks : stB2.cks.AttackerKnows trRKPre := by
    rw [stB2_cks_eq]
    exact ak_chain_ck_comm hrk hpkB1 hdhsA
  exact ⟨key2, ⟨stB2.sessionInfo "bob", .sender, 0, 2, 57,
    ⟨62, eventLoggedAt_of_at? (at?_mono t10_le_trRKPre t10_mkB0_at)⟩⟩,
    .inl (ak_seed hcks)⟩

theorem trRKPre_honestDH_dhsB1 : (mkTestTracePredicates trRKPre).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t10_le_trRKPre t10_stB1_at, rfl⟩

theorem trRKPre_honestDH_dhsA : (mkTestTracePredicates trRKPre).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t10_le_trRKPre t10_stA0_at, rfl⟩

/-! ## Witness trace `trRKPost` -/

def trRKPost1 : ExecTrace := exposeRkTr t11 "bob" stB1
def trRKPost2 : ExecTrace := exposeDhsTr trRKPost1 "bob" stB1

/-- `t11` extended by exposing `stB1.rk` and `dhsB1` and encrypting message 0 from `stA4`. -/
def trRKPost : ExecTrace := encTr trRKPost2 "alice" 71 stA4 key3

private theorem trRKPost2_len : trRKPost2.length = 76 := by
  dsimp only [trRKPost2, trRKPost1, exposeDhsTr, exposeRkTr]
  rw [expose_len, expose_len, t11_length]

private theorem trRKPost_len : trRKPost.length = 83 := by
  dsimp only [trRKPost]; rw [encTr_len, trRKPost2_len]

private theorem t11_le_trRKPost2 : t11 ≤ trRKPost2 :=
  Trace.le_trans t11 trRKPost1 trRKPost2 (expose_le _ _ _) (expose_le _ _ _)

private theorem t11_le_trRKPost : t11 ≤ trRKPost :=
  Trace.le_trans t11 trRKPost2 trRKPost t11_le_trRKPost2 (encTr_le _ _ _ _ _)

abbrev mkA4_0 : Bytes := (kdfCk stA4.cks).2

@[simp] theorem saltDepth_mkA4_0 : saltDepth mkA4_0 = 9 := by
  change saltDepth (kdfCk stA4.cks).2 = 9; simp

theorem trRKPost_reach : trRKPost.Reachable reachability := by
  have r1 := exposeRk_reach (stH := 53) t11_reach t11_stB1_at
  have r2 := exposeDhs_reach (stH := 53) r1 (at?_mono (expose_le _ _ _) t11_stB1_at)
  have hcur : TripleRatchet.isCurrentSnapshot trRKPost2 71 = true :=
    isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t11_cur_71)))
  exact reach_of_runs
    (Runs.messageEncrypt (tr := trRKPost2) (stH := 71) (pqH := 78) (st := stA4) (pq := key3)
      (at?_mono t11_le_trRKPost2 t11_stA4_at) (by decide)
      (encTr_pq_pre trRKPost2 stA4 key3 (by rw [trRKPost2_len]; rfl) (by rw [trRKPost2_len])))
    (messageEncrypt_reachable r2 hcur)

private theorem trRKPost_noCompromise : NoCompromise trRKPost :=
  noCompromise_encTr (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
    (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ t11_noCompromise))))

theorem trRKPost_compromised {k : Bytes} (h : (mkTestTracePredicates trRKPost).Compromised k) :
    k = stB1.rk ∨ k = dhsB1 := by
  have hexp : ExposedKey trRKPost k :=
    (compromised_iff_exposedKey_of_noCompromise trRKPost_noCompromise).mp h
  rcases exposedKey_append_expose (exposedKey_encTr hexp) with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_t11 h0)
    · exact .inl rfl
  · exact .inr rfl

theorem trRKPost_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trRKPost).Compromised k) : saltDepth k = 6 ∨ saltDepth k = 0 := by
  rcases trRKPost_compromised h with rfl | rfl
  · exact .inl saltDepth_stB1_rk
  · exact .inr (saltDepth_rnd 45 32)

private theorem trRKPost_mkA4_0_at :
    trRKPost.at? 80 =
      some (EvT (.MessageKey (stA4.sessionInfo "alice") .sender mkA4_0 key3 0 3
        71)) :=
  encTr_mk_at trRKPost2 "alice" 71 stA4 key3 mkA4_0 rfl
    (by rw [trRKPost2_len])

private theorem trRKPost_rk73_at : trRKPost.at? 73 = some (NetE stB1.rk) :=
  at?_mono (Trace.le_trans _ _ _ (expose_le _ _ _) (encTr_le _ _ _ _ _))
    (expose_net_at t11 _ stB1.rk (by rw [t11_length]))

private theorem trRKPost_dhs75_at : trRKPost.at? 75 = some (NetE dhsB1) :=
  at?_mono (encTr_le _ _ _ _ _)
    (expose_net_at trRKPost1 _ dhsB1
      (by dsimp only [trRKPost1, exposeRkTr]; rw [expose_len, t11_length]))

private theorem trRKPost_msg82_at : trRKPost.at? 82 = some (NetE (encMsg stA4 coins3 key3 m3)) :=
  encTr_msg_at trRKPost2 "alice" 71 stA4 coins3 key3 m3
    (by rw [trRKPost2_len]) (by rw [trRKPost2_len]) (by rw [trRKPost2_len])

theorem trRKPost_messageKey : (mkTestTracePredicates trRKPost).MessageKey mkA4_0 :=
  ⟨key3, stA4.sessionInfo "alice", .sender, 0, 3, 71,
    ⟨80, eventLoggedAt_of_at? trRKPost_mkA4_0_at⟩⟩

theorem trRKPost_knows_cks : stA4.cks.AttackerKnows trRKPost := by
  have hrk : stB1.rk.AttackerKnows trRKPost := ak_net (i := 73) trRKPost_rk73_at
  have hdhsB1 : dhsB1.AttackerKnows trRKPost := ak_net (i := 75) trRKPost_dhs75_at
  have hpkA2 : (dhPk dhsA2).AttackerKnows trRKPost :=
    knows_encMsg_ratchetKey (tr := trRKPost) (st := stA4) (coins := coins3) (pq := key3)
      (m := m3) (i := 82) trRKPost_msg82_at
  rw [stA4_cks_eq]
  exact ak_chain_ck_comm hrk hpkA2 hdhsB1

theorem trRKPost_knows : (mkTestTracePredicates trRKPost).AttackerKnows mkA4_0 :=
  ⟨key3, ⟨stA4.sessionInfo "alice", .sender, 0, 3, 71,
    ⟨80, eventLoggedAt_of_at? trRKPost_mkA4_0_at⟩⟩,
    .inl (ak_seed trRKPost_knows_cks)⟩

theorem trRKPost_honestDH_dhsB1 : (mkTestTracePredicates trRKPost).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t11_le_trRKPost t11_stB1_at, rfl⟩

theorem trRKPost_honestDH_dhsA : (mkTestTracePredicates trRKPost).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t11_le_trRKPost t11_stA0_at, rfl⟩

/-! ## Witness trace `trRKP2` -/

abbrev coinsRKP2 : Bytes := rnd 84 32
def pqRKP2 : Bytes := (Spqr.spqrSend stA5.spqr coinsRKP2).2.1

/-- `trRKPost` extended with Alice encrypting message 1 from `stA5`. -/
def trRKP2 : ExecTrace := encTr trRKPost "alice" 81 stA5 pqRKP2

abbrev mkA4_1 : Bytes := (kdfCk stA5.cks).2

@[simp] theorem saltDepth_mkA4_1 : saltDepth mkA4_1 = 10 := by
  change saltDepth (kdfCk stA5.cks).2 = 10; simp

private theorem t11_le_trRKP2 : t11 ≤ trRKP2 :=
  Trace.le_trans t11 trRKPost trRKP2 t11_le_trRKPost (encTr_le _ _ _ _ _)

theorem trRKP2_reach : trRKP2.Reachable reachability :=
  reach_of_runs
    (Runs.messageEncrypt (tr := trRKPost) (stH := 81) (pqH := 85) (st := stA5) (pq := pqRKP2)
      (encTr_st_at trRKPost2 "alice" 71 stA4 stA5 key3 (by rw [trRKPost2_len]; rfl)
        (by rw [trRKPost2_len]))
      (by decide)
      (encTr_pq_pre trRKPost stA5 pqRKP2 (by rw [trRKPost_len]; rfl) (by rw [trRKPost_len])))
    (messageEncrypt_reachable trRKPost_reach
      (isCurrentSnapshot_encTr_self trRKPost2 "alice" 71 stA4 key3 (by rw [trRKPost2_len])))

theorem trRKP2_compromised {k : Bytes} (h : (mkTestTracePredicates trRKP2).Compromised k) :
    k = stB1.rk ∨ k = dhsB1 := by
  have hexp : ExposedKey trRKP2 k :=
    (compromised_iff_exposedKey_of_noCompromise (noCompromise_encTr trRKPost_noCompromise)).mp h
  rcases exposedKey_append_expose (exposedKey_encTr (exposedKey_encTr hexp)) with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_t11 h0)
    · exact .inl rfl
  · exact .inr rfl

theorem trRKP2_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trRKP2).Compromised k) : saltDepth k = 6 ∨ saltDepth k = 0 := by
  rcases trRKP2_compromised h with rfl | rfl
  · exact .inl saltDepth_stB1_rk
  · exact .inr (saltDepth_rnd 45 32)

private theorem trRKP2_mkA4_1_at :
    trRKP2.at? 87 =
      some (EvT (.MessageKey (stA5.sessionInfo "alice") .sender mkA4_1 pqRKP2 1 3
        81)) :=
  encTr_mk_at trRKPost "alice" 81 stA5 pqRKP2 mkA4_1 rfl
    (by rw [trRKPost_len])

theorem trRKP2_messageKey : (mkTestTracePredicates trRKP2).MessageKey mkA4_1 :=
  ⟨pqRKP2, stA5.sessionInfo "alice", .sender, 1, 3, 81,
    ⟨87, eventLoggedAt_of_at? trRKP2_mkA4_1_at⟩⟩

theorem trRKP2_knows : (mkTestTracePredicates trRKP2).AttackerKnows mkA4_1 := by
  have hrk : stB1.rk.AttackerKnows trRKP2 :=
    ak_net (i := 73) (at?_mono (encTr_le _ _ _ _ _) trRKPost_rk73_at)
  have hdhsB1 : dhsB1.AttackerKnows trRKP2 :=
    ak_net (i := 75) (at?_mono (encTr_le _ _ _ _ _) trRKPost_dhs75_at)
  have hpkA2 : (dhPk dhsA2).AttackerKnows trRKP2 :=
    knows_encMsg_ratchetKey (tr := trRKP2) (st := stA4) (coins := coins3) (pq := key3)
      (m := m3) (i := 82) (at?_mono (encTr_le _ _ _ _ _) trRKPost_msg82_at)
  have hcks : stA4.cks.AttackerKnows trRKP2 := by
    rw [stA4_cks_eq]
    exact ak_chain_ck_comm hrk hpkA2 hdhsB1
  exact ⟨pqRKP2, ⟨stA5.sessionInfo "alice", .sender, 1, 3, 81,
    ⟨87, eventLoggedAt_of_at? trRKP2_mkA4_1_at⟩⟩,
    .inl (ak_seed (ak_hmac hcks (ak_lit _)))⟩

theorem trRKP2_honestDH_dhsB1 : (mkTestTracePredicates trRKP2).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t11_le_trRKP2 t11_stB1_at, rfl⟩

theorem trRKP2_honestDH_dhsA : (mkTestTracePredicates trRKP2).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t11_le_trRKP2 t11_stA0_at, rfl⟩

theorem isChainRoot_stA4_cks : IsChainRoot stA4.cks := by
  rw [stA4_cks_eq]; exact isChainRoot_createChain_snd _ _ _

theorem trRKP2_not_ck {ck : Bytes} (hDM : DerivesMsgKey ck mkA4_1)
    (hComp : (mkTestTracePredicates trRKP2).Compromised ck) : False := by
  rcases hDM with ⟨steps, hmk⟩
  have h : chainKeyAt stA4.cks 1 = chainKeyAt ck steps := kdfCk_snd_inj hmk
  have hd := trRKP2_compromised_saltDepth hComp
  exact not_chainKeyAt_eq_of_root isChainRoot_stA4_cks
    (by rw [saltDepth_stA4_cks]; omega) h

/-! ## Witness trace `trDC` -/

def trDC1 : ExecTrace := exposeRkTr t11 "alice" stA0
def trDC2 : ExecTrace := exposeDhsTr trDC1 "alice" stA0
def trDC3 : ExecTrace := exposeDhsTr trDC2 "alice" stA4
abbrev coinsDC : Bytes := rnd 79 32
def pqDC : Bytes := (Spqr.spqrSend stA4.spqr coinsDC).2.1

/-- `t11` extended by exposing `stA0.rk`, `dhsA`, and `dhsA2`, and encrypting message 0 from `stA4`. -/
def trDC : ExecTrace := encTr trDC3 "alice" 71 stA4 pqDC

private theorem trDC3_len : trDC3.length = 78 := by
  dsimp only [trDC3, trDC2, trDC1, exposeDhsTr, exposeRkTr]
  rw [expose_len, expose_len, expose_len, t11_length]

private theorem t11_le_trDC2 : t11 ≤ trDC2 :=
  Trace.le_trans t11 trDC1 trDC2 (expose_le _ _ _) (expose_le _ _ _)

private theorem t11_le_trDC3 : t11 ≤ trDC3 :=
  Trace.le_trans t11 trDC2 trDC3 t11_le_trDC2 (expose_le _ _ _)

private theorem t11_le_trDC : t11 ≤ trDC :=
  Trace.le_trans t11 trDC3 trDC t11_le_trDC3 (encTr_le _ _ _ _ _)

theorem trDC_reach : trDC.Reachable reachability := by
  have r1 := exposeRk_reach (stH := 30) t11_reach t11_stA0_at
  have r2 := exposeDhs_reach (stH := 30) r1 (at?_mono (expose_le _ _ _) t11_stA0_at)
  have r3 := exposeDhs_reach (stH := 71) r2 (at?_mono t11_le_trDC2 t11_stA4_at)
  have hcur : TripleRatchet.isCurrentSnapshot trDC3 71 = true :=
    isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t11_cur_71)))))
  exact reach_of_runs
    (Runs.messageEncrypt (tr := trDC3) (stH := 71) (pqH := 80) (st := stA4) (pq := pqDC)
      (at?_mono t11_le_trDC3 t11_stA4_at) (by decide)
      (encTr_pq_pre trDC3 stA4 pqDC (by rw [trDC3_len]; rfl) (by rw [trDC3_len])))
    (messageEncrypt_reachable r3 hcur)

theorem trDC_compromised {k : Bytes} (h : (mkTestTracePredicates trDC).Compromised k) :
    k = stA0.rk ∨ k = dhsA ∨ k = dhsA2 := by
  have hnc : NoCompromise trDC :=
    noCompromise_encTr (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
      (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
        (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ t11_noCompromise))))))
  have hexp : ExposedKey trDC k := (compromised_iff_exposedKey_of_noCompromise hnc).mp h
  rcases exposedKey_append_expose (exposedKey_encTr hexp) with h2 | rfl
  · rcases exposedKey_append_expose h2 with h1 | rfl
    · rcases exposedKey_append_expose h1 with h0 | rfl
      · exact False.elim (not_exposedKey_t11 h0)
      · exact .inl rfl
    · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem trDC_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trDC).Compromised k) : saltDepth k = 4 ∨ saltDepth k = 0 := by
  rcases trDC_compromised h with rfl | rfl | rfl
  · exact .inl saltDepth_stA0_rk
  · exact .inr (saltDepth_rnd 24 32)
  · exact .inr (saltDepth_rnd 65 32)

private theorem trDC_mkA4_0_at :
    trDC.at? 82 =
      some (EvT (.MessageKey (stA4.sessionInfo "alice") .sender mkA4_0 pqDC 0 3
        71)) :=
  encTr_mk_at trDC3 "alice" 71 stA4 pqDC mkA4_0 rfl (by rw [trDC3_len])

theorem trDC_messageKey : (mkTestTracePredicates trDC).MessageKey mkA4_0 :=
  ⟨pqDC, stA4.sessionInfo "alice", .sender, 0, 3, 71,
    ⟨82, eventLoggedAt_of_at? trDC_mkA4_0_at⟩⟩

theorem trDC_knows : (mkTestTracePredicates trDC).AttackerKnows mkA4_0 := by
  have hrkA0 : stA0.rk.AttackerKnows trDC :=
    ak_net (i := 73)
      (at?_mono (Trace.le_trans _ _ _ (expose_le _ _ _)
        (Trace.le_trans _ _ _ (expose_le _ _ _) (encTr_le _ _ _ _ _)))
        (expose_net_at t11 _ stA0.rk (by rw [t11_length])))
  have hdhsA : dhsA.AttackerKnows trDC :=
    ak_net (i := 75)
      (at?_mono (Trace.le_trans _ _ _ (expose_le _ _ _) (encTr_le _ _ _ _ _))
        (expose_net_at trDC1 _ dhsA
          (by dsimp only [trDC1, exposeRkTr]; rw [expose_len, t11_length])))
  have hdhsA2 : dhsA2.AttackerKnows trDC :=
    ak_net (i := 77)
      (at?_mono (encTr_le _ _ _ _ _)
        (expose_net_at trDC2 _ dhsA2
          (by dsimp only [trDC2, trDC1, exposeDhsTr, exposeRkTr]
              rw [expose_len, expose_len, t11_length])))
  have hpkB1 : (dhPk dhsB1).AttackerKnows trDC :=
    knows_encMsg_ratchetKey (tr := trDC) (st := stB2) (coins := coins2) (pq := key2)
      (m := m2) (i := 64) (at?_mono t11_le_trDC t11_msg2_at)
  have hrkB1 : stB1.rk.AttackerKnows trDC := by
    rw [stB1_rk_eq]
    exact ak_chain_rk_comm hrkA0 hpkB1 hdhsA
  have hcks : stA4.cks.AttackerKnows trDC := by
    rw [stA4_cks_eq]
    exact ak_chain_ck hrkB1 hpkB1 hdhsA2
  exact ⟨pqDC, ⟨stA4.sessionInfo "alice", .sender, 0, 3, 71,
    ⟨82, eventLoggedAt_of_at? trDC_mkA4_0_at⟩⟩,
    .inl (ak_seed hcks)⟩

theorem trDC_honestDH_dhsA2 : (mkTestTracePredicates trDC).HonestDH dhsA2 :=
  .inr ⟨"alice", stA4, 71, at?_mono t11_le_trDC t11_stA4_at, rfl⟩

theorem trDC_honestDH_dhsB1 : (mkTestTracePredicates trDC).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t11_le_trDC t11_stB1_at, rfl⟩

/-! ## Witness trace `trRP` -/

def trRP1 : ExecTrace := exposeRkTr t11 "alice" stA4
def trRP2 : ExecTrace := exposeDhsTr trRP1 "alice" stA4
def trRP3 : ExecTrace := encTr trRP2 "alice" 71 stA4 key3

private theorem trRP2_len : trRP2.length = 76 := by
  dsimp only [trRP2, trRP1, exposeDhsTr, exposeRkTr]
  rw [expose_len, expose_len, t11_length]

private theorem trRP3_len : trRP3.length = 83 := by
  dsimp only [trRP3]; rw [encTr_len, trRP2_len]

private theorem t11_le_trRP2 : t11 ≤ trRP2 :=
  Trace.le_trans t11 trRP1 trRP2 (expose_le _ _ _) (expose_le _ _ _)

private theorem t11_le_trRP3 : t11 ≤ trRP3 :=
  Trace.le_trans t11 trRP2 trRP3 t11_le_trRP2 (encTr_le _ _ _ _ _)

def trRP4 : ExecTrace :=
  let tr1 := (((trRP3.append (RndE 32)).append (NetE (recvKey stB3.spqr pqm3))).append
    (EvT (.DHRatchet "bob" "alice" (dhPk dhsA2) (dhPk dhsB2)))).append
    (EvT (.HonestDH (stB4'.sessionInfo "bob") dhsB2 2))
  ((tr1.append (EvT (.Received "bob" "alice" (dhPk dhsA2) 0 m3))).append
    (EvT (.MessageKey (stB4'.sessionInfo "bob") .receiver seedB3 key3 0 4 63))).append
    (StT "bob" stB5)

private theorem trRP4_len : trRP4.length = 90 := by
  simp only [trRP4, append_len, trRP3_len]

private theorem trRP3_le_trRP4 : trRP3 ≤ trRP4 := by
  dsimp only [trRP4]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le trRP3 _) _) _) _) _) _) _

theorem trRP4_runs : Runs (TripleRatchet.messageDecrypt "bob" 63 82 78 3) trRP3 89 trRP4 := by
  have hne : dhPk dhsA ≠ dhPk dhsA2 := dhPk_rnd_ne (by decide)
  have hrs : ratchetState stB3 (encSig stA4 coins3 key3 m3).ratchetKey (rnd trRP3.length 32) =
      (stB4', cB2) := by
    rw [trRP3_len]; rfl
  have hset : setRecvChain stB4'.recv cB2' = [cB'', cB2'] := by
    simp [setRecvChain, stB4', ratchetState, cB2', cB2, stB3, encSt, stB2, cB'', cB', cB,
      stB00, bobSt0, encSig, stA0, aliceSt, hne, maxReceiverChains]
  have hfind : findRecvChain stB3.recv (dhPk dhsA2) = none := by
    simp [findRecvChain, stB3, encSt, stB2, cB'', cB', cB, stB00, bobSt0, ratchetState, encSig,
      stA0, aliceSt, hne]
  have hst : trRP3.at? 63 = some (StT "bob" stB3) :=
    at?_mono (Trace.le_trans _ _ _ t10_le_t11 t11_le_trRP3) t10_stB3_at
  have hmsg : trRP3.at? 82 = some (NetE (encMsg stA4 coins3 key3 m3)) :=
    encTr_msg_at trRP2 "alice" 71 stA4 coins3 key3 m3
      (by rw [trRP2_len]) (by rw [trRP2_len]) (by rw [trRP2_len])
  have hpq : ((trRP3.append (RndE 32)).append (NetE (recvKey stB3.spqr pqm3))).at? 78 =
      some (NetE key3) :=
    at?_mono (expose_le _ _ _)
      (encTr_pq_at trRP2 "alice" 71 stA4 key3 key3 (by rw [trRP2_len]; rfl) (by rw [trRP2_len]))
  have hrun := Runs.messageDecrypt_ratchet (st := stB3) (st' := stB4') (c := cB2) (c' := cB2')
    (msg := encSig stA4 coins3 key3 m3) (t := encMsg stA4 coins3 key3 m3) (pq := key3)
    (seed := seedB3) (m := m3)
    hst hmsg (parse_encMsg _ _ _ _) rfl hfind (x25519LowOrder_dhPk dhsA2) hrs rfl recv15 hpq
    (mac_ok seedB3_eq rfl rfl) (dec_ok seedB3_eq) (stOut := stB5) (by rw [hset]; rfl)
  dsimp only at hrun
  rw [skipTr_zero _ _ _ _ _ _ rfl] at hrun
  have hlen : ((((trRP3.append (RndE 32)).append (NetE (recvKey stB3.spqr pqm3))).append
      (EvT (.DHRatchet "bob" stB4'.peer (encSig stA4 coins3 key3 m3).ratchetKey
        (dhPk stB4'.dhs)))).append
      (EvT (.HonestDH (stB4'.sessionInfo "bob") stB4'.dhs (stB4'.rIdx - 2)))).length + 2 = 89 := by
    simp only [append_len, trRP3_len]
  rw [hlen] at hrun
  exact hrun

abbrev mRP : Bytes := rnd 90 32
abbrev coinsRP : Bytes := rnd 91 32
def pqRP : Bytes := (Spqr.spqrSend stB5.spqr coinsRP).2.1

/-- `t11` extended by exposing `stA4.rk` and `dhsA2`, delivering Alice's message with a DH ratchet
step, and encrypting Bob's epoch-3 message 0 from `stB5`. -/
def trRP : ExecTrace := encTr trRP4 "bob" 89 stB5 pqRP

abbrev mkB5_0 : Bytes := (kdfCk stB5.cks).2

@[simp] theorem saltDepth_mkB5_0 : saltDepth mkB5_0 = 11 := by
  rw [saltDepth_kdfCk_snd, saltDepth_stB5_cks]

private theorem t11_le_trRP : t11 ≤ trRP :=
  Trace.le_trans t11 trRP4 trRP (Trace.le_trans t11 trRP3 trRP4 t11_le_trRP3 trRP3_le_trRP4)
    (encTr_le _ _ _ _ _)

theorem trRP_reach : trRP.Reachable reachability := by
  have r1 := exposeRk_reach (stH := 71) t11_reach t11_stA4_at
  have r2 := exposeDhs_reach (stH := 71) r1 (at?_mono (expose_le _ _ _) t11_stA4_at)
  have hcur71 : TripleRatchet.isCurrentSnapshot trRP2 71 = true :=
    isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t11_cur_71)))
  have r3 := reach_of_runs
    (Runs.messageEncrypt (tr := trRP2) (stH := 71) (pqH := 78) (st := stA4) (pq := key3)
      (at?_mono t11_le_trRP2 t11_stA4_at) (by decide)
      (encTr_pq_pre trRP2 stA4 key3 (by rw [trRP2_len]; rfl) (by rw [trRP2_len])))
    (messageEncrypt_reachable r2 hcur71)
  have hcur63 : TripleRatchet.isCurrentSnapshot trRP3 63 = true := by
    have h11 : TripleRatchet.isCurrentSnapshot t11 63 = true := by
      dsimp only [t11]
      refine isCurrentSnapshot_append_st_ne (me := "bob") (st := stB3) ?_ (by decide)
        (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
            (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t10_cur_63))))))
      exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
        (le_append_of_le (le_append_of_le (Trace.append_le t10 _) _) _) _) _) _) t10_stB3_at
    have s11 : t11.at? 63 = some (StT "bob" stB3) := at?_mono t10_le_t11 t10_stB3_at
    have hRP2 : TripleRatchet.isCurrentSnapshot trRP2 63 = true :=
      isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl h11)))
    exact isCurrentSnapshot_encTr_other (at?_mono t11_le_trRP2 s11) hRP2 (by decide)
  have r4 := reach_of_runs trRP4_runs (messageDecrypt_reachable r3 hcur63)
  have hst89 : trRP4.at? 89 = some (StT "bob" stB5) := by
    dsimp only [trRP4]
    apply at?_append_at
    simp only [append_len, trRP3_len]
  have hcur89 : TripleRatchet.isCurrentSnapshot trRP4 89 = true := by
    dsimp only [trRP4]
    apply isCurrentSnapshot_append_self
    simp only [append_len, trRP3_len]
  exact reach_of_runs
    (Runs.messageEncrypt (tr := trRP4) (stH := 89) (pqH := 92) (st := stB5) (pq := pqRP)
      hst89 (by decide)
      (encTr_pq_pre trRP4 stB5 pqRP (by rw [trRP4_len]; rfl) (by rw [trRP4_len])))
    (messageEncrypt_reachable r4 hcur89)

theorem trRP_compromised {k : Bytes} (h : (mkTestTracePredicates trRP).Compromised k) :
    k = stA4.rk ∨ k = dhsA2 := by
  have hnc_rp3 : NoCompromise trRP3 :=
    noCompromise_encTr (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
      (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ t11_noCompromise))))
  have hnc_rp4 : NoCompromise trRP4 := by
    dsimp only [trRP4]
    exact noCompromise_append_non_pq _ (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
      (noCompromise_append_non_pq _ (noCompromise_append_non_pq _ (noCompromise_append_non_pq _
        (noCompromise_append_non_pq _ hnc_rp3))))))
  have hexp : ExposedKey trRP k :=
    (compromised_iff_exposedKey_of_noCompromise (noCompromise_encTr hnc_rp4)).mp h
  have hexp := exposedKey_encTr hexp
  dsimp only [trRP4] at hexp
  have hexp := exposedKey_append_ev_nonExpose rfl (exposedKey_append_other hexp)
  have hexp := exposedKey_append_ev_nonExpose rfl (exposedKey_append_ev_nonExpose rfl hexp)
  have hexp := exposedKey_append_other (exposedKey_append_ev_nonExpose rfl hexp)
  have hexp := exposedKey_encTr (exposedKey_append_other hexp)
  rcases exposedKey_append_expose hexp with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_t11 h0)
    · exact .inl rfl
  · exact .inr rfl

theorem trRP_compromised_saltDepth {k : Bytes}
    (h : (mkTestTracePredicates trRP).Compromised k) : saltDepth k = 8 ∨ saltDepth k = 0 := by
  rcases trRP_compromised h with rfl | rfl
  · exact .inl saltDepth_stA4_rk
  · exact .inr (saltDepth_rnd 65 32)

private theorem trRP_mkB5_0_at :
    trRP.at? 94 =
      some (EvT (.MessageKey (stB5.sessionInfo "bob") .sender mkB5_0 pqRP 0 4
        89)) :=
  encTr_mk_at trRP4 "bob" 89 stB5 pqRP mkB5_0 rfl (by rw [trRP4_len])

theorem trRP_messageKey : (mkTestTracePredicates trRP).MessageKey mkB5_0 :=
  ⟨pqRP, stB5.sessionInfo "bob", .sender, 0, 4, 89,
    ⟨94, eventLoggedAt_of_at? trRP_mkB5_0_at⟩⟩

theorem trRP_knows : (mkTestTracePredicates trRP).AttackerKnows mkB5_0 := by
  have hrkA4 : stA4.rk.AttackerKnows trRP :=
    ak_net (i := 73)
      (at?_mono (Trace.le_trans _ _ _ (expose_le _ _ _)
        (Trace.le_trans _ _ _ (encTr_le _ _ _ _ _)
          (Trace.le_trans _ _ _ trRP3_le_trRP4 (encTr_le _ _ _ _ _))))
        (expose_net_at t11 _ stA4.rk (by rw [t11_length])))
  have hdhsA2 : dhsA2.AttackerKnows trRP :=
    ak_net (i := 75)
      (at?_mono (Trace.le_trans _ _ _ (encTr_le _ _ _ _ _)
        (Trace.le_trans _ _ _ trRP3_le_trRP4 (encTr_le _ _ _ _ _)))
        (expose_net_at trRP1 _ dhsA2
          (by dsimp only [trRP1, exposeRkTr]; rw [expose_len, t11_length])))
  have hpkB2 : (dhPk dhsB2).AttackerKnows trRP :=
    knows_encMsg_ratchetKey (tr := trRP) (st := stB5) (coins := coinsRP) (pq := pqRP)
      (m := mRP) (i := 96)
      (encTr_msg_at trRP4 "bob" 89 stB5 coinsRP pqRP mRP
        (by rw [trRP4_len]) (by rw [trRP4_len]) (by rw [trRP4_len]))
  have hcks : stB5.cks.AttackerKnows trRP := by
    rw [stB5_cks_eq]
    exact ak_chain_ck_comm hrkA4 hpkB2 hdhsA2
  exact ⟨pqRP, ⟨stB5.sessionInfo "bob", .sender, 0, 4, 89,
    ⟨94, eventLoggedAt_of_at? trRP_mkB5_0_at⟩⟩,
    .inl (ak_seed hcks)⟩

theorem trRP_honestDH_dhsB1 : (mkTestTracePredicates trRP).HonestDH dhsB1 :=
  .inr ⟨"bob", stB1, 53, at?_mono t11_le_trRP t11_stB1_at, rfl⟩

theorem trRP_honestDH_dhsA : (mkTestTracePredicates trRP).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30, at?_mono t11_le_trRP t11_stA0_at, rfl⟩

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRPCSTraces
