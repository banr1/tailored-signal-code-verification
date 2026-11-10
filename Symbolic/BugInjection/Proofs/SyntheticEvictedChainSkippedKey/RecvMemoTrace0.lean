/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
public import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
public import Symbolic.Proofs.Swarm.UA.XlateSteps
public import Symbolic.DYBridge.DY.Trace.Basic
public import Symbolic.DYBridge.DY.Trace.Manipulation
public import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.DYBridge.DY.Actions.Network
public import Symbolic.DYBridge.DY.Actions.ProtocolEvent
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup

/-!
# Clean-Step Symbolic Execution Combinators

Defines coin-length-parametric encryption (`encTrGen`, `step_messageEncrypt_next`), fresh-ratchet
`counter = 0` decryption (`decSt0`, `decTr0`, `step_messageDecrypt0_next`), and trace-append
projections for `storedSecrets`, `storedStates`, `skippedStoredEvents`, and `honestKeysOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0

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

open DY (Bytes Participant Trace Traceful ExecTrace ExecTraceTypes TraceEntryHas)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg TREvent RecvChain SessionInfo messageVersion u32Max
   kdfCk trMsgKeys computeMac createChain findRecvChain setRecvChain
   consumeMessageKey parseTrSignalMsg x25519LowOrder)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Step setupTrace storedStates storedSecrets honestKeysOf newIndices)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs RndE NetE EvT StT rnd encMsg encSt encSig parse_encMsg mac_ok dec_ok
   ratchetState recvSt recvKey notInit_send notInit_recv skipTr createChain_comm dhPk_rnd_ne)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_not_init)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux (pqSecretsList)

theorem length_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    (h : tr₀ ≤ tr) (e : E) : tr₀ ≤ tr.append e :=
  Trace.le_trans tr₀ tr (tr.append e) h (Trace.append_le tr e)

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_self {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

theorem at?_append_eq {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  subst hi; exact at?_append_self tr e

theorem at?_mono {E : Type} [ExecTraceTypes.Has E] {tr₁ tr₂ : ExecTrace}
    (hle : tr₁ ≤ tr₂) {i : Nat} {e : E} (h : tr₁.at? i = some e) :
    tr₂.at? i = some e := by
  simp only [Trace.at?] at h ⊢
  split at h
  · rename_i hi
    have hi2 : i < tr₂.length := Nat.lt_of_lt_of_le hi (Trace.length_le tr₁ tr₂ hle)
    simp only [hi2, ↓reduceDIte]
    rw [← Trace.at_le tr₁ tr₂ i hi hle]
    exact h
  · simp at h

theorem getMessageSentAt_mono {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂) {i : Nat} {m : Bytes}
    (h : tr₁.getMessageSentAt i = some m) : tr₂.getMessageSentAt i = some m := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h ⊢
  cases h1 : (tr₁.at? i : Option DY.Network.ExecEntryT) with
  | none => rw [h1] at h; cases h
  | some x =>
    rw [at?_mono hle h1]
    rw [h1] at h
    exact h

theorem range_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) (f : Option E2 → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++
      (f (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  rw [length_append, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

theorem newIndices_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr₀ tr : ExecTrace) (e : E1) (f : Nat → Option E2 → Option α)
    (hle : tr₀.length ≤ tr.length) :
    ((newIndices tr₀ (tr.append e)).filterMap fun i => f i ((tr.append e).at? i)) =
      ((newIndices tr₀ tr).filterMap fun i => f i (tr.at? i)) ++
      (f tr.length (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  unfold newIndices
  rw [length_append, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  have hilt : i < tr.length := by
    have hm := List.mem_range'.mp hi
    omega
  rw [at?_append_of_lt tr e hilt]

private theorem runs_cast {α : Type} {x : Traceful α} {tr : ExecTrace} {a₁ a₂ : α}
    {tr₁ tr₂ : ExecTrace} (h : Runs x tr a₁ tr₁) (ha : a₁ = a₂) (htr : tr₁ = tr₂) :
    Runs x tr a₂ tr₂ :=
  ha ▸ htr ▸ h

theorem x25519LowOrder_dhPk (sk : Bytes) : x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
  have hl0 : (dhPk sk).view? DY.Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
  have hl : DY.Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]
  unfold x25519LowOrder DY.X25519.normalizeX25519Key
  rw [hv, hl]

theorem bytesToLiteral_spqrSendMsg (st coins : Bytes) :
    DY.Literal.bytesToLiteral (DY.Spqr.spqrSend st coins).2.2 = none := by
  have hl0 : ((DY.Spqr.spqrSend st coins).2.2).view? DY.Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ st := st, coins := coins } : DY.Spqr.SendMsg.SubF Bytes)
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [DY.Libsignal.TripleRatchet.logSkippedKeys, Traceful.run_pure]

/-- Trace after `Step.messageEncrypt me stH cl pqH` with arbitrary coin draw length `cl`. -/
def encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (cl : Nat) (pq : Bytes) : ExecTrace :=
  let m := rnd tr.length 32
  let coins := rnd (tr.length + 1) cl
  ((((((tr.append (RndE 32)).append (RndE cl)).append
    (NetE (DY.Spqr.spqrSend st.spqr coins).2.1)).append
    (EvT (.Sent me st.peer (dhPk st.dhs) st.ns m))).append
    (EvT (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH))).append
    (StT me (encSt st coins))).append
    (NetE (encMsg st coins pq m))

theorem Runs.messageEncryptGen {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
    {st : TRState} {pq : Bytes}
    (hst : tr.at? stH = some (StT me st)) (hns : st.ns ≠ u32Max)
    (hpq : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)).at? pqH = some (NetE pq)) :
    Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl pqH) tr (tr.length + 6)
      (encTrGen tr me stH st cl pq) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.guard _ hns) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  have hpq' :
      (((tr.append (RndE 32)).append (RndE cl)).append
        (NetE (DY.Spqr.spqrSend st.spqr
          (rnd (tr.append (RndE 32)).length cl)).2.1)).at? pqH = some (NetE pq) := by
    rw [length_append]; exact hpq
  refine Runs.bind (Runs.receiveMessage hpq') ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
  refine runs_cast (Runs.sendMessage _ _) ?_ ?_
  · simp only [NetE, EvT, StT, length_append, Nat.add_assoc]
  · simp only [encTrGen, encSt, encMsg, RndE, NetE, EvT, StT, length_append]
    dsimp only [kdfCk, DY.Spqr.spqrSend]

theorem step_messageEncrypt_next {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
    {st : TRState} (hst : tr.at? stH = some (StT me st)) (hns : st.ns ≠ u32Max)
    (hpqH : pqH = tr.length + 2) :
    let coins := rnd (tr.length + 1) cl
    let pq := (DY.Spqr.spqrSend st.spqr coins).2.1
    (Step.messageEncrypt me stH cl pqH).next tr = encTrGen tr me stH st cl pq := by
  subst hpqH
  dsimp only [Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
    DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stH, cl, tr.length + 2) tr]
  refine (Runs.messageEncryptGen hst hns ?_).2
  have hlen : ((tr.append (RndE 32)).append (RndE cl)).length = tr.length + 2 := by
    simp only [length_append]
  rw [← hlen, at?_append_self]
  rfl

theorem length_encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (cl : Nat) (pq : Bytes) :
    (encTrGen tr me stH st cl pq).length = tr.length + 7 := by
  simp only [encTrGen, length_append]

theorem encTrGen_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (cl : Nat) (pq : Bytes) : tr ≤ encTrGen tr me stH st cl pq := by
  unfold encTrGen; dsimp only
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

theorem encTrGen_at?_pq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (cl : Nat) (pq : Bytes) {i : Nat} (hi : i = tr.length + 2) :
    (encTrGen tr me stH st cl pq).at? i =
      some (NetE (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1) := by
  subst hi
  unfold encTrGen; dsimp only
  repeat rw [at?_append_of_lt _ _ (by simp only [length_append]; omega)]
  rw [at?_append_eq _ _ (by simp only [length_append])]; rfl

theorem encTrGen_getMessageSentAt_pq (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) (pq : Bytes) :
    (encTrGen tr me stH st cl pq).getMessageSentAt (tr.length + 2) =
      some (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1 := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
    encTrGen_at?_pq tr me stH st cl pq rfl]

theorem encTrGen_at?_st (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (cl : Nat) (pq : Bytes) {i : Nat} (hi : i = tr.length + 5) :
    (encTrGen tr me stH st cl pq).at? i =
      some (StT me (encSt st (rnd (tr.length + 1) cl))) := by
  subst hi
  unfold encTrGen; dsimp only
  rw [at?_append_of_lt _ _ (by simp only [length_append]; omega)]
  rw [at?_append_eq _ _ (by simp only [length_append])]; rfl

theorem encTrGen_at?_msg (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (cl : Nat) (pq : Bytes) {i : Nat} (hi : i = tr.length + 6) :
    (encTrGen tr me stH st cl pq).at? i =
      some (NetE (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32))) := by
  subst hi
  unfold encTrGen; dsimp only
  rw [at?_append_eq _ _ (by simp only [length_append])]; rfl

theorem encTrGen_getMessageSentAt_msg (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) (pq : Bytes) {i : Nat} (hi : i = tr.length + 6) :
    (encTrGen tr me stH st cl pq).getMessageSentAt i =
      some (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32)) := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
    encTrGen_at?_msg tr me stH st cl pq hi]

/-- Updated `TRState` after receiving a fresh-ratchet `counter = 0` message. -/
def decSt0 (st : TRState) (peerDhs newDhs pqm : Bytes) : TRState :=
  let (st', c) := ratchetState st (dhPk peerDhs) newDhs
  let c' : RecvChain := { c with chainKey := (kdfCk c.chainKey).1, index := 1 }
  { st' with recv := setRecvChain st'.recv c', spqr := recvSt st.spqr pqm }

/-- Trace after `Step.messageDecrypt` on a fresh-ratchet `counter = 0` message. -/
def decTr0 (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (peerDhs pq pqm m : Bytes) : ExecTrace :=
  let newDhs := rnd tr.length 32
  let (st', c) := ratchetState st (dhPk peerDhs) newDhs
  let seed := (kdfCk c.chainKey).2
  let key := recvKey st.spqr pqm
  let tr1 := (((tr.append (RndE 32)).append (NetE key)).append
      (EvT (.DHRatchet me st'.peer (dhPk peerDhs) (dhPk st'.dhs)))).append
      (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2)))
  ((tr1.append (EvT (.Received me st'.peer (dhPk peerDhs) 0 m))).append
    (EvT (.MessageKey (st'.sessionInfo me) .receiver seed pq 0 c.rIdx stH))).append
    (StT me (decSt0 st peerDhs newDhs pqm))

theorem step_messageDecrypt0_next {tr : ExecTrace} {me : Participant}
    {stH msgH pqH : Nat} {idx : UInt32} {st sSt : TRState} {coins pq m : Bytes}
    (hst : tr.at? stH = some (StT me st))
    (hmsg : tr.at? msgH = some (NetE (encMsg sSt coins pq m)))
    (hpq : tr.at? pqH = some (NetE pq)) (hpq_lt : pqH < tr.length)
    (hns0 : sSt.ns = 0)
    (hnotInit : st.spqr.view? DY.Spqr.InitState.SubF = none)
    (hfind : findRecvChain st.recv (dhPk sSt.dhs) = none)
    (hcks : sSt.cks = (createChain st.rk (dhPk st.dhs) sSt.dhs).2)
    (hpIk : st.peerIk = sSt.myIk) (hmIk : st.myIk = sSt.peerIk) :
    let pqm := (DY.Spqr.spqrSend sSt.spqr coins).2.2
    (Step.messageDecrypt me stH msgH pqH idx).next tr =
      decTr0 tr me stH st sSt.dhs pq pqm m := by
  intro pqm
  dsimp only [Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
    DY.Libsignal.TripleRatchet.messageDecrypt.reachability (me, stH, msgH, pqH, idx) tr]
  let newDhs := rnd tr.length 32
  let st' := (ratchetState st (dhPk sSt.dhs) newDhs).1
  let c := (ratchetState st (dhPk sSt.dhs) newDhs).2
  let seed := (kdfCk c.chainKey).2
  let c' : RecvChain := { c with chainKey := (kdfCk c.chainKey).1, index := 1 }
  have hparse := parse_encMsg sSt coins pq m
  have hfind' : findRecvChain st.recv (encSig sSt coins pq m).ratchetKey = none := hfind
  have hlow : x25519LowOrder (encSig sSt coins pq m).ratchetKey = false :=
    x25519LowOrder_dhPk sSt.dhs
  have hrs : ratchetState st (encSig sSt coins pq m).ratchetKey newDhs = (st', c) := rfl
  have hcnt : (encSig sSt coins pq m).counter = 0 := hns0
  have hcons : consumeMessageKey c (encSig sSt coins pq m).counter = some (seed, c') := by
    rw [hcnt]; rfl
  have hspqr_eq : st'.spqr = st.spqr := rfl
  have hpqm_eq : (encSig sSt coins pq m).pqRatchet = pqm := rfl
  have hrecv : DY.Spqr.spqrRecv st'.spqr (encSig sSt coins pq m).pqRatchet idx =
      some (recvSt st.spqr pqm, recvKey st.spqr pqm) := by
    rw [hspqr_eq, hpqm_eq]
    exact spqrRecv_not_init st.spqr pqm idx hnotInit (bytesToLiteral_spqrSendMsg sSt.spqr coins)
  have hpq' : ((tr.append (RndE 32)).append (NetE (recvKey st.spqr pqm))).at? pqH =
      some (NetE pq) := by
    rw [at?_append_of_lt _ _ (by rw [length_append]; omega), at?_append_of_lt _ _ hpq_lt]
    exact hpq
  have hseed_eq : (kdfCk sSt.cks).2 = seed := by
    dsimp only [seed, c, ratchetState, DY.Libsignal.TripleRatchet.dhRatchetStep]
    rw [hcks, createChain_comm st.rk sSt.dhs st.dhs]
  have hmac := mac_ok (coins := coins) (pq := pq) (m := m) hseed_eq hpIk hmIk
  have hdec := dec_ok (coins := coins) (pq := pq) (m := m) hseed_eq
  have hrun := Runs.messageDecrypt_ratchet hst hmsg hparse rfl hfind' hlow hrs hcons hrecv
    hpq' hmac hdec (stOut := decSt0 st sSt.dhs newDhs pqm) rfl
  have hskip : skipTr
      ((((tr.append (RndE 32)).append (NetE (recvKey st.spqr pqm))).append
        (EvT (.DHRatchet me st'.peer (encSig sSt coins pq m).ratchetKey (dhPk st'.dhs)))).append
        (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2))))
      (st'.sessionInfo me) (encSig sSt coins pq m).ratchetKey c stH
      (encSig sSt coins pq m).counter =
      ((((tr.append (RndE 32)).append (NetE (recvKey st.spqr pqm))).append
        (EvT (.DHRatchet me st'.peer (dhPk sSt.dhs) (dhPk st'.dhs)))).append
        (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2)))) := by
    rw [hcnt]
    exact skipTr_zero _ _ _ _ _ 0 rfl
  have h2 := hrun.2
  rw [hskip, hcnt] at h2
  exact h2

theorem length_decTr0 (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (peerDhs pq pqm m : Bytes) :
    (decTr0 tr me stH st peerDhs pq pqm m).length = tr.length + 7 := by
  simp only [decTr0, length_append]

theorem decTr0_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (peerDhs pq pqm m : Bytes) : tr ≤ decTr0 tr me stH st peerDhs pq pqm m := by
  unfold decTr0; dsimp only
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

theorem decTr0_at?_st (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (peerDhs pq pqm m : Bytes) {i : Nat} (hi : i = tr.length + 6) :
    (decTr0 tr me stH st peerDhs pq pqm m).at? i =
      some (StT me (decSt0 st peerDhs (rnd tr.length 32) pqm)) := by
  subst hi
  unfold decTr0; dsimp only
  rw [at?_append_eq _ _ (by simp only [length_append])]; rfl

/-- Trace-level projection of all `TREvent.SkippedKeyStored` entries `(s, pk, n, seed)`. -/
def skippedStoredEvents (tr : ExecTrace) : List (SessionInfo × Bytes × UInt32 × Bytes) :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt TREvent i with
    | some (.SkippedKeyStored s pk n seed _ _) => some (s, pk, n, seed)
    | _ => none

theorem skippedStoredEvents_nil : skippedStoredEvents Trace.nil = [] := by
  rw [skippedStoredEvents, Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

theorem skippedStoredEvents_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    skippedStoredEvents (tr.append e) =
      skippedStoredEvents tr ++
      (match (tr.append e).getEventAt TREvent tr.length with
       | some (.SkippedKeyStored s pk n seed _ _) => [(s, pk, n, seed)]
       | _ => []) := by
  unfold skippedStoredEvents
  rw [length_append, List.range_succ, List.filterMap_append]
  congr 1
  · apply List.filterMap_congr
    intro i hi
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr e (List.mem_range.mp hi)]
  · cases hge : (tr.append e).getEventAt TREvent tr.length with
    | none => simp [hge]
    | some ev => cases ev <;> simp [hge]

def isNotSkippedEvent (o : Option (DY.ProtocolEvent.ExecEntryT TREvent)) : Bool :=
  match o with
  | none => true
  | some x =>
    match x.ev with
    | .SkippedKeyStored .. => false
    | _ => true

theorem skippedStoredEvents_append_non {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1)
    (h : isNotSkippedEvent
           (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
             Option (DY.ProtocolEvent.ExecEntryT TREvent)) = true) :
    skippedStoredEvents (tr.append e) = skippedStoredEvents tr := by
  rw [skippedStoredEvents_append, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self]
  cases hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT TREvent)) with
  | none => simp only [List.append_nil]
  | some x =>
    rw [hproj] at h
    unfold isNotSkippedEvent at h
    dsimp only at h ⊢
    generalize x.ev = ev at h ⊢
    cases ev <;> first | (dsimp only; exact List.append_nil _) | cases h

theorem skippedStoredEvents_append_skipped (tr : ExecTrace) (s : SessionInfo)
    (pk : Bytes) (n : UInt32) (seed : Bytes) (rIdx : Nat) (src : Nat) :
    skippedStoredEvents (tr.append (EvT (.SkippedKeyStored s pk n seed rIdx src))) =
      skippedStoredEvents tr ++ [(s, pk, n, seed)] := by
  rw [skippedStoredEvents_append, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self]
  rfl

theorem skippedStoredEvents_encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) (pq : Bytes) :
    skippedStoredEvents (encTrGen tr me stH st cl pq) = skippedStoredEvents tr := by
  unfold encTrGen; dsimp only
  repeat rw [skippedStoredEvents_append_non _ _ rfl]

theorem skippedStoredEvents_decTr0 (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (peerDhs pq pqm m : Bytes) :
    skippedStoredEvents (decTr0 tr me stH st peerDhs pq pqm m) = skippedStoredEvents tr := by
  unfold decTr0; dsimp only
  repeat rw [skippedStoredEvents_append_non _ _ rfl]

theorem storedSecrets_append_pub {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    storedSecrets (tr.append e) =
      storedSecrets tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)))).map
        fun x => DY.Comparse.serialize x.st).toList := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  simp only [Option.map_map]
  exact range_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState))
    tr e (fun o => o.map fun x => DY.Comparse.serialize x.st)

theorem storedSecrets_encTrGen (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (cl : Nat) (pq : Bytes) :
    storedSecrets (encTrGen tr me stH st cl pq) = storedSecrets tr := by
  simp only [encTrGen, storedSecrets_append_pub]
  repeat erw [List.append_nil]

theorem storedSecrets_decTr0 (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (peerDhs pq pqm m : Bytes) :
    storedSecrets (decTr0 tr me stH st peerDhs pq pqm m) = storedSecrets tr := by
  simp only [decTr0, storedSecrets_append_pub]
  repeat erw [List.append_nil]

theorem storedStates_append_pub {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (r : ProtocolSetup) (e : E1)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append e) =
      storedStates r tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState TRState)))).map (·.st)).toList := by
  exact newIndices_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState))
    (setupTrace r) tr e (fun _ o => o.map (·.st)) hle

theorem storedStates_encTrGen (r : ProtocolSetup) (tr : ExecTrace) (me : Participant)
    (stH : Nat) (st : TRState) (cl : Nat) (pq : Bytes)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (encTrGen tr me stH st cl pq) =
      storedStates r tr ++ [⟨me, encSt st (rnd (tr.length + 1) cl)⟩] := by
  unfold encTrGen; dsimp only
  repeat rw [storedStates_append_pub _ r _ (by simp -failIfUnchanged only [length_append]; omega)]
  repeat erw [List.append_nil]
  rfl

theorem storedStates_decTr0 (r : ProtocolSetup) (tr : ExecTrace) (me : Participant)
    (stH : Nat) (st : TRState) (peerDhs pq pqm m : Bytes)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (decTr0 tr me stH st peerDhs pq pqm m) =
      storedStates r tr ++ [⟨me, decSt0 st peerDhs (rnd tr.length 32) pqm⟩] := by
  unfold decTr0; dsimp only
  repeat rw [storedStates_append_pub _ r _ (by simp -failIfUnchanged only [length_append]; omega)]
  repeat erw [List.append_nil]
  rfl

theorem honestKeysOf_append (tr : ExecTrace) (s₁ s₂ : List Step) :
    honestKeysOf tr (s₁ ++ s₂) =
      honestKeysOf tr s₁ ++ honestKeysOf (s₁.foldl (fun t s => s.next t) tr) s₂ := by
  induction s₁ generalizing tr with
  | nil => simp [honestKeysOf]
  | cons s ss ih =>
    simp only [List.cons_append, List.foldl_cons, honestKeysOf, ih (s.next tr), List.append_assoc]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
