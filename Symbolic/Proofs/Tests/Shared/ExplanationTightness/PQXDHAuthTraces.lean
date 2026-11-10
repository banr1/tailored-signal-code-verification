/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.Adversary
import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# PQXDH Authentication Tightness Witness Traces

Constructs execution traces and event-absence lemmas for PQXDH `Authentication` tightness tests:
`r3aTrace` (Bob's signed prekey re-encoded as an X25519 torsion variant and re-signed after
`compromiseIK "bob"`) and `r3bTrace` (Bob's unsigned one-time prekey re-encoded without key
compromise), together with event-filter facts on shared compromise traces.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHAuthTraces

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (advIkA advSetup advSpkB advSpkNonce
  ak_concat ak_lit ak_net ak_sign breakDHTr compIkTr compIkTr_reach compSpkTr forgedBobStartTr
  forgedPreKeyPrefix forgedPreKeyStage2 invertTr isBrokenDH isCompIK isCompIkOf isCompSPK
  not_loggedBefore_of_none regCorruptTr sendAttacker_reach trAlias trAlias1 trAlias2 trAlias3
  trAlias4 trBrokenDHB trBrokenDHB_pre trIKA trIKA_pre trSPKB trSPKB_pre)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (evIdx ikA ikB isCompromise kh1 khOpk
  mem_evIdx not_logged opkB pqNonce pqskB spkB spkNonce t1 t1_length t2 t2_length t3 t3_length t4
  t4Opk t4Opk_length t4Opk_reach t4_length t4_reach t5 t6 t7 t8)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_init_agree)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.aliceStart
  Runs.aliceStartOpk Runs.bobStart Runs.bobStartOpk Runs.genPQPrekey Runs.genSignedPrekey
  Runs.messageEncrypt Runs.registerIdentity StP StT aliceOut aliceOutOpk aliceSt
  aliceStart_reachable aliceTr aliceTrOpk aliceTrOpt bobAgreement_honest bobAgreement_honest_opk
  bobSt0 bobStart_reachable createChain_comm dec_ok encMsg encSig encTr genOneTimePrekeyTr
  genPQPrekeyTr genSignedPrekeyTr mac_ok messageEncrypt_reachable parse_encMsg ratchetState
  reach_of_runs recvSt registerIdentityTr rnd skipTr)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem DY.Literal DY.Concat
open DY.Libsignal.Composed
open TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent SignalMsg hmac kdfCk chainKeyAt
  createChain x25519LowOrder computeMac messageVersion maxReceiverChains maxForwardJumps u32Max
  lit litByte hkdfBlock1 hkdfBlock2 hkdfBlock3 zeroSalt consumeMessageKey
  findRecvChain setRecvChain recvChainFor TRState TREvent TRSignalMsg spqrA2B spqrB2A trMsgKeys
  trHonestWireMsg parseTrSignalMsg)
open PQXDH (PQXDHState PQXDHEvent KeyKind HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles serializedIk AliceHandshakeOut BobHandshakeOut aliceAgreement bobAgreement
  pqxdhKdf pqxdhIkm pqxdhLabel discontinuity agree isCanonicalKey encodeEC encodeKEM NoCompromise
  HonestRun KeyKnown IsHandshakeBlock LoggedBefore SessionStateExposed
  errToOption)

/-! ## X25519 public-key re-encoding helpers -/

theorem ak_x25519Variant1 {tr : ExecTrace} {k : Bytes} (hk : k.AttackerKnows tr) :
    (X25519.x25519TorsionVariant k 1 0).AttackerKnows tr :=
  Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ tr ⟨k, 1, 0, rfl, hk⟩

theorem dhPk_view_variant_none (sk : Bytes) :
    (dhPk sk).view? X25519.Variant.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem x25519Key_dhPk (sk : Bytes) :
    X25519.normalizeX25519Key (dhPk sk) = dhPk sk := by
  simp [X25519.normalizeX25519Key, dhPk_view_variant_none]

theorem x25519Key_variant1_dhPk (sk : Bytes) :
    X25519.normalizeX25519Key (X25519.x25519TorsionVariant (dhPk sk) 1 0) = dhPk sk := by
  simp [X25519.x25519TorsionVariant, X25519.normalizeX25519Key, BytesView.view_pack,
    dhPk_view_variant_none]

theorem x25519Variant1_ne_dhPk (sk : Bytes) :
    X25519.x25519TorsionVariant (dhPk sk) 1 0 ≠ dhPk sk := by
  intro h
  have h1 : (X25519.x25519TorsionVariant (dhPk sk) 1 0).view? X25519.Variant.SubF =
      some { key := dhPk sk, variation := 1, torsion := 0 } := by
    simp [X25519.x25519TorsionVariant, BytesView.view_pack, x25519Key_dhPk]
  have h2 : (dhPk sk).view? X25519.Variant.SubF = none := dhPk_view_variant_none sk
  rw [h, h2] at h1
  cases h1

theorem agree_variant1_dhPk (sk other : Bytes) :
    agree (X25519.x25519TorsionVariant (dhPk sk) 1 0) other = agree (dhPk sk) other := by
  simp only [agree, x25519Key_variant1_dhPk, x25519Key_dhPk]

theorem createChain_variant1_dhPk (rk sk other : Bytes) :
    createChain rk (X25519.x25519TorsionVariant (dhPk sk) 1 0) other =
      createChain rk (dhPk sk) other := by
  simp only [createChain, DY.X25519.agree, x25519Key_variant1_dhPk, x25519Key_dhPk]

theorem x25519LowOrder_variant1_dhPk (sk : Bytes) :
    x25519LowOrder (X25519.x25519TorsionVariant (dhPk sk) 1 0) = false := by
  simp only [x25519LowOrder, x25519Key_variant1_dhPk]
  have hl0 : (dhPk sk).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

theorem x25519LowOrder_some_variant1_dhPk (sk : Bytes) :
    ((some (X25519.x25519TorsionVariant (dhPk sk) 1 0)).all (!x25519LowOrder ·)) = true := by
  simp only [Option.all, x25519LowOrder_variant1_dhPk]
  rfl

private theorem x25519LowOrder_dhPk_local (sk : Bytes) :
    x25519LowOrder (dhPk sk) = false := by
  simp only [x25519LowOrder, x25519Key_dhPk]
  have hl0 : (dhPk sk).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

private theorem isCanonicalKey_dhPk_local (sk : Bytes) :
    isCanonicalKey (dhPk sk) = true := by
  have hl : PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk_local sk
  unfold isCanonicalKey
  rw [dhPk_view_variant_none, hl]; rfl

private theorem bytesToLiteral_spqrSendMsg_local (st coins : Bytes) :
    Literal.bytesToLiteral (Spqr.spqrSend st coins).2.2 = none := by
  have hl0 : ((Spqr.spqrSend st coins).2.2).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes)
  dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

private theorem isCurrentSnapshot_append_self_local (tr : ExecTrace) (me : Participant)
    (st : TRState) {k : Nat} (hk : tr.length = k) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [Trace.at?_append tr (StT me st), Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.sub_self]; rfl

private theorem skipTr_zero_local (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  unfold TripleRatchet.logSkippedKeys
  erw [Traceful.run_pure]

private theorem runs_cast_local {α : Type} {x : Traceful α} {tr ta tb : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 ta) (ha : a1 = a2) (ht : ta = tb) : Runs x tr a2 tb := by
  subst ha; subst ht; exact h

private theorem hat_snoc {E : Type} [ExecTraceTypes.Has E]
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

private theorem at?_append_self_proj_local {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc, ↓reduceIte]

private theorem at?_append_of_lt_local {E1 E2 : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  have hne : i ≠ tr.length := Nat.ne_of_lt hi
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc, hne, hi, ↓reduceIte]

private theorem eventLoggedAt_of_at?_local {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact h

private theorem evIdx_nil_local (p : PQXDHEvent → Bool) : evIdx Trace.nil p = [] := by
  simp only [evIdx, Symbolic.DYBridge.DY.Trace.length_eq_1, List.range_zero, List.filter_nil]

private theorem evIdx_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    evIdx (tr.append x) p = evIdx tr p := by
  unfold evIdx
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj_local, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt_local tr x (List.mem_range.mp hi)]

private theorem evIdx_append_ev (tr : ExecTrace) (ev : PQXDHEvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvP ev)) p = cond (p ev) (evIdx tr p ++ [tr.length]) (evIdx tr p) := by
  unfold evIdx
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
        decide),
      List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt_local tr (EvP ev) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]),
      List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt_local tr (EvP ev) (List.mem_range.mp hi)])

private theorem evIdx_encTr (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) (p : PQXDHEvent → Bool) :
    evIdx (encTr tr me stH st pq) p = evIdx tr p := by
  dsimp only [encTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl]

private theorem evIdx_aliceTrOpt_false (tr : ExecTrace) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) (p : PQXDHEvent → Bool)
    (hp : ∀ ikA' ikB' spk' pq' opk' ek' ct' ks',
      p (.AliceDone a b ikA' ikB' spk' pq' opk' ek' ct' ks') = false) :
    evIdx (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk) p = evIdx tr p := by
  dsimp only [aliceTrOpt]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hp, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]

private theorem evIdx_aliceTrOpt_true (tr : ExecTrace) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) (p : PQXDHEvent → Bool)
    (hp : ∀ ikA' ikB' spk' pq' opk' ek' ct' ks',
      p (.AliceDone a b ikA' ikB' spk' pq' opk' ek' ct' ks') = true) :
    evIdx (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk) p = evIdx tr p ++ [tr.length + 5] := by
  dsimp only [aliceTrOpt]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hp, Bool.cond_true, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem evIdx_forgedPreKeyPrefix (tr : ExecTrace) (ikA ikB spkB pqskB : Bytes)
    (p : PQXDHEvent → Bool) :
    evIdx (forgedPreKeyPrefix tr ikA ikB spkB pqskB) p = evIdx tr p := by
  dsimp only [forgedPreKeyPrefix, forgedPreKeyStage2]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]

private theorem evIdx_forgedBobStartTr_false (trPre : ExecTrace) (b a : Participant)
    (ikA ikB spkB pqskB : Bytes) (p : PQXDHEvent → Bool)
    (hp : ∀ ikB' ikA' spk' pq' opk' ek' ct' ks',
      p (.BobDone b a ikB' ikA' spk' pq' opk' ek' ct' ks') = false) :
    evIdx (forgedBobStartTr trPre b a ikA ikB spkB pqskB) p = evIdx trPre p := by
  dsimp only [forgedBobStartTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hp, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]

private theorem evIdx_genOneTimePrekeyTr_false (tr : ExecTrace) (b : Participant)
    (p : PQXDHEvent → Bool) (hp : ∀ k, p (.OneTimePrekeyPublished b k) = false) :
    evIdx (genOneTimePrekeyTr tr b) p = evIdx tr p := by
  dsimp only [genOneTimePrekeyTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_ev, hp,
    Bool.cond_false, evIdx_append_non _ _ _ rfl]

private theorem someEventB_of_evIdx_nil {tr : ExecTrace} {p : PQXDHEvent → Bool}
    (h : evIdx tr p = []) : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  intro i hi
  cases hat : (tr.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => dsimp only; exact Bool.false_ne_true
  | some ev =>
    dsimp only
    cases hp : p ev.ev
    · exact Bool.false_ne_true
    · intro _
      have hmem : i ∈ evIdx tr p := mem_evIdx (eventLoggedAt_of_at?_local hat) hp
      rw [h] at hmem
      exact List.not_mem_nil hmem

private theorem t1_eq_local : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by
    simp only [Bool.not_eq_true']
    exact someEventB_of_evIdx_nil (evIdx_nil_local _))).2

private theorem t2_eq_local : t2 = registerIdentityTr t1 "bob" :=
  (Runs.registerIdentity (by
    simp only [Bool.not_eq_true']
    refine someEventB_of_evIdx_nil ?_
    rw [t1_eq_local]; dsimp only [registerIdentityTr]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_ev]
    dsimp only
    rw [show ("alice" == "bob") = false by decide,
      Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_nil_local])).2

private theorem t3_eq_local : t3 = genSignedPrekeyTr t2 "bob" ikB :=
  (Runs.genSignedPrekey (by
    rw [t2_eq_local]
    simp only [registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t1_length, ↓reduceIte]
    rfl)).2

private theorem t4_eq_local : t4 = genPQPrekeyTr t3 "bob" ikB :=
  (Runs.genPQPrekey (by
    rw [t3_eq_local, t2_eq_local]
    simp only [genSignedPrekeyTr, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      hat_snoc, Symbolic.DYBridge.DY.Trace.length_eq_2, t1_length, ↓reduceIte]
    rfl)).2

private theorem t4_facts_local :
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (Signature.vk ikA) true)) ∧
    t4.at? 4 = some (StP "alice" { kind := .identity, sk := ikA }) ∧
    t4.at? 6 = some (EvP (.IdentityRegistered "bob" (dhPk ikB) (Signature.vk ikB) true)) ∧
    t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) ∧
    t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) ∧
    t4.at? 14 = some (NetE (dhPk spkB)) ∧
    t4.at? 15 = some (NetE (Signature.sign ikB spkNonce (encodeEC (dhPk spkB)))) ∧
    t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) ∧
    t4.at? 20 = some (NetE (kemPk pqskB)) ∧
    t4.at? 21 = some (NetE (Signature.sign ikB pqNonce (encodeKEM (kemPk pqskB)))) := by
  rw [t4_eq_local, t3_eq_local, t2_eq_local, t1_eq_local]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [genPQPrekeyTr, genSignedPrekeyTr, registerIdentityTr,
      Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc, Symbolic.DYBridge.DY.Trace.length_eq_2,
      Symbolic.DYBridge.DY.Trace.length_eq_1, ↓reduceIte]; rfl)

private theorem evIdx_t4_false_local (p : PQXDHEvent → Bool)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx t4 p = [] := by
  rw [t4_eq_local]; dsimp only [genPQPrekeyTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h3, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  rw [t3_eq_local]; dsimp only [genSignedPrekeyTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h2, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  rw [t2_eq_local]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h1, Bool.cond_false, evIdx_append_non _ _ _ rfl]
  rw [t1_eq_local]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h1, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_nil_local]

/-! ## Signed-prekey re-encoding trace `r3aTrace` -/

abbrev spkVar : Bytes := X25519.x25519TorsionVariant (dhPk spkB) 1 0

abbrev spkVarSig : Bytes := Signature.sign ikB advSpkNonce (encodeEC spkVar)

def r3aTr1 : ExecTrace := compIkTr t4 "bob" ikB
def r3aTr2 : ExecTrace := (r3aTr1.append (NetE spkVar)).append (NetE spkVarSig)
def r3aBh : BundleHandles := { spk := 24, spkSig := 25, pqpk := 20, pqpkSig := 21, opk := none }
def r3aTr3 : ExecTrace := aliceTr r3aTr2 "alice" "bob" ikA (dhPk ikB) spkVar (kemPk pqskB)

abbrev r3a_out : AliceHandshakeOut := aliceOut r3aTr2 ikA (dhPk ikB) spkVar (kemPk pqskB)
abbrev r3a_keys : HandshakeKeys := r3a_out.keys
abbrev r3a_dhsA : Bytes := rnd 28 32
def r3a_stA0 : TRState := aliceSt "bob" r3a_out r3a_dhsA

abbrev r3a_m0 : Bytes := rnd 35 32
abbrev r3a_coins0 : Bytes := rnd 36 32
def r3a_key0 : Bytes := (Spqr.spqrSend r3a_stA0.spqr r3a_coins0).2.1
def r3a_pqm0 : Bytes := (Spqr.spqrSend r3a_stA0.spqr r3a_coins0).2.2
def r3aTr4 : ExecTrace := encTr r3aTr3 "alice" 34 r3a_stA0 r3a_key0

def r3a_mh : PreKeyMsgHandles := { ek := 29, ct := 30, msg := 41 }
abbrev r3a_dhsB1 : Bytes := rnd 42 32
def r3a_stB00 : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) r3a_keys
    (encSig r3a_stA0 r3a_coins0 r3a_key0 r3a_m0)
def r3a_stB0' : TRState := (ratchetState r3a_stB00 (dhPk r3a_dhsA) r3a_dhsB1).1
def r3a_cB : RecvChain := (ratchetState r3a_stB00 (dhPk r3a_dhsA) r3a_dhsB1).2
def r3a_cB' : RecvChain := { r3a_cB with chainKey := (kdfCk r3a_cB.chainKey).1, index := 1 }
def r3a_seedB0 : Bytes := (kdfCk r3a_cB.chainKey).2
def r3a_stB1 : TRState :=
  { r3a_stB0' with
    recv := [r3a_cB'], spqr := recvSt (Spqr.spqrInit r3a_keys.pqr spqrB2A) r3a_pqm0 }

def r3aTrace : ExecTrace :=
  let tr1 := (r3aTr4.append (RndE 32)).append (NetE r3a_key0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none r3a_out.ek r3a_out.ct r3a_keys))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk r3a_dhsA) (dhPk r3a_dhsB1)))).append
      (EvT (.HonestDH (r3a_stB0'.sessionInfo "bob") r3a_dhsB1 0))).append
      (EvC (.HandshakeSession (r3a_stB0'.sessionInfo "bob") 44))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk r3a_dhsA) 0 r3a_m0))).append
    (EvT (.MessageKey (r3a_stB0'.sessionInfo "bob") .receiver r3a_seedB0
      r3a_key0 0 2 50))).append
    (StT "bob" r3a_stB1)

theorem r3a_aliceAgreement_eq :
    aliceAgreement ikA (rnd 26 32) (dhPk ikB) spkVar (kemPk pqskB) none (rnd 27 32) =
      aliceAgreement ikA (rnd 26 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none (rnd 27 32) := by
  simp only [aliceAgreement, spkVar, agree_variant1_dhPk]

private theorem le_append_local {E : Type} [ExecTraceTypes.Has E] {ta tb : ExecTrace}
    (h : ta ≤ tb) (e : E) : ta ≤ tb.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le tb e)

private theorem at?_mono_local {E : Type} [ExecTraceTypes.Has E] {ta tb : ExecTrace} {i : Nat}
    {x : E} (hle : ta ≤ tb) (h : ta.at? i = some x) : tb.at? i = some x := by
  have := Trace.at?_le (EntryT := E) ta tb i hle
  rwa [h] at this

private theorem aliceTrOpt_le_local (tr : ExecTrace) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    tr ≤ aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk := by
  dsimp only [aliceTrOpt]
  exact le_append_local (le_append_local (le_append_local (le_append_local (le_append_local
    (le_append_local (le_append_local (le_append_local (Trace.append_le _ _) _) _) _) _) _) _) _) _

private theorem encTr_le_local (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_local (le_append_local (le_append_local (le_append_local (le_append_local
    (le_append_local (Trace.append_le _ _) _) _) _) _) _) _

theorem r3a_bobAgreement :
    bobAgreement ikB spkB pqskB none (dhPk ikA) r3a_out.ek r3a_out.ct = some r3a_keys := by
  have hlen2 : r3aTr2.length = 26 := by
    simp only [r3aTr2, r3aTr1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have hek : r3a_out.ek = dhPk (rnd 26 32) := by
    dsimp only [r3a_out, aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [hlen2]; rfl
  have hct : r3a_out.ct =
      (aliceAgreement ikA (rnd 26 32) (dhPk ikB) spkVar (kemPk pqskB) none (rnd 27 32)).1 := by
    dsimp only [r3a_out, aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [hlen2]; rfl
  have hkeys : r3a_keys =
      (aliceAgreement ikA (rnd 26 32) (dhPk ikB) spkVar (kemPk pqskB) none (rnd 27 32)).2 := by
    dsimp only [r3a_keys, r3a_out, aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [hlen2]; rfl
  rw [hek, hct, hkeys, r3a_aliceAgreement_eq]
  exact bobAgreement_honest ikA (rnd 26 32) ikB spkB pqskB (rnd 27 32)

theorem r3a_seedB0_eq : (kdfCk r3a_stA0.cks).2 = r3a_seedB0 := by
  show (kdfCk (createChain r3a_keys.rk spkVar r3a_dhsA).2).2 =
    (kdfCk (createChain r3a_keys.rk (dhPk r3a_dhsA) spkB).2).2
  rw [createChain_variant1_dhPk, createChain_comm r3a_keys.rk r3a_dhsA spkB]

theorem r3aTrace_reach : r3aTrace.Reachable reachability := by
  obtain ⟨ha1, ha4, hb6, hb9, hs13, hs14, _, hp19, hp20, hp21⟩ := t4_facts_local
  have hlen1 : r3aTr1.length = 24 := by
    simp only [r3aTr1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have hlen2 : r3aTr2.length = 26 := by
    simp only [r3aTr2, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1]
  have hlen3 : r3aTr3.length = 35 := by
    simp only [r3aTr3, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2]
  have hlen4 : r3aTr4.length = 42 := by
    simp only [r3aTr4, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3]
  have h4_1 : t4 ≤ r3aTr1 := by
    dsimp only [r3aTr1, compIkTr]; exact le_append_local (Trace.append_le _ _) _
  have h1_2 : r3aTr1 ≤ r3aTr2 := by
    dsimp only [r3aTr2]; exact le_append_local (Trace.append_le _ _) _
  have h4_2 : t4 ≤ r3aTr2 := Trace.le_trans _ _ _ h4_1 h1_2
  have h2_3 : r3aTr2 ≤ r3aTr3 := aliceTrOpt_le_local _ _ _ _ _ _ _ _
  have h3_4 : r3aTr3 ≤ r3aTr4 := encTr_le_local _ _ _ _ _
  have h4_4 : t4 ≤ r3aTr4 := Trace.le_trans _ _ _ h4_2 (Trace.le_trans _ _ _ h2_3 h3_4)
  have r1 : r3aTr1.Reachable reachability := compIkTr_reach (idx := 9) t4_reach hb9
  have r1a : (r3aTr1.append (NetE spkVar)).Reachable reachability :=
    sendAttacker_reach r1 (ak_x25519Variant1 (ak_net (i := 14) (at?_mono_local h4_1 hs14)))
  have r2 : r3aTr2.Reachable reachability :=
    sendAttacker_reach r1a
      (ak_sign
        (ak_net (i := 23) (at?_mono_local (Trace.append_le _ _) (by
          simp only [r3aTr1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
            Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length, ↓reduceIte]; rfl)))
        (ak_lit _)
        (ak_concat (ak_lit _) (ak_net (i := 24) (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc, hlen1, ↓reduceIte]; rfl))))
  have h24 : r3aTr2.at? 24 = some (NetE spkVar) := by
    simp only [r3aTr2, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1, ↓reduceIte]; rfl
  have h25 : r3aTr2.at? 25 = some (NetE spkVarSig) := by
    simp only [r3aTr2, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1, ↓reduceIte]; rfl
  have r3 : r3aTr3.Reachable reachability :=
    reach_of_runs
      (Runs.aliceStart (idH := 4) (regB := 6) (h := r3aBh) (honest := true)
        (at?_mono_local h4_2 ha4) (at?_mono_local h4_2 hb6) h24 h25
        (at?_mono_local h4_2 hp20) (at?_mono_local h4_2 hp21)
        (Signature.verify_sign _ _ _) (Signature.verify_sign _ _ _)
        rfl (x25519LowOrder_variant1_dhPk spkB))
      (aliceStart_reachable r2)
  have h34 : r3aTr3.at? 34 = some (StT "alice" r3a_stA0) := by
    simp only [r3aTr3, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl
  have h37_enc : (((r3aTr3.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend r3a_stA0.spqr (rnd (r3aTr3.length + 1) 32)).2.1)).at? 37 =
      some (NetE r3a_key0) := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3, ↓reduceIte]; rfl
  have r4 : r3aTr4.Reachable reachability :=
    reach_of_runs
      (Runs.messageEncrypt (tr := r3aTr3) (stH := 34) (pqH := 37) (st := r3a_stA0)
        (pq := r3a_key0) h34 (by decide) h37_enc)
      (messageEncrypt_reachable r3 (by
        dsimp only [r3aTr3, aliceTr, aliceTrOpt]
        exact isCurrentSnapshot_append_self_local _ _ _ (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2])))
  have hset : setRecvChain r3a_stB0'.recv r3a_cB' = [r3a_cB'] := by
    simp [setRecvChain, r3a_stB0', ratchetState, r3a_cB', r3a_cB, r3a_stB00,
      bobSt0, maxReceiverChains]
  have hrs :
      ratchetState
        (bobSt0 "alice" ikB spkB (dhPk ikA) r3a_keys
          (encSig r3a_stA0 r3a_coins0 r3a_key0 r3a_m0))
        (encSig r3a_stA0 r3a_coins0 r3a_key0 r3a_m0).ratchetKey
        (rnd r3aTr4.length 32) = (r3a_stB0', r3a_cB) := by
    rw [hlen4]; rfl
  have hrecv : Spqr.spqrRecv r3a_stB0'.spqr r3a_pqm0 1 =
      some (recvSt (Spqr.spqrInit r3a_keys.pqr spqrB2A) r3a_pqm0, r3a_key0) :=
    spqrRecv_init_agree r3a_keys.pqr r3a_coins0 r3a_pqm0 .b2a
      (bytesToLiteral_spqrSendMsg_local _ _)
  have h29 : r3aTr4.at? 29 = some (NetE r3a_out.ek) :=
    at?_mono_local h3_4 (by
      simp only [r3aTr3, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl)
  have h30 : r3aTr4.at? 30 = some (NetE r3a_out.ct) :=
    at?_mono_local h3_4 (by
      simp only [r3aTr3, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl)
  have h41 : r3aTr4.at? 41 = some (NetE (encMsg r3a_stA0 r3a_coins0 r3a_key0 r3a_m0)) := by
    simp only [r3aTr4, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3, ↓reduceIte]; rfl
  have h37_bob : ((r3aTr4.append (RndE 32)).append (NetE r3a_key0)).at? 37 =
      some (NetE r3a_key0) :=
    at?_mono_local (le_append_local (Trace.append_le _ _) _) (by
      simp only [r3aTr4, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3, ↓reduceIte]; rfl)
  have hcan : isCanonicalKey r3a_out.ek = true := by
    dsimp only [r3a_out, aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    exact isCanonicalKey_dhPk_local _
  have hruns : Runs (Composed.bobStart "bob" "alice" kh1 1 r3a_mh 37 1) r3aTr4 50 r3aTrace :=
    runs_cast_local
      (Runs.bobStart (kh := kh1) (mh := r3a_mh) (keys := r3a_keys)
        (msg := encSig r3a_stA0 r3a_coins0 r3a_key0 r3a_m0)
        (t := encMsg r3a_stA0 r3a_coins0 r3a_key0 r3a_m0)
        (st' := r3a_stB0') (c := r3a_cB) (c' := r3a_cB') (seed := r3a_seedB0)
        (pq := r3a_key0) (m := r3a_m0)
        (at?_mono_local h4_4 hb9) (at?_mono_local h4_4 hs13) (at?_mono_local h4_4 hp19) rfl
        (at?_mono_local h4_4 ha1) h29 h30 hcan r3a_bobAgreement h41 (parse_encMsg _ _ _ _) rfl
        (x25519LowOrder_dhPk_local r3a_dhsA) hrs rfl hrecv h37_bob
        (mac_ok r3a_seedB0_eq rfl rfl) (dec_ok r3a_seedB0_eq) (stOut := r3a_stB1)
        (by rw [hset]; rfl))
      (by rw [skipTr_zero_local _ _ _ _ _ _ rfl]; simp only [
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen4])
      (by rw [skipTr_zero_local _ _ _ _ _ _ rfl]; dsimp only [r3aTrace]; simp only [
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen4]; rfl)
  exact reach_of_runs hruns (bobStart_reachable r4)

theorem r3aTrace_bobDone :
    r3aTrace.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none r3a_out.ek r3a_out.ct r3a_keys) 44 := by
  have hlen4 : r3aTr4.length = 42 := by
    simp only [r3aTr4, encTr, r3aTr3, aliceTr, aliceTrOpt, r3aTr2, r3aTr1, compIkTr,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  simp only [r3aTrace, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
    Symbolic.DYBridge.DY.Trace.length_eq_2, hlen4, ↓reduceIte]; rfl

private theorem evIdx_r3aTrace (p : PQXDHEvent → Bool)
    (hb : ∀ ikB' ikA' spk' pq' opk' ek' ct' ks',
      p (.BobDone "bob" "alice" ikB' ikA' spk' pq' opk' ek' ct' ks') = false) :
    evIdx r3aTrace p = evIdx r3aTr3 p := by
  dsimp only [r3aTrace, r3aTr4]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hb, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_encTr]

theorem r3aTrace_compromise_indices : evIdx r3aTrace isCompromise = [22] := by
  rw [evIdx_r3aTrace _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [r3aTr3, aliceTr, r3aTr2, r3aTr1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompromise (.CompromisedIK "bob" (dhPk ikB)) = true from rfl,
    Bool.cond_true,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl),
    t4_length, List.nil_append]

abbrev isAliceDoneAny : PQXDHEvent → Bool :=
  fun | .AliceDone .. => true | _ => false

theorem r3aTrace_aliceDone_indices : evIdx r3aTrace isAliceDoneAny = [31] := by
  rw [evIdx_r3aTrace _ (fun _ _ _ _ _ _ _ _ => rfl)]
  have hlen2 : r3aTr2.length = 26 := by
    simp only [r3aTr2, r3aTr1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  dsimp only [r3aTr3, aliceTr]
  rw [evIdx_aliceTrOpt_true _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl), hlen2]
  dsimp only [r3aTr2, r3aTr1, compIkTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isAliceDoneAny (.CompromisedIK "bob" (dhPk ikB)) = false from rfl,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl),
    List.nil_append]

theorem r3aTrace_aliceDone_spk_eq {a b' : Participant} {ikA' ikB' spk' pqpk' : Bytes}
    {opk' : Option Bytes} {ek' ct' : Bytes} {keys' : HandshakeKeys} {j : Nat}
    (h : r3aTrace.EventLoggedAt
      (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') j) :
    spk' = spkVar := by
  have hm := mem_evIdx h (p := isAliceDoneAny) rfl
  rw [r3aTrace_aliceDone_indices, List.mem_singleton] at hm
  subst hm
  have hlen2 : r3aTr2.length = 26 := by
    simp only [r3aTr2, r3aTr1, compIkTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length]
  have h2_3 : r3aTr3 ≤ r3aTrace := by
    have h3_4 : r3aTr3 ≤ r3aTr4 := encTr_le_local _ _ _ _ _
    dsimp only [r3aTrace]
    exact Trace.le_trans _ _ _ h3_4
      (le_append_local (le_append_local (le_append_local (le_append_local (le_append_local
        (le_append_local (le_append_local (le_append_local (Trace.append_le _ _) _) _) _) _) _)
          _) _) _)
  have h31 : r3aTrace.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) spkVar (kemPk pqskB)
        none r3a_out.ek r3a_out.ct r3a_keys) 31 := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    exact at?_mono_local h2_3 (by
      simp only [r3aTr3, aliceTr, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl)
  rw [Trace.EventLoggedAt_eq_getEventAt] at h h31
  rw [h31] at h
  injection h with hEv
  injection hEv with _ _ _ _ hSpk
  exact hSpk.symm

/-! ## One-time-prekey re-encoding trace `r3bTrace` -/

abbrev opkVar : Bytes := X25519.x25519TorsionVariant (dhPk opkB) 1 0

def r3bTr1 : ExecTrace := t4Opk.append (NetE opkVar)
def r3bBh : BundleHandles := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := some 26 }
def r3bTr2 : ExecTrace :=
  aliceTrOpk r3bTr1 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) opkVar

abbrev r3b_out : AliceHandshakeOut :=
  aliceOutOpk r3bTr1 ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) opkVar
abbrev r3b_keys : HandshakeKeys := r3b_out.keys
abbrev r3b_dhsA : Bytes := rnd 29 32
def r3b_stA0 : TRState := aliceSt "bob" r3b_out r3b_dhsA

abbrev r3b_m0 : Bytes := rnd 36 32
abbrev r3b_coins0 : Bytes := rnd 37 32
def r3b_key0 : Bytes := (Spqr.spqrSend r3b_stA0.spqr r3b_coins0).2.1
def r3b_pqm0 : Bytes := (Spqr.spqrSend r3b_stA0.spqr r3b_coins0).2.2
def r3bTr3 : ExecTrace := encTr r3bTr2 "alice" 35 r3b_stA0 r3b_key0

def r3b_mh : PreKeyMsgHandles := { ek := 30, ct := 31, msg := 42 }
abbrev r3b_dhsB1 : Bytes := rnd 43 32
def r3b_stB00 : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) r3b_keys
    (encSig r3b_stA0 r3b_coins0 r3b_key0 r3b_m0)
def r3b_stB0' : TRState := (ratchetState r3b_stB00 (dhPk r3b_dhsA) r3b_dhsB1).1
def r3b_cB : RecvChain := (ratchetState r3b_stB00 (dhPk r3b_dhsA) r3b_dhsB1).2
def r3b_cB' : RecvChain := { r3b_cB with chainKey := (kdfCk r3b_cB.chainKey).1, index := 1 }
def r3b_seedB0 : Bytes := (kdfCk r3b_cB.chainKey).2
def r3b_stB1 : TRState :=
  { r3b_stB0' with
    recv := [r3b_cB'], spqr := recvSt (Spqr.spqrInit r3b_keys.pqr spqrB2A) r3b_pqm0 }

def r3bTrace : ExecTrace :=
  let tr1 := ((r3bTr3.append (RndE 32)).append (NetE r3b_key0)).append
    (EvP (.OPKUsed "bob" (dhPk opkB)))
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) (some (dhPk opkB)) r3b_out.ek r3b_out.ct r3b_keys))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk r3b_dhsA) (dhPk r3b_dhsB1)))).append
      (EvT (.HonestDH (r3b_stB0'.sessionInfo "bob") r3b_dhsB1 0))).append
      (EvC (.HandshakeSession (r3b_stB0'.sessionInfo "bob") 46))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk r3b_dhsA) 0 r3b_m0))).append
    (EvT (.MessageKey (r3b_stB0'.sessionInfo "bob") .receiver r3b_seedB0
      r3b_key0 0 2 52))).append
    (StT "bob" r3b_stB1)

theorem r3b_aliceAgreement_eq :
    aliceAgreement ikA (rnd 27 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some opkVar)
      (rnd 28 32) =
      aliceAgreement ikA (rnd 27 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some (dhPk opkB))
        (rnd 28 32) := by
  simp only [aliceAgreement, Option.map, opkVar, agree_variant1_dhPk]

theorem r3b_bobAgreement :
    bobAgreement ikB spkB pqskB (some opkB) (dhPk ikA) r3b_out.ek r3b_out.ct = some r3b_keys := by
  have hlen1 : r3bTr1.length = 27 := by
    simp only [r3bTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]
  have hek : r3b_out.ek = dhPk (rnd 27 32) := by
    dsimp only [r3b_out, aliceOutOpk,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [hlen1]; rfl
  have hct : r3b_out.ct =
      (aliceAgreement ikA (rnd 27 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some opkVar)
        (rnd 28 32)).1 := by
    dsimp only [r3b_out, aliceOutOpk,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [hlen1]; rfl
  have hkeys : r3b_keys =
      (aliceAgreement ikA (rnd 27 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some opkVar)
        (rnd 28 32)).2 := by
    dsimp only [r3b_keys, r3b_out, aliceOutOpk,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [hlen1]; rfl
  rw [hek, hct, hkeys, r3b_aliceAgreement_eq]
  exact bobAgreement_honest_opk ikA (rnd 27 32) ikB spkB pqskB opkB (rnd 28 32)

theorem r3b_seedB0_eq : (kdfCk r3b_stA0.cks).2 = r3b_seedB0 := by
  show (kdfCk (createChain r3b_keys.rk (dhPk spkB) r3b_dhsA).2).2 =
    (kdfCk (createChain r3b_keys.rk (dhPk r3b_dhsA) spkB).2).2
  rw [createChain_comm r3b_keys.rk r3b_dhsA spkB]

theorem r3bTrace_reach : r3bTrace.Reachable reachability := by
  obtain ⟨ha1, ha4, hb6, hb9, hs13, hs14, hs15, hp19, hp20, hp21⟩ := t4_facts_local
  have hlen1 : r3bTr1.length = 27 := by
    simp only [r3bTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]
  have hlen2 : r3bTr2.length = 36 := by
    simp only [r3bTr2, aliceTrOpk, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1]
  have hlen3 : r3bTr3.length = 43 := by
    simp only [r3bTr3, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2]
  have h4_opk : t4 ≤ t4Opk := by
    dsimp only [t4Opk, genOneTimePrekeyTr]
    exact le_append_local (le_append_local (le_append_local (Trace.append_le _ _) _) _) _
  have hopk_1 : t4Opk ≤ r3bTr1 := Trace.append_le _ _
  have h4_1 : t4 ≤ r3bTr1 := Trace.le_trans _ _ _ h4_opk hopk_1
  have h1_2 : r3bTr1 ≤ r3bTr2 := aliceTrOpt_le_local _ _ _ _ _ _ _ _
  have h2_3 : r3bTr2 ≤ r3bTr3 := encTr_le_local _ _ _ _ _
  have hopk_3 : t4Opk ≤ r3bTr3 := Trace.le_trans _ _ _ hopk_1 (Trace.le_trans _ _ _ h1_2 h2_3)
  have h4_3 : t4 ≤ r3bTr3 := Trace.le_trans _ _ _ h4_opk hopk_3
  have hopk24 : t4Opk.at? 24 = some (StP "bob" { kind := .oneTimePrekey, sk := opkB }) := by
    simp only [t4Opk, genOneTimePrekeyTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length, ↓reduceIte]; rfl
  have hopk25 : t4Opk.at? 25 = some (NetE (dhPk opkB)) := by
    simp only [t4Opk, genOneTimePrekeyTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4_length, ↓reduceIte]; rfl
  have r1 : r3bTr1.Reachable reachability :=
    sendAttacker_reach t4Opk_reach (ak_x25519Variant1 (ak_net (i := 25) hopk25))
  have h26 : r3bTr1.at? 26 = some (NetE opkVar) := by
    simp only [r3bTr1, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc, t4Opk_length,
      ↓reduceIte]; rfl
  have r2 : r3bTr2.Reachable reachability :=
    reach_of_runs
      (Runs.aliceStartOpk (idH := 4) (regB := 6) (oi := 26) (h := r3bBh) (honest := true)
        (at?_mono_local h4_1 ha4) (at?_mono_local h4_1 hb6)
        (at?_mono_local h4_1 hs14) (at?_mono_local h4_1 hs15)
        (at?_mono_local h4_1 hp20) (at?_mono_local h4_1 hp21)
        (Signature.verify_sign _ _ _) (Signature.verify_sign _ _ _)
        rfl h26 (x25519LowOrder_dhPk_local spkB) (x25519LowOrder_some_variant1_dhPk opkB))
      (aliceStart_reachable r1)
  have h35 : r3bTr2.at? 35 = some (StT "alice" r3b_stA0) := by
    simp only [r3bTr2, aliceTrOpk, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1, ↓reduceIte]; rfl
  have h38_enc : (((r3bTr2.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend r3b_stA0.spqr (rnd (r3bTr2.length + 1) 32)).2.1)).at? 38 =
      some (NetE r3b_key0) := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl
  have r3 : r3bTr3.Reachable reachability :=
    reach_of_runs
      (Runs.messageEncrypt (tr := r3bTr2) (stH := 35) (pqH := 38) (st := r3b_stA0)
        (pq := r3b_key0) h35 (by decide) h38_enc)
      (messageEncrypt_reachable r2 (by
        dsimp only [r3bTr2, aliceTrOpk, aliceTrOpt]
        exact isCurrentSnapshot_append_self_local _ _ _ (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1])))
  have hset : setRecvChain r3b_stB0'.recv r3b_cB' = [r3b_cB'] := by
    simp [setRecvChain, r3b_stB0', ratchetState, r3b_cB', r3b_cB, r3b_stB00,
      bobSt0, maxReceiverChains]
  have hrecv : Spqr.spqrRecv r3b_stB0'.spqr r3b_pqm0 1 =
      some (recvSt (Spqr.spqrInit r3b_keys.pqr spqrB2A) r3b_pqm0, r3b_key0) :=
    spqrRecv_init_agree r3b_keys.pqr r3b_coins0 r3b_pqm0 .b2a
      (bytesToLiteral_spqrSendMsg_local _ _)
  have hrs :
      ratchetState
        (bobSt0 "alice" ikB spkB (dhPk ikA) r3b_keys (encSig r3b_stA0 r3b_coins0 r3b_key0 r3b_m0))
        (encSig r3b_stA0 r3b_coins0 r3b_key0 r3b_m0).ratchetKey (rnd r3bTr3.length 32) =
      (r3b_stB0', r3b_cB) := by
    rw [hlen3]; rfl
  have h30 : r3bTr3.at? 30 = some (NetE r3b_out.ek) :=
    at?_mono_local h2_3 (by
      simp only [r3bTr2, aliceTrOpk, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1, ↓reduceIte]; rfl)
  have h31 : r3bTr3.at? 31 = some (NetE r3b_out.ct) :=
    at?_mono_local h2_3 (by
      simp only [r3bTr2, aliceTrOpk, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1, ↓reduceIte]; rfl)
  have h42 : r3bTr3.at? 42 = some (NetE (encMsg r3b_stA0 r3b_coins0 r3b_key0 r3b_m0)) := by
    simp only [r3bTr3, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
      Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl
  have h38_bob : ((r3bTr3.append (RndE 32)).append (NetE r3b_key0)).at? 38 =
      some (NetE r3b_key0) :=
    at?_mono_local (le_append_local (Trace.append_le _ _) _) (by
      simp only [r3bTr3, encTr, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen2, ↓reduceIte]; rfl)
  have hcan : isCanonicalKey r3b_out.ek = true := by
    dsimp only [r3b_out, aliceOutOpk,
      _root_.Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    exact isCanonicalKey_dhPk_local _
  have hopkUnused :
      (!PQXDH.opkUsedB ((r3bTr3.append (RndE 32)).append (NetE r3b_key0)) "bob" (dhPk opkB)) =
        true := by
    simp only [Bool.not_eq_true']
    refine someEventB_of_evIdx_nil ?_
    dsimp only [r3bTr3, r3bTr2, aliceTrOpk, r3bTr1, t4Opk]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_encTr,
      evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
      evIdx_append_non _ _ _ rfl, evIdx_genOneTimePrekeyTr_false _ _ _ (fun _ => rfl),
      evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  have hruns : Runs (Composed.bobStart "bob" "alice" khOpk 1 r3b_mh 38 1) r3bTr3 52 r3bTrace :=
    runs_cast_local
      (Runs.bobStartOpk (kh := khOpk) (mh := r3b_mh) (keys := r3b_keys)
        (msg := encSig r3b_stA0 r3b_coins0 r3b_key0 r3b_m0)
        (t := encMsg r3b_stA0 r3b_coins0 r3b_key0 r3b_m0)
        (st' := r3b_stB0') (c := r3b_cB) (c' := r3b_cB') (seed := r3b_seedB0)
        (pq := r3b_key0) (m := r3b_m0)
        (at?_mono_local h4_3 hb9) (at?_mono_local h4_3 hs13) (at?_mono_local h4_3 hp19) rfl
        (at?_mono_local hopk_3 hopk24) (at?_mono_local h4_3 ha1) h30 h31 hcan r3b_bobAgreement
        h42 (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk_local r3b_dhsA) hrs rfl hrecv h38_bob
        (mac_ok r3b_seedB0_eq rfl rfl) (dec_ok r3b_seedB0_eq) hopkUnused
        (stOut := r3b_stB1) (by rw [hset]; rfl))
      (by rw [skipTr_zero_local _ _ _ _ _ _ rfl]; simp only [
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3])
      (by rw [skipTr_zero_local _ _ _ _ _ _ rfl]; dsimp only [r3bTrace]; simp only [
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3]; rfl)
  exact reach_of_runs hruns (bobStart_reachable r3)

theorem r3bTrace_bobDone :
    r3bTrace.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) r3b_out.ek r3b_out.ct r3b_keys) 46 := by
  have hlen3 : r3bTr3.length = 43 := by
    simp only [r3bTr3, encTr, r3bTr2, aliceTrOpk, aliceTrOpt, r3bTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  simp only [r3bTrace, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
    Symbolic.DYBridge.DY.Trace.length_eq_2, hlen3, ↓reduceIte]; rfl

private theorem evIdx_r3bTrace (p : PQXDHEvent → Bool)
    (hopk : ∀ b k, p (.OPKUsed b k) = false)
    (hb : ∀ ikB' ikA' spk' pq' opk' ek' ct' ks',
      p (.BobDone "bob" "alice" ikB' ikA' spk' pq' opk' ek' ct' ks') = false) :
    evIdx r3bTrace p = evIdx r3bTr2 p := by
  dsimp only [r3bTrace, r3bTr3]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hb, Bool.cond_false, evIdx_append_ev, hopk, Bool.cond_false,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_encTr]

theorem r3bTrace_compromise_indices : evIdx r3bTrace isCompromise = [] := by
  rw [evIdx_r3bTrace _ (fun _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [r3bTr2, aliceTrOpk, r3bTr1, t4Opk]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_genOneTimePrekeyTr_false _ _ _ (fun _ => rfl),
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem r3bTrace_aliceDone_indices : evIdx r3bTrace isAliceDoneAny = [32] := by
  rw [evIdx_r3bTrace _ (fun _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl)]
  have hlen1 : r3bTr1.length = 27 := by
    simp only [r3bTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]
  dsimp only [r3bTr2, aliceTrOpk]
  rw [evIdx_aliceTrOpt_true _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl), hlen1]
  dsimp only [r3bTr1, t4Opk]
  rw [evIdx_append_non _ _ _ rfl, evIdx_genOneTimePrekeyTr_false _ _ _ (fun _ => rfl),
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl),
    List.nil_append]

theorem r3bTrace_aliceDone_opk_eq {a b' : Participant} {ikA' ikB' spk' pqpk' : Bytes}
    {opk' : Option Bytes} {ek' ct' : Bytes} {keys' : HandshakeKeys} {j : Nat}
    (h : r3bTrace.EventLoggedAt
      (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') j) :
    opk' = some opkVar := by
  have hm := mem_evIdx h (p := isAliceDoneAny) rfl
  rw [r3bTrace_aliceDone_indices, List.mem_singleton] at hm
  subst hm
  have hlen1 : r3bTr1.length = 27 := by
    simp only [r3bTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, t4Opk_length]
  have h2_full : r3bTr2 ≤ r3bTrace := by
    have h2_3 : r3bTr2 ≤ r3bTr3 := encTr_le_local _ _ _ _ _
    dsimp only [r3bTrace]
    exact Trace.le_trans _ _ _ h2_3
      (le_append_local (le_append_local (le_append_local (le_append_local (le_append_local
        (le_append_local (le_append_local (le_append_local (le_append_local
          (Trace.append_le _ _) _) _) _) _) _) _) _) _) _)
  have h32 : r3bTrace.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some opkVar) r3b_out.ek r3b_out.ct r3b_keys) 32 := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    exact at?_mono_local h2_full (by
      simp only [r3bTr2, aliceTrOpk, aliceTrOpt, Symbolic.DYBridge.DY.Trace.append_eq_1, hat_snoc,
        Symbolic.DYBridge.DY.Trace.length_eq_2, hlen1, ↓reduceIte]; rfl)
  rw [Trace.EventLoggedAt_eq_getEventAt] at h h32
  rw [h32] at h
  injection h with hEv
  injection hEv with _ _ _ _ _ _ hOpk
  exact hOpk.symm

/-! ## Event-absence lemmas on compromise traces -/

theorem no_thm8Agreement_of_no_aliceDone {tr : ExecTrace} (hidx : evIdx tr isAliceDoneAny = [])
    {a : Participant} {spk pqpk : Bytes} {opk : Option Bytes} {i : Nat} :
    ¬ PQXDH.ResponderSessionAgreement a spk pqpk opk i tr := by
  rintro ⟨b', ikA', ikB', spk', opk', ek', ct', keys', j, hEv, _⟩
  exact not_logged hidx (p := isAliceDoneAny) rfl ⟨j, hEv⟩

theorem trIKA_no_aliceDone : evIdx trIKA isAliceDoneAny = [] := by
  dsimp only [trIKA, trIKA_pre, compIkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isAliceDoneAny (.CompromisedIK "alice" (dhPk advIkA)) = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trSPKB_no_aliceDone : evIdx trSPKB isAliceDoneAny = [] := by
  dsimp only [trSPKB, trSPKB_pre, compSpkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isAliceDoneAny (.CompromisedSPK "bob" (dhPk advSpkB)) = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trBrokenDHB_no_aliceDone : evIdx trBrokenDHB isAliceDoneAny = [] := by
  dsimp only [trBrokenDHB, trBrokenDHB_pre, invertTr, breakDHTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isAliceDoneAny .BrokenDH = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trIKA_no_thm8Agreement (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes) (i : Nat) :
    ¬ PQXDH.ResponderSessionAgreement a spk pqpk opk i trIKA :=
  no_thm8Agreement_of_no_aliceDone trIKA_no_aliceDone

theorem trSPKB_no_thm8Agreement (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes) (i : Nat) :
    ¬ PQXDH.ResponderSessionAgreement a spk pqpk opk i trSPKB :=
  no_thm8Agreement_of_no_aliceDone trSPKB_no_aliceDone

theorem trBrokenDHB_no_thm8Agreement (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) :
    ¬ PQXDH.ResponderSessionAgreement a spk pqpk opk i trBrokenDHB :=
  no_thm8Agreement_of_no_aliceDone trBrokenDHB_no_aliceDone

theorem trIKA_no_compSPK : evIdx trIKA isCompSPK = [] := by
  dsimp only [trIKA, trIKA_pre, compIkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompSPK (.CompromisedIK "alice" (dhPk advIkA)) = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trIKA_no_brokenDH : evIdx trIKA isBrokenDH = [] := by
  dsimp only [trIKA, trIKA_pre, compIkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isBrokenDH (.CompromisedIK "alice" (dhPk advIkA)) = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trSPKB_no_compIK : evIdx trSPKB isCompIK = [] := by
  dsimp only [trSPKB, trSPKB_pre, compSpkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompIK (.CompromisedSPK "bob" (dhPk advSpkB)) = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trSPKB_no_brokenDH : evIdx trSPKB isBrokenDH = [] := by
  dsimp only [trSPKB, trSPKB_pre, compSpkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isBrokenDH (.CompromisedSPK "bob" (dhPk advSpkB)) = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trBrokenDHB_no_compIK : evIdx trBrokenDHB isCompIK = [] := by
  dsimp only [trBrokenDHB, trBrokenDHB_pre, invertTr, breakDHTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompIK .BrokenDH = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trBrokenDHB_no_compSPK : evIdx trBrokenDHB isCompSPK = [] := by
  dsimp only [trBrokenDHB, trBrokenDHB_pre, invertTr, breakDHTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_forgedPreKeyPrefix, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompSPK .BrokenDH = false from rfl, Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

/-- Case-indexed form of `PQXDH.HandshakeAuthWasCompromised` indexed by `Fin 3`. -/
def Thm8Case (b a : Participant) (ikA spk : Bytes) (i : Nat) (tr : ExecTrace) : Fin 3 → Prop
  | 0 => PQXDH.LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr
  | 1 => PQXDH.LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr
  | 2 => PQXDH.LoggedBefore PQXDHEvent.BrokenDH i tr

theorem handshakeAuthWasCompromised_iff_exists_thm8Case
    (b a : Participant) (ikA spk : Bytes) (i : Nat) (tr : ExecTrace) :
    PQXDH.HandshakeAuthWasCompromised b a ikA spk i tr ↔
      ∃ k : Fin 3, Thm8Case b a ikA spk i tr k := by
  constructor
  · rintro (h0 | h1 | h2)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  · rintro ⟨k, hk⟩
    match k with
    | 0 => exact .inl hk
    | 1 => exact .inr (.inl hk)
    | 2 => exact .inr (.inr hk)

theorem trIKA_not_other_thm8Case (k : Fin 3) (hk : k ≠ 0) :
    ¬ Thm8Case "bob" "alice" (dhPk advIkA) (dhPk advSpkB) 29 trIKA k := by
  match k with
  | 0 => exact absurd rfl hk
  | 1 => exact not_loggedBefore_of_none trIKA_no_compSPK rfl
  | 2 => exact not_loggedBefore_of_none trIKA_no_brokenDH rfl

theorem trSPKB_not_other_thm8Case (k : Fin 3) (hk : k ≠ 1) :
    ¬ Thm8Case "bob" "alice" (dhPk advIkA) (dhPk advSpkB) 29 trSPKB k := by
  match k with
  | 0 => exact not_loggedBefore_of_none trSPKB_no_compIK rfl
  | 1 => exact absurd rfl hk
  | 2 => exact not_loggedBefore_of_none trSPKB_no_brokenDH rfl

theorem trBrokenDHB_not_other_thm8Case (k : Fin 3) (hk : k ≠ 2) :
    ¬ Thm8Case "bob" "alice" (dhPk advIkA) (dhPk advSpkB) 29 trBrokenDHB k := by
  match k with
  | 0 => exact not_loggedBefore_of_none trBrokenDHB_no_compIK rfl
  | 1 => exact not_loggedBefore_of_none trBrokenDHB_no_compSPK rfl
  | 2 => exact absurd rfl hk

private theorem evIdx_trAlias (p : PQXDHEvent → Bool)
    (hb : ∀ ikB' ikA' spk' pq' opk' ek' ct' ks',
      p (.BobDone "bob" "alice" ikB' ikA' spk' pq' opk' ek' ct' ks') = false) :
    evIdx trAlias p = evIdx trAlias3 p := by
  dsimp only [trAlias, trAlias4]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hb, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_encTr]

theorem trAlias_no_compIKA : evIdx trAlias (isCompIkOf "alice") = [] := by
  rw [evIdx_trAlias _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [trAlias3, aliceTr, trAlias2, regCorruptTr, trAlias1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_ev, show isCompIkOf "alice" (.CompromisedIK "carol" (dhPk ikB)) = false by decide,
    Bool.cond_false, evIdx_append_ev,
    show isCompIkOf "alice" (.IdentityRegistered "carol" (dhPk ikB) (Signature.vk ikB) false) =
      false from rfl,
    Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompIkOf "alice" (.CompromisedIK "bob" (dhPk ikB)) = false by decide,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trAlias_no_compSPK : evIdx trAlias isCompSPK = [] := by
  rw [evIdx_trAlias _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [trAlias3, aliceTr, trAlias2, regCorruptTr, trAlias1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_ev, show isCompSPK (.CompromisedIK "carol" (dhPk ikB)) = false from rfl,
    Bool.cond_false, evIdx_append_ev,
    show isCompSPK (.IdentityRegistered "carol" (dhPk ikB) (Signature.vk ikB) false) = false
      from rfl,
    Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompSPK (.CompromisedIK "bob" (dhPk ikB)) = false from rfl,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trAlias_no_brokenDH : evIdx trAlias isBrokenDH = [] := by
  rw [evIdx_trAlias _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [trAlias3, aliceTr, trAlias2, regCorruptTr, trAlias1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_ev, show isBrokenDH (.CompromisedIK "carol" (dhPk ikB)) = false from rfl,
    Bool.cond_false, evIdx_append_ev,
    show isBrokenDH (.IdentityRegistered "carol" (dhPk ikB) (Signature.vk ikB) false) = false
      from rfl,
    Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isBrokenDH (.CompromisedIK "bob" (dhPk ikB)) = false from rfl,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem trAlias_no_thm8Excuse :
    ¬ PQXDH.HandshakeAuthWasCompromised "bob" "alice" (dhPk ikA) (dhPk spkB) 44 trAlias := by
  rintro (hk | hk | hk)
  · exact not_loggedBefore_of_none trAlias_no_compIKA (by simp [isCompIkOf]) hk
  · exact not_loggedBefore_of_none trAlias_no_compSPK rfl hk
  · exact not_loggedBefore_of_none trAlias_no_brokenDH rfl hk

theorem r3aTrace_no_compIKA : evIdx r3aTrace (isCompIkOf "alice") = [] := by
  rw [evIdx_r3aTrace _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [r3aTr3, aliceTr, r3aTr2, r3aTr1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompIkOf "alice" (.CompromisedIK "bob" (dhPk ikB)) = false by decide,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem r3aTrace_no_compSPK : evIdx r3aTrace isCompSPK = [] := by
  rw [evIdx_r3aTrace _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [r3aTr3, aliceTr, r3aTr2, r3aTr1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompSPK (.CompromisedIK "bob" (dhPk ikB)) = false from rfl,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem r3aTrace_no_brokenDH : evIdx r3aTrace isBrokenDH = [] := by
  rw [evIdx_r3aTrace _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [r3aTr3, aliceTr, r3aTr2, r3aTr1, compIkTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isBrokenDH (.CompromisedIK "bob" (dhPk ikB)) = false from rfl,
    Bool.cond_false,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem r3aTrace_no_thm8Excuse :
    ¬ PQXDH.HandshakeAuthWasCompromised "bob" "alice" (dhPk ikA) (dhPk spkB) 44 r3aTrace := by
  rintro (hk | hk | hk)
  · exact not_loggedBefore_of_none r3aTrace_no_compIKA (by simp [isCompIkOf]) hk
  · exact not_loggedBefore_of_none r3aTrace_no_compSPK rfl hk
  · exact not_loggedBefore_of_none r3aTrace_no_brokenDH rfl hk

theorem r3bTrace_no_thm8Excuse :
    ¬ PQXDH.HandshakeAuthWasCompromised "bob" "alice" (dhPk ikA) (dhPk spkB) 46 r3bTrace := by
  rintro (hk | hk | hk)
  · exact not_loggedBefore_of_none r3bTrace_compromise_indices rfl hk
  · exact not_loggedBefore_of_none r3bTrace_compromise_indices rfl hk
  · exact not_loggedBefore_of_none r3bTrace_compromise_indices rfl hk

private theorem evIdx_t8 (p : PQXDHEvent → Bool)
    (hb : ∀ ikB' ikA' spk' pq' opk' ek' ct' ks',
      p (.BobDone "bob" "alice" ikB' ikA' spk' pq' opk' ek' ct' ks') = false) :
    evIdx t8 p = evIdx t5 p := by
  dsimp only [t8, t7, t6]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hb, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_encTr, evIdx_encTr]

theorem t8_no_thm8Case (k : Fin 3) :
    ¬ Thm8Case "bob" "alice" (dhPk ikA) (dhPk spkB) 47 t8 k := by
  have hnc : evIdx t8 isCompromise = [] := by
    rw [evIdx_t8 _ (fun _ _ _ _ _ _ _ _ => rfl)]
    dsimp only [t5, aliceTr]
    rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
      evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  match k with
  | 0 => exact not_loggedBefore_of_none hnc rfl
  | 1 => exact not_loggedBefore_of_none hnc rfl
  | 2 => exact not_loggedBefore_of_none hnc rfl

theorem t8_aliceDone_indices : evIdx t8 isAliceDoneAny = [27] := by
  rw [evIdx_t8 _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [t5, aliceTr]
  rw [evIdx_aliceTrOpt_true _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl), t4_length,
    evIdx_t4_false_local _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl),
    List.nil_append]

theorem t8_aliceDone_idx_eq {a b' : Participant} {ikA' ikB' spk' pqpk' : Bytes}
    {opk' : Option Bytes} {ek' ct' : Bytes} {keys' : HandshakeKeys} {j : Nat}
    (h : t8.EventLoggedAt
      (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') j) :
    j = 27 := by
  have hm := mem_evIdx h (p := isAliceDoneAny) rfl
  rw [t8_aliceDone_indices, List.mem_singleton] at hm
  exact hm

theorem not_loggedBefore_gap_of_singleton {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {i k gap : Nat} (hidx : evIdx tr p = [k]) (hp : p e = true)
    (hik : i ≤ k + gap) : ∀ j, tr.EventLoggedAt e j → ¬ (j + gap < i) := by
  intro j hj hlt
  have hm := mem_evIdx hj hp
  rw [hidx, List.mem_singleton] at hm
  omega

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHAuthTraces
