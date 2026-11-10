/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
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
import Symbolic.DYBridge.DY.EquationalTheory.Sign

/-!
# Shared Adversarial Combinators, Knowledge Lemmas, and Witness Traces

Defines symbolic `Runs` combinators, trace builders, and reachability wrappers for PQXDH and
Triple Ratchet adversary and compromise transitions in `DY.Libsignal.Composed.reachability`,
establishes `AttackerKnows` derivation lemmas for `HandshakeKeys` and forged bundles or prekey
messages, and constructs concrete reachable compromise witness traces.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Shared.Composed.Adversary

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (bh1 cA0 cBOpk cB'Opk coins0Opk dhsAOpk
  dhsB1 evIdx ikA ikB isCompromise key0Opk keys1 keysOpk kh1 khOpk length_wTrOpk m0Opk mem_evIdx
  mhOpk noCompromise_idx noCompromise_of_evIdx noCompromise_opk_idx not_logged o1 oOpk opkB pqm0Opk
  pqNonce pqskB recv7Opk seedB0Opk seedB0Opk_eq spkB spkNonce stA0 stA0Opk stB00 stB00Opk stB0'Opk
  t1 t1_length t2 t2_length t3 t3_length t4 t4Opk t4Opk_length t4_length t4_reach t5 t5Opk
  t5Opk_length t5_aliceDone_at t5_length t5_reach t5_stA0_at t6 t6Opk t6Opk_length t6Opk_reach
  t7 t7Opk t8 t8_bobDone_at t8_length t8_reach wTrOpk wTrOpk_bobDone_at wTrOpk_reach)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_init_agree)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.aliceStart
  Runs.bind Runs.bobStart Runs.bobStartOpk Runs.exposeCkr Runs.exposeCks Runs.exposeDhs Runs.exposeRk
  Runs.exposeSkipped Runs.exposeSpqr Runs.genPQPrekey Runs.genSignedPrekey Runs.getKey
  Runs.logEvent Runs.messageEncrypt Runs.receiveMessage Runs.registerIdentity
  Runs.guardTrace Runs.sendMessage StP StT agree_comm aliceOut aliceOutOpk aliceOutOpt
  aliceSt aliceStart_reachable aliceTr aliceTrOpk aliceTrOpt bobAgreement_honest
  bobAgreement_honest_opk bobOut bobSt0 bobStart_reachable breakDH_reachable breakKEM_reachable
  compromiseIK_reachable compromiseOPK_reachable compromisePQSPK_reachable compromiseSPK_reachable
  createChain_comm dec_ok encMsg encSig encTr exposeCkrTr exposeCksTr exposeDhsTr
  exposeKey_reachable exposeRkTr exposeSkippedTr exposeSkipped_reachable exposeSpqrTr
  exposeSpqr_reachable genOneTimePrekeyTr genPQPrekeyTr genSignedPrekeyTr invertDH_reachable
  invertKEM_reachable kemDecap_kemEncap mac_ok messageEncrypt_reachable parse_encMsg ratchetState
  reach_of_runs recvSt registerCorruptIdentity_reachable registerIdentityTr rnd
  sendMessage_reachable skipTr)
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

/-! ## Adversary and Compromise Transition Wrappers -/

theorem sendAttacker_reach {tr : ExecTrace} (h : tr.Reachable reachability) {b : Bytes}
    (hb : b.AttackerKnows tr) : (tr.append (NetE b)).Reachable reachability :=
  sendMessage_reachable h hb

private theorem nil_len : (Trace.nil : ExecTrace).length = 0 :=
  Symbolic.DYBridge.DY.Trace.length_eq_1

private theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace}
    (h : t1 ≤ t2) (e : E) : t1 ≤ t2.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le t2 e)

private theorem le_append2 {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {t1 t2 : ExecTrace} (h : t1 ≤ t2) (e1 : E1) (e2 : E2) :
    t1 ≤ (t2.append e1).append e2 :=
  le_append_of_le (le_append_of_le h e1) e2

private theorem at?_mono {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace} {i : Nat} {x : E}
    (hle : t1 ≤ t2) (h : t1.at? i = some x) : t2.at? i = some x := by
  have := Trace.at?_le (EntryT := E) t1 t2 i hle
  rwa [h] at this

private theorem at?_append_at {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

private theorem at?_append_self_proj {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self]
  simp only [Trace.at?, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

private theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hi' : i < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hne : i ≠ tr.length := by omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]

private theorem runs_cast {α : Type} {x : Traceful α} {tr t1 t2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1) (ha : a1 = a2) (ht : t1 = t2) : Runs x tr a2 t2 := by
  subst ha; subst ht; exact h

private theorem eventLoggedAt_of_at? {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact h

private theorem eventLoggedAt_mono {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {t1 t2 : ExecTrace} {ev : Ev} {i : Nat}
    (hle : t1 ≤ t2) (h : t1.EventLoggedAt ev i) : t2.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono hle h

private theorem messageSentAt_of_at? {tr : ExecTrace} {b : Bytes} {i : Nat}
    (h : tr.at? i = some (NetE b)) : tr.MessageSentAt b i := by
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact h

private theorem append1_ev_at {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) {i : Nat} (hi : tr.length = i) :
    (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev i :=
  eventLoggedAt_of_at? (at?_append_at tr _ hi)

private theorem append2_ev_at {Ev E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    [ExecTraceTypes.Has E] (tr : ExecTrace) (ev : Ev) (x : E) {i : Nat} (hi : tr.length = i) :
    ((tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)).append x).EventLoggedAt ev i :=
  eventLoggedAt_mono (Trace.append_le _ _) (append1_ev_at tr ev hi)

private theorem append2_snd_at {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) {i : Nat} (hi : tr.length + 1 = i) :
    ((tr.append e1).append e2).at? i = some e2 :=
  at?_append_at (tr.append e1) e2 (by rw [append_len, hi])

private theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [TripleRatchet.logSkippedKeys, Traceful.run_pure]

private theorem isCurrentSnapshot_append_self (tr : ExecTrace) (me : Participant) (st : TRState)
    {k : Nat} (hk : tr.length = k) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [Trace.at?_append tr (StT me st), append_len, Nat.sub_self]; rfl

private theorem normalizeX25519Key_dhPk (sk : Bytes) :
    X25519.normalizeX25519Key (dhPk sk) = dhPk sk := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  unfold X25519.normalizeX25519Key; rw [hv]

private theorem x25519LowOrder_dhPk (sk : Bytes) :
    TripleRatchet.x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl0 : (dhPk sk).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl : Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]
  unfold TripleRatchet.x25519LowOrder X25519.normalizeX25519Key
  rw [hv, hl]

private theorem isCanonicalKey_dhPk (sk : Bytes) :
    PQXDH.isCanonicalKey (dhPk sk) = true := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl : PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk sk
  unfold PQXDH.isCanonicalKey
  rw [hv, hl]; rfl

private theorem bytesToLiteral_spqrSendMsg (st coins : Bytes) :
    Literal.bytesToLiteral (Spqr.spqrSend st coins).2.2 = none := by
  have hl0 : ((Spqr.spqrSend st coins).2.2).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes)
  dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

private theorem someEventB_nil (p : PQXDHEvent → Bool) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) Trace.nil p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]; rw [nil_len]; rfl

private theorem someEventB_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) (tr.append x) p = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt tr x (List.mem_range.mp hi)]
    exact h i hi
  · rw [at?_append_self_proj, hnone]

private theorem someEventB_append_false (tr : ExecTrace) (ev : PQXDHEvent)
    (p : PQXDHEvent → Bool) (hp : p ev = false)
    (h : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) (tr.append (EvP ev)) p = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
    exact h i hi
  · rw [Trace.at?_append]; exact hp

private theorem someEventB_of_at? {tr : ExecTrace} {i : Nat} {ev : PQXDHEvent}
    {p : PQXDHEvent → Bool} (h : tr.at? i = some (EvP ev)) (hp : p ev = true) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = true := by
  have hi : i < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := ProtocolEvent.ExecEntryT PQXDHEvent) tr i
    rwa [h] at this
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by rw [h]; exact hp⟩

private theorem someEventB_of_evIdx_nil {tr : ExecTrace} {p : PQXDHEvent → Bool}
    (h : evIdx tr p = []) : (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) tr p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [List.any_eq_false]
  intro i hi
  cases hat : (tr.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => dsimp only; exact Bool.false_ne_true
  | some ev =>
    rw [Bool.not_eq_true]
    cases hp : p ev.ev
    · dsimp only; exact hp
    · exfalso
      have hmem : i ∈ evIdx tr p := mem_evIdx (eventLoggedAt_of_at? hat) hp
      rw [h] at hmem
      exact List.not_mem_nil hmem

def regCorruptTr (tr : ExecTrace) (p : Participant) (ik : Bytes) : ExecTrace :=
  (tr.append (EvP (.IdentityRegistered p (dhPk ik) (Signature.vk ik) false))).append
    (EvP (.CompromisedIK p (dhPk ik)))

theorem Runs.registerCorruptIdentity {tr : ExecTrace} {p : Participant} {skIdx : Nat} {ik : Bytes}
    (hunreg : (!PQXDH.isRegisteredB tr p) = true) (hnet : tr.at? skIdx = some (NetE ik)) :
    Runs (PQXDH.registerCorruptIdentity p skIdx) tr () (regCorruptTr tr p ik) := by
  unfold PQXDH.registerCorruptIdentity
  refine Runs.bind (Runs.requireTracePredicate hunreg) ?_
  refine Runs.bind (Runs.receiveMessage hnet) ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  exact Runs.logEvent _ _

theorem regCorruptTr_reach {tr : ExecTrace} {p : Participant} {skIdx : Nat} {ik : Bytes}
    (hr : tr.Reachable reachability) (hunreg : (!PQXDH.isRegisteredB tr p) = true)
    (hnet : tr.at? skIdx = some (NetE ik)) :
    (regCorruptTr tr p ik).Reachable reachability :=
  reach_of_runs (Runs.registerCorruptIdentity hunreg hnet) (registerCorruptIdentity_reachable hr)

def compIkTr (tr : ExecTrace) (p : Participant) (ik : Bytes) : ExecTrace :=
  (tr.append (EvP (.CompromisedIK p (dhPk ik)))).append (NetE ik)

theorem Runs.compromiseIK {tr : ExecTrace} {p : Participant} {idx : Nat} {ik : Bytes}
    (hst : tr.at? idx = some (StP p { kind := .identity, sk := ik })) :
    Runs (PQXDH.compromiseIK p idx) tr (tr.length + 1) (compIkTr tr p ik) := by
  unfold PQXDH.compromiseIK
  exact runs_cast (Runs.bind (Runs.getKey hst) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _)))
    (append_len _ _) rfl

theorem compIkTr_reach {tr : ExecTrace} {p : Participant} {idx : Nat} {ik : Bytes}
    (hr : tr.Reachable reachability)
    (hst : tr.at? idx = some (StP p { kind := .identity, sk := ik })) :
    (compIkTr tr p ik).Reachable reachability :=
  reach_of_runs (Runs.compromiseIK hst) (compromiseIK_reachable hr)

def compSpkTr (tr : ExecTrace) (b : Participant) (spk : Bytes) : ExecTrace :=
  (tr.append (EvP (.CompromisedSPK b (dhPk spk)))).append (NetE spk)

theorem Runs.compromiseSPK {tr : ExecTrace} {b : Participant} {idx : Nat} {spk : Bytes}
    (hst : tr.at? idx = some (StP b { kind := .signedPrekey, sk := spk })) :
    Runs (PQXDH.compromiseSPK b idx) tr (tr.length + 1) (compSpkTr tr b spk) := by
  unfold PQXDH.compromiseSPK
  exact runs_cast (Runs.bind (Runs.getKey hst) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _)))
    (append_len _ _) rfl

theorem compSpkTr_reach {tr : ExecTrace} {b : Participant} {idx : Nat} {spk : Bytes}
    (hr : tr.Reachable reachability)
    (hst : tr.at? idx = some (StP b { kind := .signedPrekey, sk := spk })) :
    (compSpkTr tr b spk).Reachable reachability :=
  reach_of_runs (Runs.compromiseSPK hst) (compromiseSPK_reachable hr)

def compPqTr (tr : ExecTrace) (b : Participant) (pqsk : Bytes) : ExecTrace :=
  (tr.append (EvP (.CompromisedPQSPK b (kemPk pqsk)))).append (NetE pqsk)

theorem Runs.compromisePQSPK {tr : ExecTrace} {b : Participant} {idx : Nat} {pqsk : Bytes}
    (hst : tr.at? idx = some (StP b { kind := .pqPrekey, sk := pqsk })) :
    Runs (PQXDH.compromisePQSPK b idx) tr (tr.length + 1) (compPqTr tr b pqsk) := by
  unfold PQXDH.compromisePQSPK
  exact runs_cast (Runs.bind (Runs.getKey hst) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _)))
    (append_len _ _) rfl

theorem compPqTr_reach {tr : ExecTrace} {b : Participant} {idx : Nat} {pqsk : Bytes}
    (hr : tr.Reachable reachability)
    (hst : tr.at? idx = some (StP b { kind := .pqPrekey, sk := pqsk })) :
    (compPqTr tr b pqsk).Reachable reachability :=
  reach_of_runs (Runs.compromisePQSPK hst) (compromisePQSPK_reachable hr)

def compOpkTr (tr : ExecTrace) (b : Participant) (opk : Bytes) : ExecTrace :=
  (tr.append (EvP (.CompromisedOPK b (dhPk opk)))).append (NetE opk)

theorem Runs.compromiseOPK {tr : ExecTrace} {b : Participant} {idx : Nat} {opk : Bytes}
    (hst : tr.at? idx = some (StP b { kind := .oneTimePrekey, sk := opk }))
    (hguard : (!PQXDH.opkUsedB tr b (dhPk opk)) = true) :
    Runs (PQXDH.compromiseOPK b idx) tr (tr.length + 1) (compOpkTr tr b opk) := by
  unfold PQXDH.compromiseOPK
  exact runs_cast (Runs.bind (Runs.getKey hst)
    (Runs.bind (Runs.requireTracePredicate hguard)
      (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _))))
    (append_len _ _) rfl

theorem compOpkTr_reach {tr : ExecTrace} {b : Participant} {idx : Nat} {opk : Bytes}
    (hr : tr.Reachable reachability)
    (hst : tr.at? idx = some (StP b { kind := .oneTimePrekey, sk := opk }))
    (hguard : (!PQXDH.opkUsedB tr b (dhPk opk)) = true) :
    (compOpkTr tr b opk).Reachable reachability :=
  reach_of_runs (Runs.compromiseOPK hst hguard) (compromiseOPK_reachable hr)

def breakDHTr (tr : ExecTrace) : ExecTrace := tr.append (EvP .BrokenDH)

theorem Runs.breakDH (tr : ExecTrace) : Runs PQXDH.breakDH tr () (breakDHTr tr) :=
  Runs.logEvent tr PQXDHEvent.BrokenDH

theorem breakDHTr_reach {tr : ExecTrace} (hr : tr.Reachable reachability) :
    (breakDHTr tr).Reachable reachability :=
  reach_of_runs (Runs.breakDH tr) (breakDH_reachable hr)

def breakKEMTr (tr : ExecTrace) : ExecTrace := tr.append (EvP .BrokenKEM)

theorem Runs.breakKEM (tr : ExecTrace) : Runs PQXDH.breakKEM tr () (breakKEMTr tr) :=
  Runs.logEvent tr PQXDHEvent.BrokenKEM

theorem breakKEMTr_reach {tr : ExecTrace} (hr : tr.Reachable reachability) :
    (breakKEMTr tr).Reachable reachability :=
  reach_of_runs (Runs.breakKEM tr) (breakKEM_reachable hr)

def invertTr (tr : ExecTrace) (sk : Bytes) : ExecTrace := tr.append (NetE sk)
abbrev invertDHTr := invertTr
abbrev invertKEMTr := invertTr

theorem Runs.invertDH {tr : ExecTrace} {pkIdx : Nat} {sk : Bytes}
    (hbr : PQXDH.brokenDHB tr = true) (hpk : tr.at? pkIdx = some (NetE (dhPk sk))) :
    Runs (PQXDH.invertDH pkIdx) tr tr.length (invertTr tr sk) := by
  have h1 : X25519.normalizeX25519Key (dhPk sk) = dhPk sk := normalizeX25519Key_dhPk sk
  have hsk : PQXDH.extractDhSecretKey (X25519.normalizeX25519Key (dhPk sk)) = some sk := by
    rw [h1]; simp only [PQXDH.extractDhSecretKey, dhPk, BytesView.view_pack]
  unfold PQXDH.invertDH
  refine Runs.bind (Runs.requireTracePredicate hbr) (Runs.bind (Runs.receiveMessage hpk) ?_)
  rw [hsk]
  exact Runs.sendMessage _ _

theorem invertDH_reach_sk {tr : ExecTrace} {pkIdx : Nat} {sk : Bytes}
    (hr : tr.Reachable reachability) (hbr : PQXDH.brokenDHB tr = true)
    (hpk : tr.at? pkIdx = some (NetE (dhPk sk))) :
    (invertTr tr sk).Reachable reachability :=
  reach_of_runs (Runs.invertDH hbr hpk) (invertDH_reachable hr)

theorem Runs.invertKEM {tr : ExecTrace} {pkIdx : Nat} {sk : Bytes}
    (hbr : PQXDH.brokenKEMB tr = true) (hpk : tr.at? pkIdx = some (NetE (kemPk sk))) :
    Runs (PQXDH.invertKEM pkIdx) tr tr.length (invertTr tr sk) := by
  have hsk : PQKem.invertKemPublicKey (kemPk sk) = some sk := by
    simp only [PQKem.invertKemPublicKey, kemPk, BytesView.view_pack]
  unfold PQXDH.invertKEM
  refine Runs.bind (Runs.requireTracePredicate hbr) (Runs.bind (Runs.receiveMessage hpk) ?_)
  rw [hsk]
  exact Runs.bind
    ⟨by dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [Traceful.run_mk],
     by dsimp only [liftM, monadLift, MonadLift.monadLift]; rw [Traceful.run_mk]⟩
    (Runs.sendMessage _ _)

theorem invertKEM_reach_sk {tr : ExecTrace} {pkIdx : Nat} {sk : Bytes}
    (hr : tr.Reachable reachability) (hbr : PQXDH.brokenKEMB tr = true)
    (hpk : tr.at? pkIdx = some (NetE (kemPk sk))) :
    (invertTr tr sk).Reachable reachability :=
  reach_of_runs (Runs.invertKEM hbr hpk) (invertKEM_reachable hr)

theorem exposeRk_reach {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hr : tr.Reachable reachability) (hst : tr.at? stH = some (StT me st)) :
    (exposeRkTr tr me st).Reachable reachability :=
  reach_of_runs (Runs.exposeRk hst) (exposeKey_reachable hr)

theorem exposeDhs_reach {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hr : tr.Reachable reachability) (hst : tr.at? stH = some (StT me st)) :
    (exposeDhsTr tr me st).Reachable reachability :=
  reach_of_runs (Runs.exposeDhs hst) (exposeKey_reachable hr)

theorem exposeCks_reach {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hr : tr.Reachable reachability) (hst : tr.at? stH = some (StT me st)) :
    (exposeCksTr tr me st).Reachable reachability :=
  reach_of_runs (Runs.exposeCks hst) (exposeKey_reachable hr)

theorem exposeCkr_reach {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    {pk : Bytes} {c : RecvChain} (hr : tr.Reachable reachability)
    (hst : tr.at? stH = some (StT me st)) (hfind : findRecvChain st.recv pk = some c) :
    (exposeCkrTr tr me st c).Reachable reachability :=
  reach_of_runs (Runs.exposeCkr hst hfind) (exposeKey_reachable hr)

theorem exposeSpqr_reach {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState}
    (hr : tr.Reachable reachability) (hst : tr.at? stH = some (StT me st)) :
    (exposeSpqrTr tr me st).Reachable reachability :=
  reach_of_runs (Runs.exposeSpqr hst) (exposeSpqr_reachable hr)

theorem exposeSkipped_reach {tr : ExecTrace} {skH : Nat} {s : SessionInfo} {pk : Bytes}
    {n : UInt32} {seed : Bytes} {rIdx srcIdx : Nat} (hr : tr.Reachable reachability)
    (hsk : tr.at? skH = some (EvT (.SkippedKeyStored s pk n seed rIdx srcIdx)))
    (hunused : (!TripleRatchet.receiverKeyUsedB tr s seed n rIdx) = true) :
    (exposeSkippedTr tr s seed n rIdx).Reachable reachability :=
  reach_of_runs (Runs.exposeSkipped hsk hunused) (exposeSkipped_reachable hr)

/-! ## Attacker-Knowledge Combinators and Handshake Key Derivations -/

theorem ak_net {tr : ExecTrace} {i : Nat} {b : Bytes} (h : tr.at? i = some (NetE b)) :
    b.AttackerKnows tr := Trace.MessageSentAt_implies_AttackerKnows tr b i (messageSentAt_of_at? h)

theorem ak_lit {tr : ExecTrace} (b : ByteArray) :
    Bytes.AttackerKnows (literalToBytes b) tr :=
  Literal.attacker_knows_literalToBytes b tr

theorem ak_concat {tr : ExecTrace} {a b : Bytes}
    (ha : a.AttackerKnows tr) (hb : b.AttackerKnows tr) :
    (concat a b).AttackerKnows tr :=
  Concat.attacker_knows_concat a b tr ha hb

theorem ak_trunc8 {tr : ExecTrace} {a : Bytes} (ha : a.AttackerKnows tr) :
    (Trunc.trunc8 a).AttackerKnows tr :=
  Bytes.AttackerKnows.prove Trunc.trunc8.attackerKnowledge _ tr ⟨a, rfl, ha⟩

theorem ak_dhPk {tr : ExecTrace} {sk : Bytes} (hsk : sk.AttackerKnows tr) :
    (dhPk sk).AttackerKnows tr :=
  DiffieHellman.attacker_knows_dhPk sk tr hsk

theorem ak_dh {tr : ExecTrace} {pk sk : Bytes}
    (hpk : pk.AttackerKnows tr) (hsk : sk.AttackerKnows tr) :
    (DiffieHellman.dh pk sk).AttackerKnows tr :=
  DiffieHellman.attacker_knows_dh pk sk tr hpk hsk

theorem ak_agree {tr : ExecTrace} {skA skB : Bytes}
    (hpkA : (dhPk skA).AttackerKnows tr) (hskB : skB.AttackerKnows tr) :
    (agree (dhPk skB) skA).AttackerKnows tr := by
  rw [agree_comm skB skA]; unfold PQXDH.agree; rw [normalizeX25519Key_dhPk]; exact ak_dh hpkA hskB

theorem ak_agree_direct {tr : ExecTrace} {skA skB : Bytes}
    (hpkB : (dhPk skB).AttackerKnows tr) (hskA : skA.AttackerKnows tr) :
    (agree (dhPk skB) skA).AttackerKnows tr := by
  unfold PQXDH.agree; rw [normalizeX25519Key_dhPk]; exact ak_dh hpkB hskA

theorem ak_kemPk {tr : ExecTrace} {sk : Bytes} (hsk : sk.AttackerKnows tr) :
    (kemPk sk).AttackerKnows tr :=
  Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ tr ⟨sk, rfl, hsk⟩

theorem ak_kemEncap_ct {tr : ExecTrace} {pk e : Bytes}
    (hpk : pk.AttackerKnows tr) (he : e.AttackerKnows tr) :
    (kemEncap pk e).1.AttackerKnows tr :=
  Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge _ tr
    ⟨pk, e, (kemEncap pk e).2, rfl, hpk, he⟩

theorem ak_kemEncap_ss {tr : ExecTrace} {pk e : Bytes}
    (hpk : pk.AttackerKnows tr) (he : e.AttackerKnows tr) :
    (kemEncap pk e).2.AttackerKnows tr :=
  Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge _ tr
    ⟨pk, e, (kemEncap pk e).1, rfl, hpk, he⟩

theorem ak_kemDecap_ss {tr : ExecTrace} {sk e : Bytes}
    (hsk : sk.AttackerKnows tr) (hct : (kemEncap (kemPk sk) e).1.AttackerKnows tr) :
    (kemEncap (kemPk sk) e).2.AttackerKnows tr :=
  Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge _ tr
    ⟨sk, (kemEncap (kemPk sk) e).1, (kemDecap_kemEncap sk e).symm, hsk, hct⟩

theorem ak_sign {tr : ExecTrace} {sk n m : Bytes}
    (hsk : sk.AttackerKnows tr) (hn : n.AttackerKnows tr) (hm : m.AttackerKnows tr) :
    (Signature.sign sk n m).AttackerKnows tr :=
  Bytes.AttackerKnows.prove Signature.sign.attackerKnowledge _ tr
    (by rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred]; exact ⟨sk, n, m, rfl, hsk, hn, hm⟩)

theorem ak_hmac {tr : ExecTrace} {k m : Bytes}
    (hk : k.AttackerKnows tr) (hm : m.AttackerKnows tr) :
    (hmac k m).AttackerKnows tr :=
  KdfExtract.attacker_knows_kdfExtract k m tr hk hm

theorem ak_symEnc {tr : ExecTrace} {k iv m : Bytes}
    (hk : k.AttackerKnows tr) (hiv : iv.AttackerKnows tr) (hm : m.AttackerKnows tr) :
    (SymEnc.symEnc k iv m).AttackerKnows tr :=
  Bytes.AttackerKnows.prove SymEnc.symEnc.attackerKnowledge _ tr ⟨k, iv, m, rfl, hk, hiv, hm⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem ak_spqrInit {tr : ExecTrace} {authKey params : Bytes}
    (hk : authKey.AttackerKnows tr) (hp : params.AttackerKnows tr) :
    (Spqr.spqrInit authKey params).AttackerKnows tr :=
  Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ tr ⟨authKey, params, rfl, hk, hp⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem ak_spqrSendKey {tr : ExecTrace} {st coins : Bytes}
    (hst : st.AttackerKnows tr) (hc : coins.AttackerKnows tr) :
    (Spqr.spqrSend st coins).2.1.AttackerKnows tr :=
  Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ tr ⟨st, coins, rfl, hst, hc⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem ak_spqrSendMsg {tr : ExecTrace} {st coins : Bytes}
    (hst : st.AttackerKnows tr) (hc : coins.AttackerKnows tr) :
    (Spqr.spqrSend st coins).2.2.AttackerKnows tr :=
  Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ tr ⟨st, coins, rfl, hst, hc⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem ak_trWireMsg {tr : ExecTrace} (v : UInt8) {rk : Bytes} (n pn : UInt32) {ct pq : Bytes}
    (enc : TrWire.EncodingVariation)
    (hrk : rk.AttackerKnows tr) (hct : ct.AttackerKnows tr) (hpq : pq.AttackerKnows tr) :
    (TrWire.trWireMsg v rk n pn ct pq enc).AttackerKnows tr :=
  Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ tr
    ⟨⟨v, rk, n, pn, ct, pq, enc⟩, rfl, hrk, hct, hpq⟩

theorem ak_hkdf1 {tr : ExecTrace} {prk info : Bytes}
    (hp : prk.AttackerKnows tr) (hi : info.AttackerKnows tr) :
    (hkdfBlock1 prk info).AttackerKnows tr :=
  ak_hmac hp (ak_concat hi (ak_lit _))

theorem ak_hkdf2 {tr : ExecTrace} {prk info : Bytes}
    (hp : prk.AttackerKnows tr) (hi : info.AttackerKnows tr) :
    (hkdfBlock2 prk info).AttackerKnows tr :=
  ak_hmac hp (ak_concat (ak_hkdf1 hp hi) (ak_concat hi (ak_lit _)))

theorem ak_hkdf3 {tr : ExecTrace} {prk info : Bytes}
    (hp : prk.AttackerKnows tr) (hi : info.AttackerKnows tr) :
    (hkdfBlock3 prk info).AttackerKnows tr :=
  ak_hmac hp (ak_concat (ak_hkdf2 hp hi) (ak_concat hi (ak_lit _)))

theorem ak_chain_rk {tr : ExecTrace} {rk sk pk : Bytes}
    (hrk : rk.AttackerKnows tr) (hpk : (dhPk pk).AttackerKnows tr) (hsk : sk.AttackerKnows tr) :
    (createChain rk (dhPk pk) sk).1.AttackerKnows tr := by
  unfold createChain DY.X25519.agree; rw [normalizeX25519Key_dhPk]; exact ak_hkdf1 (ak_hmac hrk (ak_dh hpk hsk)) (ak_lit _)

theorem ak_chain_ck {tr : ExecTrace} {rk sk pk : Bytes}
    (hrk : rk.AttackerKnows tr) (hpk : (dhPk pk).AttackerKnows tr) (hsk : sk.AttackerKnows tr) :
    (createChain rk (dhPk pk) sk).2.AttackerKnows tr := by
  unfold createChain DY.X25519.agree; rw [normalizeX25519Key_dhPk]; exact ak_hkdf2 (ak_hmac hrk (ak_dh hpk hsk)) (ak_lit _)

theorem ak_chain_rk_comm {tr : ExecTrace} {rk s1 s2 : Bytes}
    (hrk : rk.AttackerKnows tr) (hpk2 : (dhPk s2).AttackerKnows tr) (hs1 : s1.AttackerKnows tr) :
    (createChain rk (dhPk s1) s2).1.AttackerKnows tr :=
  (congrArg (fun (p : Bytes × Bytes) => p.1.AttackerKnows tr) (createChain_comm rk s1 s2)).mpr
    (ak_chain_rk hrk hpk2 hs1)

theorem ak_chain_ck_comm {tr : ExecTrace} {rk s1 s2 : Bytes}
    (hrk : rk.AttackerKnows tr) (hpk2 : (dhPk s2).AttackerKnows tr) (hs1 : s1.AttackerKnows tr) :
    (createChain rk (dhPk s1) s2).2.AttackerKnows tr :=
  (congrArg (fun (p : Bytes × Bytes) => p.2.AttackerKnows tr) (createChain_comm rk s1 s2)).mpr
    (ak_chain_ck hrk hpk2 hs1)

theorem ak_seed {tr : ExecTrace} {ck : Bytes} (hck : ck.AttackerKnows tr) :
    (kdfCk ck).2.AttackerKnows tr :=
  ak_hmac hck (ak_lit _)

theorem ak_encMsg {tr : ExecTrace} {st : TRState} {coins pq m : Bytes}
    (hcks : st.cks.AttackerKnows tr) (hdhs : (dhPk st.dhs).AttackerKnows tr)
    (hspqr : st.spqr.AttackerKnows tr) (hikS : st.myIk.AttackerKnows tr)
    (hikR : st.peerIk.AttackerKnows tr) (hc : coins.AttackerKnows tr)
    (hpq : pq.AttackerKnows tr) (hm : m.AttackerKnows tr) :
    (encMsg st coins pq m).AttackerKnows tr := by
  have hpqM : (Spqr.spqrSend st.spqr coins).2.2.AttackerKnows tr := ak_spqrSendMsg hspqr hc
  have hprk : (hmac pq (kdfCk st.cks).2).AttackerKnows tr := ak_hmac hpq (ak_seed hcks)
  let keys := trMsgKeys pq (kdfCk st.cks).2
  have hct : (SymEnc.symEnc keys.cipherKey keys.iv m).AttackerKnows tr :=
    ak_symEnc (ak_hkdf1 hprk (ak_lit _)) (ak_hkdf3 hprk (ak_lit _)) hm
  have hwire : (trHonestWireMsg (dhPk st.dhs) st.ns st.pn
      (SymEnc.symEnc keys.cipherKey keys.iv m) (Spqr.spqrSend st.spqr coins).2.2).AttackerKnows tr :=
    ak_trWireMsg _ _ _ _ hdhs hct hpqM
  exact ak_concat hwire (ak_trunc8 (ak_hmac (ak_hkdf2 hprk (ak_lit _))
    (ak_concat hikS (ak_concat hikR hwire))))

theorem ak_pqxdhIkm {tr : ExecTrace} {dh1 dh2 dh3 ss : Bytes} {dh4 : Option Bytes}
    (h1 : dh1.AttackerKnows tr) (h2 : dh2.AttackerKnows tr) (h3 : dh3.AttackerKnows tr)
    (h4 : match dh4 with | none => True | some d => d.AttackerKnows tr)
    (hss : ss.AttackerKnows tr) :
    (pqxdhIkm dh1 dh2 dh3 dh4 ss).AttackerKnows tr := by
  cases dh4 with
  | none =>
    exact ak_concat (ak_lit _) (ak_concat h1 (ak_concat h2 (ak_concat h3 hss)))
  | some d =>
    exact ak_concat (ak_lit _) (ak_concat h1 (ak_concat h2 (ak_concat h3 (ak_concat h4 hss))))

theorem ak_pqxdhKdf_rk {tr : ExecTrace} {ikm : Bytes} (hikm : ikm.AttackerKnows tr) :
    (pqxdhKdf ikm).rk.AttackerKnows tr :=
  ak_hkdf1 (ak_hmac (ak_lit _) hikm) (ak_lit _)

theorem ak_pqxdhKdf_ck {tr : ExecTrace} {ikm : Bytes} (hikm : ikm.AttackerKnows tr) :
    (pqxdhKdf ikm).ck.AttackerKnows tr :=
  ak_hkdf2 (ak_hmac (ak_lit _) hikm) (ak_lit _)

theorem ak_pqxdhKdf_pqr {tr : ExecTrace} {ikm : Bytes} (hikm : ikm.AttackerKnows tr) :
    (pqxdhKdf ikm).pqr.AttackerKnows tr :=
  ak_hkdf3 (ak_hmac (ak_lit _) hikm) (ak_lit _)

theorem ak_pqxdhKdf_block {tr : ExecTrace} {ikm : Bytes} (hikm : ikm.AttackerKnows tr)
    {k : Bytes} (hk : IsHandshakeBlock (pqxdhKdf ikm) k) :
    k.AttackerKnows tr := by
  rcases hk with rfl | rfl | rfl
  · exact ak_pqxdhKdf_rk hikm
  · exact ak_pqxdhKdf_ck hikm
  · exact ak_pqxdhKdf_pqr hikm

theorem ak_pqxdhRk {tr : ExecTrace} {dh1 dh2 dh3 ss : Bytes}
    (h1 : dh1.AttackerKnows tr) (h2 : dh2.AttackerKnows tr)
    (h3 : dh3.AttackerKnows tr) (hss : ss.AttackerKnows tr) :
    (pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss)).rk.AttackerKnows tr :=
  ak_pqxdhKdf_rk (ak_pqxdhIkm h1 h2 h3 trivial hss)

theorem ak_pqxdhCk {tr : ExecTrace} {dh1 dh2 dh3 ss : Bytes}
    (h1 : dh1.AttackerKnows tr) (h2 : dh2.AttackerKnows tr)
    (h3 : dh3.AttackerKnows tr) (hss : ss.AttackerKnows tr) :
    (pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss)).ck.AttackerKnows tr :=
  ak_pqxdhKdf_ck (ak_pqxdhIkm h1 h2 h3 trivial hss)

theorem ak_pqxdhPqr {tr : ExecTrace} {dh1 dh2 dh3 ss : Bytes}
    (h1 : dh1.AttackerKnows tr) (h2 : dh2.AttackerKnows tr)
    (h3 : dh3.AttackerKnows tr) (hss : ss.AttackerKnows tr) :
    (pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss)).pqr.AttackerKnows tr :=
  ak_pqxdhKdf_pqr (ak_pqxdhIkm h1 h2 h3 trivial hss)

/-- Attacker knowledge of `aliceAgreement` input key material from responder secret keys
(`ikB`, `spkSk`, `pqSk`, and optional `opkSk`), public keys, and KEM ciphertext. -/
theorem ak_aliceAgreement_ikm_of_responderSecrets {tr : ExecTrace}
    {ikA ek ikB spkSk pqSk e : Bytes} {opkSk : Option Bytes}
    (hikA : (dhPk ikA).AttackerKnows tr) (hek : (dhPk ek).AttackerKnows tr)
    (hikB : ikB.AttackerKnows tr) (hspk : spkSk.AttackerKnows tr) (hpq : pqSk.AttackerKnows tr)
    (hopk : match opkSk with | none => True | some sk => sk.AttackerKnows tr)
    (hct : (kemEncap (kemPk pqSk) e).1.AttackerKnows tr) :
    (pqxdhIkm (agree (dhPk spkSk) ikA) (agree (dhPk ikB) ek) (agree (dhPk spkSk) ek)
      ((opkSk.map dhPk).map (agree · ek)) (kemEncap (kemPk pqSk) e).2).AttackerKnows tr := by
  refine ak_pqxdhIkm (ak_agree hikA hspk) (ak_agree hek hikB) (ak_agree hek hspk) ?_
    (ak_kemDecap_ss hpq hct)
  cases opkSk with
  | none => trivial
  | some sk => exact ak_agree hek hopk

theorem ak_aliceAgreement_block_of_responderSecrets {tr : ExecTrace}
    {ikA ek ikB spkSk pqSk e : Bytes} {opkSk : Option Bytes}
    (hikA : (dhPk ikA).AttackerKnows tr) (hek : (dhPk ek).AttackerKnows tr)
    (hikB : ikB.AttackerKnows tr) (hspk : spkSk.AttackerKnows tr) (hpq : pqSk.AttackerKnows tr)
    (hopk : match opkSk with | none => True | some sk => sk.AttackerKnows tr)
    (hct : (kemEncap (kemPk pqSk) e).1.AttackerKnows tr)
    {k : Bytes}
    (hk : IsHandshakeBlock
      (aliceAgreement ikA ek (dhPk ikB) (dhPk spkSk) (kemPk pqSk) (opkSk.map dhPk) e).2 k) :
    k.AttackerKnows tr :=
  ak_pqxdhKdf_block
    (ak_aliceAgreement_ikm_of_responderSecrets hikA hek hikB hspk hpq hopk hct) hk

/-- Attacker knowledge of `aliceAgreement` input key material from initiator secret keys
(`ikA`, `ek`), Kyber secret `pqSk`, responder public keys, and KEM ciphertext. -/
theorem ak_aliceAgreement_ikm_of_initiatorSecrets {tr : ExecTrace}
    {ikA ek ikB spkSk pqSk e : Bytes} {opkSk : Option Bytes}
    (hikA : ikA.AttackerKnows tr) (hek : ek.AttackerKnows tr)
    (hikB : (dhPk ikB).AttackerKnows tr) (hspk : (dhPk spkSk).AttackerKnows tr)
    (hpq : pqSk.AttackerKnows tr)
    (hopk : match opkSk with | none => True | some sk => (dhPk sk).AttackerKnows tr)
    (hct : (kemEncap (kemPk pqSk) e).1.AttackerKnows tr) :
    (pqxdhIkm (agree (dhPk spkSk) ikA) (agree (dhPk ikB) ek) (agree (dhPk spkSk) ek)
      ((opkSk.map dhPk).map (agree · ek)) (kemEncap (kemPk pqSk) e).2).AttackerKnows tr := by
  refine ak_pqxdhIkm (ak_agree_direct hspk hikA) (ak_agree_direct hikB hek)
    (ak_agree_direct hspk hek) ?_ (ak_kemDecap_ss hpq hct)
  cases opkSk with
  | none => trivial
  | some sk => exact ak_agree_direct hopk hek

theorem ak_aliceAgreement_block_of_initiatorSecrets {tr : ExecTrace}
    {ikA ek ikB spkSk pqSk e : Bytes} {opkSk : Option Bytes}
    (hikA : ikA.AttackerKnows tr) (hek : ek.AttackerKnows tr)
    (hikB : (dhPk ikB).AttackerKnows tr) (hspk : (dhPk spkSk).AttackerKnows tr)
    (hpq : pqSk.AttackerKnows tr)
    (hopk : match opkSk with | none => True | some sk => (dhPk sk).AttackerKnows tr)
    (hct : (kemEncap (kemPk pqSk) e).1.AttackerKnows tr)
    {k : Bytes}
    (hk : IsHandshakeBlock
      (aliceAgreement ikA ek (dhPk ikB) (dhPk spkSk) (kemPk pqSk) (opkSk.map dhPk) e).2 k) :
    k.AttackerKnows tr :=
  ak_pqxdhKdf_block
    (ak_aliceAgreement_ikm_of_initiatorSecrets hikA hek hikB hspk hpq hopk hct) hk

/-! ## Forged-Bundle `aliceStart` and Forged-Message-0 `bobStart` -/

abbrev advSpkSk : Bytes := lit "adv-spk-secret-key-32-bytes-0001"
abbrev advPqSk : Bytes := lit "adv-pq-secret-key-64-bytes-00001-padding-for-mlkem1024-seed-0001"
abbrev advSpkNonce : Bytes := lit "adv-spk-xeddsa-nonce-64-bytes-01-padding-for-signature-nonce-001"
abbrev advPqNonce : Bytes := lit "adv-pq-xeddsa-nonce-64-bytes-002-padding-for-signature-nonce-002"
abbrev advEkSk : Bytes := lit "adv-ephemeral-ek-32-bytes-000001"
abbrev advEntropy : Bytes := lit "adv-kem-encap-entropy-32-bytes-1"
abbrev advDhsA : Bytes := lit "adv-ratchet-secret-32-bytes-0001"
abbrev advCoins : Bytes := lit "adv-spqr-send-coins-64-bytes-001-padding-for-spqr-encap-coins-01"
abbrev advPlain : Bytes := lit "adv-initial-plaintext-32-bytes-1"

/-- Appends an attacker-forged prekey bundle (`dhPk advSpkSk` and `kemPk advPqSk`, both signed under
leaked/inverted identity secret `ikB`) to `tr`. -/
def forgedBundlePrefix (tr : ExecTrace) (ikB : Bytes) : ExecTrace :=
  (((tr.append (NetE (dhPk advSpkSk))).append
    (NetE (Signature.sign ikB advSpkNonce (encodeEC (dhPk advSpkSk))))).append
    (NetE (kemPk advPqSk))).append
    (NetE (Signature.sign ikB advPqNonce (encodeKEM (kemPk advPqSk))))

def forgedBundleHandles (tr : ExecTrace) : BundleHandles :=
  let n := tr.length
  { spk := n, spkSig := n + 1, pqpk := n + 2, pqpkSig := n + 3, opk := none }

theorem forgedBundlePrefix_reach {tr : ExecTrace} {ikB : Bytes} {ikIdx : Nat}
    (hr : tr.Reachable reachability)
    (h1 : (tr.append (NetE (dhPk advSpkSk))).at? ikIdx = some (NetE ikB))
    (h3 : (((tr.append (NetE (dhPk advSpkSk))).append
      (NetE (Signature.sign ikB advSpkNonce (encodeEC (dhPk advSpkSk))))).append
      (NetE (kemPk advPqSk))).at? ikIdx = some (NetE ikB)) :
    (forgedBundlePrefix tr ikB).Reachable reachability := by
  have r1 := sendAttacker_reach hr (b := dhPk advSpkSk) (ak_dhPk (ak_lit _))
  have r2 := sendAttacker_reach r1
    (b := Signature.sign ikB advSpkNonce (encodeEC (dhPk advSpkSk)))
    (ak_sign (ak_net h1) (ak_lit _) (ak_concat (ak_lit _) (ak_dhPk (ak_lit _))))
  have r3 := sendAttacker_reach r2 (b := kemPk advPqSk) (ak_kemPk (ak_lit _))
  exact sendAttacker_reach r3
    (b := Signature.sign ikB advPqNonce (encodeKEM (kemPk advPqSk)))
    (ak_sign (ak_net h3) (ak_lit _) (ak_concat (ak_lit _) (ak_kemPk (ak_lit _))))

theorem Runs.aliceStart_forged {tr : ExecTrace} {a b : Participant} {idH regB : Nat}
    {ikA ikB : Bytes} {honest : Bool}
    (hid : (forgedBundlePrefix tr ikB).at? idH = some (StP a { kind := .identity, sk := ikA }))
    (hreg : (forgedBundlePrefix tr ikB).at? regB =
      some (EvP (.IdentityRegistered b (dhPk ikB) (Signature.vk ikB) honest)))
    (hspk : (forgedBundlePrefix tr ikB).at? tr.length = some (NetE (dhPk advSpkSk)))
    (hspkSig : (forgedBundlePrefix tr ikB).at? (tr.length + 1) =
      some (NetE (Signature.sign ikB advSpkNonce (encodeEC (dhPk advSpkSk)))))
    (hpq : (forgedBundlePrefix tr ikB).at? (tr.length + 2) = some (NetE (kemPk advPqSk)))
    (hpqSig : (forgedBundlePrefix tr ikB).at? (tr.length + 3) =
      some (NetE (Signature.sign ikB advPqNonce (encodeKEM (kemPk advPqSk))))) :
    Runs (Composed.aliceStart a b idH regB (forgedBundleHandles tr)) (forgedBundlePrefix tr ikB)
      ((forgedBundlePrefix tr ikB).length + 8)
      (aliceTr (forgedBundlePrefix tr ikB) a b ikA (dhPk ikB) (dhPk advSpkSk) (kemPk advPqSk)) :=
  Runs.aliceStart hid hreg hspk hspkSig hpq hpqSig
    (Signature.verify_sign _ _ _) (Signature.verify_sign _ _ _) rfl (x25519LowOrder_dhPk advSpkSk)

/-- Handshake keys and KEM ciphertext of an attacker-forged message 0 to Bob (`advEkSk`,
`advEntropy`). -/
abbrev forgedBobKeys (ikA ikB spkB pqskB : Bytes) : HandshakeKeys :=
  (aliceAgreement ikA advEkSk (dhPk ikB) (dhPk spkB) (kemPk pqskB) none advEntropy).2

abbrev forgedBobCt (ikA ikB spkB pqskB : Bytes) : Bytes :=
  (aliceAgreement ikA advEkSk (dhPk ikB) (dhPk spkB) (kemPk pqskB) none advEntropy).1

/-- Fake initiator `TRState` used by the attacker to construct a valid inner Triple Ratchet message 0
for `Composed.bobStart`. -/
def stFakeMsg0 (ikAPk ikBPk spkPk : Bytes) (keys : HandshakeKeys) : TRState :=
  { peer := "bob", myIk := serializedIk ikAPk, peerIk := serializedIk ikBPk,
    rk := (createChain keys.rk spkPk advDhsA).1, dhs := advDhsA,
    cks := (createChain keys.rk spkPk advDhsA).2, ns := 0, pn := 0,
    sid := concat (dhPk advDhsA) keys.rk, initiator := true, rIdx := 1,
    recv := [{ ratchetKey := spkPk, chainKey := keys.ck, index := 0, rIdx := 1 }],
    spqr := Spqr.spqrInit keys.pqr spqrA2B }

def forgedSpqrKey (keys : HandshakeKeys) : Bytes :=
  (Spqr.spqrSend (Spqr.spqrInit keys.pqr spqrA2B) advCoins).2.1

def forgedSpqrMsg (keys : HandshakeKeys) : Bytes :=
  (Spqr.spqrSend (Spqr.spqrInit keys.pqr spqrA2B) advCoins).2.2

def forgedPreKeyStage2 (tr : ExecTrace) (ikA ikB spkB pqskB : Bytes) : ExecTrace :=
  (tr.append (NetE (dhPk advEkSk))).append (NetE (forgedBobCt ikA ikB spkB pqskB))

/-- Appends a forged 3-message `PreKeySignalMessage` (`ek`, `ct`, `encMsg`) to `tr`. -/
def forgedPreKeyPrefix (tr : ExecTrace) (ikA ikB spkB pqskB : Bytes) : ExecTrace :=
  let keys := forgedBobKeys ikA ikB spkB pqskB
  let st := stFakeMsg0 (dhPk ikA) (dhPk ikB) (dhPk spkB) keys
  (forgedPreKeyStage2 tr ikA ikB spkB pqskB).append
    (NetE (encMsg st advCoins (forgedSpqrKey keys) advPlain))

def forgedMsgHandles (tr : ExecTrace) : PreKeyMsgHandles :=
  let n := tr.length
  { ek := n, ct := n + 1, msg := n + 2 }

theorem ak_forgedBobKeys_ikm {tr : ExecTrace} {ikA ikB spkB pqskB : Bytes}
    (hdh1 : (agree (dhPk spkB) ikA).AttackerKnows tr)
    (hikB : (dhPk ikB).AttackerKnows tr) (hspk : (dhPk spkB).AttackerKnows tr)
    (hpq : (kemPk pqskB).AttackerKnows tr) :
    (pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) advEkSk) (agree (dhPk spkB) advEkSk)
      none (kemEncap (kemPk pqskB) advEntropy).2).AttackerKnows tr :=
  ak_pqxdhIkm hdh1 (ak_agree_direct hikB (ak_lit _)) (ak_agree_direct hspk (ak_lit _)) trivial
    (ak_kemEncap_ss hpq (ak_lit _))

theorem ak_forgedBobKeys_block {tr : ExecTrace} {ikA ikB spkB pqskB : Bytes}
    (hdh1 : (agree (dhPk spkB) ikA).AttackerKnows tr)
    (hikB : (dhPk ikB).AttackerKnows tr) (hspk : (dhPk spkB).AttackerKnows tr)
    (hpq : (kemPk pqskB).AttackerKnows tr)
    {k : Bytes} (hk : IsHandshakeBlock (forgedBobKeys ikA ikB spkB pqskB) k) :
    k.AttackerKnows tr :=
  ak_pqxdhKdf_block (ak_forgedBobKeys_ikm hdh1 hikB hspk hpq) hk

theorem forgedPreKeyPrefix_reach {tr : ExecTrace} {ikA ikB spkB pqskB : Bytes}
    {pqIdx ikAIdx ikBIdx spkIdx : Nat}
    (hr : tr.Reachable reachability)
    (hpq1 : (tr.append (NetE (dhPk advEkSk))).at? pqIdx = some (NetE (kemPk pqskB)))
    (hdh1 : (agree (dhPk spkB) ikA).AttackerKnows (forgedPreKeyStage2 tr ikA ikB spkB pqskB))
    (hikA2 : (forgedPreKeyStage2 tr ikA ikB spkB pqskB).at? ikAIdx = some (NetE (dhPk ikA)))
    (hikB2 : (forgedPreKeyStage2 tr ikA ikB spkB pqskB).at? ikBIdx = some (NetE (dhPk ikB)))
    (hspk2 : (forgedPreKeyStage2 tr ikA ikB spkB pqskB).at? spkIdx = some (NetE (dhPk spkB)))
    (hpq2 : (forgedPreKeyStage2 tr ikA ikB spkB pqskB).at? pqIdx = some (NetE (kemPk pqskB))) :
    (forgedPreKeyPrefix tr ikA ikB spkB pqskB).Reachable reachability := by
  have r1 := sendAttacker_reach hr (b := dhPk advEkSk) (ak_dhPk (ak_lit _))
  have r2 := sendAttacker_reach r1 (b := forgedBobCt ikA ikB spkB pqskB)
    (ak_kemEncap_ct (ak_net hpq1) (ak_lit _))
  have hikm := ak_forgedBobKeys_ikm hdh1 (ak_net hikB2) (ak_net hspk2) (ak_net hpq2)
  have hrk := ak_pqxdhKdf_rk hikm
  have hpqr := ak_pqxdhKdf_pqr hikm
  let keys := forgedBobKeys ikA ikB spkB pqskB
  let st := stFakeMsg0 (dhPk ikA) (dhPk ikB) (dhPk spkB) keys
  have hspqr : st.spqr.AttackerKnows (forgedPreKeyStage2 tr ikA ikB spkB pqskB) :=
    ak_spqrInit hpqr (ak_lit _)
  have hcks : st.cks.AttackerKnows (forgedPreKeyStage2 tr ikA ikB spkB pqskB) :=
    ak_chain_ck hrk (ak_net hspk2) (ak_lit _)
  have hpqKey : (forgedSpqrKey keys).AttackerKnows (forgedPreKeyStage2 tr ikA ikB spkB pqskB) :=
    ak_spqrSendKey hspqr (ak_lit _)
  exact sendAttacker_reach r2
    (b := encMsg st advCoins (forgedSpqrKey keys) advPlain)
    (ak_encMsg hcks (ak_dhPk (ak_lit _)) hspqr
      (ak_concat (ak_lit _) (ak_net hikA2)) (ak_concat (ak_lit _) (ak_net hikB2))
      (ak_lit _) hpqKey (ak_lit _))

/-- Trace produced when Bob accepts `forgedPreKeyPrefix` via `Composed.bobStart`. -/
def forgedBobStartTr (trPre : ExecTrace) (b a : Participant) (ikA ikB spkB pqskB : Bytes) :
    ExecTrace :=
  let keys := forgedBobKeys ikA ikB spkB pqskB
  let stS := stFakeMsg0 (dhPk ikA) (dhPk ikB) (dhPk spkB) keys
  let pqKey := forgedSpqrKey keys
  let pqm := forgedSpqrMsg keys
  let sig := encSig stS advCoins pqKey advPlain
  let dhsB1 := rnd trPre.length 32
  let stB00 := bobSt0 a ikB spkB (dhPk ikA) keys sig
  let st' := (ratchetState stB00 (dhPk advDhsA) dhsB1).1
  let c := (ratchetState stB00 (dhPk advDhsA) dhsB1).2
  let c' : RecvChain := { c with chainKey := (kdfCk c.chainKey).1, index := 1 }
  let seed := (kdfCk c.chainKey).2
  let stOut : TRState :=
    { st' with recv := [c'], spqr := recvSt (Spqr.spqrInit keys.pqr spqrB2A) pqm }
  let o := bobOut ikB spkB pqskB (dhPk ikA) (dhPk advEkSk) (forgedBobCt ikA ikB spkB pqskB) keys
  let tr1 := (trPre.append (RndE 32)).append (NetE pqKey)
  let tr5 := (((tr1.append
      (EvP (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
      (EvT (.DHRatchet b st'.peer (dhPk advDhsA) (dhPk st'.dhs)))).append
      (EvT (.HonestDH (st'.sessionInfo b) st'.dhs (st'.rIdx - 2)))).append
      (EvC (.HandshakeSession (st'.sessionInfo b) tr1.length))
  let child := tr5.length + 2
  ((tr5.append (EvT (.Received b st'.peer (dhPk advDhsA) 0 advPlain))).append
    (EvT (.MessageKey (st'.sessionInfo b) .receiver seed pqKey 0 c.rIdx
      child))).append
    (StT b stOut)

theorem Runs.bobStart_forged {tr : ExecTrace} {b a : Participant} {kh : BobKeyHandles} {regA : Nat}
    {ikA ikB spkB pqskB : Bytes} {honest : Bool}
    (hik : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? kh.ik =
      some (StP b { kind := .identity, sk := ikB }))
    (hspk : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? kh.spk =
      some (StP b { kind := .signedPrekey, sk := spkB }))
    (hpqk : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? kh.pqspk =
      some (StP b { kind := .pqPrekey, sk := pqskB }))
    (hopk : kh.opk = none)
    (hreg : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? regA =
      some (EvP (.IdentityRegistered a (dhPk ikA) (Signature.vk ikA) honest)))
    (hek : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? tr.length =
      some (NetE (dhPk advEkSk)))
    (hct : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? (tr.length + 1) =
      some (NetE (forgedBobCt ikA ikB spkB pqskB)))
    (hmsg : (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? (tr.length + 2) =
      some (NetE (encMsg (stFakeMsg0 (dhPk ikA) (dhPk ikB) (dhPk spkB)
        (forgedBobKeys ikA ikB spkB pqskB))
        advCoins (forgedSpqrKey (forgedBobKeys ikA ikB spkB pqskB)) advPlain)))
    (hpq : (((forgedPreKeyPrefix tr ikA ikB spkB pqskB).append (RndE 32)).append
      (NetE (forgedSpqrKey (forgedBobKeys ikA ikB spkB pqskB)))).at? (tr.length + 4) =
      some (NetE (forgedSpqrKey (forgedBobKeys ikA ikB spkB pqskB)))) :
    Runs (Composed.bobStart b a kh regA (forgedMsgHandles tr) (tr.length + 4) 1)
      (forgedPreKeyPrefix tr ikA ikB spkB pqskB)
      ((forgedPreKeyPrefix tr ikA ikB spkB pqskB).length + 8)
      (forgedBobStartTr (forgedPreKeyPrefix tr ikA ikB spkB pqskB) b a ikA ikB spkB pqskB) := by
  let keys := forgedBobKeys ikA ikB spkB pqskB
  let stS := stFakeMsg0 (dhPk ikA) (dhPk ikB) (dhPk spkB) keys
  let pqKey := forgedSpqrKey keys
  let pqm := forgedSpqrMsg keys
  let sig := encSig stS advCoins pqKey advPlain
  let trPre := forgedPreKeyPrefix tr ikA ikB spkB pqskB
  let dhsB1 := rnd trPre.length 32
  let stB00 := bobSt0 a ikB spkB (dhPk ikA) keys sig
  let st' := (ratchetState stB00 (dhPk advDhsA) dhsB1).1
  let c := (ratchetState stB00 (dhPk advDhsA) dhsB1).2
  let c' : RecvChain := { c with chainKey := (kdfCk c.chainKey).1, index := 1 }
  let seed := (kdfCk c.chainKey).2
  let stOut : TRState :=
    { st' with recv := [c'], spqr := recvSt (Spqr.spqrInit keys.pqr spqrB2A) pqm }
  have hset : setRecvChain st'.recv c' = [c'] := by
    simp [setRecvChain, st', ratchetState, c', c, stB00, bobSt0, maxReceiverChains]
  have hseed : (kdfCk stS.cks).2 = seed := by
    show (kdfCk (createChain keys.rk (dhPk spkB) advDhsA).2).2 =
      (kdfCk (createChain keys.rk (dhPk advDhsA) spkB).2).2
    rw [createChain_comm keys.rk advDhsA spkB]
  have hrecv : Spqr.spqrRecv st'.spqr pqm 1 =
      some (recvSt (Spqr.spqrInit keys.pqr spqrB2A) pqm, pqKey) :=
    spqrRecv_init_agree keys.pqr advCoins pqm .b2a (bytesToLiteral_spqrSendMsg _ _)
  exact runs_cast (Runs.bobStart (keys := keys) (msg := sig)
    (t := encMsg stS advCoins pqKey advPlain) (st' := st') (c := c) (c' := c') (seed := seed)
    (pq := pqKey) (m := advPlain)
    hik hspk hpqk hopk hreg hek hct (isCanonicalKey_dhPk advEkSk)
    (bobAgreement_honest ikA advEkSk ikB spkB pqskB advEntropy)
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk advDhsA) rfl rfl hrecv hpq
    (mac_ok hseed rfl rfl) (dec_ok hseed) (stOut := stOut) (by rw [hset]))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; dsimp only [forgedBobStartTr]; simp only [append_len]; rfl)

/-! ## Event-Filtering Helpers and Concrete Witness Traces -/

abbrev isCompIK : PQXDHEvent → Bool := fun | .CompromisedIK .. => true | _ => false
abbrev isCompIkOf (p : Participant) : PQXDHEvent → Bool :=
  fun | .CompromisedIK p' _ => p' == p | _ => false
abbrev isCompSPK : PQXDHEvent → Bool := fun | .CompromisedSPK .. => true | _ => false
abbrev isCompPQ : PQXDHEvent → Bool := fun | .CompromisedPQSPK .. => true | _ => false
abbrev isCompOPK : PQXDHEvent → Bool := fun | .CompromisedOPK .. => true | _ => false
abbrev isBrokenDH : PQXDHEvent → Bool := fun | .BrokenDH => true | _ => false
abbrev isBrokenKEM : PQXDHEvent → Bool := fun | .BrokenKEM => true | _ => false

def isAnyTRExposure : TREvent → Bool
  | .ExposedDHs .. | .ExposedRK .. | .ExposedCKs .. | .ExposedCKr .. | .ExposedMK ..
  | .ExposedSpqr .. => true
  | _ => false

def trEvIdx (tr : ExecTrace) (p : TREvent → Bool) : List Nat :=
  (List.range tr.length).filter fun i =>
    match tr.getEventAt TREvent i with | some e => p e | none => false

theorem mem_trEvIdx {tr : ExecTrace} {p : TREvent → Bool} {e : TREvent} {i : Nat}
    (h : tr.EventLoggedAt e i) (hp : p e = true) : i ∈ trEvIdx tr p := by
  have hl := Trace.EventLoggedAt_implies_i_le_length e i tr h
  rw [Trace.EventLoggedAt_eq_getEventAt] at h
  simp only [trEvIdx, List.mem_filter, List.mem_range, h, hp, and_self, hl]

theorem not_tr_logged {tr : ExecTrace} {p : TREvent → Bool} (hidx : trEvIdx tr p = [])
    {e : TREvent} (hp : p e = true) : ¬ tr.EventLogged e :=
  fun ⟨_, hi⟩ => List.not_mem_nil (hidx ▸ mem_trEvIdx hi hp)

theorem not_sessionStateExposed_of_no_trExposure {tr : ExecTrace}
    (hidx : trEvIdx tr isAnyTRExposure = []) (keys : HandshakeKeys) (k : Bytes) :
    ¬ SessionStateExposed tr keys k := by
  rintro ⟨s, j, _, _, ⟨_, sp, r, h⟩ | ⟨_, n, r, h⟩ | ⟨_, n, r, h⟩ | ⟨_, r, h⟩⟩
  · exact not_tr_logged hidx (e := .ExposedSpqr s sp r) rfl h
  · exact not_tr_logged hidx (e := .ExposedCKr s keys.ck n r) rfl h
  · exact not_tr_logged hidx (e := .ExposedCKs s keys.ck n r) rfl h
  · exact not_tr_logged hidx (e := .ExposedRK s keys.rk r) rfl h

theorem logged_after_of_singleton {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {i k : Nat} (hidx : evIdx tr p = [k]) (hp : p e = true)
    (hik : i < k) : ∀ j, tr.EventLoggedAt e j → i < j := by
  intro j hj; have hm := mem_evIdx hj hp; rw [hidx, List.mem_singleton] at hm; omega

theorem not_loggedBefore_of_singleton {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {i k : Nat} (hidx : evIdx tr p = [k]) (hp : p e = true)
    (hik : i ≤ k) : ¬ LoggedBefore e i tr := by
  rintro ⟨j, hj, hlt⟩; have hm := mem_evIdx hj hp; rw [hidx, List.mem_singleton] at hm; omega

theorem not_loggedBefore_of_none {tr : ExecTrace} {p : PQXDHEvent → Bool}
    {e : PQXDHEvent} {i : Nat} (hidx : evIdx tr p = []) (hp : p e = true) :
    ¬ LoggedBefore e i tr := fun ⟨j, hj, _⟩ => not_logged hidx hp ⟨j, hj⟩

private theorem le_trans {a b c : ExecTrace} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Trace.le_trans a b c h1 h2

private theorem at?_idx_eq {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i j : Nat} {x : E}
    (h : tr.at? i = some x) (hij : i = j) : tr.at? j = some x := hij ▸ h

private theorem eventLoggedAt_idx_eq {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev : Ev} {i j : Nat} (h : tr.EventLoggedAt ev i) (hij : i = j) :
    tr.EventLoggedAt ev j := hij ▸ h

private theorem le_aliceTrOpt {t0 tr : ExecTrace} (h : t0 ≤ tr) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    t0 ≤ aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk := by
  dsimp only [aliceTrOpt]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le h _) _) _) _) _) _) _) _) _

private theorem le_encTr {t0 tr : ExecTrace} (h : t0 ≤ tr) (me : Participant) (stH : Nat)
    (st : TRState) (pq : Bytes) : t0 ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le h _) _) _) _) _) _) _

private theorem le_forgedBobStartTr {t0 trPre : ExecTrace} (h : t0 ≤ trPre) (b a : Participant)
    (ikA ikB spkB pqskB : Bytes) :
    t0 ≤ forgedBobStartTr trPre b a ikA ikB spkB pqskB := by
  dsimp only [forgedBobStartTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le h _) _) _) _) _) _) _) _) _

private theorem evIdx_nil (p : PQXDHEvent → Bool) : evIdx Trace.nil p = [] := by
  unfold evIdx; rw [nil_len]; rfl

private theorem evIdx_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    evIdx (tr.append x) p = evIdx tr p := by
  unfold evIdx
  rw [append_len, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr x (List.mem_range.mp hi)]

private theorem evIdx_append_ev (tr : ExecTrace) (ev : PQXDHEvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvP ev)) p = cond (p ev) (evIdx tr p ++ [tr.length]) (evIdx tr p) := by
  unfold evIdx
  rw [append_len, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
        decide),
      List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]),
      List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)])

private theorem evIdx_append_ev_net (tr : ExecTrace) (ev : PQXDHEvent) (x : Bytes)
    (p : PQXDHEvent → Bool) (hp : p ev = true) :
    evIdx ((tr.append (EvP ev)).append (NetE x)) p = evIdx tr p ++ [tr.length] := by
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_ev, hp]; rfl

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

private theorem evIdx_forgedBobStartTr_false (trPre : ExecTrace) (b a : Participant)
    (ikA ikB spkB pqskB : Bytes) (p : PQXDHEvent → Bool)
    (hp : ∀ ikB' ikA' spk' pq' opk' ek' ct' ks',
      p (.BobDone b a ikB' ikA' spk' pq' opk' ek' ct' ks') = false) :
    evIdx (forgedBobStartTr trPre b a ikA ikB spkB pqskB) p = evIdx trPre p := by
  dsimp only [forgedBobStartTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, hp, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]

private theorem trEvIdx_nil : trEvIdx Trace.nil isAnyTRExposure = [] := by
  unfold trEvIdx; rw [nil_len]; rfl

private theorem trEvIdx_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    trEvIdx (tr.append x) isAnyTRExposure = trEvIdx tr isAnyTRExposure := by
  unfold trEvIdx
  rw [append_len, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr x (List.mem_range.mp hi)]

private theorem trEvIdx_append_ev_false (tr : ExecTrace) (ev : TREvent)
    (hp : isAnyTRExposure ev = false) :
    trEvIdx (tr.append (EvT ev)) isAnyTRExposure = trEvIdx tr isAnyTRExposure := by
  unfold trEvIdx
  rw [append_len, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr (EvT ev) (List.mem_range.mp hi)]

private theorem trEvIdx_encTr (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) :
    trEvIdx (encTr tr me stH st pq) isAnyTRExposure = trEvIdx tr isAnyTRExposure := by
  dsimp only [encTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]

private theorem trEvIdx_aliceTrOpt (tr : ExecTrace) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    trEvIdx (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk) isAnyTRExposure =
      trEvIdx tr isAnyTRExposure := by
  dsimp only [aliceTrOpt]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]

private theorem trEvIdx_forgedBobStartTr (trPre : ExecTrace) (b a : Participant)
    (ikA ikB spkB pqskB : Bytes) :
    trEvIdx (forgedBobStartTr trPre b a ikA ikB spkB pqskB) isAnyTRExposure =
      trEvIdx trPre isAnyTRExposure := by
  dsimp only [forgedBobStartTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]

private theorem aliceTrOpt_facts (tr : ExecTrace) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    let o := aliceOutOpt tr ikA ikBPk spkPk pqPk opkPk
    (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk).length = tr.length + 9 ∧
    (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk).at? (tr.length + 3) = some (NetE o.ek) ∧
    (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk).at? (tr.length + 4) = some (NetE o.ct) ∧
    (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk).EventLoggedAt
      (PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) (tr.length + 5) ∧
    (aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk).at? (tr.length + 8) =
      some (StT a (aliceSt b o (rnd (tr.length + 2) 32))) := by
  dsimp only [aliceTrOpt]
  refine ⟨by simp only [append_len], ?_, ?_, ?_, ?_⟩
  · exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (Trace.append_le _ _) _) _) _) _) (at?_append_at _ _ (by simp only [append_len]))
  · exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (Trace.append_le _ _) _) _) _) (at?_append_at _ _ (by simp only [append_len]))
  · exact eventLoggedAt_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (append1_ev_at _ _ (by simp only [append_len]))
  · exact at?_append_at _ _ (by simp only [append_len])

private theorem forgedBundle_entries (tr : ExecTrace) (ikB : Bytes) :
    tr ≤ forgedBundlePrefix tr ikB ∧
    (forgedBundlePrefix tr ikB).length = tr.length + 4 ∧
    (forgedBundlePrefix tr ikB).at? tr.length = some (NetE (dhPk advSpkSk)) ∧
    (forgedBundlePrefix tr ikB).at? (tr.length + 1) =
      some (NetE (Signature.sign ikB advSpkNonce (encodeEC (dhPk advSpkSk)))) ∧
    (forgedBundlePrefix tr ikB).at? (tr.length + 2) = some (NetE (kemPk advPqSk)) ∧
    (forgedBundlePrefix tr ikB).at? (tr.length + 3) =
      some (NetE (Signature.sign ikB advPqNonce (encodeKEM (kemPk advPqSk)))) := by
  dsimp only [forgedBundlePrefix]
  refine ⟨le_append2 (le_append2 (Trace.le_refl _) _ _) _ _, by simp only [append_len],
    ?_, ?_, ?_, ?_⟩
  · exact at?_mono (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _)
      (at?_append_at _ _ rfl)
  · exact at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ (by simp only [append_len]))
  · exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len]))
  · exact at?_append_at _ _ (by simp only [append_len])

private theorem forgedPreKey_entries (tr : ExecTrace) (ikA ikB spkB pqskB : Bytes) :
    tr ≤ forgedPreKeyStage2 tr ikA ikB spkB pqskB ∧
    forgedPreKeyStage2 tr ikA ikB spkB pqskB ≤ forgedPreKeyPrefix tr ikA ikB spkB pqskB ∧
    (forgedPreKeyPrefix tr ikA ikB spkB pqskB).length = tr.length + 3 ∧
    (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? tr.length = some (NetE (dhPk advEkSk)) ∧
    (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? (tr.length + 1) =
      some (NetE (forgedBobCt ikA ikB spkB pqskB)) ∧
    (forgedPreKeyPrefix tr ikA ikB spkB pqskB).at? (tr.length + 2) =
      some (NetE (encMsg (stFakeMsg0 (dhPk ikA) (dhPk ikB) (dhPk spkB)
        (forgedBobKeys ikA ikB spkB pqskB))
        advCoins (forgedSpqrKey (forgedBobKeys ikA ikB spkB pqskB)) advPlain)) ∧
    (((forgedPreKeyPrefix tr ikA ikB spkB pqskB).append (RndE 32)).append
      (NetE (forgedSpqrKey (forgedBobKeys ikA ikB spkB pqskB)))).at? (tr.length + 4) =
      some (NetE (forgedSpqrKey (forgedBobKeys ikA ikB spkB pqskB))) := by
  dsimp only [forgedPreKeyPrefix, forgedPreKeyStage2]
  refine ⟨le_append2 (Trace.le_refl _) _ _, Trace.append_le _ _, by simp only [append_len],
    ?_, ?_, ?_, ?_⟩
  · exact at?_mono (le_append2 (Trace.le_refl _) _ _) (at?_append_at _ _ rfl)
  · exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len]))
  · exact at?_append_at _ _ (by simp only [append_len])
  · exact at?_append_at _ _ (by simp only [append_len])

private theorem forgedBobStartTr_done_at (trPre : ExecTrace) (b a : Participant)
    (ikA ikB spkB pqskB : Bytes) {i : Nat} (hi : trPre.length + 2 = i) :
    (forgedBobStartTr trPre b a ikA ikB spkB pqskB).EventLoggedAt
      (PQXDHEvent.BobDone b a (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none (dhPk advEkSk) (forgedBobCt ikA ikB spkB pqskB)
        (forgedBobKeys ikA ikB spkB pqskB)) i := by
  dsimp only [forgedBobStartTr, bobOut]
  exact eventLoggedAt_mono
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (Trace.append_le _ _) _) _) _) _) _)
    (append1_ev_at _ _ (by simp only [append_len]; omega))

private theorem t1_eq : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by unfold PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2

private theorem t2_eq : t2 = registerIdentityTr t1 "bob" := by
  refine (Runs.registerIdentity ?_).2
  unfold PQXDH.isRegisteredB; rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [someEventB_append_non _ _ _ rfl (someEventB_append_non _ _ _ rfl
    (someEventB_append_non _ _ _ rfl (someEventB_append_false _ _ _ rfl
      (someEventB_append_non _ _ _ rfl (someEventB_nil _)))))]
  rfl

private theorem t3_eq : t3 = genSignedPrekeyTr t2 "bob" ikB := by
  have hb : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  exact (Runs.genSignedPrekey hb).2

private theorem t4_eq : t4 = genPQPrekeyTr t3 "bob" ikB := by
  have hb2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have h23 : t2 ≤ t3 := by
    rw [t3_eq]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t2 _) _) _) _) _) _
  exact (Runs.genPQPrekey (at?_mono h23 hb2)).2

private theorem t4_facts :
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (Signature.vk ikA) true)) ∧
    t4.at? 2 = some (NetE (dhPk ikA)) ∧
    t4.at? 4 = some (StP "alice" { kind := .identity, sk := ikA }) ∧
    t4.at? 6 = some (EvP (.IdentityRegistered "bob" (dhPk ikB) (Signature.vk ikB) true)) ∧
    t4.at? 7 = some (NetE (dhPk ikB)) ∧
    t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) ∧
    t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) ∧
    t4.at? 14 = some (NetE (dhPk spkB)) ∧
    t4.at? 15 = some (NetE (Signature.sign ikB spkNonce (encodeEC (dhPk spkB)))) ∧
    t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) ∧
    t4.at? 20 = some (NetE (kemPk pqskB)) ∧
    t4.at? 21 = some (NetE (Signature.sign ikB pqNonce (encodeKEM (kemPk pqskB)))) := by
  have h12 : t1 ≤ t2 := by
    rw [t2_eq]
    exact le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t1 _) _) _) _) _
  have h23 : t2 ≤ t3 := by
    rw [t3_eq]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t2 _) _) _) _) _) _
  have h34 : t3 ≤ t4 := by
    rw [t4_eq]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t3 _) _) _) _) _) _
  have h24 : t2 ≤ t4 := Trace.le_trans _ _ _ h23 h34
  have h14 : t1 ≤ t4 := Trace.le_trans _ _ _ h12 h24
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append2 (Trace.append_le _ _) _ _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_append_at _ _ (by simp only [append_len, nil_len])
  · refine at?_mono h24 ?_; rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_mono (le_append2 (Trace.append_le _ _) _ _)
      (at?_append_at _ _ (by simp only [append_len, t1_length]))
  · refine at?_mono h24 ?_; rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ (by simp only [append_len, t1_length]))
  · refine at?_mono h24 ?_; rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_append_at _ _ (by simp only [append_len, t2_length])
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_append_at _ _ (by simp only [append_len, t3_length])

private theorem evIdx_t4_false (p : PQXDHEvent → Bool)
    (h1a : ∀ k v b, p (.IdentityRegistered "alice" k v b) = false)
    (h1b : ∀ k v b, p (.IdentityRegistered "bob" k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdx t4 p = [] := by
  rw [t4_eq]; dsimp only [genPQPrekeyTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h3, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  rw [t3_eq]; dsimp only [genSignedPrekeyTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h2, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  rw [t2_eq]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h1b, Bool.cond_false, evIdx_append_non _ _ _ rfl]
  rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h1a, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_nil]

private theorem trEvIdx_t4 : trEvIdx t4 isAnyTRExposure = [] := by
  rw [t4_eq]; dsimp only [genPQPrekeyTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  rw [t3_eq]; dsimp only [genSignedPrekeyTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  rw [t2_eq]; dsimp only [registerIdentityTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_nil]

private theorem honest_facts :
    t4 ≤ t5 ∧
    t5 ≤ t8 ∧
    t4 ≤ wTrOpk ∧
    t5.at? 25 = some (NetE (dhPk (rnd t4.length 32))) ∧
    t5.at? 26 = some (NetE (kemEncap (kemPk pqskB) (rnd (t4.length + 1) 32)).1) ∧
    wTrOpk.at? 24 = some (StP "bob" { kind := .oneTimePrekey, sk := opkB }) ∧
    wTrOpk.at? 29 = some (NetE (dhPk (rnd t4Opk.length 32))) ∧
    wTrOpk.at? 30 = some (NetE (kemEncap (kemPk pqskB) (rnd (t4Opk.length + 1) 32)).1) ∧
    evIdx t4 isCompromise = [] ∧
    evIdx t5 isCompromise = [] ∧
    evIdx t8 isCompromise = [] ∧
    trEvIdx t4 isAnyTRExposure = [] ∧
    trEvIdx t5 isAnyTRExposure = [] ∧
    trEvIdx t8 isAnyTRExposure = [] ∧
    trEvIdx wTrOpk isAnyTRExposure = [] := by
  have h45 : t4 ≤ t5 := le_aliceTrOpt (Trace.le_refl _) _ _ _ _ _ _ _
  have h58 : t5 ≤ t8 := by
    dsimp only [t8]
    refine le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le ?_ _) _) _) _) _) _) _) _) _
    exact le_encTr (le_encTr (Trace.le_refl _) _ _ _ _) _ _ _ _
  have h4_4o : t4 ≤ t4Opk := by
    dsimp only [t4Opk, genOneTimePrekeyTr]
    exact le_append2 (le_append2 (Trace.le_refl _) _ _) _ _
  have h5o : t5Opk ≤ wTrOpk := by
    dsimp only [wTrOpk, t7Opk]
    refine le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le ?_ _) _) _) _) _) _) _) _) _) _
    exact le_encTr (Trace.le_refl _) _ _ _ _
  have h4o : t4 ≤ wTrOpk :=
    Trace.le_trans _ _ _ (le_aliceTrOpt h4_4o _ _ _ _ _ _ _) h5o
  have hev4 : evIdx t4 isCompromise = [] :=
    evIdx_t4_false isCompromise (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hev5 : evIdx t5 isCompromise = [] := by
    dsimp only [t5, aliceTr]
    rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
    exact hev4
  have hev8 : evIdx t8 isCompromise = [] := by
    dsimp only [t8]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
      evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
    dsimp only [t7, t6]; rw [evIdx_encTr, evIdx_encTr]
    exact hev5
  have htr5 : trEvIdx t5 isAnyTRExposure = [] := by
    dsimp only [t5, aliceTr]; rw [trEvIdx_aliceTrOpt]; exact trEvIdx_t4
  have htr8 : trEvIdx t8 isAnyTRExposure = [] := by
    dsimp only [t8]
    rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
      trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_non _ _ rfl,
      trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
      trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
    dsimp only [t7, t6]; rw [trEvIdx_encTr, trEvIdx_encTr]; exact htr5
  have htrOpk : trEvIdx wTrOpk isAnyTRExposure = [] := by
    dsimp only [wTrOpk, t7Opk]
    rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
      trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_non _ _ rfl,
      trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
      trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
      trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
    dsimp only [t6Opk]; rw [trEvIdx_encTr]
    dsimp only [t5Opk, aliceTrOpk]; rw [trEvIdx_aliceTrOpt]
    dsimp only [t4Opk, genOneTimePrekeyTr]
    rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
      trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
    exact trEvIdx_t4
  refine ⟨h45, h58, h4o,
    at?_idx_eq
      (aliceTrOpt_facts t4 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) none).2.1
      (by rw [t4_length]),
    at?_idx_eq
      (aliceTrOpt_facts t4 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) none).2.2.1
      (by rw [t4_length]),
    ?_,
    at?_mono h5o (at?_idx_eq
      (aliceTrOpt_facts t4Opk "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB))).2.1
      (by rw [t4Opk_length])),
    at?_mono h5o (at?_idx_eq
      (aliceTrOpt_facts t4Opk "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB))).2.2.1
      (by rw [t4Opk_length])),
    hev4, hev5, hev8, trEvIdx_t4, htr5, htr8, htrOpk⟩
  have h24 : t4Opk.at? 24 = some (StP "bob" { kind := .oneTimePrekey, sk := opkB }) := by
    dsimp only [t4Opk, genOneTimePrekeyTr, opkB]; rw [t4_length]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t4_length]))
  exact at?_mono (Trace.le_trans _ _ _ (le_aliceTrOpt (Trace.le_refl _) _ _ _ _ _ _ _)
    h5o) h24

abbrev advIkA : Bytes := ikA
abbrev advIkB : Bytes := ikB
abbrev advSpkB : Bytes := spkB
abbrev advPqskB : Bytes := pqskB

abbrev advSetup1 : ExecTrace := t1
abbrev advSetup2 : ExecTrace := t2
abbrev advSetup3 : ExecTrace := t3
abbrev advSetup : ExecTrace := t4

abbrev advBh : BundleHandles := bh1
abbrev advKh : BobKeyHandles := kh1

abbrev advSetup_reach : advSetup.Reachable reachability := t4_reach

/-! ### Witness Trace `trIKB` -/

def trIKB_pre : ExecTrace := forgedBundlePrefix (compIkTr advSetup "bob" advIkB) advIkB
def trIKB : ExecTrace :=
  aliceTr trIKB_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
abbrev trIKB_out : AliceHandshakeOut :=
  aliceOut trIKB_pre advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)

theorem trIKB_reach : trIKB.Reachable reachability := by
  obtain ⟨_, _, ha4, hb6, _, hb9, _, _, _, _, _, _⟩ := t4_facts
  have rc : (compIkTr advSetup "bob" advIkB).Reachable reachability :=
    compIkTr_reach (idx := 9) advSetup_reach hb9
  have hik23 : (compIkTr advSetup "bob" advIkB).at? 23 = some (NetE advIkB) :=
    append2_snd_at _ _ _ (by rw [t4_length])
  have rf : trIKB_pre.Reachable reachability :=
    forgedBundlePrefix_reach (ikIdx := 23) rc
      (at?_mono (Trace.append_le _ _) hik23)
      (at?_mono (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) hik23)
  obtain ⟨hleF, _, hspk, hspkSig, hpq, hpqSig⟩ :=
    forgedBundle_entries (compIkTr advSetup "bob" advIkB) advIkB
  have h4_pre : t4 ≤ trIKB_pre := le_trans (le_append2 (Trace.le_refl _) _ _) hleF
  exact reach_of_runs (Runs.aliceStart_forged (idH := 4) (regB := 6) (honest := true)
    (at?_mono h4_pre ha4) (at?_mono h4_pre hb6) hspk hspkSig hpq hpqSig) (aliceStart_reachable rf)

theorem trIKB_aliceDone :
    trIKB.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
        none trIKB_out.ek trIKB_out.ct trIKB_out.keys) 33 :=
  eventLoggedAt_idx_eq
    (aliceTrOpt_facts trIKB_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk) none).2.2.2.1
    (by dsimp only [trIKB_pre, forgedBundlePrefix, compIkTr, advSetup]; simp only [append_len, t4_length])

theorem trIKB_compIK :
    trIKB.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk advIkB)) 22 :=
  eventLoggedAt_mono
    (le_aliceTrOpt (forgedBundle_entries _ _).1 _ _ _ _ _ _ _)
    (append2_ev_at _ _ _ (by rw [t4_length]))

theorem trIKB_compromise_indices : evIdx trIKB isCompromise = [22] := by
  dsimp only [trIKB, aliceTr, trIKB_pre, forgedBundlePrefix, compIkTr, advSetup]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.1, t4_length]; rfl

theorem trIKB_trExposure_indices : trEvIdx trIKB isAnyTRExposure = [] := by
  dsimp only [trIKB, aliceTr, trIKB_pre, forgedBundlePrefix, compIkTr, advSetup]
  rw [trEvIdx_aliceTrOpt, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact trEvIdx_t4

theorem trIKB_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trIKB trIKB_out.keys k :=
  not_sessionStateExposed_of_no_trExposure trIKB_trExposure_indices _ k

theorem trIKB_knows_block {k : Bytes} (hk : IsHandshakeBlock trIKB_out.keys k) :
    k.AttackerKnows trIKB := by
  have hc_tr : compIkTr advSetup "bob" advIkB ≤ trIKB :=
    le_aliceTrOpt (forgedBundle_entries _ _).1 _ _ _ _ _ _ _
  have h4_tr : t4 ≤ trIKB := le_trans (le_append2 (Trace.le_refl _) _ _) hc_tr
  have af := aliceTrOpt_facts trIKB_pre "alice" "bob" advIkA (dhPk advIkB)
    (dhPk advSpkSk) (kemPk advPqSk) none
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net af.2.1)
    (ak_net (at?_mono hc_tr (append2_snd_at _ _ _ rfl)))
    (ak_lit _) (ak_lit _) trivial
    (ak_net af.2.2.1) hk

/-! ### Witness Trace `trBrokenDHA` -/

def trBrokenDHA_pre : ExecTrace :=
  forgedBundlePrefix (invertTr (breakDHTr advSetup) advIkB) advIkB
def trBrokenDHA : ExecTrace :=
  aliceTr trBrokenDHA_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
abbrev trBrokenDHA_out : AliceHandshakeOut :=
  aliceOut trBrokenDHA_pre advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)

theorem trBrokenDHA_reach : trBrokenDHA.Reachable reachability := by
  obtain ⟨_, _, ha4, hb6, hb7, _, _, _, _, _, _, _⟩ := t4_facts
  have rb : (breakDHTr advSetup).Reachable reachability := breakDHTr_reach advSetup_reach
  have ri : (invertTr (breakDHTr advSetup) advIkB).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 7) rb
      (someEventB_of_at? (Trace.at?_append _ _) rfl)
      (at?_mono (Trace.append_le _ _) hb7)
  have hik23 : (invertTr (breakDHTr advSetup) advIkB).at? 23 = some (NetE advIkB) :=
    append2_snd_at _ _ _ (by rw [t4_length])
  have rf : trBrokenDHA_pre.Reachable reachability :=
    forgedBundlePrefix_reach (ikIdx := 23) ri
      (at?_mono (Trace.append_le _ _) hik23)
      (at?_mono (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) hik23)
  obtain ⟨hleF, _, hspk, hspkSig, hpq, hpqSig⟩ :=
    forgedBundle_entries (invertTr (breakDHTr advSetup) advIkB) advIkB
  have h4_pre : t4 ≤ trBrokenDHA_pre := le_trans (le_append2 (Trace.le_refl _) _ _) hleF
  exact reach_of_runs (Runs.aliceStart_forged (idH := 4) (regB := 6) (honest := true)
    (at?_mono h4_pre ha4) (at?_mono h4_pre hb6) hspk hspkSig hpq hpqSig) (aliceStart_reachable rf)

theorem trBrokenDHA_aliceDone :
    trBrokenDHA.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
        none trBrokenDHA_out.ek trBrokenDHA_out.ct trBrokenDHA_out.keys) 33 :=
  eventLoggedAt_idx_eq
    (aliceTrOpt_facts trBrokenDHA_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk) none).2.2.2.1
    (by dsimp only [trBrokenDHA_pre, forgedBundlePrefix, invertTr, breakDHTr, advSetup]; simp only [append_len, t4_length])

theorem trBrokenDHA_brokenDH :
    trBrokenDHA.EventLoggedAt PQXDHEvent.BrokenDH 22 :=
  eventLoggedAt_mono
    (le_aliceTrOpt (le_trans (le_append_of_le (Trace.le_refl _) _) (forgedBundle_entries _ _).1) _ _ _ _ _ _ _)
    (append1_ev_at _ _ (by rw [t4_length]))

theorem trBrokenDHA_compromise_indices : evIdx trBrokenDHA isCompromise = [22] := by
  dsimp only [trBrokenDHA, aliceTr, trBrokenDHA_pre, forgedBundlePrefix, invertTr, breakDHTr, advSetup]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompromise .BrokenDH = true from rfl,
    honest_facts.2.2.2.2.2.2.2.2.1, t4_length]; rfl

theorem trBrokenDHA_trExposure_indices : trEvIdx trBrokenDHA isAnyTRExposure = [] := by
  dsimp only [trBrokenDHA, aliceTr, trBrokenDHA_pre, forgedBundlePrefix, invertTr, breakDHTr, advSetup]
  rw [trEvIdx_aliceTrOpt, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact trEvIdx_t4

theorem trBrokenDHA_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trBrokenDHA trBrokenDHA_out.keys k :=
  not_sessionStateExposed_of_no_trExposure trBrokenDHA_trExposure_indices _ k

theorem trBrokenDHA_knows_block {k : Bytes} (hk : IsHandshakeBlock trBrokenDHA_out.keys k) :
    k.AttackerKnows trBrokenDHA := by
  have hi_tr : invertTr (breakDHTr advSetup) advIkB ≤ trBrokenDHA :=
    le_aliceTrOpt (forgedBundle_entries _ _).1 _ _ _ _ _ _ _
  have h4_tr : t4 ≤ trBrokenDHA := le_trans (le_append2 (Trace.le_refl _) _ _) hi_tr
  have af := aliceTrOpt_facts trBrokenDHA_pre "alice" "bob" advIkA (dhPk advIkB)
    (dhPk advSpkSk) (kemPk advPqSk) none
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net af.2.1)
    (ak_net (at?_mono hi_tr (append2_snd_at _ _ _ rfl)))
    (ak_lit _) (ak_lit _) trivial
    (ak_net af.2.2.1) hk

/-! ### Witness Trace `trIKA` -/

abbrev advForgedBobKeys : HandshakeKeys := forgedBobKeys advIkA advIkB advSpkB advPqskB
abbrev advForgedBobCt : Bytes := forgedBobCt advIkA advIkB advSpkB advPqskB

def trIKA_pre : ExecTrace :=
  forgedPreKeyPrefix (compIkTr advSetup "alice" advIkA) advIkA advIkB advSpkB advPqskB
def trIKA : ExecTrace :=
  forgedBobStartTr trIKA_pre "bob" "alice" advIkA advIkB advSpkB advPqskB

theorem trIKA_reach : trIKA.Reachable reachability := by
  obtain ⟨ha1, ha2, ha4, _, hb7, hb9, hs13, hs14, _, hp19, hp20, _⟩ := t4_facts
  have rc : (compIkTr advSetup "alice" advIkA).Reachable reachability :=
    compIkTr_reach (idx := 4) advSetup_reach ha4
  obtain ⟨hleS2, hlePre, _, hek, hct, hmsg, hpq⟩ :=
    forgedPreKey_entries (compIkTr advSetup "alice" advIkA) advIkA advIkB advSpkB advPqskB
  have h4_c : t4 ≤ compIkTr advSetup "alice" advIkA := le_append2 (Trace.le_refl _) _ _
  have h4_s2 : t4 ≤ forgedPreKeyStage2 (compIkTr advSetup "alice" advIkA) advIkA advIkB advSpkB advPqskB :=
    le_trans h4_c hleS2
  have h4_pre : t4 ≤ trIKA_pre := le_trans h4_s2 hlePre
  have hik23 : (compIkTr advSetup "alice" advIkA).at? 23 = some (NetE advIkA) :=
    append2_snd_at _ _ _ (by rw [t4_length])
  have rf : trIKA_pre.Reachable reachability :=
    forgedPreKeyPrefix_reach (pqIdx := 20) (ikAIdx := 2) (ikBIdx := 7) (spkIdx := 14)
      rc (at?_mono (le_append_of_le h4_c _) hp20)
      (ak_agree_direct (ak_net (at?_mono h4_s2 hs14)) (ak_net (at?_mono hleS2 hik23)))
      (at?_mono h4_s2 ha2) (at?_mono h4_s2 hb7) (at?_mono h4_s2 hs14) (at?_mono h4_s2 hp20)
  exact reach_of_runs (Runs.bobStart_forged (kh := advKh) (regA := 1) (honest := true)
    (at?_mono h4_pre hb9) (at?_mono h4_pre hs13) (at?_mono h4_pre hp19) rfl
    (at?_mono h4_pre ha1) hek hct hmsg hpq) (bobStart_reachable rf)

theorem trIKA_bobDone :
    trIKA.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
        none (dhPk advEkSk) advForgedBobCt advForgedBobKeys) 29 :=
  forgedBobStartTr_done_at _ _ _ _ _ _ _
    (by dsimp only [trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compIkTr, advSetup]
        simp only [append_len, t4_length])

theorem trIKA_compIK :
    trIKA.EventLoggedAt (PQXDHEvent.CompromisedIK "alice" (dhPk advIkA)) 22 := by
  obtain ⟨hleS2, hlePre, _⟩ :=
    forgedPreKey_entries (compIkTr advSetup "alice" advIkA) advIkA advIkB advSpkB advPqskB
  exact eventLoggedAt_mono
    (le_forgedBobStartTr (le_trans hleS2 hlePre) _ _ _ _ _ _)
    (append2_ev_at _ _ _ (by rw [t4_length]))

theorem trIKA_compromise_indices : evIdx trIKA isCompromise = [22] := by
  dsimp only [trIKA, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compIkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.1, t4_length]; rfl

theorem trIKA_trExposure_indices : trEvIdx trIKA isAnyTRExposure = [] := by
  dsimp only [trIKA, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compIkTr, advSetup]
  rw [trEvIdx_forgedBobStartTr, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact trEvIdx_t4

theorem trIKA_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trIKA advForgedBobKeys k :=
  not_sessionStateExposed_of_no_trExposure trIKA_trExposure_indices _ k

theorem trIKA_knows_block {k : Bytes} (hk : IsHandshakeBlock advForgedBobKeys k) :
    k.AttackerKnows trIKA := by
  obtain ⟨_, _, _, _, hb7, _, _, hs14, _, _, hp20, _⟩ := t4_facts
  obtain ⟨hleS2, hlePre, _⟩ :=
    forgedPreKey_entries (compIkTr advSetup "alice" advIkA) advIkA advIkB advSpkB advPqskB
  have hc_tr : compIkTr advSetup "alice" advIkA ≤ trIKA :=
    le_forgedBobStartTr (le_trans hleS2 hlePre) _ _ _ _ _ _
  have h4_tr : t4 ≤ trIKA := le_trans (le_append2 (Trace.le_refl _) _ _) hc_tr
  exact ak_forgedBobKeys_block
    (ak_agree_direct (ak_net (at?_mono h4_tr hs14))
      (ak_net (at?_mono hc_tr (append2_snd_at _ _ _ rfl))))
    (ak_net (at?_mono h4_tr hb7)) (ak_net (at?_mono h4_tr hs14))
    (ak_net (at?_mono h4_tr hp20)) hk

/-! ### Witness Trace `trSPKB` -/

def trSPKB_pre : ExecTrace :=
  forgedPreKeyPrefix (compSpkTr advSetup "bob" advSpkB) advIkA advIkB advSpkB advPqskB
def trSPKB : ExecTrace :=
  forgedBobStartTr trSPKB_pre "bob" "alice" advIkA advIkB advSpkB advPqskB

theorem trSPKB_reach : trSPKB.Reachable reachability := by
  obtain ⟨ha1, ha2, _, _, hb7, hb9, hs13, hs14, _, hp19, hp20, _⟩ := t4_facts
  have rc : (compSpkTr advSetup "bob" advSpkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) advSetup_reach hs13
  obtain ⟨hleS2, hlePre, _, hek, hct, hmsg, hpq⟩ :=
    forgedPreKey_entries (compSpkTr advSetup "bob" advSpkB) advIkA advIkB advSpkB advPqskB
  have h4_c : t4 ≤ compSpkTr advSetup "bob" advSpkB := le_append2 (Trace.le_refl _) _ _
  have h4_s2 : t4 ≤ forgedPreKeyStage2 (compSpkTr advSetup "bob" advSpkB) advIkA advIkB advSpkB advPqskB :=
    le_trans h4_c hleS2
  have h4_pre : t4 ≤ trSPKB_pre := le_trans h4_s2 hlePre
  have hspk23 : (compSpkTr advSetup "bob" advSpkB).at? 23 = some (NetE advSpkB) :=
    append2_snd_at _ _ _ (by rw [t4_length])
  have rf : trSPKB_pre.Reachable reachability :=
    forgedPreKeyPrefix_reach (pqIdx := 20) (ikAIdx := 2) (ikBIdx := 7) (spkIdx := 14)
      rc (at?_mono (le_append_of_le h4_c _) hp20)
      (ak_agree (ak_net (at?_mono h4_s2 ha2)) (ak_net (at?_mono hleS2 hspk23)))
      (at?_mono h4_s2 ha2) (at?_mono h4_s2 hb7) (at?_mono h4_s2 hs14) (at?_mono h4_s2 hp20)
  exact reach_of_runs (Runs.bobStart_forged (kh := advKh) (regA := 1) (honest := true)
    (at?_mono h4_pre hb9) (at?_mono h4_pre hs13) (at?_mono h4_pre hp19) rfl
    (at?_mono h4_pre ha1) hek hct hmsg hpq) (bobStart_reachable rf)

theorem trSPKB_bobDone :
    trSPKB.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
        none (dhPk advEkSk) advForgedBobCt advForgedBobKeys) 29 :=
  forgedBobStartTr_done_at _ _ _ _ _ _ _
    (by dsimp only [trSPKB_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compSpkTr, advSetup]
        simp only [append_len, t4_length])

theorem trSPKB_compSPK :
    trSPKB.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk advSpkB)) 22 := by
  obtain ⟨hleS2, hlePre, _⟩ :=
    forgedPreKey_entries (compSpkTr advSetup "bob" advSpkB) advIkA advIkB advSpkB advPqskB
  exact eventLoggedAt_mono
    (le_forgedBobStartTr (le_trans hleS2 hlePre) _ _ _ _ _ _)
    (append2_ev_at _ _ _ (by rw [t4_length]))

theorem trSPKB_compromise_indices : evIdx trSPKB isCompromise = [22] := by
  dsimp only [trSPKB, trSPKB_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compSpkTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.1, t4_length]; rfl

theorem trSPKB_trExposure_indices : trEvIdx trSPKB isAnyTRExposure = [] := by
  dsimp only [trSPKB, trSPKB_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compSpkTr, advSetup]
  rw [trEvIdx_forgedBobStartTr, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact trEvIdx_t4

theorem trSPKB_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trSPKB advForgedBobKeys k :=
  not_sessionStateExposed_of_no_trExposure trSPKB_trExposure_indices _ k

theorem trSPKB_knows_block {k : Bytes} (hk : IsHandshakeBlock advForgedBobKeys k) :
    k.AttackerKnows trSPKB := by
  obtain ⟨_, ha2, _, _, hb7, _, _, hs14, _, _, hp20, _⟩ := t4_facts
  obtain ⟨hleS2, hlePre, _⟩ :=
    forgedPreKey_entries (compSpkTr advSetup "bob" advSpkB) advIkA advIkB advSpkB advPqskB
  have hc_tr : compSpkTr advSetup "bob" advSpkB ≤ trSPKB :=
    le_forgedBobStartTr (le_trans hleS2 hlePre) _ _ _ _ _ _
  have h4_tr : t4 ≤ trSPKB := le_trans (le_append2 (Trace.le_refl _) _ _) hc_tr
  exact ak_forgedBobKeys_block
    (ak_agree (ak_net (at?_mono h4_tr ha2))
      (ak_net (at?_mono hc_tr (append2_snd_at _ _ _ rfl))))
    (ak_net (at?_mono h4_tr hb7)) (ak_net (at?_mono h4_tr hs14))
    (ak_net (at?_mono h4_tr hp20)) hk

/-! ### Witness Trace `trBrokenDHB` -/

def trBrokenDHB_pre : ExecTrace :=
  forgedPreKeyPrefix (invertTr (breakDHTr advSetup) advIkA) advIkA advIkB advSpkB advPqskB
def trBrokenDHB : ExecTrace :=
  forgedBobStartTr trBrokenDHB_pre "bob" "alice" advIkA advIkB advSpkB advPqskB

theorem trBrokenDHB_reach : trBrokenDHB.Reachable reachability := by
  obtain ⟨ha1, ha2, _, _, hb7, hb9, hs13, hs14, _, hp19, hp20, _⟩ := t4_facts
  have rb : (breakDHTr advSetup).Reachable reachability := breakDHTr_reach advSetup_reach
  have ri : (invertTr (breakDHTr advSetup) advIkA).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 2) rb
      (someEventB_of_at? (Trace.at?_append _ _) rfl)
      (at?_mono (Trace.append_le _ _) ha2)
  obtain ⟨hleS2, hlePre, _, hek, hct, hmsg, hpq⟩ :=
    forgedPreKey_entries (invertTr (breakDHTr advSetup) advIkA) advIkA advIkB advSpkB advPqskB
  have h4_i : t4 ≤ invertTr (breakDHTr advSetup) advIkA := le_append2 (Trace.le_refl _) _ _
  have h4_s2 : t4 ≤ forgedPreKeyStage2 (invertTr (breakDHTr advSetup) advIkA) advIkA advIkB advSpkB advPqskB :=
    le_trans h4_i hleS2
  have h4_pre : t4 ≤ trBrokenDHB_pre := le_trans h4_s2 hlePre
  have hik23 : (invertTr (breakDHTr advSetup) advIkA).at? 23 = some (NetE advIkA) :=
    append2_snd_at _ _ _ (by rw [t4_length])
  have rf : trBrokenDHB_pre.Reachable reachability :=
    forgedPreKeyPrefix_reach (pqIdx := 20) (ikAIdx := 2) (ikBIdx := 7) (spkIdx := 14)
      ri (at?_mono (le_append_of_le h4_i _) hp20)
      (ak_agree_direct (ak_net (at?_mono h4_s2 hs14)) (ak_net (at?_mono hleS2 hik23)))
      (at?_mono h4_s2 ha2) (at?_mono h4_s2 hb7) (at?_mono h4_s2 hs14) (at?_mono h4_s2 hp20)
  exact reach_of_runs (Runs.bobStart_forged (kh := advKh) (regA := 1) (honest := true)
    (at?_mono h4_pre hb9) (at?_mono h4_pre hs13) (at?_mono h4_pre hp19) rfl
    (at?_mono h4_pre ha1) hek hct hmsg hpq) (bobStart_reachable rf)

theorem trBrokenDHB_bobDone :
    trBrokenDHB.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk advIkB) (dhPk advIkA) (dhPk advSpkB) (kemPk advPqskB)
        none (dhPk advEkSk) advForgedBobCt advForgedBobKeys) 29 :=
  forgedBobStartTr_done_at _ _ _ _ _ _ _
    (by dsimp only [trBrokenDHB_pre, forgedPreKeyPrefix, forgedPreKeyStage2, invertTr, breakDHTr, advSetup]
        simp only [append_len, t4_length])

theorem trBrokenDHB_brokenDH :
    trBrokenDHB.EventLoggedAt PQXDHEvent.BrokenDH 22 := by
  obtain ⟨hleS2, hlePre, _⟩ :=
    forgedPreKey_entries (invertTr (breakDHTr advSetup) advIkA) advIkA advIkB advSpkB advPqskB
  exact eventLoggedAt_mono
    (le_forgedBobStartTr (le_trans (le_append_of_le (Trace.le_refl _) _) (le_trans hleS2 hlePre)) _ _ _ _ _ _)
    (append1_ev_at _ _ (by rw [t4_length]))

theorem trBrokenDHB_compromise_indices : evIdx trBrokenDHB isCompromise = [22] := by
  dsimp only [trBrokenDHB, trBrokenDHB_pre, forgedPreKeyPrefix, forgedPreKeyStage2, invertTr, breakDHTr, advSetup]
  rw [evIdx_forgedBobStartTr_false _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl),
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_ev,
    show isCompromise .BrokenDH = true from rfl,
    honest_facts.2.2.2.2.2.2.2.2.1, t4_length]; rfl

theorem trBrokenDHB_trExposure_indices : trEvIdx trBrokenDHB isAnyTRExposure = [] := by
  dsimp only [trBrokenDHB, trBrokenDHB_pre, forgedPreKeyPrefix, forgedPreKeyStage2, invertTr, breakDHTr, advSetup]
  rw [trEvIdx_forgedBobStartTr, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact trEvIdx_t4

theorem trBrokenDHB_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trBrokenDHB advForgedBobKeys k :=
  not_sessionStateExposed_of_no_trExposure trBrokenDHB_trExposure_indices _ k

theorem trBrokenDHB_knows_block {k : Bytes} (hk : IsHandshakeBlock advForgedBobKeys k) :
    k.AttackerKnows trBrokenDHB := by
  obtain ⟨_, _, _, _, hb7, _, _, hs14, _, _, hp20, _⟩ := t4_facts
  obtain ⟨hleS2, hlePre, _⟩ :=
    forgedPreKey_entries (invertTr (breakDHTr advSetup) advIkA) advIkA advIkB advSpkB advPqskB
  have hi_tr : invertTr (breakDHTr advSetup) advIkA ≤ trBrokenDHB :=
    le_forgedBobStartTr (le_trans hleS2 hlePre) _ _ _ _ _ _
  have h4_tr : t4 ≤ trBrokenDHB := le_trans (le_append2 (Trace.le_refl _) _ _) hi_tr
  exact ak_forgedBobKeys_block
    (ak_agree_direct (ak_net (at?_mono h4_tr hs14))
      (ak_net (at?_mono hi_tr (append2_snd_at _ _ _ rfl))))
    (ak_net (at?_mono h4_tr hb7)) (ak_net (at?_mono h4_tr hs14))
    (ak_net (at?_mono h4_tr hp20)) hk

/-! ### Witness Trace `trAlias` -/

def trAlias1 : ExecTrace := compIkTr t4 "bob" ikB
def trAlias2 : ExecTrace := regCorruptTr trAlias1 "carol" ikB
def trAlias3 : ExecTrace := aliceTr trAlias2 "alice" "carol" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)

abbrev trAlias_out : AliceHandshakeOut :=
  aliceOut trAlias2 ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
abbrev trAlias_keys : HandshakeKeys := trAlias_out.keys
abbrev trAlias_dhsA : Bytes := rnd 28 32
def trAlias_stA0 : TRState := aliceSt "carol" trAlias_out trAlias_dhsA

abbrev trAlias_m0 : Bytes := rnd 35 32
abbrev trAlias_coins0 : Bytes := rnd 36 32
def trAlias_key0 : Bytes := (Spqr.spqrSend trAlias_stA0.spqr trAlias_coins0).2.1
def trAlias_pqm0 : Bytes := (Spqr.spqrSend trAlias_stA0.spqr trAlias_coins0).2.2
def trAlias4 : ExecTrace := encTr trAlias3 "alice" 34 trAlias_stA0 trAlias_key0

def trAlias_mh : PreKeyMsgHandles := { ek := 29, ct := 30, msg := 41 }
abbrev trAlias_dhsB1 : Bytes := rnd 42 32
def trAlias_stB00 : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) trAlias_keys
    (encSig trAlias_stA0 trAlias_coins0 trAlias_key0 trAlias_m0)
def trAlias_stB0' : TRState := (ratchetState trAlias_stB00 (dhPk trAlias_dhsA) trAlias_dhsB1).1
def trAlias_cB : RecvChain := (ratchetState trAlias_stB00 (dhPk trAlias_dhsA) trAlias_dhsB1).2
def trAlias_cB' : RecvChain := { trAlias_cB with chainKey := (kdfCk trAlias_cB.chainKey).1, index := 1 }
def trAlias_seedB0 : Bytes := (kdfCk trAlias_cB.chainKey).2
def trAlias_stB1 : TRState :=
  { trAlias_stB0' with
    recv := [trAlias_cB'], spqr := recvSt (Spqr.spqrInit trAlias_keys.pqr spqrB2A) trAlias_pqm0 }

def trAlias : ExecTrace :=
  let tr1 := (trAlias4.append (RndE 32)).append (NetE trAlias_key0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none trAlias_out.ek trAlias_out.ct trAlias_keys))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk trAlias_dhsA) (dhPk trAlias_dhsB1)))).append
      (EvT (.HonestDH (trAlias_stB0'.sessionInfo "bob") trAlias_dhsB1 0))).append
      (EvC (.HandshakeSession (trAlias_stB0'.sessionInfo "bob") 44))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk trAlias_dhsA) 0 trAlias_m0))).append
    (EvT (.MessageKey (trAlias_stB0'.sessionInfo "bob") .receiver trAlias_seedB0
      trAlias_key0 0 2 50))).append
    (StT "bob" trAlias_stB1)

theorem trAlias_seedB0_eq : (kdfCk trAlias_stA0.cks).2 = trAlias_seedB0 := by
  show (kdfCk (createChain trAlias_keys.rk (dhPk spkB) trAlias_dhsA).2).2 =
    (kdfCk (createChain trAlias_keys.rk (dhPk trAlias_dhsA) spkB).2).2
  rw [createChain_comm trAlias_keys.rk trAlias_dhsA spkB]

theorem trAlias_reach : trAlias.Reachable reachability := by
  obtain ⟨ha1, _, ha4, _, _, hb9, hs13, hs14, hs15, hp19, hp20, hp21⟩ := t4_facts
  have hl1 : trAlias1.length = 24 := by dsimp only [trAlias1, compIkTr]; simp only [append_len, t4_length]
  have hl2 : trAlias2.length = 26 := by dsimp only [trAlias2, regCorruptTr]; simp only [append_len, hl1]
  have hl3 : trAlias3.length = 35 := by dsimp only [trAlias3, aliceTr, aliceTrOpt]; simp only [append_len, hl2]
  have hl4 : trAlias4.length = 42 := by dsimp only [trAlias4, encTr]; simp only [append_len, hl3]
  have r1 : trAlias1.Reachable reachability := compIkTr_reach (idx := 9) t4_reach hb9
  have hunreg : (!PQXDH.isRegisteredB trAlias1 "carol") = true := by
    unfold PQXDH.isRegisteredB
    rw [someEventB_of_evIdx_nil]; · rfl
    dsimp only [trAlias1, compIkTr]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_ev]
    dsimp only
    exact evIdx_t4_false _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have r2 : trAlias2.Reachable reachability :=
    regCorruptTr_reach (skIdx := 23) r1 hunreg (append2_snd_at _ _ _ (by rw [t4_length]))
  have h4_2 : t4 ≤ trAlias2 := le_append2 (le_append2 (Trace.le_refl _) _ _) _ _
  have hreg24 : trAlias2.at? 24 =
      some (EvP (.IdentityRegistered "carol" (dhPk ikB) (Signature.vk ikB) false)) :=
    at?_mono (Trace.append_le _ _) (at?_append_at _ _ hl1)
  have r3 : trAlias3.Reachable reachability :=
    reach_of_runs
      (Runs.aliceStart (idH := 4) (regB := 24) (h := bh1) (honest := false)
        (at?_mono h4_2 ha4) hreg24 (at?_mono h4_2 hs14) (at?_mono h4_2 hs15)
        (at?_mono h4_2 hp20) (at?_mono h4_2 hp21)
        (Signature.verify_sign _ _ _) (Signature.verify_sign _ _ _) rfl (x25519LowOrder_dhPk spkB))
      (aliceStart_reachable r2)
  have af := aliceTrOpt_facts trAlias2 "alice" "carol" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
  have hst34 : trAlias3.at? 34 = some (StT "alice" trAlias_stA0) := by
    have h : trAlias3.at? 34 = _ := at?_idx_eq af.2.2.2.2 (by omega)
    have hd : rnd (trAlias2.length + 2) 32 = trAlias_dhsA := by rw [hl2]
    rwa [hd] at h
  have hpq37 : (((trAlias3.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend trAlias_stA0.spqr (rnd (trAlias3.length + 1) 32)).2.1)).at? 37 =
      some (NetE trAlias_key0) := by
    have hc : rnd (trAlias3.length + 1) 32 = trAlias_coins0 := by rw [hl3]
    rw [hc]
    exact at?_append_at _ (NetE trAlias_key0) (by simp only [append_len, hl3])
  have r4 : trAlias4.Reachable reachability :=
    reach_of_runs
      (Runs.messageEncrypt (tr := trAlias3) (stH := 34) (pqH := 37) (st := trAlias_stA0)
        (pq := trAlias_key0) hst34 (by decide) hpq37)
      (messageEncrypt_reachable r3 (hcur := by
        dsimp only [trAlias3, aliceTr, aliceTrOpt]
        exact isCurrentSnapshot_append_self _ _ _ (by simp only [append_len, hl2])))
  have h3_4 : trAlias3 ≤ trAlias4 := le_encTr (Trace.le_refl _) _ _ _ _
  have h4_4 : t4 ≤ trAlias4 := le_encTr (le_aliceTrOpt h4_2 _ _ _ _ _ _ _) _ _ _ _
  have hset : setRecvChain trAlias_stB0'.recv trAlias_cB' = [trAlias_cB'] := by
    simp [setRecvChain, trAlias_stB0', ratchetState, trAlias_cB', trAlias_cB, trAlias_stB00,
      bobSt0, maxReceiverChains]
  have hrs :
      ratchetState
        (bobSt0 "alice" ikB spkB (dhPk ikA) trAlias_keys
          (encSig trAlias_stA0 trAlias_coins0 trAlias_key0 trAlias_m0))
        (encSig trAlias_stA0 trAlias_coins0 trAlias_key0 trAlias_m0).ratchetKey
        (rnd trAlias4.length 32) = (trAlias_stB0', trAlias_cB) := by
    rw [hl4]; rfl
  have hrecv : Spqr.spqrRecv trAlias_stB0'.spqr trAlias_pqm0 1 =
      some (recvSt (Spqr.spqrInit trAlias_keys.pqr spqrB2A) trAlias_pqm0, trAlias_key0) :=
    spqrRecv_init_agree trAlias_keys.pqr trAlias_coins0 trAlias_pqm0 .b2a
      (bytesToLiteral_spqrSendMsg _ _)
  have hmsg41 : trAlias4.at? 41 =
      some (NetE (encMsg trAlias_stA0 trAlias_coins0 trAlias_key0 trAlias_m0)) := by
    dsimp only [trAlias4, encTr]
    have hm : rnd trAlias3.length 32 = trAlias_m0 := by rw [hl3]
    have hc : rnd (trAlias3.length + 1) 32 = trAlias_coins0 := by rw [hl3]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, hl3])
  have hpq37_4 : ((trAlias4.append (RndE 32)).append (NetE trAlias_key0)).at? 37 =
      some (NetE trAlias_key0) := by
    refine at?_mono (le_append2 (Trace.le_refl _) _ _) ?_
    dsimp only [trAlias4, encTr]
    exact at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) hpq37
  have hruns : Runs (Composed.bobStart "bob" "alice" kh1 1 trAlias_mh 37 1) trAlias4 50 trAlias :=
    runs_cast (Runs.bobStart (kh := kh1) (mh := trAlias_mh) (keys := trAlias_keys)
      (msg := encSig trAlias_stA0 trAlias_coins0 trAlias_key0 trAlias_m0)
      (t := encMsg trAlias_stA0 trAlias_coins0 trAlias_key0 trAlias_m0)
      (st' := trAlias_stB0') (c := trAlias_cB) (c' := trAlias_cB') (seed := trAlias_seedB0)
      (pq := trAlias_key0) (m := trAlias_m0)
      (at?_mono h4_4 hb9) (at?_mono h4_4 hs13) (at?_mono h4_4 hp19) rfl (at?_mono h4_4 ha1)
      (at?_mono h3_4 (at?_idx_eq af.2.1 (by dsimp only [trAlias_mh]; omega)))
      (at?_mono h3_4 (at?_idx_eq af.2.2.1 (by dsimp only [trAlias_mh]; omega)))
      (isCanonicalKey_dhPk _)
      (bobAgreement_honest ikA (rnd trAlias2.length 32) ikB spkB pqskB (rnd (trAlias2.length + 1) 32))
      hmsg41 (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk trAlias_dhsA) hrs rfl hrecv hpq37_4
      (mac_ok trAlias_seedB0_eq rfl rfl) (dec_ok trAlias_seedB0_eq) (stOut := trAlias_stB1)
      (by rw [hset]; rfl))
      (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, hl4])
      (by rw [skipTr_zero _ _ _ _ _ _ rfl]; dsimp only [trAlias]; simp only [append_len, hl4]; rfl)
  exact reach_of_runs hruns (bobStart_reachable r4)

private theorem trAlias3_le_trAlias : trAlias3 ≤ trAlias := by
  dsimp only [trAlias]
  refine le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le ?_ _) _) _) _) _) _) _) _) _
  exact le_encTr (Trace.le_refl _) _ _ _ _

theorem trAlias_aliceDone :
    trAlias.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "carol" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        none trAlias_out.ek trAlias_out.ct trAlias_keys) 31 :=
  eventLoggedAt_mono trAlias3_le_trAlias
    (eventLoggedAt_idx_eq
      (aliceTrOpt_facts trAlias2 "alice" "carol" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) none).2.2.2.1
      (by dsimp only [trAlias2, regCorruptTr, trAlias1, compIkTr]; simp only [append_len, t4_length]))

abbrev trAlias_aliceDone_carol := trAlias_aliceDone

theorem trAlias_bobDone :
    trAlias.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none trAlias_out.ek trAlias_out.ct trAlias_keys) 44 := by
  dsimp only [trAlias]
  exact eventLoggedAt_mono
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (Trace.append_le _ _) _) _) _) _) _)
    (append1_ev_at _ _ (by
      dsimp only [trAlias4, encTr, trAlias3, aliceTr, aliceTrOpt, trAlias2, regCorruptTr, trAlias1, compIkTr]
      simp only [append_len, t4_length]))

theorem trAlias_compIK :
    trAlias.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 22 :=
  eventLoggedAt_mono
    (le_trans (le_aliceTrOpt (le_append2 (Trace.le_refl _) _ _) _ _ _ _ _ _ _) trAlias3_le_trAlias)
    (append2_ev_at _ _ _ (by rw [t4_length]))

theorem trAlias_regCarol :
    trAlias.EventLoggedAt
      (PQXDHEvent.IdentityRegistered "carol" (dhPk ikB) (Signature.vk ikB) false) 24 :=
  eventLoggedAt_mono
    (le_trans (le_aliceTrOpt (Trace.le_refl _) _ _ _ _ _ _ _) trAlias3_le_trAlias)
    (append2_ev_at _ _ _ (by dsimp only [trAlias1, compIkTr]; simp only [append_len, t4_length]))

abbrev isAliceDoneBob : PQXDHEvent → Bool :=
  fun | .AliceDone "alice" "bob" .. => true | _ => false

theorem trAlias_aliceDoneBob_indices : evIdx trAlias isAliceDoneBob = [] := by
  dsimp only [trAlias]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isAliceDoneBob _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [trAlias4]; rw [evIdx_encTr]
  dsimp only [trAlias3, aliceTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [trAlias2, regCorruptTr, trAlias1, compIkTr]
  rw [evIdx_append_ev, show isAliceDoneBob _ = false from rfl, Bool.cond_false,
    evIdx_append_ev, show isAliceDoneBob _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isAliceDoneBob _ = false from rfl, Bool.cond_false]
  exact evIdx_t4_false _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trAlias_no_aliceDone_bob (ikA' ikB' spk' pqpk' : Bytes) (opk' : Option Bytes)
    (ek' ct' : Bytes) (keys' : HandshakeKeys) :
    ¬ trAlias.EventLogged
      (PQXDHEvent.AliceDone "alice" "bob" ikA' ikB' spk' pqpk' opk' ek' ct' keys') :=
  not_logged trAlias_aliceDoneBob_indices rfl

theorem trAlias_compIK_carol :
    trAlias.EventLoggedAt (PQXDHEvent.CompromisedIK "carol" (dhPk ikB)) 25 :=
  eventLoggedAt_mono
    (le_trans (le_aliceTrOpt (Trace.le_refl _) _ _ _ _ _ _ _) trAlias3_le_trAlias)
    (eventLoggedAt_of_at? (append2_snd_at _ _ _
      (by dsimp only [trAlias1, compIkTr]; simp only [append_len, t4_length])))

theorem trAlias_compromise_indices : evIdx trAlias isCompromise = [22, 25] := by
  dsimp only [trAlias]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [trAlias4]; rw [evIdx_encTr]
  dsimp only [trAlias3, aliceTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [trAlias2, regCorruptTr]
  rw [evIdx_append_ev, show isCompromise (.CompromisedIK "carol" (dhPk ikB)) = true from rfl,
    evIdx_append_ev,
    show isCompromise (.IdentityRegistered "carol" (dhPk ikB) (Signature.vk ikB) false) = false from rfl,
    Bool.cond_false]
  dsimp only [trAlias1, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t4_length]; rfl

theorem trAlias_trExposure_indices : trEvIdx trAlias isAnyTRExposure = [] := by
  dsimp only [trAlias]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  dsimp only [trAlias4]; rw [trEvIdx_encTr]
  dsimp only [trAlias3, aliceTr]; rw [trEvIdx_aliceTrOpt]
  dsimp only [trAlias2, regCorruptTr, trAlias1, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact trEvIdx_t4

/-! ## Post-Exchange Compromise Witness Traces on Honest Sessions -/

/-! ### Witness Trace `trThm7Case1_pq` -/

def trThm7Case1_pq : ExecTrace :=
  compPqTr (compSpkTr (compIkTr t5 "bob" ikB) "bob" spkB) "bob" pqskB

theorem trThm7Case1_pq_reach : trThm7Case1_pq.Reachable reachability := by
  obtain ⟨_, _, _, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_facts
  have h45 := honest_facts.1
  have r1 : (compIkTr t5 "bob" ikB).Reachable reachability :=
    compIkTr_reach (idx := 9) t5_reach (at?_mono h45 hb9)
  have r2 : (compSpkTr (compIkTr t5 "bob" ikB) "bob" spkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) r1 (at?_mono (le_append2 h45 _ _) hs13)
  exact compPqTr_reach (idx := 19) r2 (at?_mono (le_append2 (le_append2 h45 _ _) _ _) hp19)

theorem trThm7Case1_pq_aliceDone :
    trThm7Case1_pq.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    t5_aliceDone_at

theorem trThm7Case1_pq_compIK :
    trThm7Case1_pq.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 31 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append2_ev_at _ _ _ t5_length)
theorem trThm7Case1_pq_compSPK :
    trThm7Case1_pq.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 33 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _)
    (append2_ev_at _ _ _ (by dsimp only [compIkTr]; simp only [append_len, t5_length]))
theorem trThm7Case1_pq_compPQ :
    trThm7Case1_pq.EventLoggedAt (PQXDHEvent.CompromisedPQSPK "bob" (kemPk pqskB)) 35 :=
  append2_ev_at _ _ _ (by dsimp only [compSpkTr, compIkTr]; simp only [append_len, t5_length])

theorem trThm7Case1_pq_compromise_indices : evIdx trThm7Case1_pq isCompromise = [31, 33, 35] := by
  dsimp only [trThm7Case1_pq, compPqTr, compSpkTr, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_ev_net _ _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t5_length]; rfl
theorem trThm7Case1_pq_trExposure_indices : trEvIdx trThm7Case1_pq isAnyTRExposure = [] := by
  dsimp only [trThm7Case1_pq, compPqTr, compSpkTr, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm7Case1_pq_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm7Case1_pq keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm7Case1_pq_trExposure_indices _ k

theorem trThm7Case1_pq_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm7Case1_pq := by
  have h5_tr : t5 ≤ trThm7Case1_pq :=
    le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _
  have h4_tr : t4 ≤ trThm7Case1_pq := le_trans honest_facts.1 h5_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.1))
    (ak_net (at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm7Case1_kem` -/

def trThm7Case1_kem : ExecTrace :=
  invertTr (breakKEMTr (compSpkTr (compIkTr t5 "bob" ikB) "bob" spkB)) pqskB

theorem trThm7Case1_kem_reach : trThm7Case1_kem.Reachable reachability := by
  obtain ⟨_, _, _, _, _, hb9, hs13, _, _, _, hp20, _⟩ := t4_facts
  have h45 := honest_facts.1
  have r1 : (compIkTr t5 "bob" ikB).Reachable reachability :=
    compIkTr_reach (idx := 9) t5_reach (at?_mono h45 hb9)
  have r2 : (compSpkTr (compIkTr t5 "bob" ikB) "bob" spkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) r1 (at?_mono (le_append2 h45 _ _) hs13)
  have r3 : (breakKEMTr (compSpkTr (compIkTr t5 "bob" ikB) "bob" spkB)).Reachable reachability :=
    breakKEMTr_reach r2
  exact invertKEM_reach_sk (pkIdx := 20) r3
    (someEventB_of_at? (Trace.at?_append _ _) rfl)
    (at?_mono (le_append_of_le (le_append2 (le_append2 h45 _ _) _ _) _) hp20)

theorem trThm7Case1_kem_aliceDone :
    trThm7Case1_kem.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    t5_aliceDone_at

theorem trThm7Case1_kem_compIK :
    trThm7Case1_kem.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 31 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append2_ev_at _ _ _ t5_length)
theorem trThm7Case1_kem_compSPK :
    trThm7Case1_kem.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 33 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _)
    (append2_ev_at _ _ _ (by dsimp only [compIkTr]; simp only [append_len, t5_length]))
theorem trThm7Case1_kem_brokenKEM :
    trThm7Case1_kem.EventLoggedAt PQXDHEvent.BrokenKEM 35 :=
  append2_ev_at _ _ _ (by dsimp only [compSpkTr, compIkTr]; simp only [append_len, t5_length])

theorem trThm7Case1_kem_compromise_indices : evIdx trThm7Case1_kem isCompromise = [31, 33, 35] := by
  dsimp only [trThm7Case1_kem, invertTr, breakKEMTr, compSpkTr, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_ev_net _ _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t5_length]; rfl
theorem trThm7Case1_kem_trExposure_indices : trEvIdx trThm7Case1_kem isAnyTRExposure = [] := by
  dsimp only [trThm7Case1_kem, invertTr, breakKEMTr, compSpkTr, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm7Case1_kem_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm7Case1_kem keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm7Case1_kem_trExposure_indices _ k

theorem trThm7Case1_kem_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm7Case1_kem := by
  have h5_tr : t5 ≤ trThm7Case1_kem :=
    le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _
  have h4_tr : t4 ≤ trThm7Case1_kem := le_trans honest_facts.1 h5_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.1))
    (ak_net (at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm7Case3_pq` -/

def trThm7Case3_pq : ExecTrace :=
  compPqTr (invertTr (invertTr (breakDHTr t5) ikB) spkB) "bob" pqskB

theorem trThm7Case3_pq_reach : trThm7Case3_pq.Reachable reachability := by
  obtain ⟨_, _, _, _, hb7, _, _, hs14, _, hp19, _, _⟩ := t4_facts
  have h45 := honest_facts.1
  have r1 : (breakDHTr t5).Reachable reachability := breakDHTr_reach t5_reach
  have r2 : (invertTr (breakDHTr t5) ikB).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 7) r1
      (someEventB_of_at? (Trace.at?_append _ _) rfl)
      (at?_mono (le_append_of_le h45 _) hb7)
  have r3 : (invertTr (invertTr (breakDHTr t5) ikB) spkB).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 14) r2
      (someEventB_of_at? (at?_mono (Trace.append_le _ _) (Trace.at?_append _ _)) rfl)
      (at?_mono (le_append2 h45 _ _) hs14)
  exact compPqTr_reach (idx := 19) r3 (at?_mono (le_append_of_le (le_append2 h45 _ _) _) hp19)

theorem trThm7Case3_pq_aliceDone :
    trThm7Case3_pq.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono (le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _)
    t5_aliceDone_at

theorem trThm7Case3_pq_brokenDH :
    trThm7Case3_pq.EventLoggedAt PQXDHEvent.BrokenDH 31 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append1_ev_at _ _ t5_length)
theorem trThm7Case3_pq_compPQ :
    trThm7Case3_pq.EventLoggedAt (PQXDHEvent.CompromisedPQSPK "bob" (kemPk pqskB)) 34 :=
  append2_ev_at _ _ _ (by dsimp only [invertTr, breakDHTr]; simp only [append_len, t5_length])

theorem trThm7Case3_pq_compromise_indices : evIdx trThm7Case3_pq isCompromise = [31, 34] := by
  dsimp only [trThm7Case3_pq, compPqTr, invertTr, breakDHTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t5_length]; rfl
theorem trThm7Case3_pq_trExposure_indices : trEvIdx trThm7Case3_pq isAnyTRExposure = [] := by
  dsimp only [trThm7Case3_pq, compPqTr, invertTr, breakDHTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm7Case3_pq_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm7Case3_pq keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm7Case3_pq_trExposure_indices _ k

theorem trThm7Case3_pq_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm7Case3_pq := by
  have h5_tr : t5 ≤ trThm7Case3_pq :=
    le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _
  have h4_tr : t4 ≤ trThm7Case3_pq := le_trans honest_facts.1 h5_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.1))
    (ak_net (at?_mono (le_append2 (le_append_of_le (Trace.le_refl _) _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm7Case3_kem` -/

def trThm7Case3_kem : ExecTrace :=
  invertTr (breakKEMTr (invertTr (invertTr (breakDHTr t5) ikB) spkB)) pqskB

theorem trThm7Case3_kem_reach : trThm7Case3_kem.Reachable reachability := by
  obtain ⟨_, _, _, _, hb7, _, _, hs14, _, _, hp20, _⟩ := t4_facts
  have h45 := honest_facts.1
  have r1 : (breakDHTr t5).Reachable reachability := breakDHTr_reach t5_reach
  have r2 : (invertTr (breakDHTr t5) ikB).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 7) r1
      (someEventB_of_at? (Trace.at?_append _ _) rfl)
      (at?_mono (le_append_of_le h45 _) hb7)
  have r3 : (invertTr (invertTr (breakDHTr t5) ikB) spkB).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 14) r2
      (someEventB_of_at? (at?_mono (Trace.append_le _ _) (Trace.at?_append _ _)) rfl)
      (at?_mono (le_append2 h45 _ _) hs14)
  have r4 : (breakKEMTr (invertTr (invertTr (breakDHTr t5) ikB) spkB)).Reachable reachability :=
    breakKEMTr_reach r3
  exact invertKEM_reach_sk (pkIdx := 20) r4
    (someEventB_of_at? (Trace.at?_append _ _) rfl)
    (at?_mono (le_append2 (le_append2 h45 _ _) _ _) hp20)

theorem trThm7Case3_kem_aliceDone :
    trThm7Case3_kem.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono (le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _)
    t5_aliceDone_at

theorem trThm7Case3_kem_brokenDH :
    trThm7Case3_kem.EventLoggedAt PQXDHEvent.BrokenDH 31 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append1_ev_at _ _ t5_length)
theorem trThm7Case3_kem_brokenKEM :
    trThm7Case3_kem.EventLoggedAt PQXDHEvent.BrokenKEM 34 :=
  append2_ev_at _ _ _ (by dsimp only [invertTr, breakDHTr]; simp only [append_len, t5_length])

theorem trThm7Case3_kem_compromise_indices : evIdx trThm7Case3_kem isCompromise = [31, 34] := by
  dsimp only [trThm7Case3_kem, invertTr, breakKEMTr, breakDHTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t5_length]; rfl
theorem trThm7Case3_kem_trExposure_indices : trEvIdx trThm7Case3_kem isAnyTRExposure = [] := by
  dsimp only [trThm7Case3_kem, invertTr, breakKEMTr, breakDHTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm7Case3_kem_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm7Case3_kem keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm7Case3_kem_trExposure_indices _ k

theorem trThm7Case3_kem_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm7Case3_kem := by
  have h5_tr : t5 ≤ trThm7Case3_kem :=
    le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _
  have h4_tr : t4 ≤ trThm7Case3_kem := le_trans honest_facts.1 h5_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.1))
    (ak_net (at?_mono (le_append2 (le_append_of_le (Trace.le_refl _) _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm9Case2` -/

def trThm9Case2 : ExecTrace :=
  compPqTr (compSpkTr (compIkTr t8 "bob" ikB) "bob" spkB) "bob" pqskB

theorem trThm9Case2_reach : trThm9Case2.Reachable reachability := by
  obtain ⟨_, _, _, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_facts
  have h48 := le_trans honest_facts.1 honest_facts.2.1
  have r1 : (compIkTr t8 "bob" ikB).Reachable reachability :=
    compIkTr_reach (idx := 9) t8_reach (at?_mono h48 hb9)
  have r2 : (compSpkTr (compIkTr t8 "bob" ikB) "bob" spkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) r1 (at?_mono (le_append2 h48 _ _) hs13)
  exact compPqTr_reach (idx := 19) r2 (at?_mono (le_append2 (le_append2 h48 _ _) _ _) hp19)

theorem trThm9Case2_bobDone :
    trThm9Case2.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    t8_bobDone_at

theorem trThm9Case2_compIK :
    trThm9Case2.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 54 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append2_ev_at _ _ _ t8_length)
theorem trThm9Case2_compSPK :
    trThm9Case2.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 56 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _)
    (append2_ev_at _ _ _ (by dsimp only [compIkTr]; simp only [append_len, t8_length]))
theorem trThm9Case2_compPQ :
    trThm9Case2.EventLoggedAt (PQXDHEvent.CompromisedPQSPK "bob" (kemPk pqskB)) 58 :=
  append2_ev_at _ _ _ (by dsimp only [compSpkTr, compIkTr]; simp only [append_len, t8_length])

theorem trThm9Case2_compromise_indices : evIdx trThm9Case2 isCompromise = [54, 56, 58] := by
  dsimp only [trThm9Case2, compPqTr, compSpkTr, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_ev_net _ _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t8_length]; rfl
theorem trThm9Case2_trExposure_indices : trEvIdx trThm9Case2 isAnyTRExposure = [] := by
  dsimp only [trThm9Case2, compPqTr, compSpkTr, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm9Case2_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm9Case2 keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm9Case2_trExposure_indices _ k

theorem trThm9Case2_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm9Case2 := by
  have h8_tr : t8 ≤ trThm9Case2 :=
    le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _
  have h5_tr : t5 ≤ trThm9Case2 := le_trans honest_facts.2.1 h8_tr
  have h4_tr : t4 ≤ trThm9Case2 := le_trans honest_facts.1 h5_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.1))
    (ak_net (at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm9Case3` -/

def trThm9Case3 : ExecTrace :=
  invertTr (breakKEMTr (compSpkTr (compIkTr t8 "bob" ikB) "bob" spkB)) pqskB

theorem trThm9Case3_reach : trThm9Case3.Reachable reachability := by
  obtain ⟨_, _, _, _, _, hb9, hs13, _, _, _, hp20, _⟩ := t4_facts
  have h48 := le_trans honest_facts.1 honest_facts.2.1
  have r1 : (compIkTr t8 "bob" ikB).Reachable reachability :=
    compIkTr_reach (idx := 9) t8_reach (at?_mono h48 hb9)
  have r2 : (compSpkTr (compIkTr t8 "bob" ikB) "bob" spkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) r1 (at?_mono (le_append2 h48 _ _) hs13)
  have r3 : (breakKEMTr (compSpkTr (compIkTr t8 "bob" ikB) "bob" spkB)).Reachable reachability :=
    breakKEMTr_reach r2
  exact invertKEM_reach_sk (pkIdx := 20) r3
    (someEventB_of_at? (Trace.at?_append _ _) rfl)
    (at?_mono (le_append_of_le (le_append2 (le_append2 h48 _ _) _ _) _) hp20)

theorem trThm9Case3_bobDone :
    trThm9Case3.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    t8_bobDone_at

theorem trThm9Case3_compIK :
    trThm9Case3.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 54 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append2_ev_at _ _ _ t8_length)
theorem trThm9Case3_compSPK :
    trThm9Case3.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 56 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _)
    (append2_ev_at _ _ _ (by dsimp only [compIkTr]; simp only [append_len, t8_length]))
theorem trThm9Case3_brokenKEM :
    trThm9Case3.EventLoggedAt PQXDHEvent.BrokenKEM 58 :=
  append2_ev_at _ _ _ (by dsimp only [compSpkTr, compIkTr]; simp only [append_len, t8_length])

theorem trThm9Case3_compromise_indices : evIdx trThm9Case3 isCompromise = [54, 56, 58] := by
  dsimp only [trThm9Case3, invertTr, breakKEMTr, compSpkTr, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_ev_net _ _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t8_length]; rfl
theorem trThm9Case3_trExposure_indices : trEvIdx trThm9Case3 isAnyTRExposure = [] := by
  dsimp only [trThm9Case3, invertTr, breakKEMTr, compSpkTr, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm9Case3_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm9Case3 keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm9Case3_trExposure_indices _ k

theorem trThm9Case3_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm9Case3 := by
  have h8_tr : t8 ≤ trThm9Case3 :=
    le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _
  have h5_tr : t5 ≤ trThm9Case3 := le_trans honest_facts.2.1 h8_tr
  have h4_tr : t4 ≤ trThm9Case3 := le_trans honest_facts.1 h5_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.1))
    (ak_net (at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm9Case5` -/

def trThm9Case5 : ExecTrace :=
  compPqTr (invertTr (invertTr (breakDHTr t8) ikA) (rnd 22 32)) "bob" pqskB

theorem trThm9Case5_reach : trThm9Case5.Reachable reachability := by
  obtain ⟨_, ha2, _, _, _, _, _, _, _, hp19, _, _⟩ := t4_facts
  have h58 := honest_facts.2.1
  have h48 := le_trans honest_facts.1 h58
  have hek22 : t5.at? 25 = some (NetE (dhPk (rnd 22 32))) := by
    have h := honest_facts.2.2.2.1; rwa [t4_length] at h
  have r1 : (breakDHTr t8).Reachable reachability := breakDHTr_reach t8_reach
  have r2 : (invertTr (breakDHTr t8) ikA).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 2) r1
      (someEventB_of_at? (Trace.at?_append _ _) rfl)
      (at?_mono (le_append_of_le h48 _) ha2)
  have r3 : (invertTr (invertTr (breakDHTr t8) ikA) (rnd 22 32)).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 25) r2
      (someEventB_of_at? (at?_mono (Trace.append_le _ _) (Trace.at?_append _ _)) rfl)
      (at?_mono (le_append2 h58 _ _) hek22)
  exact compPqTr_reach (idx := 19) r3 (at?_mono (le_append_of_le (le_append2 h48 _ _) _) hp19)

theorem trThm9Case5_bobDone :
    trThm9Case5.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono (le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _)
    t8_bobDone_at

theorem trThm9Case5_brokenDH :
    trThm9Case5.EventLoggedAt PQXDHEvent.BrokenDH 54 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append1_ev_at _ _ t8_length)
theorem trThm9Case5_compPQ :
    trThm9Case5.EventLoggedAt (PQXDHEvent.CompromisedPQSPK "bob" (kemPk pqskB)) 57 :=
  append2_ev_at _ _ _ (by dsimp only [invertTr, breakDHTr]; simp only [append_len, t8_length])

theorem trThm9Case5_compromise_indices : evIdx trThm9Case5 isCompromise = [54, 57] := by
  dsimp only [trThm9Case5, compPqTr, invertTr, breakDHTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t8_length]; rfl
theorem trThm9Case5_trExposure_indices : trEvIdx trThm9Case5 isAnyTRExposure = [] := by
  dsimp only [trThm9Case5, compPqTr, invertTr, breakDHTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm9Case5_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm9Case5 keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm9Case5_trExposure_indices _ k

theorem trThm9Case5_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm9Case5 := by
  obtain ⟨_, _, _, _, hb7, _, _, hs14, _, _, _, _⟩ := t4_facts
  have h8_tr : t8 ≤ trThm9Case5 :=
    le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _
  have h5_tr : t5 ≤ trThm9Case5 := le_trans honest_facts.2.1 h8_tr
  have h4_tr : t4 ≤ trThm9Case5 := le_trans honest_facts.1 h5_tr
  have hek : (rnd t4.length 32).AttackerKnows trThm9Case5 := by
    rw [t4_length]
    exact ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ rfl))
  exact ak_aliceAgreement_block_of_initiatorSecrets (opkSk := none)
    (ak_net (at?_mono (le_append2 (le_append_of_le (Trace.le_refl _) _) _ _)
      (append2_snd_at _ _ _ rfl)))
    hek
    (ak_net (at?_mono h4_tr hb7))
    (ak_net (at?_mono h4_tr hs14))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Trace `trThm9Case6` -/

def trThm9Case6 : ExecTrace :=
  invertTr (breakKEMTr (invertTr (invertTr (breakDHTr t8) ikA) (rnd 22 32))) pqskB

theorem trThm9Case6_reach : trThm9Case6.Reachable reachability := by
  obtain ⟨_, ha2, _, _, _, _, _, _, _, _, hp20, _⟩ := t4_facts
  have h58 := honest_facts.2.1
  have h48 := le_trans honest_facts.1 h58
  have hek22 : t5.at? 25 = some (NetE (dhPk (rnd 22 32))) := by
    have h := honest_facts.2.2.2.1; rwa [t4_length] at h
  have r1 : (breakDHTr t8).Reachable reachability := breakDHTr_reach t8_reach
  have r2 : (invertTr (breakDHTr t8) ikA).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 2) r1
      (someEventB_of_at? (Trace.at?_append _ _) rfl)
      (at?_mono (le_append_of_le h48 _) ha2)
  have r3 : (invertTr (invertTr (breakDHTr t8) ikA) (rnd 22 32)).Reachable reachability :=
    invertDH_reach_sk (pkIdx := 25) r2
      (someEventB_of_at? (at?_mono (Trace.append_le _ _) (Trace.at?_append _ _)) rfl)
      (at?_mono (le_append2 h58 _ _) hek22)
  have r4 : (breakKEMTr (invertTr (invertTr (breakDHTr t8) ikA) (rnd 22 32))).Reachable reachability :=
    breakKEMTr_reach r3
  exact invertKEM_reach_sk (pkIdx := 20) r4
    (someEventB_of_at? (Trace.at?_append _ _) rfl)
    (at?_mono (le_append2 (le_append2 h48 _ _) _ _) hp20)

theorem trThm9Case6_bobDone :
    trThm9Case6.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono (le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _)
    t8_bobDone_at

theorem trThm9Case6_brokenDH :
    trThm9Case6.EventLoggedAt PQXDHEvent.BrokenDH 54 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append1_ev_at _ _ t8_length)
theorem trThm9Case6_brokenKEM :
    trThm9Case6.EventLoggedAt PQXDHEvent.BrokenKEM 57 :=
  append2_ev_at _ _ _ (by dsimp only [invertTr, breakDHTr]; simp only [append_len, t8_length])

theorem trThm9Case6_compromise_indices : evIdx trThm9Case6 isCompromise = [54, 57] := by
  dsimp only [trThm9Case6, invertTr, breakKEMTr, breakDHTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, honest_facts.2.2.2.2.2.2.2.2.2.2.1]
  simp only [append_len, t8_length]; rfl
theorem trThm9Case6_trExposure_indices : trEvIdx trThm9Case6 isAnyTRExposure = [] := by
  dsimp only [trThm9Case6, invertTr, breakKEMTr, breakDHTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trThm9Case6_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm9Case6 keys1 k :=
  not_sessionStateExposed_of_no_trExposure trThm9Case6_trExposure_indices _ k

theorem trThm9Case6_knows_block {k : Bytes} (hk : IsHandshakeBlock keys1 k) :
    k.AttackerKnows trThm9Case6 := by
  obtain ⟨_, _, _, _, hb7, _, _, hs14, _, _, _, _⟩ := t4_facts
  have h8_tr : t8 ≤ trThm9Case6 :=
    le_append2 (le_append_of_le (le_append2 (Trace.le_refl _) _ _) _) _ _
  have h5_tr : t5 ≤ trThm9Case6 := le_trans honest_facts.2.1 h8_tr
  have h4_tr : t4 ≤ trThm9Case6 := le_trans honest_facts.1 h5_tr
  have hek : (rnd t4.length 32).AttackerKnows trThm9Case6 := by
    rw [t4_length]
    exact ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (at?_append_at _ _ rfl))
  exact ak_aliceAgreement_block_of_initiatorSecrets (opkSk := none)
    (ak_net (at?_mono (le_append2 (le_append_of_le (Trace.le_refl _) _) _ _)
      (append2_snd_at _ _ _ rfl)))
    hek
    (ak_net (at?_mono h4_tr hb7))
    (ak_net (at?_mono h4_tr hs14))
    (ak_net (append2_snd_at _ _ _ rfl))
    trivial
    (ak_net (at?_mono h5_tr honest_facts.2.2.2.2.1)) hk

/-! ### Witness Traces `trThm9Case2_opk` and `trThm9Case3_opk` -/

def t6Opk_comp : ExecTrace := compOpkTr t6Opk "bob" opkB
abbrev dhsB1Opk_comp : Bytes := rnd 44 32
def stB0'Opk_comp : TRState := (ratchetState stB00Opk (dhPk dhsAOpk) dhsB1Opk_comp).1
def stB1Opk_comp : TRState :=
  { stB0'Opk_comp with recv := [cB'Opk], spqr := recvSt (Spqr.spqrInit keysOpk.pqr spqrB2A) pqm0Opk }

def wTrOpk_comp : ExecTrace :=
  let tr1 := ((t6Opk_comp.append (RndE 32)).append (NetE key0Opk)).append
    (EvP (.OPKUsed "bob" (dhPk opkB)))
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsAOpk) (dhPk dhsB1Opk_comp)))).append
      (EvT (.HonestDH (stB0'Opk_comp.sessionInfo "bob") dhsB1Opk_comp 0))).append
      (EvC (.HandshakeSession (stB0'Opk_comp.sessionInfo "bob") 47))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsAOpk) 0 m0Opk))).append
    (EvT (.MessageKey (stB0'Opk_comp.sessionInfo "bob") .receiver seedB0Opk key0Opk 0 2 53))).append
    (StT "bob" stB1Opk_comp)

private theorem t6Opk_comp_length : t6Opk_comp.length = 44 := by
  dsimp only [t6Opk_comp, compOpkTr]; simp only [append_len, t6Opk_length]

private theorem wTrOpk_comp_length : wTrOpk_comp.length = 54 := by
  dsimp only [wTrOpk_comp]; simp only [append_len, t6Opk_comp_length]

private theorem t6Opk_comp_le_wTrOpk_comp : t6Opk_comp ≤ wTrOpk_comp := by
  dsimp only [wTrOpk_comp]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _) _

private theorem t6Opk_le_wTrOpk_comp : t6Opk ≤ wTrOpk_comp :=
  le_trans (le_append2 (Trace.le_refl _) _ _) t6Opk_comp_le_wTrOpk_comp

private theorem t4Opk_le_t6Opk : t4Opk ≤ t6Opk :=
  le_trans (le_aliceTrOpt (Trace.le_refl _) _ _ _ _ _ _ _) (le_encTr (Trace.le_refl _) _ _ _ _)

private theorem t4_le_t6Opk : t4 ≤ t6Opk := by
  have h4o : t4 ≤ t4Opk := by
    dsimp only [t4Opk, genOneTimePrekeyTr]
    exact le_append2 (le_append2 (Trace.le_refl _) _ _) _ _
  exact le_trans h4o t4Opk_le_t6Opk

private theorem t4_le_wTrOpk_comp : t4 ≤ wTrOpk_comp :=
  le_trans t4_le_t6Opk t6Opk_le_wTrOpk_comp

private theorem t6Opk_opk24 :
    t6Opk.at? 24 = some (StP "bob" { kind := .oneTimePrekey, sk := opkB }) := by
  refine at?_mono t4Opk_le_t6Opk ?_
  dsimp only [t4Opk, genOneTimePrekeyTr, opkB]; rw [t4_length]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t4_length]))

private theorem t6Opk_ek_at : t6Opk.at? 29 = some (NetE oOpk.ek) := by
  refine at?_mono (le_encTr (Trace.le_refl _) _ _ _ _) ?_
  exact at?_idx_eq
    (aliceTrOpt_facts t4Opk "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
      (some (dhPk opkB))).2.1
    (by rw [t4Opk_length])

private theorem t6Opk_ct_at : t6Opk.at? 30 = some (NetE oOpk.ct) := by
  refine at?_mono (le_encTr (Trace.le_refl _) _ _ _ _) ?_
  exact at?_idx_eq
    (aliceTrOpt_facts t4Opk "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
      (some (dhPk opkB))).2.2.1
    (by rw [t4Opk_length])

private theorem wTrOpk_comp_reach : wTrOpk_comp.Reachable reachability := by
  obtain ⟨ha1, _, _, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_facts
  have hopkUnused6 : (!PQXDH.opkUsedB t6Opk "bob" (dhPk opkB)) = true := by
    unfold PQXDH.opkUsedB
    rw [someEventB_of_evIdx_nil]; · rfl
    dsimp only [t6Opk]; rw [evIdx_encTr]
    dsimp only [t5Opk, aliceTrOpk]
    rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
    dsimp only [t4Opk, genOneTimePrekeyTr]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_ev, show _ = false from rfl, Bool.cond_false, evIdx_append_non _ _ _ rfl]
    exact evIdx_t4_false _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have r6c : t6Opk_comp.Reachable reachability :=
    compOpkTr_reach (idx := 24) t6Opk_reach t6Opk_opk24 hopkUnused6
  have h6_6c : t6Opk ≤ t6Opk_comp := le_append2 (Trace.le_refl _) _ _
  have h4_6c : t4 ≤ t6Opk_comp := le_trans t4_le_t6Opk h6_6c
  have hmsg : t6Opk_comp.at? 41 = some (NetE (encMsg stA0Opk coins0Opk key0Opk m0Opk)) := by
    refine at?_mono h6_6c ?_; dsimp only [t6Opk, encTr]
    have hm : rnd t5Opk.length 32 = m0Opk := by rw [t5Opk_length]
    have hc : rnd (t5Opk.length + 1) 32 = coins0Opk := by rw [t5Opk_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5Opk_length])
  have hpq : ((t6Opk_comp.append (RndE 32)).append (NetE key0Opk)).at? 37 = some (NetE key0Opk) := by
    refine at?_mono (le_append_of_le (le_append_of_le h6_6c _) _) ?_
    dsimp only [t6Opk, encTr]
    have hc : rnd (t5Opk.length + 1) 32 = coins0Opk := by rw [t5Opk_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key0Opk) (by simp only [append_len, t5Opk_length]))
  have hopkUnused_c :
      (!PQXDH.opkUsedB ((t6Opk_comp.append (RndE 32)).append (NetE key0Opk)) "bob" (dhPk opkB)) =
      true := by
    unfold PQXDH.opkUsedB
    rw [someEventB_of_evIdx_nil]; · rfl
    dsimp only [t6Opk_comp, compOpkTr]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_ev, show _ = false from rfl, Bool.cond_false]
    dsimp only [t6Opk]; rw [evIdx_encTr]
    dsimp only [t5Opk, aliceTrOpk]
    rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
    dsimp only [t4Opk, genOneTimePrekeyTr]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_ev, show _ = false from rfl, Bool.cond_false, evIdx_append_non _ _ _ rfl]
    exact evIdx_t4_false _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hset : setRecvChain stB0'Opk_comp.recv cB'Opk = [cB'Opk] := by
    simp [setRecvChain, stB0'Opk_comp, ratchetState, cB'Opk, cBOpk, stB00Opk, bobSt0, maxReceiverChains]
  have hrs :
      ratchetState
        (bobSt0 "alice" ikB spkB (dhPk ikA) keysOpk (encSig stA0Opk coins0Opk key0Opk m0Opk))
        (encSig stA0Opk coins0Opk key0Opk m0Opk).ratchetKey (rnd t6Opk_comp.length 32) =
      (stB0'Opk_comp, cBOpk) := by
    rw [t6Opk_comp_length]; rfl
  have hruns : Runs (Composed.bobStart "bob" "alice" khOpk 1 mhOpk 37 1) t6Opk_comp 53 wTrOpk_comp :=
    runs_cast (Runs.bobStartOpk (kh := khOpk) (mh := mhOpk) (keys := keysOpk)
      (msg := encSig stA0Opk coins0Opk key0Opk m0Opk)
      (t := encMsg stA0Opk coins0Opk key0Opk m0Opk) (st' := stB0'Opk_comp) (c := cBOpk) (c' := cB'Opk)
      (seed := seedB0Opk) (pq := key0Opk) (m := m0Opk)
      (at?_mono h4_6c hb9) (at?_mono h4_6c hs13) (at?_mono h4_6c hp19) rfl (at?_mono h6_6c t6Opk_opk24)
      (at?_mono h4_6c ha1) (at?_mono h6_6c t6Opk_ek_at) (at?_mono h6_6c t6Opk_ct_at)
      (isCanonicalKey_dhPk _)
      (bobAgreement_honest_opk ikA (rnd t4Opk.length 32) ikB spkB pqskB opkB
        (rnd (t4Opk.length + 1) 32))
      hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsAOpk) hrs rfl
      (show Spqr.spqrRecv stB0'Opk_comp.spqr pqm0Opk 1 = _ from recv7Opk) hpq
      (mac_ok seedB0Opk_eq rfl rfl) (dec_ok seedB0Opk_eq) hopkUnused_c (stOut := stB1Opk_comp)
      (by rw [hset]; rfl))
      (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, t6Opk_comp_length])
      (by rw [skipTr_zero _ _ _ _ _ _ rfl]; dsimp only [wTrOpk_comp]; simp only [append_len, t6Opk_comp_length]; rfl)
  exact reach_of_runs hruns (bobStart_reachable r6c)

private theorem wTrOpk_comp_bobDone_at :
    wTrOpk_comp.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) 47 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [wTrOpk_comp]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t6Opk_comp_length]))

private theorem wTrOpk_comp_compOPK_at :
    wTrOpk_comp.EventLoggedAt (PQXDHEvent.CompromisedOPK "bob" (dhPk opkB)) 42 :=
  eventLoggedAt_mono t6Opk_comp_le_wTrOpk_comp (append2_ev_at _ _ _ t6Opk_length)

private theorem wTrOpk_comp_netOpk_at : wTrOpk_comp.at? 43 = some (NetE opkB) :=
  at?_mono t6Opk_comp_le_wTrOpk_comp (append2_snd_at _ _ _ (by rw [t6Opk_length]))

private theorem wTrOpk_comp_compromise_indices : evIdx wTrOpk_comp isCompromise = [42] := by
  dsimp only [wTrOpk_comp]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [t6Opk_comp, compOpkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, t6Opk_length]
  have h6 : evIdx t6Opk isCompromise = [] := by
    dsimp only [t6Opk]; rw [evIdx_encTr]
    dsimp only [t5Opk, aliceTrOpk]
    rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
    dsimp only [t4Opk, genOneTimePrekeyTr]
    rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
      evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
      evIdx_append_non _ _ _ rfl]
    exact honest_facts.2.2.2.2.2.2.2.2.1
  rw [h6]; rfl

private theorem wTrOpk_comp_trExposure_indices : trEvIdx wTrOpk_comp isAnyTRExposure = [] := by
  dsimp only [wTrOpk_comp]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_ev_false _ _ rfl, trEvIdx_append_ev_false _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  dsimp only [t6Opk_comp, compOpkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  dsimp only [t6Opk]; rw [trEvIdx_encTr]
  dsimp only [t5Opk, aliceTrOpk]; rw [trEvIdx_aliceTrOpt]
  dsimp only [t4Opk, genOneTimePrekeyTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.2.1

def trThm9Case2_opk : ExecTrace :=
  compPqTr (compSpkTr (compIkTr wTrOpk_comp "bob" ikB) "bob" spkB) "bob" pqskB

theorem trThm9Case2_opk_reach : trThm9Case2_opk.Reachable reachability := by
  obtain ⟨_, _, _, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_facts
  have h4o := t4_le_wTrOpk_comp
  have r1 : (compIkTr wTrOpk_comp "bob" ikB).Reachable reachability :=
    compIkTr_reach (idx := 9) wTrOpk_comp_reach (at?_mono h4o hb9)
  have r2 : (compSpkTr (compIkTr wTrOpk_comp "bob" ikB) "bob" spkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) r1 (at?_mono (le_append2 h4o _ _) hs13)
  exact compPqTr_reach (idx := 19) r2 (at?_mono (le_append2 (le_append2 h4o _ _) _ _) hp19)

theorem trThm9Case2_opk_bobDone :
    trThm9Case2_opk.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) 47 :=
  eventLoggedAt_mono
    (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    wTrOpk_comp_bobDone_at

theorem trThm9Case2_opk_compIK :
    trThm9Case2_opk.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 54 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append2_ev_at _ _ _ wTrOpk_comp_length)
theorem trThm9Case2_opk_compSPK :
    trThm9Case2_opk.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 56 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _)
    (append2_ev_at _ _ _ (by dsimp only [compIkTr]; simp only [append_len, wTrOpk_comp_length]))
theorem trThm9Case2_opk_compPQ :
    trThm9Case2_opk.EventLoggedAt (PQXDHEvent.CompromisedPQSPK "bob" (kemPk pqskB)) 58 :=
  append2_ev_at _ _ _
    (by dsimp only [compSpkTr, compIkTr]; simp only [append_len, wTrOpk_comp_length])
theorem trThm9Case2_opk_compOPK :
    trThm9Case2_opk.EventLoggedAt (PQXDHEvent.CompromisedOPK "bob" (dhPk opkB)) 42 :=
  eventLoggedAt_mono
    (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    wTrOpk_comp_compOPK_at

theorem trThm9Case2_opk_compromise_indices :
    evIdx trThm9Case2_opk isCompromise = [42, 54, 56, 58] := by
  dsimp only [trThm9Case2_opk, compPqTr, compSpkTr, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_ev_net _ _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, wTrOpk_comp_compromise_indices]
  simp only [append_len, wTrOpk_comp_length]; rfl
theorem trThm9Case2_opk_trExposure_indices : trEvIdx trThm9Case2_opk isAnyTRExposure = [] := by
  dsimp only [trThm9Case2_opk, compPqTr, compSpkTr, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact wTrOpk_comp_trExposure_indices

theorem trThm9Case2_opk_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm9Case2_opk keysOpk k :=
  not_sessionStateExposed_of_no_trExposure trThm9Case2_opk_trExposure_indices _ k

theorem trThm9Case2_opk_knows_block {k : Bytes} (hk : IsHandshakeBlock keysOpk k) :
    k.AttackerKnows trThm9Case2_opk := by
  have ho_tr : wTrOpk_comp ≤ trThm9Case2_opk :=
    le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _
  have h6_tr : t6Opk ≤ trThm9Case2_opk := le_trans t6Opk_le_wTrOpk_comp ho_tr
  have h4_tr : t4 ≤ trThm9Case2_opk := le_trans t4_le_t6Opk h6_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := some opkB)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h6_tr t6Opk_ek_at))
    (ak_net (at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    (ak_net (at?_mono ho_tr wTrOpk_comp_netOpk_at))
    (ak_net (at?_mono h6_tr t6Opk_ct_at)) hk

def trThm9Case3_opk : ExecTrace :=
  invertTr (breakKEMTr (compSpkTr (compIkTr wTrOpk_comp "bob" ikB) "bob" spkB)) pqskB

theorem trThm9Case3_opk_reach : trThm9Case3_opk.Reachable reachability := by
  obtain ⟨_, _, _, _, _, hb9, hs13, _, _, _, hp20, _⟩ := t4_facts
  have h4o := t4_le_wTrOpk_comp
  have r1 : (compIkTr wTrOpk_comp "bob" ikB).Reachable reachability :=
    compIkTr_reach (idx := 9) wTrOpk_comp_reach (at?_mono h4o hb9)
  have r2 : (compSpkTr (compIkTr wTrOpk_comp "bob" ikB) "bob" spkB).Reachable reachability :=
    compSpkTr_reach (idx := 13) r1 (at?_mono (le_append2 h4o _ _) hs13)
  have r3 : (breakKEMTr (compSpkTr (compIkTr wTrOpk_comp "bob" ikB) "bob" spkB)).Reachable reachability :=
    breakKEMTr_reach r2
  exact invertKEM_reach_sk (pkIdx := 20) r3
    (someEventB_of_at? (Trace.at?_append _ _) rfl)
    (at?_mono (le_append_of_le (le_append2 (le_append2 h4o _ _) _ _) _) hp20)

theorem trThm9Case3_opk_bobDone :
    trThm9Case3_opk.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) 47 :=
  eventLoggedAt_mono
    (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    wTrOpk_comp_bobDone_at

theorem trThm9Case3_opk_compIK :
    trThm9Case3_opk.EventLoggedAt (PQXDHEvent.CompromisedIK "bob" (dhPk ikB)) 54 :=
  eventLoggedAt_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
    (append2_ev_at _ _ _ wTrOpk_comp_length)
theorem trThm9Case3_opk_compSPK :
    trThm9Case3_opk.EventLoggedAt (PQXDHEvent.CompromisedSPK "bob" (dhPk spkB)) 56 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _)
    (append2_ev_at _ _ _ (by dsimp only [compIkTr]; simp only [append_len, wTrOpk_comp_length]))
theorem trThm9Case3_opk_brokenKEM :
    trThm9Case3_opk.EventLoggedAt PQXDHEvent.BrokenKEM 58 :=
  append2_ev_at _ _ _
    (by dsimp only [compSpkTr, compIkTr]; simp only [append_len, wTrOpk_comp_length])
theorem trThm9Case3_opk_compOPK :
    trThm9Case3_opk.EventLoggedAt (PQXDHEvent.CompromisedOPK "bob" (dhPk opkB)) 42 :=
  eventLoggedAt_mono
    (le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _)
    wTrOpk_comp_compOPK_at

theorem trThm9Case3_opk_compromise_indices :
    evIdx trThm9Case3_opk isCompromise = [42, 54, 56, 58] := by
  dsimp only [trThm9Case3_opk, invertTr, breakKEMTr, compSpkTr, compIkTr]
  rw [evIdx_append_ev_net _ _ _ _ rfl, evIdx_append_ev_net _ _ _ _ rfl,
    evIdx_append_ev_net _ _ _ _ rfl, wTrOpk_comp_compromise_indices]
  simp only [append_len, wTrOpk_comp_length]; rfl
theorem trThm9Case3_opk_trExposure_indices : trEvIdx trThm9Case3_opk isAnyTRExposure = [] := by
  dsimp only [trThm9Case3_opk, invertTr, breakKEMTr, compSpkTr, compIkTr]
  rw [trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl,
    trEvIdx_append_non _ _ rfl, trEvIdx_append_non _ _ rfl]
  exact wTrOpk_comp_trExposure_indices

theorem trThm9Case3_opk_no_sessionStateExposed (k : Bytes) :
    ¬ SessionStateExposed trThm9Case3_opk keysOpk k :=
  not_sessionStateExposed_of_no_trExposure trThm9Case3_opk_trExposure_indices _ k

theorem trThm9Case3_opk_knows_block {k : Bytes} (hk : IsHandshakeBlock keysOpk k) :
    k.AttackerKnows trThm9Case3_opk := by
  have ho_tr : wTrOpk_comp ≤ trThm9Case3_opk :=
    le_append2 (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _) _ _
  have h6_tr : t6Opk ≤ trThm9Case3_opk := le_trans t6Opk_le_wTrOpk_comp ho_tr
  have h4_tr : t4 ≤ trThm9Case3_opk := le_trans t4_le_t6Opk h6_tr
  exact ak_aliceAgreement_block_of_responderSecrets (opkSk := some opkB)
    (ak_net (at?_mono h4_tr t4_facts.2.1))
    (ak_net (at?_mono h6_tr t6Opk_ek_at))
    (ak_net (at?_mono (le_append2 (le_append2 (Trace.le_refl _) _ _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (at?_mono (le_append2 (Trace.le_refl _) _ _)
      (append2_snd_at _ _ _ rfl)))
    (ak_net (append2_snd_at _ _ _ rfl))
    (ak_net (at?_mono ho_tr wTrOpk_comp_netOpk_at))
    (ak_net (at?_mono h6_tr t6Opk_ct_at)) hk

/-! ### Witness Trace `trSessionExposedCKr` -/

def trSessionExposedCKr : ExecTrace := exposeCkrTr t8 "alice" stA0 cA0

theorem trSessionExposedCKr_reach : trSessionExposedCKr.Reachable reachability :=
  exposeCkr_reach (stH := 30) (pk := dhPk spkB) t8_reach
    (at?_mono honest_facts.2.1 t5_stA0_at)
    (by simp [findRecvChain, stA0, aliceSt, o1, cA0]; rfl)

theorem trSessionExposedCKr_aliceDone :
    trSessionExposedCKr.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_mono (le_append2 honest_facts.2.1 _ _) t5_aliceDone_at

theorem trSessionExposedCKr_bobDone :
    trSessionExposedCKr.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        none o1.ek o1.ct keys1) 47 :=
  eventLoggedAt_mono (le_append2 (Trace.le_refl _) _ _) t8_bobDone_at

theorem trSessionExposedCKr_exposedCKr :
    trSessionExposedCKr.EventLoggedAt (TREvent.ExposedCKr (stA0.sessionInfo "alice") keys1.ck 0 1) 54 :=
  append2_ev_at _ _ _ t8_length

theorem trSessionExposedCKr_compromise_indices : evIdx trSessionExposedCKr isCompromise = [] := by
  dsimp only [trSessionExposedCKr, exposeCkrTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  exact honest_facts.2.2.2.2.2.2.2.2.2.2.1
theorem trSessionExposedCKr_noCompromise : NoCompromise trSessionExposedCKr :=
  noCompromise_of_evIdx trSessionExposedCKr_compromise_indices

theorem trSessionExposedCKr_knows_ck : keys1.ck.AttackerKnows trSessionExposedCKr :=
  ak_net (append2_snd_at _ _ _ rfl)

end Symbolic.Proofs.Tests.Shared.Composed.Adversary
