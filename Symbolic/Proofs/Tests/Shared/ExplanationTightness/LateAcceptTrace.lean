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
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Late-Accept Tightness Witness

Constructs the reachable, single-session, non-replay late-accept trace `trLateAccept` separating
the existential root-compromise predicate `HandshakeRootCompromised_old_alice` from the
session-scoped universal `HandshakeRootCompromised`. Alice completes her handshake and sends
message 0 before Alice's identity key is compromised and Bob accepts, so Bob's handshake is
excused while Alice's earlier handshake is unexcused.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.LateAcceptTrace

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (coins0 dhsA ikA ikB key0 keys1 kh1 m0
  mh1 o1 pqm0 pqskB recv8 seedB0_eq spkB stA0 stB00 t1 t1_length t2 t2_length t3 t3_length t4
  t4_length t5 t5_aliceDone_at t5_length t6 t6_length t6_reach)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.bind
  Runs.bobStart Runs.genPQPrekey Runs.genSignedPrekey Runs.getKey Runs.logEvent
  Runs.registerIdentity Runs.sendMessage StP StT aliceTr aliceTrOpt bobAgreement_honest bobSt0
  bobStart_reachable compromiseIK_reachable dec_ok encMsg encSig encTr genPQPrekeyTr
  genSignedPrekeyTr mac_ok parse_encMsg ratchetState reach_of_runs recvSt registerIdentityTr
  rnd skipTr)

open DY DY.Comparse DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo kdfCk createChain setRecvChain TRState
  TREvent spqrB2A DerivesChain DerivesMsgKey)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys HandshakeKeysAt HandshakeWasCompromisedAt
  AliceHandshakeWasCompromised BobHandshakeWasCompromised LoggedBefore)
open DY.Libsignal.TripleRatchet.Cheval (HandshakeRootCompromised CompromisedKey)

/-! ## Trace plumbing helpers -/

private theorem nil_len : (Trace.nil : ExecTrace).length = 0 :=
  Symbolic.DYBridge.DY.Trace.length_eq_1

private theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace}
    (h : t1 ≤ t2) (e : E) : t1 ≤ t2.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le t2 e)

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

private theorem eventLoggedAt_of_at? {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact h

private theorem someEventB_nil (p : PQXDHEvent → Bool) :
    (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) Trace.nil p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]; rw [nil_len]; rfl

private theorem someEventB_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h : (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false) :
    (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append x) p = false := by
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
    (h : (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) tr p = false) :
    (DY.Libsignal.PQXDH.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent) (tr.append (EvP ev)) p = false := by
  simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
  rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
    exact h i hi
  · rw [Trace.at?_append]; exact hp

private theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [DY.Libsignal.TripleRatchet.logSkippedKeys, Traceful.run_pure]

private theorem x25519LowOrder_dhPk (sk : Bytes) :
    DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl0 : (dhPk sk).view? Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Literal.Literal.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl : Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]
  unfold DY.Libsignal.TripleRatchet.x25519LowOrder X25519.normalizeX25519Key
  rw [hv, hl]

private theorem isCanonicalKey_dhPk (sk : Bytes) :
    DY.Libsignal.PQXDH.isCanonicalKey (dhPk sk) = true := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl : DY.Libsignal.PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk sk
  unfold DY.Libsignal.PQXDH.isCanonicalKey
  rw [hv, hl]; rfl

private theorem runs_cast {α : Type} {x : Traceful α} {tr t1' t2' : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1') (ha : a1 = a2) (ht : t1' = t2') : Runs x tr a2 t2' := by
  subst ha; subst ht; exact h

private theorem aliceTrOpt_le (tr : ExecTrace) (a b : Participant)
    (ikA' ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    tr ≤ aliceTrOpt tr a b ikA' ikBPk spkPk pqPk opkPk := by
  dsimp only [aliceTrOpt]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _

private theorem encTr_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

private theorem t1_eq : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2

private theorem t2_eq : t2 = registerIdentityTr t1 "bob" := by
  refine (Runs.registerIdentity ?_).2
  unfold DY.Libsignal.PQXDH.isRegisteredB; rw [t1_eq]; dsimp only [registerIdentityTr]
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

private theorem t4_entry_facts :
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (Signature.vk ikA) true)) ∧
    t4.at? 4 = some (StP "alice" { kind := .identity, sk := ikA }) ∧
    t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) ∧
    t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) ∧
    t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_append_at _ _ (by simp only [append_len, nil_len])
  · refine at?_mono h24 ?_; rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))

/-! ## Late-accept trace construction -/

def tLate1 : ExecTrace :=
  (t6.append (EvP (.CompromisedIK "alice" (dhPk ikA)))).append (NetE ikA)

theorem tLate1_length : tLate1.length = 40 := by
  dsimp only [tLate1]; simp only [append_len, t6_length]

theorem tLate1_runs : Runs (DY.Libsignal.PQXDH.compromiseIK "alice" 4) t6 39 tLate1 := by
  have h46 : t4 ≤ t6 :=
    Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _) (encTr_le _ _ _ _ _)
  have ha4 : t6.at? 4 = some (StP "alice" { kind := .identity, sk := ikA }) :=
    at?_mono h46 t4_entry_facts.2.1
  unfold DY.Libsignal.PQXDH.compromiseIK
  exact runs_cast
    (Runs.bind (Runs.getKey ha4) (Runs.bind (Runs.logEvent _ _) (Runs.sendMessage _ _)))
    (by rw [append_len, t6_length]) rfl

theorem tLate1_reach : tLate1.Reachable reachability :=
  reach_of_runs tLate1_runs (compromiseIK_reachable t6_reach)

abbrev dhsBLate : Bytes := rnd 40 32

def stBLate0' : TRState := (ratchetState stB00 (dhPk dhsA) dhsBLate).1
def cBLate : RecvChain := (ratchetState stB00 (dhPk dhsA) dhsBLate).2
def cBLate' : RecvChain := { cBLate with chainKey := (kdfCk cBLate.chainKey).1, index := 1 }
def seedBLate0 : Bytes := (kdfCk cBLate.chainKey).2
def stBLate1 : TRState :=
  { stBLate0' with recv := [cBLate'], spqr := recvSt (Spqr.spqrInit keys1.pqr spqrB2A) pqm0 }

/-- Reachable single-session trace where `AliceDone` occurs at 27, `CompromisedIK "alice"` at 38,
and `BobDone` at 42. -/
def trLateAccept : ExecTrace :=
  let tr1 := (tLate1.append (RndE 32)).append (NetE key0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsBLate)))).append
      (EvT (.HonestDH (stBLate0'.sessionInfo "bob") dhsBLate 0))).append
      (EvC (.HandshakeSession (stBLate0'.sessionInfo "bob") 42))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
    (EvT (.MessageKey (stBLate0'.sessionInfo "bob") .receiver seedBLate0 key0 0 2 48))).append
    (StT "bob" stBLate1)

theorem trLateAccept_length : trLateAccept.length = 49 := by
  dsimp only [trLateAccept]; simp only [append_len, tLate1_length]

theorem trLateAccept_runs :
    Runs (DY.Libsignal.Composed.bobStart "bob" "alice" kh1 1 mh1 33 1) tLate1 48 trLateAccept := by
  obtain ⟨ha1, _, hb9, hs13, hp19⟩ := t4_entry_facts
  have h6L : t6 ≤ tLate1 := le_append_of_le (Trace.append_le _ _) _
  have h5L : t5 ≤ tLate1 := Trace.le_trans _ _ _ (encTr_le _ _ _ _ _) h6L
  have h4L : t4 ≤ tLate1 := Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _) h5L
  have hek : tLate1.at? 25 = some (NetE o1.ek) := by
    refine at?_mono h5L ?_; dsimp only [t5, aliceTr, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hct : tLate1.at? 26 = some (NetE o1.ct) := by
    refine at?_mono h5L ?_; dsimp only [t5, aliceTr, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hmsg : tLate1.at? 37 = some (NetE (encMsg stA0 coins0 key0 m0)) := by
    refine at?_mono h6L ?_; dsimp only [t6, encTr]
    have hm : rnd t5.length 32 = m0 := by rw [t5_length]
    have hc : rnd (t5.length + 1) 32 = coins0 := by rw [t5_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5_length])
  have hpq : ((tLate1.append (RndE 32)).append (NetE key0)).at? 33 = some (NetE key0) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) (at?_mono h6L ?_)
    dsimp only [t6, encTr]
    have hc : rnd (t5.length + 1) 32 = coins0 := by rw [t5_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key0) (by simp only [append_len, t5_length]))
  have hset : setRecvChain stBLate0'.recv cBLate' = [cBLate'] := by
    simp [setRecvChain, stBLate0', ratchetState, cBLate', cBLate, stB00, bobSt0,
      DY.Libsignal.TripleRatchet.maxReceiverChains]
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA0 coins0 key0 m0))
      (encSig stA0 coins0 key0 m0).ratchetKey (rnd tLate1.length 32) = (stBLate0', cBLate) := by
    rw [tLate1_length]; rfl
  exact runs_cast (Runs.bobStart (kh := kh1) (mh := mh1) (keys := keys1)
    (msg := encSig stA0 coins0 key0 m0)
    (t := encMsg stA0 coins0 key0 m0) (st' := stBLate0') (c := cBLate) (c' := cBLate')
    (seed := seedBLate0) (pq := key0) (m := m0)
    (at?_mono h4L hb9) (at?_mono h4L hs13) (at?_mono h4L hp19) rfl (at?_mono h4L ha1) hek hct
    (isCanonicalKey_dhPk _)
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsA) hrs rfl recv8 hpq
    (mac_ok seedB0_eq rfl rfl) (dec_ok seedB0_eq) (stOut := stBLate1) (by rw [hset]; rfl))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, tLate1_length])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; dsimp only [trLateAccept]; simp only [append_len, tLate1_length]; rfl)

theorem trLateAccept_reach : trLateAccept.Reachable reachability :=
  reach_of_runs trLateAccept_runs (bobStart_reachable tLate1_reach)

/-! ## Event positions and index enumerations on `trLateAccept` -/

private theorem tLate1_le_trLateAccept : tLate1 ≤ trLateAccept := by
  dsimp only [trLateAccept]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _

theorem trLateAccept_aliceDone_at :
    trLateAccept.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 := by
  have h5L : t5 ≤ trLateAccept :=
    Trace.le_trans _ _ _ (encTr_le _ _ _ _ _)
      (Trace.le_trans _ _ _ (le_append_of_le (Trace.append_le _ _) _) tLate1_le_trLateAccept)
  have h := t5_aliceDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono h5L h

theorem trLateAccept_compIK_at :
    trLateAccept.EventLoggedAt (PQXDHEvent.CompromisedIK "alice" (dhPk ikA)) 38 := by
  refine eventLoggedAt_of_at? (at?_mono tLate1_le_trLateAccept ?_)
  dsimp only [tLate1]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ t6_length)

theorem trLateAccept_bobDone_at :
    trLateAccept.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 42 := by
  refine eventLoggedAt_of_at? ?_
  dsimp only [trLateAccept]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len, tLate1_length]))

theorem trLateAccept_messageKeyA_at :
    trLateAccept.EventLoggedAt
      (TREvent.MessageKey (stA0.sessionInfo "alice") .sender (kdfCk stA0.cks).2
        key0 stA0.ns stA0.rIdx 30) 35 := by
  have h6L : t6 ≤ trLateAccept :=
    Trace.le_trans _ _ _ (le_append_of_le (Trace.append_le _ _) _) tLate1_le_trLateAccept
  refine eventLoggedAt_of_at? (at?_mono h6L ?_)
  dsimp only [t6, encTr]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ _ (by simp only [append_len, t5_length]))

private def evIdxOf (E : Type) [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (tr : ExecTrace)
    (p : E → Bool) : List Nat :=
  (List.range tr.length).filter fun i =>
    match tr.getEventAt E i with
    | some e => p e
    | none => false

private theorem mem_evIdxOf {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {tr : ExecTrace} {p : E → Bool} {e : E} {i : Nat}
    (h : tr.EventLoggedAt e i) (hp : p e = true) : i ∈ evIdxOf E tr p := by
  have hl := Trace.EventLoggedAt_implies_i_le_length e i tr h
  rw [Trace.EventLoggedAt_eq_getEventAt] at h
  simp only [evIdxOf, List.mem_filter, List.mem_range, h, hp, and_self, hl]

private theorem not_logged_of_evIdxOf {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {tr : ExecTrace} {p : E → Bool} (hidx : evIdxOf E tr p = []) {e : E} (hp : p e = true) :
    ¬ tr.EventLogged e := by
  rintro ⟨i, hi⟩
  have := mem_evIdxOf hi hp
  rw [hidx] at this
  exact List.not_mem_nil this

private theorem loggedAt_unique {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    {tr : ExecTrace} {e₁ e₂ : E} {i : Nat}
    (h₁ : tr.EventLoggedAt e₁ i) (h₂ : tr.EventLoggedAt e₂ i) : e₁ = e₂ := by
  rw [Trace.EventLoggedAt_eq_getEventAt] at h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

private theorem evIdxOf_nil {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    (p : E → Bool) : evIdxOf E Trace.nil p = [] := by
  unfold evIdxOf; rw [nil_len]; rfl

private theorem evIdxOf_append_non {E X : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] [ExecTraceTypes.Has X]
    (tr : ExecTrace) (x : X) (p : E → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT E)) = none) :
    evIdxOf E (tr.append x) p = evIdxOf E tr p := by
  unfold evIdxOf
  rw [append_len, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj, hnone]
      decide),
    List.filter_nil, List.append_nil]
  exact List.filter_congr fun i hi => by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr x (List.mem_range.mp hi)]

private theorem evIdxOf_append_ev {E : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    (tr : ExecTrace) (ev : E) (p : E → Bool) :
    evIdxOf E (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT E)) p =
      cond (p ev) (evIdxOf E tr p ++ [tr.length]) (evIdxOf E tr p) := by
  unfold evIdxOf
  rw [append_len, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by
          simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]
          decide),
        List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt tr ({ ev := ev } : ProtocolEvent.ExecEntryT E) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by
          simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append, hp]),
        List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_of_lt tr ({ ev := ev } : ProtocolEvent.ExecEntryT E) (List.mem_range.mp hi)])

private theorem evIdxOf_encTr_pq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) (p : PQXDHEvent → Bool) :
    evIdxOf PQXDHEvent (encTr tr me stH st pq) p = evIdxOf PQXDHEvent tr p := by
  dsimp only [encTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl]

private theorem evIdxOf_t4_pq_false (p : PQXDHEvent → Bool)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
    (h2 : ∀ u k, p (.SignedPrekeyPublished u k) = false)
    (h3 : ∀ u k, p (.PQPrekeyPublished u k) = false) :
    evIdxOf PQXDHEvent t4 p = [] := by
  rw [t4_eq]; dsimp only [genPQPrekeyTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, h3, Bool.cond_false, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl]
  rw [t3_eq]; dsimp only [genSignedPrekeyTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, h2, Bool.cond_false, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl]
  rw [t2_eq]; dsimp only [registerIdentityTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, h1, Bool.cond_false, evIdxOf_append_non _ _ _ rfl]
  rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, h1, Bool.cond_false, evIdxOf_append_non _ _ _ rfl, evIdxOf_nil]

private def isDoneEv : PQXDHEvent → Bool
  | .AliceDone .. | .BobDone .. => true
  | _ => false

private def isBobIKorDH : PQXDHEvent → Bool
  | .CompromisedIK p _ => p == "bob"
  | .BrokenDH => true
  | _ => false

private def isExposedEv : TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr .. | .ExposedMK .. => true
  | _ => false

private theorem trLateAccept_done_idx : evIdxOf PQXDHEvent trLateAccept isDoneEv = [27, 42] := by
  dsimp only [trLateAccept]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isDoneEv _ = true from rfl, Bool.cond_true]
  simp only [append_len, tLate1_length]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  dsimp only [tLate1]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_ev, show isDoneEv _ = false from rfl,
    Bool.cond_false]
  dsimp only [t6]; rw [evIdxOf_encTr_pq]
  dsimp only [t5, aliceTr, aliceTrOpt]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isDoneEv _ = true from rfl, Bool.cond_true]
  simp only [append_len, t4_length]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_t4_pq_false isDoneEv (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

private theorem trLateAccept_bobIKorDH_idx : evIdxOf PQXDHEvent trLateAccept isBobIKorDH = [] := by
  dsimp only [trLateAccept]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isBobIKorDH _ = false from rfl, Bool.cond_false,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  dsimp only [tLate1]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_ev,
    show isBobIKorDH (.CompromisedIK "alice" (dhPk ikA)) = false by decide,
    Bool.cond_false]
  dsimp only [t6]; rw [evIdxOf_encTr_pq]
  dsimp only [t5, aliceTr, aliceTrOpt]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isBobIKorDH _ = false from rfl, Bool.cond_false,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  exact evIdxOf_t4_pq_false isBobIKorDH (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem trLateAccept_exposed_idx : evIdxOf TREvent trLateAccept isExposedEv = [] := by
  dsimp only [trLateAccept]
  rw [evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  dsimp only [tLate1]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  dsimp only [t6, encTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  dsimp only [t5, aliceTr, aliceTrOpt]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_ev, show isExposedEv _ = false from rfl, Bool.cond_false,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  rw [t4_eq]; dsimp only [genPQPrekeyTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  rw [t3_eq]; dsimp only [genSignedPrekeyTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  rw [t2_eq]; dsimp only [registerIdentityTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl]
  rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl,
    evIdxOf_append_non _ _ _ rfl, evIdxOf_append_non _ _ _ rfl, evIdxOf_nil]

/-! ## Separation of `HandshakeRootCompromised` and `HandshakeRootCompromised_old_alice` -/

/-- Existential variant of `HandshakeRootCompromised` requiring only one compromised handshake. -/
def HandshakeRootCompromised_old_alice (tr : ExecTrace) (k : Bytes) : Prop :=
  ∃ keys j, HandshakeKeysAt tr j keys ∧ HandshakeWasCompromisedAt tr j ∧
    (k = keys.rk ∨ k = keys.ck)

theorem handshakeKeysAt_trLateAccept {j : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt trLateAccept j keys) : keys = keys1 := by
  rcases h with ⟨a, b, ikA', ikB', spk, pqpk, opk, ⟨ek, ct, h⟩ | ⟨ek, ct, h⟩⟩
  · have hm := mem_evIdxOf (p := isDoneEv) h rfl
    rw [trLateAccept_done_idx] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · cases loggedAt_unique h trLateAccept_aliceDone_at; rfl
    · cases loggedAt_unique h trLateAccept_bobDone_at
  · have hm := mem_evIdxOf (p := isDoneEv) h rfl
    rw [trLateAccept_done_idx] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · cases loggedAt_unique h trLateAccept_aliceDone_at
    · cases loggedAt_unique h trLateAccept_bobDone_at; rfl

theorem handshakeKeysAt_trLateAccept_27 : HandshakeKeysAt trLateAccept 27 keys1 :=
  ⟨_, _, _, _, _, _, _, Or.inl ⟨_, _, trLateAccept_aliceDone_at⟩⟩

theorem handshakeKeysAt_trLateAccept_42 : HandshakeKeysAt trLateAccept 42 keys1 :=
  ⟨_, _, _, _, _, _, _, Or.inr ⟨_, _, trLateAccept_bobDone_at⟩⟩

theorem excused_trLateAccept_42 : HandshakeWasCompromisedAt trLateAccept 42 :=
  Or.inr ⟨_, _, _, _, _, _, _, _, _, _, trLateAccept_bobDone_at,
    Or.inl (Or.inl ⟨38, trLateAccept_compIK_at, by decide⟩)⟩

theorem not_excused_trLateAccept_27 : ¬ HandshakeWasCompromisedAt trLateAccept 27 := by
  rintro (⟨a, b, ikA', ikB', spk, pqpk, opk, ek, ct, keys, halice, hx⟩ |
      ⟨b, a, ikB', ikA', spk, pqpk, opk, ek, ct, keys, hbob, _⟩)
  · cases loggedAt_unique halice trLateAccept_aliceDone_at
    rcases hx with ⟨j, hj, _⟩ | ⟨j, hj, _⟩
    · exact not_logged_of_evIdxOf trLateAccept_bobIKorDH_idx (by decide) ⟨j, hj⟩
    · exact not_logged_of_evIdxOf trLateAccept_bobIKorDH_idx rfl ⟨j, hj⟩
  · cases loggedAt_unique hbob trLateAccept_aliceDone_at

theorem handshakeRootCompromised_old_alice_trLateAccept :
    HandshakeRootCompromised_old_alice trLateAccept keys1.rk :=
  ⟨keys1, 42, handshakeKeysAt_trLateAccept_42, excused_trLateAccept_42, Or.inl rfl⟩

theorem not_handshakeRootCompromised_trLateAccept_any (k : Bytes) :
    ¬ HandshakeRootCompromised trLateAccept k := by
  rintro ⟨⟨keys, j, hkj, hkc⟩, hall⟩
  have hkeq := handshakeKeysAt_trLateAccept hkj
  subst hkeq
  exact not_excused_trLateAccept_27 (hall keys1 27 handshakeKeysAt_trLateAccept_27 hkc)

theorem not_handshakeRootCompromised_trLateAccept :
    ¬ HandshakeRootCompromised trLateAccept keys1.rk :=
  not_handshakeRootCompromised_trLateAccept_any keys1.rk

theorem not_compromised_trLateAccept (k : Bytes) :
    ¬ CompromisedKey trLateAccept k := by
  rintro (⟨s, i, h⟩ | ⟨s, i, h⟩ | ⟨s, ns, i, h⟩ | ⟨s, nr, i, h⟩ | ⟨s, n, i, h⟩ | hhrc | ⟨_, hbdh⟩)
  · exact not_logged_of_evIdxOf trLateAccept_exposed_idx rfl h
  · exact not_logged_of_evIdxOf trLateAccept_exposed_idx rfl h
  · exact not_logged_of_evIdxOf trLateAccept_exposed_idx rfl h
  · exact not_logged_of_evIdxOf trLateAccept_exposed_idx rfl h
  · exact not_logged_of_evIdxOf trLateAccept_exposed_idx rfl h
  · exact not_handshakeRootCompromised_trLateAccept_any k hhrc
  · exact not_logged_of_evIdxOf trLateAccept_bobIKorDH_idx rfl hbdh

/-- `trLateAccept` is reachable and separates `HandshakeRootCompromised_old_alice` from
`HandshakeRootCompromised` on `keys1.rk`. -/
theorem lateAccept_hrc_strict :
    trLateAccept.Reachable reachability ∧
    HandshakeRootCompromised_old_alice trLateAccept keys1.rk ∧
    ¬ HandshakeRootCompromised trLateAccept keys1.rk :=
  ⟨trLateAccept_reach, handshakeRootCompromised_old_alice_trLateAccept,
    not_handshakeRootCompromised_trLateAccept⟩

theorem derivesChain_stA0 : DerivesChain keys1.rk stA0.cks :=
  ⟨keys1.rk, dhPk spkB, dhsA, .refl, rfl⟩

theorem derivesMsgKey_stA0 : DerivesMsgKey stA0.cks (kdfCk stA0.cks).2 :=
  ⟨0, rfl⟩

/-- No message-key seed receives an `FSQuery` excuse under `CompromisedKey` on `trLateAccept`. -/
theorem not_fsQueryExcuse_trLateAccept (mk : Bytes) :
    ¬ (CompromisedKey trLateAccept mk ∨
        (∃ ck, DerivesMsgKey ck mk ∧ CompromisedKey trLateAccept ck) ∨
        (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ CompromisedKey trLateAccept rk)) := by
  rintro (hc | ⟨_, _, hc⟩ | ⟨_, _, _, _, hc⟩)
  · exact not_compromised_trLateAccept mk hc
  · exact not_compromised_trLateAccept _ hc
  · exact not_compromised_trLateAccept _ hc

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.LateAcceptTrace
