/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.Composed.Runs
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
public import Symbolic.Tests.ModelNonVacuity
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
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Shared Honest Session Traces for `DY.Libsignal.Composed`

Constructs two reachable, compromise-free execution traces of the composed protocol: `wTr`, a
90-entry multi-step session without a one-time prekey (`t1 .. t15`), and `wTrOpk`, a 52-entry
session with a one-time prekey (`t4Opk .. t7Opk`), together with reachability, event, and
`NoCompromise` / `HonestRun` lemmas on their prefixes.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Shared.Composed.HonestSession

open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_init_agree spqrRecv_not_init)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.aliceStart
  Runs.aliceStartOpk Runs.bobStart Runs.bobStartOpk Runs.exposeCkr Runs.exposeCks
  Runs.genOneTimePrekey Runs.genPQPrekey Runs.genSignedPrekey Runs.messageDecrypt_noRatchet
  Runs.messageDecrypt_ratchet Runs.messageEncrypt Runs.registerIdentity StP StT aliceOut
  aliceOutOpk aliceOutOpt aliceSt aliceStart_reachable aliceTr aliceTrOpk aliceTrOpt
  bobAgreement_honest bobAgreement_honest_opk bobSt0 bobStart_reachable createChain_comm dec_ok
  dhPk_rnd_ne encMsg encSig encSt encTr exposeCkrTr exposeCksTr exposeKey_reachable
  genOneTimePrekeyTr genOneTimePrekey_reachable genPQPrekeyTr genPQPrekey_reachable
  genSignedPrekeyTr genSignedPrekey_reachable mac_ok messageDecrypt_reachable
  messageEncrypt_reachable parse_encMsg ratchetState reach_of_runs recvKey recvSt
  registerIdentityTr registerIdentity_reachable rnd skipTr)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent SignalMsg hmac kdfCk chainKeyAt
  createChain x25519LowOrder computeMac messageVersion maxReceiverChains maxForwardJumps u32Max
  lit litByte hkdfBlock1 hkdfBlock2 hkdfBlock3 zeroSalt consumeMessageKey
  findRecvChain setRecvChain recvChainFor TRState TREvent TRSignalMsg spqrA2B spqrB2A trMsgKeys
  trHonestWireMsg parseTrSignalMsg)
open PQXDH (PQXDHState PQXDHEvent KeyKind HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles serializedIk AliceHandshakeOut BobHandshakeOut aliceAgreement bobAgreement
  pqxdhKdf pqxdhIkm pqxdhLabel discontinuity agree isCanonicalKey encodeEC encodeKEM NoCompromise
  HonestRun KeyKnown)

/-! ## Honest Session Trace `wTr` (without OPK) -/

abbrev ikA : Bytes := rnd 0 32
abbrev ikB : Bytes := rnd 5 32
abbrev spkB : Bytes := rnd 10 32
abbrev spkNonce : Bytes := rnd 11 64
abbrev pqskB : Bytes := rnd 16 64
abbrev pqNonce : Bytes := rnd 17 64

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

private theorem messageSentAt_of_at? {tr : ExecTrace} {b : Bytes} {i : Nat}
    (h : tr.at? i = some (NetE b)) : tr.MessageSentAt b i := by
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact h

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

private theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [TripleRatchet.logSkippedKeys, Traceful.run_pure]

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

private theorem recvSt_not_init (st msg : Bytes) :
    (recvSt st msg).view? Spqr.InitState.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Spqr.InitState.SubF
    ({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes)

private theorem spqrSend_st_not_init (st coins : Bytes) :
    (Spqr.spqrSend st coins).1.view? Spqr.InitState.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Spqr.InitState.SubF
    ({ st := st, coins := coins } : Spqr.SendState.SubF Bytes)

private theorem isCurrentSnapshot_append_self (tr : ExecTrace) (me : Participant) (st : TRState)
    {k : Nat} (hk : tr.length = k) :
    TripleRatchet.isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [Trace.at?_append tr (StT me st), append_len, Nat.sub_self]; rfl

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
      rw [at?_append_of_lt tr e (by rw [List.mem_range'_1] at hj; omega)]
      exact hcur j hj
    · rw [at?_append_self_proj, hnone]

private theorem isCurrentSnapshot_append_st_ne {tr : ExecTrace} {me me' : Participant}
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
  rw [at?_mono (Trace.append_le tr (StT me' st')) hst]
  dsimp only at hcur ⊢
  have hsub : (tr.append (StT me' st')).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
    rw [append_len]; omega
  rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
    List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hcur ⊢
    intro j hj
    rw [at?_append_of_lt tr (StT me' st') (by rw [List.mem_range'_1] at hj; omega)]
    exact hcur j hj
  · rw [Trace.at?_append]; simp [hne]

private theorem isCurrentSnapshot_encTr_self (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : TRState) (pq : Bytes) {n5 : Nat} (h5 : tr.length + 5 = n5) :
    TripleRatchet.isCurrentSnapshot (encTr tr me stH st pq) n5 = true := by
  subst h5; dsimp only [encTr]
  refine isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_self _ _ _ ?_)
  simp only [append_len]

private theorem isCurrentSnapshot_encTr_ne {tr : ExecTrace} {me me' : Participant}
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
    le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _
  refine isCurrentSnapshot_append_non_st _ rfl
    (isCurrentSnapshot_append_st_ne (at?_mono h5le hst) hne ?_)
  exact isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
    (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
      (isCurrentSnapshot_append_non_st _ rfl hcur))))

private theorem runs_cast {α : Type} {x : Traceful α} {tr t1 t2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1) (ha : a1 = a2) (ht : t1 = t2) : Runs x tr a2 t2 := by
  subst ha; subst ht; exact h

private theorem aliceTrOpt_le (tr : ExecTrace) (a b : Participant)
    (ikA ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    tr ≤ aliceTrOpt tr a b ikA ikBPk spkPk pqPk opkPk := by
  dsimp only [aliceTrOpt]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _

private theorem encTr_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

def t1 : ExecTrace := ((PQXDH.registerIdentity "alice").run Trace.nil).2.val
def t2 : ExecTrace := ((PQXDH.registerIdentity "bob").run t1).2.val
def t3 : ExecTrace := ((PQXDH.genSignedPrekey "bob" 9).run t2).2.val
def t4 : ExecTrace := ((PQXDH.genPQPrekey "bob" 9).run t3).2.val

private theorem t1_eq : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by unfold PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2

theorem t1_length : t1.length = 5 := by
  rw [t1_eq]; simp only [registerIdentityTr, append_len, nil_len]

private theorem t2_eq : t2 = registerIdentityTr t1 "bob" := by
  refine (Runs.registerIdentity ?_).2
  unfold PQXDH.isRegisteredB; rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [someEventB_append_non _ _ _ rfl (someEventB_append_non _ _ _ rfl
    (someEventB_append_non _ _ _ rfl (someEventB_append_false _ _ _ rfl
      (someEventB_append_non _ _ _ rfl (someEventB_nil _)))))]
  rfl

theorem t2_length : t2.length = 10 := by
  rw [t2_eq]; simp only [registerIdentityTr, append_len, t1_length]

private theorem t3_eq : t3 = genSignedPrekeyTr t2 "bob" ikB := by
  have hb : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  exact (Runs.genSignedPrekey hb).2

theorem t3_length : t3.length = 16 := by
  rw [t3_eq]; simp only [genSignedPrekeyTr, append_len, t2_length]

private theorem t4_eq : t4 = genPQPrekeyTr t3 "bob" ikB := by
  have hb2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have h23 : t2 ≤ t3 := by
    rw [t3_eq]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t2 _) _) _) _) _) _
  exact (Runs.genPQPrekey (at?_mono h23 hb2)).2

theorem t4_length : t4.length = 22 := by
  rw [t4_eq]; simp only [genPQPrekeyTr, append_len, t3_length]

private theorem t4_facts :
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h14 ?_; rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_append_at _ _ (by simp only [append_len, nil_len])
  · refine at?_mono h24 ?_; rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t1_length]))
  · refine at?_mono h24 ?_; rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · refine at?_mono h34 ?_; rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_append_at _ _ (by simp only [append_len, t2_length])
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))
  · rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_append_at _ _ (by simp only [append_len, t3_length])

def bh1 : BundleHandles := { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := none }

def t5 : ExecTrace := aliceTr t4 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)

theorem t5_length : t5.length = 31 := by
  dsimp only [t5, aliceTr, aliceTrOpt]; simp only [append_len, t4_length]

theorem t5_runs : Runs (Composed.aliceStart "alice" "bob" 4 6 bh1) t4 30 t5 := by
  obtain ⟨_, ha4, hb6, _, _, hs14, hs15, _, hp20, hp21⟩ := t4_facts
  exact runs_cast (Runs.aliceStart (h := bh1) ha4 hb6 hs14 hs15 hp20 hp21 (Signature.verify_sign _ _ _)
    (Signature.verify_sign _ _ _) rfl (x25519LowOrder_dhPk spkB)) (by rw [t4_length]) rfl

abbrev o1 : AliceHandshakeOut := aliceOut t4 ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
abbrev keys1 : HandshakeKeys := o1.keys
abbrev dhsA : Bytes := rnd 24 32
def stA0 : TRState := aliceSt "bob" o1 dhsA

abbrev m0 : Bytes := rnd 31 32
abbrev coins0 : Bytes := rnd 32 32
def key0 : Bytes := (Spqr.spqrSend stA0.spqr coins0).2.1
def pqm0 : Bytes := (Spqr.spqrSend stA0.spqr coins0).2.2
def t6 : ExecTrace := encTr t5 "alice" 30 stA0 key0
def stA1 : TRState := encSt stA0 coins0

theorem t6_length : t6.length = 38 := by
  dsimp only [t6, encTr]; simp only [append_len, t5_length]

theorem t6_runs : Runs (TripleRatchet.messageEncrypt "alice" 30 32 33) t5 37 t6 := by
  have hst : t5.at? 30 = some (StT "alice" stA0) := by
    dsimp only [t5, aliceTr, aliceTrOpt, stA0, dhsA]
    have hd : rnd (t4.length + 2) 32 = rnd 24 32 := by rw [t4_length]
    rw [hd]
    exact at?_append_at _ _ (by simp only [append_len, t4_length])
  have hpq : (((t5.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend stA0.spqr (rnd (t5.length + 1) 32)).2.1)).at? 33 = some (NetE key0) := by
    have hc : rnd (t5.length + 1) 32 = coins0 := by rw [t5_length]
    rw [hc]
    exact at?_append_at _ (NetE key0) (by simp only [append_len, t5_length])
  exact runs_cast (Runs.messageEncrypt (tr := t5) (stH := 30) (pqH := 33) (st := stA0) (pq := key0) hst
    (by decide) hpq) (by rw [t5_length]) rfl

abbrev m1 : Bytes := rnd 38 32
abbrev coins1 : Bytes := rnd 39 32
def key1 : Bytes := (Spqr.spqrSend stA1.spqr coins1).2.1
def pqm1 : Bytes := (Spqr.spqrSend stA1.spqr coins1).2.2
def t7 : ExecTrace := encTr t6 "alice" 36 stA1 key1
def stA2 : TRState := encSt stA1 coins1

theorem t7_length : t7.length = 45 := by
  dsimp only [t7, encTr]; simp only [append_len, t6_length]

theorem t7_runs : Runs (TripleRatchet.messageEncrypt "alice" 36 32 40) t6 44 t7 := by
  have hst : t6.at? 36 = some (StT "alice" stA1) := by
    dsimp only [t6, encTr, stA1]
    have hc : rnd (t5.length + 1) 32 = coins0 := by rw [t5_length]
    rw [hc]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t5_length]))
  have hpq : (((t6.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend stA1.spqr (rnd (t6.length + 1) 32)).2.1)).at? 40 = some (NetE key1) := by
    have hc : rnd (t6.length + 1) 32 = coins1 := by rw [t6_length]
    rw [hc]
    exact at?_append_at _ (NetE key1) (by simp only [append_len, t6_length])
  exact runs_cast (Runs.messageEncrypt (tr := t6) (stH := 36) (pqH := 40) (st := stA1) (pq := key1) hst
    (by decide) hpq) (by rw [t6_length]) rfl

def kh1 : BobKeyHandles := { ik := 9, spk := 13, pqspk := 19, opk := none }
def mh1 : PreKeyMsgHandles := { ek := 25, ct := 26, msg := 37 }
abbrev dhsB1 : Bytes := rnd 45 32
def stB00 : TRState := bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA0 coins0 key0 m0)
def stB0' : TRState := (ratchetState stB00 (dhPk dhsA) dhsB1).1
def cB : RecvChain := (ratchetState stB00 (dhPk dhsA) dhsB1).2
def cB' : RecvChain := { cB with chainKey := (kdfCk cB.chainKey).1, index := 1 }
def seedB0 : Bytes := (kdfCk cB.chainKey).2
def stB1 : TRState :=
  { stB0' with recv := [cB'], spqr := recvSt (Spqr.spqrInit keys1.pqr spqrB2A) pqm0 }

theorem recv8 : Spqr.spqrRecv stB0'.spqr pqm0 1 =
    some (recvSt (Spqr.spqrInit keys1.pqr spqrB2A) pqm0, key0) :=
  spqrRecv_init_agree keys1.pqr coins0 pqm0 .b2a (bytesToLiteral_spqrSendMsg _ _)

def t8 : ExecTrace :=
  let tr1 := (t7.append (RndE 32)).append (NetE key0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
      (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0))).append
      (EvC (.HandshakeSession (stB0'.sessionInfo "bob") 47))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
    (EvT (.MessageKey (stB0'.sessionInfo "bob") .receiver seedB0 key0 0 2 53))).append
    (StT "bob" stB1)

theorem t8_length : t8.length = 54 := by
  dsimp only [t8]; simp only [append_len, t7_length]

theorem seedB0_eq : (kdfCk stA0.cks).2 = seedB0 := by
  show (kdfCk (createChain keys1.rk (dhPk spkB) dhsA).2).2 =
    (kdfCk (createChain keys1.rk (dhPk dhsA) spkB).2).2
  rw [createChain_comm keys1.rk dhsA spkB]

theorem t8_runs : Runs (Composed.bobStart "bob" "alice" kh1 1 mh1 33 1) t7 53 t8 := by
  obtain ⟨ha1, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_facts
  have h57 : t5 ≤ t7 := Trace.le_trans _ _ _ (encTr_le _ _ _ _ _) (encTr_le _ _ _ _ _)
  have h47 : t4 ≤ t7 := Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _) h57
  have hek : t7.at? 25 = some (NetE o1.ek) := by
    refine at?_mono h57 ?_; dsimp only [t5, aliceTr, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hct : t7.at? 26 = some (NetE o1.ct) := by
    refine at?_mono h57 ?_; dsimp only [t5, aliceTr, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hmsg : t7.at? 37 = some (NetE (encMsg stA0 coins0 key0 m0)) := by
    refine at?_mono (encTr_le _ _ _ _ _) ?_; dsimp only [t6, encTr]
    have hm : rnd t5.length 32 = m0 := by rw [t5_length]
    have hc : rnd (t5.length + 1) 32 = coins0 := by rw [t5_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5_length])
  have hpq : ((t7.append (RndE 32)).append (NetE key0)).at? 33 = some (NetE key0) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) (at?_mono (encTr_le _ _ _ _ _) ?_)
    dsimp only [t6, encTr]
    have hc : rnd (t5.length + 1) 32 = coins0 := by rw [t5_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key0) (by simp only [append_len, t5_length]))
  have hset : setRecvChain stB0'.recv cB' = [cB'] := by
    simp [setRecvChain, stB0', ratchetState, cB', cB, stB00, bobSt0, maxReceiverChains]
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA0 coins0 key0 m0))
      (encSig stA0 coins0 key0 m0).ratchetKey (rnd t7.length 32) = (stB0', cB) := by
    rw [t7_length]; rfl
  exact runs_cast (Runs.bobStart (kh := kh1) (mh := mh1) (keys := keys1)
    (msg := encSig stA0 coins0 key0 m0)
    (t := encMsg stA0 coins0 key0 m0) (st' := stB0') (c := cB) (c' := cB') (seed := seedB0)
    (pq := key0) (m := m0)
    (at?_mono h47 hb9) (at?_mono h47 hs13) (at?_mono h47 hp19) rfl (at?_mono h47 ha1) hek hct
    (isCanonicalKey_dhPk _)
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsA) hrs rfl recv8 hpq
    (mac_ok seedB0_eq rfl rfl) (dec_ok seedB0_eq) (stOut := stB1) (by rw [hset]; rfl))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, t7_length])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; dsimp only [t8]; simp only [append_len, t7_length]; rfl)

def cB'' : RecvChain := { cB' with chainKey := (kdfCk cB'.chainKey).1, index := 2 }
def seedB1 : Bytes := (kdfCk cB'.chainKey).2
def stB2 : TRState := { stB1 with recv := [cB''], spqr := recvSt stB1.spqr pqm1 }

theorem recv9 : Spqr.spqrRecv stB1.spqr pqm1 2 = some (stB2.spqr, recvKey stB1.spqr pqm1) :=
  spqrRecv_not_init _ _ _ (recvSt_not_init _ _) (bytesToLiteral_spqrSendMsg _ _)

def t9 : ExecTrace :=
  let tr0 := t8.append (NetE (recvKey stB1.spqr pqm1))
  ((tr0.append (EvT (.Received "bob" "alice" (dhPk dhsA) 1 m1))).append
    (EvT (.MessageKey (stB1.sessionInfo "bob") .receiver seedB1 key1 1 2 53))).append
    (StT "bob" stB2)

theorem t9_length : t9.length = 58 := by
  dsimp only [t9]; simp only [append_len, t8_length]

theorem seedB1_eq : (kdfCk stA1.cks).2 = seedB1 := by
  show (kdfCk (kdfCk (createChain keys1.rk (dhPk spkB) dhsA).2).1).2 =
    (kdfCk (kdfCk (createChain keys1.rk (dhPk dhsA) spkB).2).1).2
  rw [createChain_comm keys1.rk dhsA spkB]

theorem t9_runs : Runs (TripleRatchet.messageDecrypt "bob" 53 44 40 2) t8 57 t9 := by
  have h78 : t7 ≤ t8 := by
    dsimp only [t8]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _
  have hst : t8.at? 53 = some (StT "bob" stB1) := by
    dsimp only [t8]; exact at?_append_at _ _ (by simp only [append_len, t7_length])
  have hmsg : t8.at? 44 = some (NetE (encMsg stA1 coins1 key1 m1)) := by
    refine at?_mono h78 ?_; dsimp only [t7, encTr]
    have hm : rnd t6.length 32 = m1 := by rw [t6_length]
    have hc : rnd (t6.length + 1) 32 = coins1 := by rw [t6_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t6_length])
  have hpq : (t8.append (NetE (recvKey stB1.spqr pqm1))).at? 40 = some (NetE key1) := by
    refine at?_mono (Trace.append_le _ _) (at?_mono h78 ?_)
    dsimp only [t7, encTr]
    have hc : rnd (t6.length + 1) 32 = coins1 := by rw [t6_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key1) (by simp only [append_len, t6_length]))
  have hset : setRecvChain stB1.recv cB'' = [cB''] := by
    simp [setRecvChain, stB1, cB'', cB']
  exact runs_cast (Runs.messageDecrypt_noRatchet (st := stB1) (msg := encSig stA1 coins1 key1 m1)
    (t := encMsg stA1 coins1 key1 m1) (c := cB') (c' := cB'') (pq := key1) (seed := seedB1)
    (m := m1) hst hmsg (parse_encMsg _ _ _ _) rfl
    (by simp [findRecvChain, stB1, encSig, stA1, encSt, stA0, aliceSt, cB', cB, ratchetState])
    rfl recv9 hpq (mac_ok seedB1_eq rfl rfl) (dec_ok seedB1_eq) (stOut := stB2)
    (by rw [hset]; rfl))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, t8_length])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; rfl)

abbrev m2 : Bytes := rnd 58 32
abbrev coins2 : Bytes := rnd 59 32
def key2 : Bytes := (Spqr.spqrSend stB2.spqr coins2).2.1
def pqm2 : Bytes := (Spqr.spqrSend stB2.spqr coins2).2.2
def t10 : ExecTrace := encTr t9 "bob" 57 stB2 key2
def stB3 : TRState := encSt stB2 coins2

theorem t10_length : t10.length = 65 := by
  dsimp only [t10, encTr]; simp only [append_len, t9_length]

theorem t10_runs : Runs (TripleRatchet.messageEncrypt "bob" 57 32 60) t9 64 t10 := by
  have hst : t9.at? 57 = some (StT "bob" stB2) := by
    dsimp only [t9]; exact at?_append_at _ _ (by simp only [append_len, t8_length])
  have hpq : (((t9.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend stB2.spqr (rnd (t9.length + 1) 32)).2.1)).at? 60 = some (NetE key2) := by
    have hc : rnd (t9.length + 1) 32 = coins2 := by rw [t9_length]
    rw [hc]
    exact at?_append_at _ (NetE key2) (by simp only [append_len, t9_length])
  exact runs_cast (Runs.messageEncrypt (tr := t9) (stH := 57) (pqH := 60) (st := stB2) (pq := key2) hst
    (by decide) hpq) (by rw [t9_length]) rfl

abbrev dhsA2 : Bytes := rnd 65 32
def stA3' : TRState := (ratchetState stA2 (dhPk dhsB1) dhsA2).1
def cA1 : RecvChain := (ratchetState stA2 (dhPk dhsB1) dhsA2).2
def cA1' : RecvChain := { cA1 with chainKey := (kdfCk cA1.chainKey).1, index := 1 }
def cA0 : RecvChain := { ratchetKey := dhPk spkB, chainKey := keys1.ck, index := 0, rIdx := 1 }
def stA4 : TRState := { stA3' with recv := [cA0, cA1'], spqr := recvSt stA2.spqr pqm2 }
def seedA1 : Bytes := (kdfCk cA1.chainKey).2

theorem recv11 : Spqr.spqrRecv stA3'.spqr pqm2 1 = some (stA4.spqr, recvKey stA2.spqr pqm2) :=
  spqrRecv_not_init _ _ _ (spqrSend_st_not_init _ _) (bytesToLiteral_spqrSendMsg _ _)

def t11 : ExecTrace :=
  let tr1 := (((t10.append (RndE 32)).append (NetE (recvKey stA2.spqr pqm2))).append
    (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1) (dhPk dhsA2)))).append
    (EvT (.HonestDH (stA3'.sessionInfo "alice") dhsA2 1))
  ((tr1.append (EvT (.Received "alice" "bob" (dhPk dhsB1) 0 m2))).append
    (EvT (.MessageKey (stA3'.sessionInfo "alice") .receiver seedA1 key2 0 3 43))).append
    (StT "alice" stA4)

theorem t11_length : t11.length = 72 := by
  dsimp only [t11]; simp only [append_len, t10_length]

theorem seedA1_eq : (kdfCk stB2.cks).2 = seedA1 := by
  show (kdfCk (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2).2 =
    (kdfCk (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsB1) dhsA).2).2
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsA dhsB1]

theorem t11_runs : Runs (TripleRatchet.messageDecrypt "alice" 43 64 60 1) t10 71 t11 := by
  have h78 : t7 ≤ t8 := by
    dsimp only [t8]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _
  have h89 : t8 ≤ t9 := by
    dsimp only [t9]
    exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _
  have h7_10 : t7 ≤ t10 := Trace.le_trans _ _ _ h78 (Trace.le_trans _ _ _ h89 (encTr_le _ _ _ _ _))
  have hst : t10.at? 43 = some (StT "alice" stA2) := by
    refine at?_mono h7_10 ?_; dsimp only [t7, encTr, stA2]
    have hc : rnd (t6.length + 1) 32 = coins1 := by rw [t6_length]
    rw [hc]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t6_length]))
  have hmsg : t10.at? 64 = some (NetE (encMsg stB2 coins2 key2 m2)) := by
    dsimp only [t10, encTr]
    have hm : rnd t9.length 32 = m2 := by rw [t9_length]
    have hc : rnd (t9.length + 1) 32 = coins2 := by rw [t9_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t9_length])
  have hpq : ((t10.append (RndE 32)).append (NetE (recvKey stA2.spqr pqm2))).at? 60 =
      some (NetE key2) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [t10, encTr]
    have hc : rnd (t9.length + 1) 32 = coins2 := by rw [t9_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key2) (by simp only [append_len, t9_length]))
  have hne : dhPk spkB ≠ dhPk dhsB1 := dhPk_rnd_ne (by decide)
  have ho1 : o1.spk = dhPk spkB := rfl
  have hrs : ratchetState stA2 (encSig stB2 coins2 key2 m2).ratchetKey (rnd t10.length 32) =
      (stA3', cA1) := by
    rw [t10_length]; rfl
  have hset : setRecvChain stA3'.recv cA1' = [cA0, cA1'] := by
    simp [setRecvChain, stA3', ratchetState, cA1', cA1, stA2, stA1, encSt, stA0, aliceSt, cA0,
      ho1, hne, maxReceiverChains]
  have hfind : findRecvChain stA2.recv (dhPk dhsB1) = none := by
    simp [findRecvChain, stA2, stA1, encSt, stA0, aliceSt, ho1, hne]
  exact runs_cast (Runs.messageDecrypt_ratchet (st := stA2) (st' := stA3') (c := cA1) (c' := cA1')
    (msg := encSig stB2 coins2 key2 m2) (t := encMsg stB2 coins2 key2 m2) (pq := key2)
    (seed := seedA1) (m := m2)
    hst hmsg (parse_encMsg _ _ _ _) rfl hfind (x25519LowOrder_dhPk dhsB1) hrs rfl recv11 hpq
    (mac_ok seedA1_eq rfl rfl) (dec_ok seedA1_eq) (stOut := stA4) (by rw [hset]; rfl))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, t10_length])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; rfl)

def t12 : ExecTrace := exposeCkrTr t11 "alice" stA4 cA0
def t13 : ExecTrace := exposeCksTr t12 "alice" stA4

theorem t12_length : t12.length = 74 := by
  dsimp only [t12, exposeCkrTr]; simp only [append_len, t11_length]
theorem t13_length : t13.length = 76 := by
  dsimp only [t13, exposeCksTr]; simp only [append_len, t12_length]

theorem find_cA0 : findRecvChain stA4.recv (dhPk spkB) = some cA0 := by
  simp [findRecvChain, stA4, cA0]

theorem t12_runs : Runs (TripleRatchet.exposeKey "alice" 71 (.ckr (dhPk spkB))) t11 73 t12 := by
  have hst : t11.at? 71 = some (StT "alice" stA4) := by
    dsimp only [t11]; exact at?_append_at _ _ (by simp only [append_len, t10_length])
  exact runs_cast (Runs.exposeCkr (tr := t11) (stH := 71) hst find_cA0) (by rw [t11_length]) rfl

theorem t13_runs : Runs (TripleRatchet.exposeKey "alice" 71 .cks) t12 75 t13 := by
  have hst11 : t11.at? 71 = some (StT "alice" stA4) := by
    dsimp only [t11]; exact at?_append_at _ _ (by simp only [append_len, t10_length])
  have hst12 : t12.at? 71 = some (StT "alice" stA4) :=
    at?_mono (le_append_of_le (Trace.append_le _ _) _) hst11
  exact runs_cast (Runs.exposeCks (tr := t12) (stH := 71) (st := stA4) hst12) (by rw [t12_length]) rfl

abbrev m3 : Bytes := rnd 76 32
abbrev coins3 : Bytes := rnd 77 32
def key3 : Bytes := (Spqr.spqrSend stA4.spqr coins3).2.1
def pqm3 : Bytes := (Spqr.spqrSend stA4.spqr coins3).2.2
def t14 : ExecTrace := encTr t13 "alice" 71 stA4 key3
def stA5 : TRState := encSt stA4 coins3

theorem t14_length : t14.length = 83 := by
  dsimp only [t14, encTr]; simp only [append_len, t13_length]

theorem t14_runs : Runs (TripleRatchet.messageEncrypt "alice" 71 32 78) t13 82 t14 := by
  have hst11 : t11.at? 71 = some (StT "alice" stA4) := by
    dsimp only [t11]; exact at?_append_at _ _ (by simp only [append_len, t10_length])
  have hst : t13.at? 71 = some (StT "alice" stA4) :=
    at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_mono (le_append_of_le (Trace.append_le _ _) _) hst11)
  have hpq : (((t13.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend stA4.spqr (rnd (t13.length + 1) 32)).2.1)).at? 78 = some (NetE key3) := by
    have hc : rnd (t13.length + 1) 32 = coins3 := by rw [t13_length]
    rw [hc]
    exact at?_append_at _ (NetE key3) (by simp only [append_len, t13_length])
  exact runs_cast (Runs.messageEncrypt (tr := t13) (stH := 71) (pqH := 78) (st := stA4) (pq := key3) hst
    (by decide) hpq) (by rw [t13_length]) rfl

abbrev dhsB2 : Bytes := rnd 83 32
def stB4' : TRState := (ratchetState stB3 (dhPk dhsA2) dhsB2).1
def cB2 : RecvChain := (ratchetState stB3 (dhPk dhsA2) dhsB2).2
def cB2' : RecvChain := { cB2 with chainKey := (kdfCk cB2.chainKey).1, index := 1 }
def stB5 : TRState := { stB4' with recv := [cB'', cB2'], spqr := recvSt stB3.spqr pqm3 }
def seedB3 : Bytes := (kdfCk cB2.chainKey).2

theorem recv15 : Spqr.spqrRecv stB4'.spqr pqm3 3 = some (stB5.spqr, recvKey stB3.spqr pqm3) :=
  spqrRecv_not_init _ _ _ (spqrSend_st_not_init _ _) (bytesToLiteral_spqrSendMsg _ _)

def t15 : ExecTrace :=
  let tr1 := (((t14.append (RndE 32)).append (NetE (recvKey stB3.spqr pqm3))).append
    (EvT (.DHRatchet "bob" "alice" (dhPk dhsA2) (dhPk dhsB2)))).append
    (EvT (.HonestDH (stB4'.sessionInfo "bob") dhsB2 2))
  ((tr1.append (EvT (.Received "bob" "alice" (dhPk dhsA2) 0 m3))).append
    (EvT (.MessageKey (stB4'.sessionInfo "bob") .receiver seedB3 key3 0 4 63))).append
    (StT "bob" stB5)

theorem t15_length : t15.length = 90 := by
  dsimp only [t15]; simp only [append_len, t14_length]

theorem seedB3_eq : (kdfCk stA4.cks).2 = seedB3 := by
  show (kdfCk (createChain (createChain (createChain keys1.rk (dhPk spkB) dhsA).1
      (dhPk dhsB1) dhsA).1 (dhPk dhsB1) dhsA2).2).2 =
    (kdfCk (createChain (createChain (createChain keys1.rk (dhPk dhsA) spkB).1
      (dhPk dhsA) dhsB1).1 (dhPk dhsA2) dhsB1).2).2
  rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsA dhsB1,
    createChain_comm _ dhsA2 dhsB1]

theorem t15_runs : Runs (TripleRatchet.messageDecrypt "bob" 63 82 78 3) t14 89 t15 := by
  have h10_11 : t10 ≤ t11 := by
    dsimp only [t11]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _
  have h11_13 : t11 ≤ t13 :=
    Trace.le_trans _ _ _ (le_append_of_le (Trace.append_le _ _) _)
      (le_append_of_le (Trace.append_le _ _) _)
  have h10_14 : t10 ≤ t14 :=
    Trace.le_trans _ _ _ h10_11 (Trace.le_trans _ _ _ h11_13 (encTr_le _ _ _ _ _))
  have hst : t14.at? 63 = some (StT "bob" stB3) := by
    refine at?_mono h10_14 ?_; dsimp only [t10, encTr, stB3]
    have hc : rnd (t9.length + 1) 32 = coins2 := by rw [t9_length]
    rw [hc]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t9_length]))
  have hmsg : t14.at? 82 = some (NetE (encMsg stA4 coins3 key3 m3)) := by
    dsimp only [t14, encTr]
    have hm : rnd t13.length 32 = m3 := by rw [t13_length]
    have hc : rnd (t13.length + 1) 32 = coins3 := by rw [t13_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t13_length])
  have hpq : ((t14.append (RndE 32)).append (NetE (recvKey stB3.spqr pqm3))).at? 78 =
      some (NetE key3) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [t14, encTr]
    have hc : rnd (t13.length + 1) 32 = coins3 := by rw [t13_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key3) (by simp only [append_len, t13_length]))
  have hne : dhPk dhsA ≠ dhPk dhsA2 := dhPk_rnd_ne (by decide)
  have hrs : ratchetState stB3 (encSig stA4 coins3 key3 m3).ratchetKey (rnd t14.length 32) =
      (stB4', cB2) := by
    rw [t14_length]; rfl
  have hset : setRecvChain stB4'.recv cB2' = [cB'', cB2'] := by
    simp [setRecvChain, stB4', ratchetState, cB2', cB2, stB3, encSt, stB2, cB'', cB', cB,
      stB00, bobSt0, encSig, stA0, aliceSt, hne, maxReceiverChains]
  have hfind : findRecvChain stB3.recv (dhPk dhsA2) = none := by
    simp [findRecvChain, stB3, encSt, stB2, cB'', cB', cB, stB00, bobSt0, ratchetState, encSig,
      stA0, aliceSt, hne]
  exact runs_cast (Runs.messageDecrypt_ratchet (st := stB3) (st' := stB4') (c := cB2) (c' := cB2')
    (msg := encSig stA4 coins3 key3 m3) (t := encMsg stA4 coins3 key3 m3) (pq := key3)
    (seed := seedB3) (m := m3)
    hst hmsg (parse_encMsg _ _ _ _) rfl hfind (x25519LowOrder_dhPk dhsA2) hrs rfl recv15 hpq
    (mac_ok seedB3_eq rfl rfl) (dec_ok seedB3_eq) (stOut := stB5) (by rw [hset]; rfl))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, t14_length])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; rfl)

/-- The 90-entry honest session trace without a one-time prekey. -/
def wTr : ExecTrace := t15

theorem length_wTr : wTr.length = 90 := t15_length

private theorem wTr_le_facts :
    t5 ≤ t8 ∧ t8 ≤ t11 ∧ t11 ≤ t12 ∧ t12 ≤ t13 ∧ t13 ≤ wTr ∧ t5 ≤ wTr ∧ t8 ≤ wTr ∧
    t11 ≤ wTr ∧ t12 ≤ wTr := by
  have h57 : t5 ≤ t7 := Trace.le_trans _ _ _ (encTr_le _ _ _ _ _) (encTr_le _ _ _ _ _)
  have h78 : t7 ≤ t8 := by
    dsimp only [t8]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _
  have h58 : t5 ≤ t8 := Trace.le_trans _ _ _ h57 h78
  have h89 : t8 ≤ t9 := by
    dsimp only [t9]
    exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _
  have h10_11 : t10 ≤ t11 := by
    dsimp only [t11]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _
  have h8_11 : t8 ≤ t11 :=
    Trace.le_trans _ _ _ h89 (Trace.le_trans _ _ _ (encTr_le _ _ _ _ _) h10_11)
  have h11_12 : t11 ≤ t12 := le_append_of_le (Trace.append_le _ _) _
  have h12_13 : t12 ≤ t13 := le_append_of_le (Trace.append_le _ _) _
  have h14_15 : t14 ≤ wTr := by
    dsimp only [wTr, t15]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _
  have h13_w : t13 ≤ wTr := Trace.le_trans _ _ _ (encTr_le _ _ _ _ _) h14_15
  have h12_w : t12 ≤ wTr := Trace.le_trans _ _ _ h12_13 h13_w
  have h11_w : t11 ≤ wTr := Trace.le_trans _ _ _ h11_12 h12_w
  have h8_w : t8 ≤ wTr := Trace.le_trans _ _ _ h8_11 h11_w
  have h5_w : t5 ≤ wTr := Trace.le_trans _ _ _ h58 h8_w
  exact ⟨h58, h8_11, h11_12, h12_13, h13_w, h5_w, h8_w, h11_w, h12_w⟩

/-! ### Reachability of every prefix `t1 .. t15` and `wTr` -/

theorem t1_reach : t1.Reachable reachability := registerIdentity_reachable .Base
theorem t2_reach : t2.Reachable reachability := registerIdentity_reachable t1_reach
theorem t3_reach : t3.Reachable reachability := genSignedPrekey_reachable t2_reach
theorem t4_reach : t4.Reachable reachability := genPQPrekey_reachable t3_reach
theorem t5_reach : t5.Reachable reachability := reach_of_runs t5_runs (aliceStart_reachable t4_reach)
theorem t6_reach : t6.Reachable reachability :=
  reach_of_runs t6_runs (messageEncrypt_reachable t5_reach
    (hcur := by
      dsimp only [t5, aliceTr, aliceTrOpt]
      exact isCurrentSnapshot_append_self _ _ _ (by simp only [append_len, t4_length])))
theorem t7_reach : t7.Reachable reachability :=
  reach_of_runs t7_runs (messageEncrypt_reachable t6_reach
    (hcur := isCurrentSnapshot_encTr_self t5 "alice" 30 stA0 key0 (by rw [t5_length])))
theorem t8_reach : t8.Reachable reachability := reach_of_runs t8_runs (bobStart_reachable t7_reach)
theorem t9_reach : t9.Reachable reachability :=
  reach_of_runs t9_runs (messageDecrypt_reachable t8_reach
    (hcur := by
      dsimp only [t8]
      exact isCurrentSnapshot_append_self _ _ _ (by simp only [append_len, t7_length])))
theorem t10_reach : t10.Reachable reachability :=
  reach_of_runs t10_runs (messageEncrypt_reachable t9_reach
    (hcur := by
      dsimp only [t9]
      exact isCurrentSnapshot_append_self _ _ _ (by simp only [append_len, t8_length])))
theorem t11_reach : t11.Reachable reachability :=
  reach_of_runs t11_runs (messageDecrypt_reachable t10_reach
    (hcur := by
      have hst7 : t7.at? 43 = some (StT "alice" stA2) := by
        dsimp only [t7, encTr, stA2]
        have hc : rnd (t6.length + 1) 32 = coins1 := by rw [t6_length]
        rw [hc]
        exact at?_mono (Trace.append_le _ _)
          (at?_append_at _ _ (by simp only [append_len, t6_length]))
      have hcur7 : TripleRatchet.isCurrentSnapshot t7 43 = true :=
        isCurrentSnapshot_encTr_self t6 "alice" 36 stA1 key1 (by rw [t6_length])
      have h78pre : t7 ≤ (((((((t7.append (RndE 32)).append (NetE key0)).append
          (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
            o1.ek o1.ct keys1))).append
          (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
          (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0))).append
          (EvC (.HandshakeSession (stB0'.sessionInfo "bob") 47))).append
          (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
          (EvT (.MessageKey (stB0'.sessionInfo "bob") .receiver seedB0 key0 0 2 53)) :=
        le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
          (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _
      have hcur8 : TripleRatchet.isCurrentSnapshot t8 43 = true := by
        dsimp only [t8]
        refine isCurrentSnapshot_append_st_ne (at?_mono h78pre hst7) rfl ?_
        exact isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
            (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
              (isCurrentSnapshot_append_non_st _ rfl
                (isCurrentSnapshot_append_non_st _ rfl hcur7)))))))
      have hst8 : t8.at? 43 = some (StT "alice" stA2) :=
        at?_mono (le_append_of_le h78pre _) hst7
      have h89pre : t8 ≤ ((t8.append (NetE (recvKey stB1.spqr pqm1))).append
          (EvT (.Received "bob" "alice" (dhPk dhsA) 1 m1))).append
          (EvT (.MessageKey (stB1.sessionInfo "bob") .receiver seedB1 key1 1 2 53)) :=
        le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _
      have hcur9 : TripleRatchet.isCurrentSnapshot t9 43 = true := by
        dsimp only [t9]
        refine isCurrentSnapshot_append_st_ne (at?_mono h89pre hst8) rfl ?_
        exact isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl hcur8))
      exact isCurrentSnapshot_encTr_ne (at?_mono (le_append_of_le h89pre _) hst8) rfl hcur9))
theorem t12_reach : t12.Reachable reachability :=
  reach_of_runs t12_runs (exposeKey_reachable t11_reach)
theorem t13_reach : t13.Reachable reachability :=
  reach_of_runs t13_runs (exposeKey_reachable t12_reach)
theorem t14_reach : t14.Reachable reachability :=
  reach_of_runs t14_runs (messageEncrypt_reachable t13_reach
    (hcur := by
      have hcur11 : TripleRatchet.isCurrentSnapshot t11 71 = true := by
        dsimp only [t11]
        exact isCurrentSnapshot_append_self _ _ _ (by simp only [append_len, t10_length])
      exact isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl hcur11)))))
theorem t15_reach : t15.Reachable reachability :=
  reach_of_runs t15_runs (messageDecrypt_reachable t14_reach
    (hcur := by
      have hst10 : t10.at? 63 = some (StT "bob" stB3) := by
        dsimp only [t10, encTr, stB3]
        have hc : rnd (t9.length + 1) 32 = coins2 := by rw [t9_length]
        rw [hc]
        exact at?_mono (Trace.append_le _ _)
          (at?_append_at _ _ (by simp only [append_len, t9_length]))
      have hcur10 : TripleRatchet.isCurrentSnapshot t10 63 = true :=
        isCurrentSnapshot_encTr_self t9 "bob" 57 stB2 key2 (by rw [t9_length])
      have h10_11pre : t10 ≤ (((((t10.append (RndE 32)).append (NetE (recvKey stA2.spqr pqm2))).append
          (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1) (dhPk dhsA2)))).append
          (EvT (.HonestDH (stA3'.sessionInfo "alice") dhsA2 1))).append
          (EvT (.Received "alice" "bob" (dhPk dhsB1) 0 m2))).append
          (EvT (.MessageKey (stA3'.sessionInfo "alice") .receiver seedA1 key2 0 3 43)) :=
        le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
          (le_append_of_le (Trace.append_le _ _) _) _) _) _) _
      have hcur11 : TripleRatchet.isCurrentSnapshot t11 63 = true := by
        dsimp only [t11]
        refine isCurrentSnapshot_append_st_ne (at?_mono h10_11pre hst10) rfl ?_
        exact isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
            (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl hcur10)))))
      have hcur13 : TripleRatchet.isCurrentSnapshot t13 63 = true :=
        isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl hcur11)))
      have hst13 : t13.at? 63 = some (StT "bob" stB3) :=
        at?_mono wTr_le_facts.2.2.2.1
          (at?_mono wTr_le_facts.2.2.1 (at?_mono (le_append_of_le h10_11pre _) hst10))
      exact isCurrentSnapshot_encTr_ne hst13 rfl hcur13))
theorem wTr_reach : wTr.Reachable reachability := t15_reach

abbrev t1_reachable := t1_reach
abbrev t2_reachable := t2_reach
abbrev t3_reachable := t3_reach
abbrev t4_reachable := t4_reach
abbrev t5_reachable := t5_reach
abbrev t6_reachable := t6_reach
abbrev t7_reachable := t7_reach
abbrev t8_reachable := t8_reach
abbrev t9_reachable := t9_reach
abbrev t10_reachable := t10_reach
abbrev t11_reachable := t11_reach
abbrev t12_reachable := t12_reach
abbrev t13_reachable := t13_reach
abbrev t14_reachable := t14_reach
abbrev t15_reachable := t15_reach
abbrev wTr_reachable := wTr_reach

/-! ### Trace facts on `wTr` and its prefixes -/

theorem t5_aliceDone_at :
    t5.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t5, aliceTr, aliceTrOpt]
  exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t4_length]))

theorem t8_aliceDone_at :
    t8.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 := by
  have h := t5_aliceDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.1 h

theorem t11_aliceDone_at :
    t11.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 := by
  have h := t8_aliceDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.1 h

theorem wTr_aliceDone_at :
    wTr.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 := by
  have h := t5_aliceDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.1 h

theorem wTr_aliceDone :
    wTr.EventLogged
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) := ⟨27, wTr_aliceDone_at⟩

theorem t5_initSession_at :
    t5.EventLoggedAt (TREvent.InitSession "alice" "bob" (dhPk dhsA) (dhPk spkB)) 28 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t5, aliceTr, aliceTrOpt, dhsA]
  have hd : rnd (t4.length + 2) 32 = rnd 24 32 := by rw [t4_length]
  rw [hd]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ _ (by simp only [append_len, t4_length]))

theorem wTr_initSession_at :
    wTr.EventLoggedAt (TREvent.InitSession "alice" "bob" (dhPk dhsA) (dhPk spkB)) 28 := by
  have h := t5_initSession_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.1 h

theorem t5_handshakeSessionA_at :
    t5.EventLoggedAt (ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27) 29 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t5, aliceTr, aliceTrOpt, stA0, dhsA]
  have hd : rnd (t4.length + 2) 32 = rnd 24 32 := by rw [t4_length]
  have h5 : t4.length + 5 = 27 := by rw [t4_length]
  rw [hd, h5]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t4_length]))

theorem wTr_handshakeSessionA_at :
    wTr.EventLoggedAt (ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27) 29 := by
  have h := t5_handshakeSessionA_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.1 h

theorem wTr_handshakeSessionA :
    wTr.EventLogged (ComposedEvent.HandshakeSession (stA0.sessionInfo "alice") 27) :=
  ⟨29, wTr_handshakeSessionA_at⟩

theorem t5_stA0_at : t5.at? 30 = some (StT "alice" stA0) := by
  dsimp only [t5, aliceTr, aliceTrOpt, stA0, dhsA]
  have hd : rnd (t4.length + 2) 32 = rnd 24 32 := by rw [t4_length]
  rw [hd]
  exact at?_append_at _ _ (by simp only [append_len, t4_length])

theorem wTr_stA0_at : wTr.at? 30 = some (StT "alice" stA0) :=
  at?_mono wTr_le_facts.2.2.2.2.2.1 t5_stA0_at

theorem t8_bobDone_at :
    t8.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 47 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t8]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t7_length]))

theorem t11_bobDone_at :
    t11.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 47 := by
  have h := t8_bobDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.1 h

theorem wTr_bobDone_at :
    wTr.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 47 := by
  have h := t8_bobDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.2.1 h

theorem wTr_bobDone :
    wTr.EventLogged
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) := ⟨47, wTr_bobDone_at⟩

theorem t8_handshakeSessionB_at :
    t8.EventLoggedAt (ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47) 50 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t8]
  exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t7_length]))

theorem wTr_handshakeSessionB_at :
    wTr.EventLoggedAt (ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47) 50 := by
  have h := t8_handshakeSessionB_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.2.1 h

theorem wTr_handshakeSessionB :
    wTr.EventLogged (ComposedEvent.HandshakeSession (stB0'.sessionInfo "bob") 47) :=
  ⟨50, wTr_handshakeSessionB_at⟩

theorem t8_stB1_at : t8.at? 53 = some (StT "bob" stB1) := by
  dsimp only [t8]; exact at?_append_at _ _ (by simp only [append_len, t7_length])
theorem wTr_stB1_at : wTr.at? 53 = some (StT "bob" stB1) :=
  at?_mono wTr_le_facts.2.2.2.2.2.2.1 t8_stB1_at

theorem t11_stA4_at : t11.at? 71 = some (StT "alice" stA4) := by
  dsimp only [t11]; exact at?_append_at _ _ (by simp only [append_len, t10_length])
theorem wTr_stA4_at : wTr.at? 71 = some (StT "alice" stA4) :=
  at?_mono wTr_le_facts.2.2.2.2.2.2.2.1 t11_stA4_at

theorem t12_exposedCKr_at :
    t12.EventLoggedAt (TREvent.ExposedCKr (stA4.sessionInfo "alice") keys1.ck 0 1) 72 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t12, exposeCkrTr, cA0]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ t11_length)

theorem wTr_exposedCKr_at :
    wTr.EventLoggedAt (TREvent.ExposedCKr (stA4.sessionInfo "alice") keys1.ck 0 1) 72 := by
  have h := t12_exposedCKr_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.2.2.2 h

theorem wTr_exposedCKr :
    wTr.EventLogged (TREvent.ExposedCKr (stA4.sessionInfo "alice") keys1.ck 0 1) :=
  ⟨72, wTr_exposedCKr_at⟩

theorem t12_ck_sent_at : t12.MessageSentAt keys1.ck 73 := by
  refine messageSentAt_of_at? ?_; dsimp only [t12, exposeCkrTr, cA0]
  exact at?_append_at _ _ (by simp only [append_len, t11_length])

theorem wTr_ck_sent_at : wTr.MessageSentAt keys1.ck 73 := by
  have h := t12_ck_sent_at
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.2.2.2.2 h

theorem t13_exposedCKs_at :
    t13.EventLoggedAt (TREvent.ExposedCKs (stA4.sessionInfo "alice") stA4.cks 0 3) 74 := by
  refine eventLoggedAt_of_at? ?_
  have hns : stA4.ns = 0 := rfl
  have hr : stA4.rIdx = 3 := rfl
  dsimp only [t13, exposeCksTr]
  rw [hns, hr]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ t12_length)

theorem wTr_exposedCKs_at :
    wTr.EventLoggedAt (TREvent.ExposedCKs (stA4.sessionInfo "alice") stA4.cks 0 3) 74 := by
  have h := t13_exposedCKs_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.1 h

theorem wTr_exposedCKs :
    wTr.EventLogged (TREvent.ExposedCKs (stA4.sessionInfo "alice") stA4.cks 0 3) :=
  ⟨74, wTr_exposedCKs_at⟩

theorem t13_cks_sent_at : t13.MessageSentAt stA4.cks 75 := by
  refine messageSentAt_of_at? ?_; dsimp only [t13, exposeCksTr]
  exact at?_append_at _ _ (by simp only [append_len, t12_length])

theorem wTr_cks_sent_at : wTr.MessageSentAt stA4.cks 75 := by
  have h := t13_cks_sent_at
  rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1] at h ⊢
  exact at?_mono wTr_le_facts.2.2.2.2.1 h

/-! ### No PQXDH compromise on `wTr` and its prefixes -/

/-- The trace indices whose `PQXDHEvent` satisfies `p`. -/
def evIdx (tr : ExecTrace) (p : PQXDHEvent → Bool) : List Nat :=
  (List.range tr.length).filter fun i =>
    match tr.getEventAt PQXDHEvent i with
    | some e => p e
    | none => false

theorem mem_evIdx {tr : ExecTrace} {p : PQXDHEvent → Bool} {e : PQXDHEvent} {i : Nat}
    (h : tr.EventLoggedAt e i) (hp : p e = true) : i ∈ evIdx tr p := by
  have hl := Trace.EventLoggedAt_implies_i_le_length e i tr h
  rw [Trace.EventLoggedAt_eq_getEventAt] at h
  simp only [evIdx, List.mem_filter, List.mem_range, h, hp, and_self, hl]

theorem not_logged {tr : ExecTrace} {p : PQXDHEvent → Bool} (hidx : evIdx tr p = [])
    {e : PQXDHEvent} (hp : p e = true) : ¬ tr.EventLogged e := by
  rintro ⟨i, hi⟩
  have := mem_evIdx hi hp
  rw [hidx] at this
  exact List.not_mem_nil this

/-- Compromise and break events. -/
def isCompromise : PQXDHEvent → Bool
  | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedPQSPK .. | .CompromisedOPK ..
  | .BrokenDH | .BrokenKEM => true
  | _ => false

theorem noCompromise_of_evIdx {tr : ExecTrace} (hidx : evIdx tr isCompromise = []) :
    NoCompromise tr :=
  ⟨fun _ _ => not_logged hidx rfl, fun _ _ => not_logged hidx rfl,
    fun _ _ => not_logged hidx rfl, fun _ _ => not_logged hidx rfl,
    not_logged hidx rfl, not_logged hidx rfl⟩

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

private theorem evIdx_eq_nil_of_le {t1 t2 : ExecTrace} {p : PQXDHEvent → Bool}
    (hle : t1 ≤ t2) (h2 : evIdx t2 p = []) : evIdx t1 p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  simp only [evIdx, List.mem_filter, List.mem_range, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hi
  cases hat : (t1.at? i : Option (ProtocolEvent.ExecEntryT PQXDHEvent)) with
  | none => rw [hat] at hi; exact Bool.noConfusion hi.2
  | some ev =>
    rw [hat] at hi
    have hmem : i ∈ evIdx t2 p :=
      mem_evIdx (eventLoggedAt_of_at? (at?_mono hle hat)) hi.2
    rw [h2] at hmem
    exact List.not_mem_nil hmem

private theorem evIdx_t4_false (p : PQXDHEvent → Bool)
    (h1 : ∀ u k v b, p (.IdentityRegistered u k v b) = false)
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
    evIdx_append_ev, h1, Bool.cond_false, evIdx_append_non _ _ _ rfl]
  rw [t1_eq]; dsimp only [registerIdentityTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, h1, Bool.cond_false, evIdx_append_non _ _ _ rfl, evIdx_nil]

theorem noCompromise_idx : evIdx wTr isCompromise = [] := by
  dsimp only [wTr, t15]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl]
  dsimp only [t14]; rw [evIdx_encTr]
  dsimp only [t13, exposeCksTr, t12, exposeCkrTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [t11]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl]
  dsimp only [t10]; rw [evIdx_encTr]
  dsimp only [t9]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [t8]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [t7, t6]; rw [evIdx_encTr, evIdx_encTr]
  dsimp only [t5, aliceTr]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
  exact evIdx_t4_false isCompromise (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem wTr_noCompromise : NoCompromise wTr := noCompromise_of_evIdx noCompromise_idx
theorem t5_noCompromise : NoCompromise t5 :=
  noCompromise_of_evIdx (evIdx_eq_nil_of_le wTr_le_facts.2.2.2.2.2.1 noCompromise_idx)
theorem t8_noCompromise : NoCompromise t8 :=
  noCompromise_of_evIdx (evIdx_eq_nil_of_le wTr_le_facts.2.2.2.2.2.2.1 noCompromise_idx)
theorem t11_noCompromise : NoCompromise t11 :=
  noCompromise_of_evIdx (evIdx_eq_nil_of_le wTr_le_facts.2.2.2.2.2.2.2.1 noCompromise_idx)

theorem wTr_honestRun : HonestRun false wTr :=
  ⟨"alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, none, o1.ek, o1.ct, keys1,
    by decide, rfl, wTr_aliceDone, wTr_bobDone⟩

theorem t8_honestRun : HonestRun false t8 :=
  ⟨"alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, none, o1.ek, o1.ct, keys1,
    by decide, rfl, ⟨27, t8_aliceDone_at⟩, ⟨47, t8_bobDone_at⟩⟩

/-! ## Honest Session Trace `wTrOpk` (with OPK) -/

abbrev opkB : Bytes := rnd 22 32

def t4Opk : ExecTrace := genOneTimePrekeyTr t4 "bob"

theorem t4Opk_length : t4Opk.length = 26 := by
  dsimp only [t4Opk, genOneTimePrekeyTr]; simp only [append_len, t4_length]

theorem t4Opk_runs : Runs (PQXDH.genOneTimePrekey "bob") t4 24 t4Opk :=
  runs_cast (Runs.genOneTimePrekey t4 "bob") (by rw [t4_length]) rfl

def bhOpk : BundleHandles :=
  { spk := 14, spkSig := 15, pqpk := 20, pqpkSig := 21, opk := some 25 }

def t5Opk : ExecTrace :=
  aliceTrOpk t4Opk "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (dhPk opkB)

theorem t5Opk_length : t5Opk.length = 35 := by
  dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]; simp only [append_len, t4Opk_length]

theorem t5Opk_runs : Runs (Composed.aliceStart "alice" "bob" 4 6 bhOpk) t4Opk 34 t5Opk := by
  obtain ⟨_, ha4, hb6, _, _, hs14, hs15, _, hp20, hp21⟩ := t4_facts
  have h4o : t4 ≤ t4Opk := by
    dsimp only [t4Opk, genOneTimePrekeyTr]
    exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _
  have hopk : t4Opk.at? 25 = some (NetE (dhPk opkB)) := by
    dsimp only [t4Opk, genOneTimePrekeyTr, opkB]; rw [t4_length]
    exact at?_append_at _ _ (by simp only [append_len, t4_length])
  have hlowOpk : ((some (dhPk opkB)).all (!x25519LowOrder ·)) = true := by
    simp [x25519LowOrder_dhPk]
  exact runs_cast (Runs.aliceStartOpk (h := bhOpk) (at?_mono h4o ha4) (at?_mono h4o hb6)
    (at?_mono h4o hs14) (at?_mono h4o hs15) (at?_mono h4o hp20) (at?_mono h4o hp21)
    (Signature.verify_sign _ _ _) (Signature.verify_sign _ _ _) rfl hopk
    (x25519LowOrder_dhPk spkB) hlowOpk) (by rw [t4Opk_length]) rfl

abbrev oOpk : AliceHandshakeOut :=
  aliceOutOpk t4Opk ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (dhPk opkB)
abbrev keysOpk : HandshakeKeys := oOpk.keys
abbrev dhsAOpk : Bytes := rnd 28 32
def stA0Opk : TRState := aliceSt "bob" oOpk dhsAOpk

abbrev m0Opk : Bytes := rnd 35 32
abbrev coins0Opk : Bytes := rnd 36 32
def key0Opk : Bytes := (Spqr.spqrSend stA0Opk.spqr coins0Opk).2.1
def pqm0Opk : Bytes := (Spqr.spqrSend stA0Opk.spqr coins0Opk).2.2
def t6Opk : ExecTrace := encTr t5Opk "alice" 34 stA0Opk key0Opk
def stA1Opk : TRState := encSt stA0Opk coins0Opk

theorem t6Opk_length : t6Opk.length = 42 := by
  dsimp only [t6Opk, encTr]; simp only [append_len, t5Opk_length]

theorem t6Opk_runs : Runs (TripleRatchet.messageEncrypt "alice" 34 32 37) t5Opk 41 t6Opk := by
  have hst : t5Opk.at? 34 = some (StT "alice" stA0Opk) := by
    dsimp only [t5Opk, aliceTrOpk, aliceTrOpt, stA0Opk, dhsAOpk]
    have hd : rnd (t4Opk.length + 2) 32 = rnd 28 32 := by rw [t4Opk_length]
    rw [hd]
    exact at?_append_at _ _ (by simp only [append_len, t4Opk_length])
  have hpq : (((t5Opk.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend stA0Opk.spqr (rnd (t5Opk.length + 1) 32)).2.1)).at? 37 =
      some (NetE key0Opk) := by
    have hc : rnd (t5Opk.length + 1) 32 = coins0Opk := by rw [t5Opk_length]
    rw [hc]
    exact at?_append_at _ (NetE key0Opk) (by simp only [append_len, t5Opk_length])
  exact runs_cast (Runs.messageEncrypt (tr := t5Opk) (stH := 34) (pqH := 37) (st := stA0Opk) (pq := key0Opk)
    hst (by decide) hpq) (by rw [t5Opk_length]) rfl

def khOpk : BobKeyHandles := { ik := 9, spk := 13, pqspk := 19, opk := some 24 }
def mhOpk : PreKeyMsgHandles := { ek := 29, ct := 30, msg := 41 }
abbrev dhsB1Opk : Bytes := rnd 42 32
def stB00Opk : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) keysOpk (encSig stA0Opk coins0Opk key0Opk m0Opk)
def stB0'Opk : TRState := (ratchetState stB00Opk (dhPk dhsAOpk) dhsB1Opk).1
def cBOpk : RecvChain := (ratchetState stB00Opk (dhPk dhsAOpk) dhsB1Opk).2
def cB'Opk : RecvChain := { cBOpk with chainKey := (kdfCk cBOpk.chainKey).1, index := 1 }
def seedB0Opk : Bytes := (kdfCk cBOpk.chainKey).2
def stB1Opk : TRState :=
  { stB0'Opk with recv := [cB'Opk], spqr := recvSt (Spqr.spqrInit keysOpk.pqr spqrB2A) pqm0Opk }

theorem recv7Opk : Spqr.spqrRecv stB0'Opk.spqr pqm0Opk 1 =
    some (recvSt (Spqr.spqrInit keysOpk.pqr spqrB2A) pqm0Opk, key0Opk) :=
  spqrRecv_init_agree keysOpk.pqr coins0Opk pqm0Opk .b2a (bytesToLiteral_spqrSendMsg _ _)

def t7Opk : ExecTrace :=
  let tr1 := ((t6Opk.append (RndE 32)).append (NetE key0Opk)).append
    (EvP (.OPKUsed "bob" (dhPk opkB)))
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsAOpk) (dhPk dhsB1Opk)))).append
      (EvT (.HonestDH (stB0'Opk.sessionInfo "bob") dhsB1Opk 0))).append
      (EvC (.HandshakeSession (stB0'Opk.sessionInfo "bob") 45))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsAOpk) 0 m0Opk))).append
    (EvT (.MessageKey (stB0'Opk.sessionInfo "bob") .receiver seedB0Opk key0Opk 0 2 51))).append
    (StT "bob" stB1Opk)

/-- The 52-entry honest session trace with a one-time prekey. -/
abbrev wTrOpk : ExecTrace := t7Opk

theorem t7Opk_length : t7Opk.length = 52 := by
  dsimp only [t7Opk]; simp only [append_len, t6Opk_length]
theorem length_wTrOpk : wTrOpk.length = 52 := t7Opk_length

theorem seedB0Opk_eq : (kdfCk stA0Opk.cks).2 = seedB0Opk := by
  show (kdfCk (createChain keysOpk.rk (dhPk spkB) dhsAOpk).2).2 =
    (kdfCk (createChain keysOpk.rk (dhPk dhsAOpk) spkB).2).2
  rw [createChain_comm keysOpk.rk dhsAOpk spkB]

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
      have hmem : i ∈ evIdx tr p := mem_evIdx (eventLoggedAt_of_at? hat) hp
      rw [h] at hmem
      exact List.not_mem_nil hmem

theorem t7Opk_runs : Runs (Composed.bobStart "bob" "alice" khOpk 1 mhOpk 37 1) t6Opk 51 t7Opk := by
  obtain ⟨ha1, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_facts
  have h4o : t4 ≤ t4Opk := by
    dsimp only [t4Opk, genOneTimePrekeyTr]
    exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _
  have h56o : t5Opk ≤ t6Opk := encTr_le _ _ _ _ _
  have h4o_6o : t4Opk ≤ t6Opk := Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _) h56o
  have h4_6o : t4 ≤ t6Opk := Trace.le_trans _ _ _ h4o h4o_6o
  have hopk24 : t6Opk.at? 24 = some (StP "bob" { kind := .oneTimePrekey, sk := opkB }) := by
    refine at?_mono h4o_6o ?_; dsimp only [t4Opk, genOneTimePrekeyTr, opkB]; rw [t4_length]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hek : t6Opk.at? 29 = some (NetE oOpk.ek) := by
    refine at?_mono h56o ?_; dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))
  have hct : t6Opk.at? 30 = some (NetE oOpk.ct) := by
    refine at?_mono h56o ?_; dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))
  have hmsg : t6Opk.at? 41 = some (NetE (encMsg stA0Opk coins0Opk key0Opk m0Opk)) := by
    dsimp only [t6Opk, encTr]
    have hm : rnd t5Opk.length 32 = m0Opk := by rw [t5Opk_length]
    have hc : rnd (t5Opk.length + 1) 32 = coins0Opk := by rw [t5Opk_length]
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5Opk_length])
  have hpq : ((t6Opk.append (RndE 32)).append (NetE key0Opk)).at? 37 = some (NetE key0Opk) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [t6Opk, encTr]
    have hc : rnd (t5Opk.length + 1) 32 = coins0Opk := by rw [t5Opk_length]
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE key0Opk) (by simp only [append_len, t5Opk_length]))
  have hopkUnused :
      (!PQXDH.opkUsedB ((t6Opk.append (RndE 32)).append (NetE key0Opk)) "bob" (dhPk opkB)) =
      true := by
    unfold PQXDH.opkUsedB
    rw [someEventB_of_evIdx_nil]
    · rfl
    · rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
      dsimp only [t6Opk]; rw [evIdx_encTr]
      dsimp only [t5Opk, aliceTrOpk]
      rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
      dsimp only [t4Opk, genOneTimePrekeyTr]
      rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
        evIdx_append_ev, show _ = false from rfl, Bool.cond_false, evIdx_append_non _ _ _ rfl]
      exact evIdx_t4_false _ (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hset : setRecvChain stB0'Opk.recv cB'Opk = [cB'Opk] := by
    simp [setRecvChain, stB0'Opk, ratchetState, cB'Opk, cBOpk, stB00Opk, bobSt0, maxReceiverChains]
  have hrs :
      ratchetState
        (bobSt0 "alice" ikB spkB (dhPk ikA) keysOpk (encSig stA0Opk coins0Opk key0Opk m0Opk))
        (encSig stA0Opk coins0Opk key0Opk m0Opk).ratchetKey (rnd t6Opk.length 32) =
      (stB0'Opk, cBOpk) := by
    rw [t6Opk_length]; rfl
  exact runs_cast (Runs.bobStartOpk (kh := khOpk) (mh := mhOpk) (keys := keysOpk)
    (msg := encSig stA0Opk coins0Opk key0Opk m0Opk)
    (t := encMsg stA0Opk coins0Opk key0Opk m0Opk) (st' := stB0'Opk) (c := cBOpk) (c' := cB'Opk)
    (seed := seedB0Opk) (pq := key0Opk) (m := m0Opk)
    (at?_mono h4_6o hb9) (at?_mono h4_6o hs13) (at?_mono h4_6o hp19) rfl hopk24
    (at?_mono h4_6o ha1) hek hct (isCanonicalKey_dhPk _)
    (bobAgreement_honest_opk ikA (rnd t4Opk.length 32) ikB spkB pqskB opkB
      (rnd (t4Opk.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsAOpk) hrs rfl recv7Opk hpq
    (mac_ok seedB0Opk_eq rfl rfl) (dec_ok seedB0Opk_eq) hopkUnused (stOut := stB1Opk)
    (by rw [hset]; rfl))
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; simp only [append_len, t6Opk_length])
    (by rw [skipTr_zero _ _ _ _ _ _ rfl]; dsimp only [t7Opk]; simp only [append_len, t6Opk_length]; rfl)

private theorem t5Opk_le_wTrOpk : t5Opk ≤ wTrOpk := by
  have h67 : t6Opk ≤ wTrOpk := by
    dsimp only [wTrOpk, t7Opk]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le
        (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _) _
  exact Trace.le_trans _ _ _ (encTr_le _ _ _ _ _) h67

/-! ### Reachability and trace facts for `t4Opk .. t7Opk` (`wTrOpk`) -/

theorem t4Opk_reach : t4Opk.Reachable reachability :=
  reach_of_runs t4Opk_runs (genOneTimePrekey_reachable t4_reach)
theorem t5Opk_reach : t5Opk.Reachable reachability :=
  reach_of_runs t5Opk_runs (aliceStart_reachable t4Opk_reach)
theorem t6Opk_reach : t6Opk.Reachable reachability :=
  reach_of_runs t6Opk_runs (messageEncrypt_reachable t5Opk_reach
    (hcur := by
      dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
      exact isCurrentSnapshot_append_self _ _ _ (by simp only [append_len, t4Opk_length])))
theorem t7Opk_reach : t7Opk.Reachable reachability :=
  reach_of_runs t7Opk_runs (bobStart_reachable t6Opk_reach)
theorem wTrOpk_reach : wTrOpk.Reachable reachability := t7Opk_reach

abbrev t4Opk_reachable := t4Opk_reach
abbrev t5Opk_reachable := t5Opk_reach
abbrev t6Opk_reachable := t6Opk_reach
abbrev t7Opk_reachable := t7Opk_reach
abbrev wTrOpk_reachable := wTrOpk_reach

theorem t5Opk_aliceDone_at :
    t5Opk.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) 31 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
  exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))

theorem wTrOpk_aliceDone_at :
    wTrOpk.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) 31 := by
  have h := t5Opk_aliceDone_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono t5Opk_le_wTrOpk h

theorem wTrOpk_aliceDone :
    wTrOpk.EventLogged
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) := ⟨31, wTrOpk_aliceDone_at⟩

theorem t5Opk_handshakeSessionA_at :
    t5Opk.EventLoggedAt (ComposedEvent.HandshakeSession (stA0Opk.sessionInfo "alice") 31) 33 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [t5Opk, aliceTrOpk, aliceTrOpt, stA0Opk, dhsAOpk]
  have hd : rnd (t4Opk.length + 2) 32 = rnd 28 32 := by rw [t4Opk_length]
  have h5 : t4Opk.length + 5 = 31 := by rw [t4Opk_length]
  rw [hd, h5]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))

theorem wTrOpk_handshakeSessionA_at :
    wTrOpk.EventLoggedAt (ComposedEvent.HandshakeSession (stA0Opk.sessionInfo "alice") 31) 33 := by
  have h := t5Opk_handshakeSessionA_at
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h ⊢
  exact at?_mono t5Opk_le_wTrOpk h

theorem t5Opk_stA0Opk_at : t5Opk.at? 34 = some (StT "alice" stA0Opk) := by
  dsimp only [t5Opk, aliceTrOpk, aliceTrOpt, stA0Opk, dhsAOpk]
  have hd : rnd (t4Opk.length + 2) 32 = rnd 28 32 := by rw [t4Opk_length]
  rw [hd]
  exact at?_append_at _ _ (by simp only [append_len, t4Opk_length])
theorem wTrOpk_stA0Opk_at : wTrOpk.at? 34 = some (StT "alice" stA0Opk) :=
  at?_mono t5Opk_le_wTrOpk t5Opk_stA0Opk_at

theorem wTrOpk_opkUsed_at :
    wTrOpk.EventLoggedAt (PQXDHEvent.OPKUsed "bob" (dhPk opkB)) 44 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [wTrOpk, t7Opk]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t6Opk_length]))

theorem wTrOpk_bobDone_at :
    wTrOpk.EventLoggedAt
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) 45 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [wTrOpk, t7Opk]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t6Opk_length]))

theorem wTrOpk_bobDone :
    wTrOpk.EventLogged
      (PQXDHEvent.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB) (kemPk pqskB)
        (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk) := ⟨45, wTrOpk_bobDone_at⟩

theorem wTrOpk_handshakeSessionB_at :
    wTrOpk.EventLoggedAt (ComposedEvent.HandshakeSession (stB0'Opk.sessionInfo "bob") 45) 48 := by
  refine eventLoggedAt_of_at? ?_; dsimp only [wTrOpk, t7Opk]
  exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t6Opk_length]))

theorem wTrOpk_stB1Opk_at : wTrOpk.at? 51 = some (StT "bob" stB1Opk) := by
  dsimp only [wTrOpk, t7Opk]; exact at?_append_at _ _ (by simp only [append_len, t6Opk_length])

theorem noCompromise_opk_idx : evIdx wTrOpk isCompromise = [] := by
  dsimp only [wTrOpk, t7Opk]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl]
  dsimp only [t6Opk]; rw [evIdx_encTr]
  dsimp only [t5Opk, aliceTrOpk]
  rw [evIdx_aliceTrOpt_false _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ => rfl)]
  dsimp only [t4Opk, genOneTimePrekeyTr]
  rw [evIdx_append_non _ _ _ rfl, evIdx_append_non _ _ _ rfl,
    evIdx_append_ev, show isCompromise _ = false from rfl, Bool.cond_false,
    evIdx_append_non _ _ _ rfl]
  exact evIdx_t4_false isCompromise (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem wTrOpk_noCompromise : NoCompromise wTrOpk := noCompromise_of_evIdx noCompromise_opk_idx
theorem t5Opk_noCompromise : NoCompromise t5Opk :=
  noCompromise_of_evIdx (evIdx_eq_nil_of_le t5Opk_le_wTrOpk noCompromise_opk_idx)

theorem wTrOpk_honestRun : HonestRun true wTrOpk :=
  ⟨"alice", "bob", dhPk ikA, dhPk ikB, dhPk spkB, kemPk pqskB, some (dhPk opkB), oOpk.ek, oOpk.ct,
    keysOpk, by decide, rfl, wTrOpk_aliceDone, wTrOpk_bobDone⟩

end Symbolic.Proofs.Tests.Shared.Composed.HonestSession
