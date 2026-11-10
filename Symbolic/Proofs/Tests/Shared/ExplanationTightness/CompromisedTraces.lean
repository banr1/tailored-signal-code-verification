/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.LateAcceptTrace
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

namespace Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (advCoins advDhsA advForgedBobKeys advIkA
  advIkB advPlain advPqSk advSetup advSpkB advSpkSk ak_aliceAgreement_block_of_responderSecrets
  ak_chain_ck ak_chain_ck_comm ak_concat ak_dhPk ak_encMsg ak_lit ak_net ak_seed ak_spqrInit
  breakDHTr breakDHTr_reach compIkTr exposeCkr_reach exposeCks_reach exposeDhs_reach exposeRk_reach
  exposeSkipped_reach forgedBobStartTr forgedBundlePrefix forgedPreKeyPrefix forgedPreKeyStage2
  forgedSpqrKey forgedSpqrMsg invertDH_reach_sk invertTr isAnyTRExposure isBrokenDH isBrokenKEM
  isCompIK isCompOPK isCompPQ isCompSPK mem_trEvIdx not_loggedBefore_of_singleton not_tr_logged
  sendAttacker_reach stFakeMsg0 trEvIdx trIKA trIKA_knows_block trIKA_pre trIKB trIKB_knows_block
  trIKB_out trIKB_pre trIKB_reach)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (cA0 cB cB' cB'' coins0 coins1 coins2 dhsA
  dhsB1 evIdx ikA ikB isCompromise key0 key1 key2 keys1 kh1 m0 m1 m2 mem_evIdx not_logged o1 pqm1
  pqskB seedB0 seedB0_eq seedB1 seedB1_eq spkB stA0 stA1 stA2 stB0' stB00 stB1 stB2 stB3 t1 t10
  t10_length t10_reach t2 t3 t4 t4_length t5 t5_aliceDone_at t5_length t5_reach t5_stA0_at t6
  t6_length t6_reach t7 t7_length t7_reach t8 t8_length t9 t9_length)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_init_pos spqrRecv_init_zero
  spqrRecv_not_init)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.bobStart
  Runs.genPQPrekey Runs.genSignedPrekey Runs.messageDecrypt_noRatchet Runs.messageDecrypt_ratchet
  Runs.messageEncrypt Runs.registerIdentity StP StT aliceOut aliceOutOpt aliceSt aliceTr
  aliceTrOpt bobAgreement_honest bobOut bobOutOpt bobSt0 bobStart_reachable createChain_comm dec_ok
  dhPk_rnd_ne encMsg encSig encSt encTr exposeCkrTr exposeCksTr exposeDhsTr exposeRkTr
  exposeSkippedTr genPQPrekeyTr genSignedPrekeyTr mac_ok messageDecrypt_reachable
  messageEncrypt_reachable notInit_send parse_encMsg ratchetState reach_of_runs recvKey recvSt
  registerIdentityTr rnd skipTr)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (ExposedKey IsChainRoot TREntry
  at?_append_cases at?_append_of_lt chainKeyAt_add chainKeyAt_root_inj
  chainKeyAt_succ_eq_kdfCk_fst createChain_fst_inj createChain_snd_inj eventLogged_append_ev
  eventLogged_append_other exposedKey_append_expose isChainRoot_createChain_snd
  isChainRoot_pqxdhKdf_ck kdfCk_snd_inj not_chainKeyAt_eq_of_root not_exposedKey_of_trEvIdx
  pqxdhKdf_ck_ne_createChain_snd pqxdhKdf_rk_ne_createChain_fst proj_inj saltDepth
  saltDepth_chainKeyAt saltDepth_kdfCk_snd saltDepth_rnd)

namespace HandshakePreserves

open DY DY.Libsignal DY.Libsignal.PQXDH

open DY DY.DiffieHellman DY.PQKem DY.Libsignal.PQXDH

variable [DY.Libsignal.PQXDH.HasExecTrace]

private def Pres (Inv : ExecTrace → Prop) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val

def PresWith (Inv : ExecTrace → Prop) {α : Type} (Post : α → Prop)
    (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val ∧ ∀ a, (m.run tr).1 = some a → Post a

private theorem Pres.of_id {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : ∀ tr, (x.run tr).2.val = tr) : Pres Inv x := by
  intro tr h; rw [hx]; exact h

private theorem Pres.pure {Inv : ExecTrace → Prop} {α : Type} (a : α) :
    Pres Inv (Pure.pure a : Traceful α) :=
  Pres.of_id fun _ => by simp only [Traceful.run_pure]

private theorem Pres.failure {Inv : ExecTrace → Prop} {α : Type} :
    Pres Inv (failure : Traceful α) :=
  Pres.of_id fun _ => by simp only [Traceful.run_failure]

private theorem Pres.guardP {Inv : ExecTrace → Prop} (p : Prop) [Decidable p] :
    Pres Inv (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact Pres.pure _
  · exact Pres.failure

private theorem Pres.getEntry {Inv : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E]
    (h : Nat) : Pres Inv (DY.getEntry h : Traceful E) :=
  Pres.of_id fun _ => by simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]

private theorem Pres.genRand {Inv : ExecTrace → Prop}
    (hRnd : ∀ tr n, Inv tr → Inv (tr.append (Random.ExecEntryT.mk n))) (n : Nat) :
    Pres Inv (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact hRnd tr n h

private theorem Pres.bind {Inv : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Pres Inv x) (hf : ∀ a, Pres Inv (f a)) : Pres Inv (x >>= f) := by
  intro tr hInv; rw [Traceful.run_bind]; rcases h : x.run tr with ⟨o, trMid, _⟩
  have hMid : Inv trMid := by have := hx tr hInv; rw [h] at this; exact this
  cases o with
  | none => exact hMid
  | some a => exact hf a trMid hMid

private theorem PresWith.pure {Inv : ExecTrace → Prop} {α : Type} {P : α → Prop}
    (a : α) (ha : P a) : PresWith Inv P (Pure.pure a : Traceful α) :=
  fun _ hInv => by
    simp only [Traceful.run_pure]
    exact ⟨hInv, fun _ h => Option.some.inj h ▸ ha⟩

private theorem PresWith.bind_pres {Inv : ExecTrace → Prop} {α β : Type}
    {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : Pres Inv x) (hf : ∀ a, PresWith Inv Q (f a)) :
    PresWith Inv Q (x >>= f) := by
  intro tr hInv
  rw [Traceful.run_bind]
  have h1 := hx tr hInv
  rcases hrun : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [hrun] at h1; exact ⟨h1, fun _ h => nomatch h⟩
  · rw [hrun] at h1; exact hf a trMid h1

private theorem Pres.receiveMessage {Inv : ExecTrace → Prop} (h : Nat) :
    Pres Inv (Network.receiveMessage h) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Pres.bind (Pres.getEntry _) fun _ => Pres.pure _

private theorem Pres.getKey {Inv : ExecTrace → Prop} (p : Participant) (stateIdx : Nat)
    (kind : KeyKind) : Pres Inv (getKey p stateIdx kind) := by
  (unfold DY.Libsignal.PQXDH.getKey; simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1])
  refine Pres.bind (Pres.bind (Pres.bind (Pres.getEntry _) fun _ => Pres.pure _) fun _ =>
    Pres.bind (Pres.guardP _) fun _ => Pres.pure _) fun _ => ?_
  exact Pres.bind (Pres.guardP _) fun _ => Pres.pure _

private theorem Pres.lookupIdentity {Inv : ExecTrace → Prop} (p : Participant)
    (regIdx : Nat) : Pres Inv (lookupIdentity p regIdx) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Pres.bind (Pres.getEntry _) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev <;> try exact Pres.failure
  exact Pres.bind (Pres.guardP _) fun _ => Pres.pure _

theorem aliceHandshake_preserves (Inv : ExecTrace → Prop)
    (hRnd : ∀ tr n, Inv tr → Inv (tr.append (Random.ExecEntryT.mk n)))
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    PresWith Inv (fun o : AliceHandshakeOut => ∃ ikm, o.keys = pqxdhKdf ikm)
      (aliceHandshake a b idStateIdx regIdxB bh) := by
  unfold aliceHandshake
  refine PresWith.bind_pres (Pres.getKey _ _ _) fun _ => ?_
  refine PresWith.bind_pres (Pres.lookupIdentity _ _) fun ⟨ikB, vkB⟩ => ?_
  refine PresWith.bind_pres (Pres.receiveMessage _) fun _ => ?_
  refine PresWith.bind_pres (Pres.receiveMessage _) fun _ => ?_
  refine PresWith.bind_pres (Pres.receiveMessage _) fun _ => ?_
  refine PresWith.bind_pres (Pres.receiveMessage _) fun _ => ?_
  refine PresWith.bind_pres (Pres.guardP _) fun _ => ?_
  refine PresWith.bind_pres (Pres.guardP _) fun _ => ?_
  rcases bh.opk with _ | idx <;> dsimp only
  · refine PresWith.bind_pres (Pres.pure _) fun _ => ?_
    refine PresWith.bind_pres (Pres.genRand hRnd 32) fun _ => ?_
    refine PresWith.bind_pres (Pres.guardP _) fun _ => ?_
    refine PresWith.bind_pres (Pres.guardP _) fun _ => ?_
    refine PresWith.bind_pres (Pres.genRand hRnd 32) fun _ => ?_
    exact PresWith.pure _ ⟨_, rfl⟩
  · refine PresWith.bind_pres (Pres.receiveMessage _) fun _ => ?_
    refine PresWith.bind_pres (Pres.pure _) fun _ => ?_
    refine PresWith.bind_pres (Pres.genRand hRnd 32) fun _ => ?_
    refine PresWith.bind_pres (Pres.guardP _) fun _ => ?_
    refine PresWith.bind_pres (Pres.guardP _) fun _ => ?_
    refine PresWith.bind_pres (Pres.genRand hRnd 32) fun _ => ?_
    exact PresWith.pure _ ⟨_, rfl⟩

end HandshakePreserves

/-!
# Shared Witness Traces and Invariants for `Compromised` Tightness

Constructs concrete reachable witness traces for the `Compromised` explanation-tightness suite
(`trCK`, `trCKr`, `trMK`, `trRK`, `trHrcRk`, `trHrcCk`, `trIKA`, and `trBDH`), together with their
attacker-knowledge and event-inventory proofs. Also establishes reachable-trace invariants showing
that every `TREvent.HonestDH` secret is stored in some `TRState` snapshot and that DH ratchet
secrets cannot excuse a logged `MessageKey` seed in `FSQuery`.
-/

section

open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.PQKem DY.Literal DY.Concat DY.KdfExtract
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyComponent KeyDir
  kdfRk createChain kdfCk chainKeyAt DerivesMsgKey RootDescends DerivesChain
  hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 lit litByte zeroSalt
  trMsgKeys trHonestWireMsg computeMac messageVersion
  maxReceiverChains maxForwardJumps receiverKeyUsedB anyEventOnTrace
  x25519LowOrder findRecvChain setRecvChain recvChainFor consumeMessageKey
  TRState TREvent TRSignalMsg spqrA2B spqrB2A
  receiveSignalMsg ensureReceiverChain dhRatchetStep verifyMacAndDecrypt
  logSkippedKeys logMessageKeyAndStore traceLength guardTrace
  messageEncrypt messageEncryptAbort messageDecrypt messageDecryptSkipped
  exposeKey exposeSpqr exposeSkipped)
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles serializedIk AliceHandshakeOut BobHandshakeOut aliceAgreement bobAgreement
  pqxdhKdf pqxdhIkm pqxdhLabel agree AliceHandshakeWasCompromised BobHandshakeWasCompromised NoCompromise HandshakeKeysAt
  HandshakeWasCompromisedAt IsHandshakeBlock LoggedBefore SessionStateExposed)

/-! ## Shared Helpers and Computable Event Filters -/

/-- The attacker extracts the sender's DH ratchet public key `dhPk st.dhs` from any `encMsg` on
the network. -/
theorem knows_encMsg_ratchetKey {tr : ExecTrace} {st : TRState} {coins pq m : Bytes}
    {i : Nat} (h : tr.at? i = some (NetE (encMsg st coins pq m))) :
    (dhPk st.dhs).AttackerKnows tr := by
  have henc := ak_net h
  let keys := trMsgKeys pq (kdfCk st.cks).2
  let wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (SymEnc.symEnc keys.cipherKey keys.iv m) (Spqr.spqrSend st.spqr coins).2.2
  let mac := computeMac keys.macKey st.myIk st.peerIk wire
  change (Concat.concat wire mac).AttackerKnows tr at henc
  have hsp := Concat.attacker_knows_split (Concat.concat wire mac) wire.length tr henc
  rw [Concat.split_concat] at hsp
  exact (DY.TrWire.attacker_knows_trWireMsg_args _ _ _ _ _ _ _ tr hsp.1).1

theorem not_fsQuery_of_no_compromised {P : TestTracePredicates} {mk : Bytes}
    (hmk : P.MessageKey mk) (hknow : P.AttackerKnows mk)
    (hno : ∀ k, ¬ P.Compromised k) : ¬ FSQueryP P := by
  intro hfs
  rcases hfs mk hmk hknow with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> exact hno _ h

theorem fsQuery_mono_compromised {P₁ P₂ : TestTracePredicates}
    (hmk : ∀ k, P₂.MessageKey k → P₁.MessageKey k)
    (hknow : ∀ k, P₂.AttackerKnows k → P₁.AttackerKnows k)
    (hcomp : ∀ k, P₁.Compromised k → P₂.Compromised k)
    (hfs : FSQueryP P₁) : FSQueryP P₂ := by
  intro mk hm hk
  rcases hfs mk (hmk mk hm) (hknow mk hk) with hc | ⟨ck, hd, hc⟩ | ⟨rk, ck, hdc, hd, hc⟩
  · exact .inl (hcomp mk hc)
  · exact .inr (.inl ⟨ck, hd, hcomp ck hc⟩)
  · exact .inr (.inr ⟨rk, ck, hdc, hd, hcomp rk hc⟩)

theorem pcsQuery_mono_compromised {P₁ P₂ : TestTracePredicates}
    (hmk : ∀ k, P₂.MessageKey k → P₁.MessageKey k)
    (hknow : ∀ k, P₂.AttackerKnows k → P₁.AttackerKnows k)
    (hdh : ∀ k, P₂.HonestDH k → P₁.HonestDH k)
    (hcomp : ∀ k, P₁.Compromised k → P₂.Compromised k)
    (hpcs : PCSQueryP P₁) : PCSQueryP P₂ := by
  intro mk rk_prev ownSk peerSk hm hk hown hpeer hstep
  rcases hpcs mk rk_prev ownSk peerSk (hmk mk hm) (hknow mk hk) (hdh ownSk hown)
      (hdh peerSk hpeer) hstep with
    hc | ⟨ck, hd, hc⟩ | ⟨rk, ck, hr, hdc, hd, hc⟩ | ⟨⟨rk, hr, hc⟩, hsk⟩
  · exact .inl (hcomp mk hc)
  · exact .inr (.inl ⟨ck, hd, hcomp ck hc⟩)
  · exact .inr (.inr (.inl ⟨rk, ck, hr, hdc, hd, hcomp rk hc⟩))
  · refine .inr (.inr (.inr ⟨⟨rk, hr, hcomp rk hc⟩, ?_⟩))
    rcases hsk with h | h
    · exact .inl (hcomp ownSk h)
    · exact .inr (hcomp peerSk h)

/-! ### Private Trace, Snapshot, and Event-Index Combinators -/

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

private theorem eventLoggedAt_of_at? {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev : Ev} {i : Nat}
    (h : tr.at? i = some ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)) :
    tr.EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  exact h

private theorem someEventB_nil (p : PQXDHEvent → Bool) :
    (PQXDH.anyEventOnTrace PQXDH.PQXDHEvent) Trace.nil p = false := by
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [nil_len]
  rfl

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
    have hilt : i < tr.length := List.mem_range.mp hi
    rw [at?_append_of_lt tr x hilt]
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
    have hilt : i < tr.length := List.mem_range.mp hi
    rw [at?_append_of_lt tr (EvP ev) hilt]
    exact h i hi
  · rw [Trace.at?_append]
    exact hp

private theorem brokenDHB_breakDHTr (tr : ExecTrace) :
    PQXDH.brokenDHB (breakDHTr tr) = true := by
  unfold PQXDH.brokenDHB breakDHTr; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [append_len, List.range_succ, List.any_append, List.any_cons, Trace.at?_append]
  simp

private theorem t1_eq : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (by unfold PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2

private theorem t1_len_eq : t1.length = 5 := by
  rw [t1_eq]; simp only [registerIdentityTr, append_len, nil_len]

private theorem t2_eq : t2 = registerIdentityTr t1 "bob" := by
  refine (Runs.registerIdentity ?_).2
  unfold PQXDH.isRegisteredB
  rw [t1_eq]
  dsimp only [registerIdentityTr]
  rw [someEventB_append_non _ _ _ rfl
    (someEventB_append_non _ _ _ rfl
      (someEventB_append_non _ _ _ rfl
        (someEventB_append_false _ _ _ rfl
          (someEventB_append_non _ _ _ rfl (someEventB_nil _)))))]
  rfl

private theorem t2_len_eq : t2.length = 10 := by
  rw [t2_eq]; simp only [registerIdentityTr, append_len, t1_len_eq]

private theorem t1_le_t2 : t1 ≤ t2 := by
  rw [t2_eq]
  exact le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le t1 _) _) _) _) _

private theorem t2_bobId_at : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
  rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_len_eq]
  exact at?_append_at _ (StP "bob" { kind := .identity, sk := ikB })
    (by simp only [append_len, t1_len_eq])

private theorem t3_eq : t3 = genSignedPrekeyTr t2 "bob" ikB :=
  (Runs.genSignedPrekey t2_bobId_at).2

private theorem t3_len_eq : t3.length = 16 := by
  rw [t3_eq]; simp only [genSignedPrekeyTr, append_len, t2_len_eq]

private theorem t2_le_t3 : t2 ≤ t3 := by
  rw [t3_eq]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le t2 _) _) _) _) _) _

private theorem t3_bobId_at : t3.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) :=
  at?_mono t2_le_t3 t2_bobId_at

private theorem t4_eq : t4 = genPQPrekeyTr t3 "bob" ikB :=
  (Runs.genPQPrekey t3_bobId_at).2

private theorem t3_le_t4 : t3 ≤ t4 := by
  rw [t4_eq]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le t3 _) _) _) _) _) _

private theorem t1_le_t4 : t1 ≤ t4 :=
  Trace.le_trans _ _ _ t1_le_t2 (Trace.le_trans _ _ _ t2_le_t3 t3_le_t4)

private theorem t2_le_t4 : t2 ≤ t4 :=
  Trace.le_trans _ _ _ t2_le_t3 t3_le_t4

private theorem t4_aliceReg_at :
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (Signature.vk ikA) true)) := by
  refine at?_mono t1_le_t4 ?_
  rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
  exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    (at?_append_at _ (EvP (.IdentityRegistered "alice" (dhPk ikA) (Signature.vk ikA) true))
      (by simp only [append_len, nil_len]))

private theorem t4_ikA_at : t4.at? 2 = some (NetE (dhPk ikA)) := by
  refine at?_mono t1_le_t4 ?_
  rw [t1_eq]; dsimp only [registerIdentityTr]; rw [nil_len]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ (NetE (dhPk ikA)) (by simp only [append_len, nil_len]))

private theorem t4_ikB_at : t4.at? 7 = some (NetE (dhPk ikB)) := by
  refine at?_mono t2_le_t4 ?_
  rw [t2_eq]; dsimp only [registerIdentityTr]; rw [t1_len_eq]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ (NetE (dhPk ikB)) (by simp only [append_len, t1_len_eq]))

private theorem t4_bobId_at : t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) :=
  at?_mono t3_le_t4 t3_bobId_at

private theorem t4_bobSpk_at : t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) := by
  refine at?_mono t3_le_t4 ?_
  rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_len_eq]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ (StP "bob" { kind := .signedPrekey, sk := spkB })
      (by simp only [append_len, t2_len_eq]))

private theorem t4_spkB_at : t4.at? 14 = some (NetE (dhPk spkB)) := by
  refine at?_mono t3_le_t4 ?_
  rw [t3_eq]; dsimp only [genSignedPrekeyTr]; rw [t2_len_eq]
  exact at?_mono (Trace.append_le _ _)
    (at?_append_at _ (NetE (dhPk spkB)) (by simp only [append_len, t2_len_eq]))

private theorem t4_bobPq_at : t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) := by
  rw [t4_eq]; dsimp only [genPQPrekeyTr]; rw [t3_len_eq]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ (StP "bob" { kind := .pqPrekey, sk := pqskB })
      (by simp only [append_len, t3_len_eq]))

private theorem aliceTr_le (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes) :
    tr ≤ aliceTr tr a b ikA ikBPk spkPk pqPk := by
  dsimp only [aliceTr, aliceTrOpt]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le tr _) _) _) _) _) _) _) _) _

private theorem aliceTr_len (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes) :
    (aliceTr tr a b ikA ikBPk spkPk pqPk).length = tr.length + 9 := by
  simp only [aliceTr, aliceTrOpt, append_len]

private theorem aliceTr_ek_at (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes)
    {n3 : Nat} (h3 : tr.length + 3 = n3) :
    (aliceTr tr a b ikA ikBPk spkPk pqPk).at? n3 =
      some (NetE (aliceOut tr ikA ikBPk spkPk pqPk).ek) := by
  subst h3; dsimp only [aliceTr, aliceTrOpt]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (Trace.append_le _ _) _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len]))

private theorem aliceTr_ct_at (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes)
    {n4 : Nat} (h4 : tr.length + 4 = n4) :
    (aliceTr tr a b ikA ikBPk spkPk pqPk).at? n4 =
      some (NetE (aliceOut tr ikA ikBPk spkPk pqPk).ct) := by
  subst h4; dsimp only [aliceTr, aliceTrOpt]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len]))

private theorem aliceTr_done_at (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk : Bytes)
    {n5 : Nat} (h5 : tr.length + 5 = n5) :
    (aliceTr tr a b ikA ikBPk spkPk pqPk).at? n5 =
      some (EvP (.AliceDone a b (dhPk ikA) ikBPk spkPk pqPk none
        (aliceOut tr ikA ikBPk spkPk pqPk).ek (aliceOut tr ikA ikBPk spkPk pqPk).ct
        (aliceOut tr ikA ikBPk spkPk pqPk).keys)) := by
  subst h5; dsimp only [aliceTr, aliceTrOpt]
  exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
    (at?_append_at _ _ (by simp only [append_len]))

private theorem aliceTr_st_at (tr : ExecTrace) (a b : Participant) (ikA ikBPk spkPk pqPk dhs : Bytes)
    {n8 : Nat} (hdhs : rnd (tr.length + 2) 32 = dhs) (h8 : tr.length + 8 = n8) :
    (aliceTr tr a b ikA ikBPk spkPk pqPk).at? n8 =
      some (StT a (aliceSt b (aliceOut tr ikA ikBPk spkPk pqPk) dhs)) := by
  subst h8; subst hdhs; dsimp only [aliceTr, aliceTrOpt]
  exact at?_append_at _ _ (by simp only [append_len])

private theorem encTr_len (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : (encTr tr me stH st pq).length = tr.length + 7 := by
  simp only [encTr, append_len]

private theorem encTr_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTr tr me stH st pq := by
  dsimp only [encTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le tr _) _) _) _) _) _) _

private theorem encTr_pq_pre (tr : ExecTrace) (st : TRState) (pq : Bytes) {n2 : Nat}
    (hpq : (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1 = pq)
    (h2 : tr.length + 2 = n2) :
    (((tr.append (RndE 32)).append (RndE 32)).append
      (NetE (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1)).at? n2 =
      some (NetE pq) := by
  subst h2; rw [hpq]
  exact at?_append_at _ (NetE pq) (by simp only [append_len])

private theorem encTr_pq_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq pq0 : Bytes) {n2 : Nat}
    (hpq0 : (Spqr.spqrSend st.spqr (rnd (tr.length + 1) 32)).2.1 = pq0)
    (h2 : tr.length + 2 = n2) :
    (encTr tr me stH st pq).at? n2 = some (NetE pq0) := by
  dsimp only [encTr]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
    (Trace.append_le _ _) _) _) _) (encTr_pq_pre tr st pq0 hpq0 h2)

private theorem encTr_mk_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq mk : Bytes) {n4 : Nat}
    (hmk : (kdfCk st.cks).2 = mk) (h4 : tr.length + 4 = n4) :
    (encTr tr me stH st pq).at? n4 =
      some (EvT (.MessageKey (st.sessionInfo me) .sender mk pq st.ns st.rIdx stH)) := by
  subst h4; subst hmk
  dsimp only [encTr]
  exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
    (at?_append_at _ _ (by simp only [append_len]))

private theorem encTr_st_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st st' : TRState)
    (pq : Bytes) {n5 : Nat}
    (hst' : encSt st (rnd (tr.length + 1) 32) = st') (h5 : tr.length + 5 = n5) :
    (encTr tr me stH st pq).at? n5 = some (StT me st') := by
  subst h5; subst hst'
  dsimp only [encTr]
  exact at?_mono (Trace.append_le _ _)
    (at?_append_at _ _ (by simp only [append_len]))

private theorem encTr_msg_at (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (coins pq m : Bytes) {n6 : Nat}
    (hm : rnd tr.length 32 = m) (hc : rnd (tr.length + 1) 32 = coins)
    (h6 : tr.length + 6 = n6) :
    (encTr tr me stH st pq).at? n6 = some (NetE (encMsg st coins pq m)) := by
  subst h6; subst hm; subst hc
  dsimp only [encTr]
  exact at?_append_at _ _ (by simp only [append_len])

private theorem expose_le {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) : tr ≤ (tr.append e1).append e2 :=
  le_append_of_le (Trace.append_le tr e1) e2

private theorem expose_len {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) : ((tr.append e1).append e2).length = tr.length + 2 := by
  simp only [append_len]

private theorem expose_ev_at {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e1 : E1) (e2 : E2) {n0 : Nat} (h0 : tr.length = n0) :
    ((tr.append e1).append e2).at? n0 = some e1 := by
  subst h0
  exact at?_mono (Trace.append_le _ e2) (at?_append_at tr e1 rfl)

private theorem expose_net_at {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e1 : E1) (k : Bytes) {n1 : Nat} (h1 : tr.length + 1 = n1) :
    ((tr.append e1).append (NetE k)).at? n1 = some (NetE k) := by
  subst h1
  exact at?_append_at (tr.append e1) (NetE k) (by rw [append_len])

private theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]
  rw [hz]
  simp only [TripleRatchet.logSkippedKeys, Traceful.run_pure]

private theorem skipTr_one (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (h1 : n.toNat - c.index.toNat = 1) :
    skipTr tr s pk c src n =
      tr.append (EvT (.SkippedKeyStored s pk c.index (kdfCk c.chainKey).2 c.rIdx src)) := by
  dsimp only [skipTr]
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

private theorem isCanonicalKey_dhPk (sk : Bytes) :
    PQXDH.isCanonicalKey (dhPk sk) = true := by
  have hv : (dhPk sk).view? X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none X25519.Variant.SubF
      ({ sk := sk } : DiffieHellman.DhPk.SubF Bytes)
  have hl : PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk sk
  unfold PQXDH.isCanonicalKey
  rw [hv, hl]
  rfl

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
    · rw [at?_append_self_proj, hnone]

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

private theorem getEventAt_append_of_lt {Ev E : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] [ExecTraceTypes.Has E]
    (tr : ExecTrace) (x : E) {i : Nat} (hi : i < tr.length) :
    (tr.append x).getEventAt Ev i = tr.getEventAt Ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_of_lt tr x hi]

private theorem getEventAt_append_self_non {Ev E : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] [ExecTraceTypes.Has E]
    (tr : ExecTrace) (x : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT Ev)) = none) :
    (tr.append x).getEventAt Ev tr.length = none := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self_proj, hnone]

private theorem getEventAt_append_self_ev {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev)).getEventAt Ev tr.length = some ev := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Trace.at?_append]

private theorem evIdx_nil (p : PQXDHEvent → Bool) : evIdx Trace.nil p = [] := by
  unfold evIdx; rw [nil_len]; rfl

private theorem evIdx_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    evIdx (tr.append x) p = evIdx tr p := by
  unfold evIdx
  rw [append_len, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by rw [getEventAt_append_self_non tr x hnone]; simp),
    List.filter_nil, List.append_nil]
  apply List.filter_congr
  intro i hi
  rw [getEventAt_append_of_lt tr x (List.mem_range.mp hi)]

private theorem evIdx_append_ev (tr : ExecTrace) (ev : PQXDHEvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvP ev)) p = cond (p ev) (evIdx tr p ++ [tr.length]) (evIdx tr p) := by
  unfold evIdx
  rw [append_len, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by rw [getEventAt_append_self_ev]; dsimp only; rw [hp]; simp),
      List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      rw [getEventAt_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by rw [getEventAt_append_self_ev]; dsimp only; exact hp),
      List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      rw [getEventAt_append_of_lt tr (EvP ev) (List.mem_range.mp hi)])

private theorem evIdx_append_rnd (tr : ExecTrace) (n : Nat) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (RndE n)) p = evIdx tr p := evIdx_append_non tr _ p rfl
private theorem evIdx_append_net (tr : ExecTrace) (b : Bytes) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (NetE b)) p = evIdx tr p := evIdx_append_non tr _ p rfl
private theorem evIdx_append_stP (tr : ExecTrace) (u : Participant) (s : PQXDHState)
    (p : PQXDHEvent → Bool) :
    evIdx (tr.append (StP u s)) p = evIdx tr p := evIdx_append_non tr _ p rfl
private theorem evIdx_append_stT (tr : ExecTrace) (u : Participant) (s : TRState)
    (p : PQXDHEvent → Bool) :
    evIdx (tr.append (StT u s)) p = evIdx tr p := evIdx_append_non tr _ p rfl
private theorem evIdx_append_evT (tr : ExecTrace) (e : TREvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvT e)) p = evIdx tr p := evIdx_append_non tr _ p rfl
private theorem evIdx_append_evC (tr : ExecTrace) (e : ComposedEvent) (p : PQXDHEvent → Bool) :
    evIdx (tr.append (EvC e)) p = evIdx tr p := evIdx_append_non tr _ p rfl

private theorem evIdx_encTr (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) (p : PQXDHEvent → Bool) :
    evIdx (encTr tr me stH st pq) p = evIdx tr p := by
  simp only [encTr, evIdx_append_rnd, evIdx_append_net, evIdx_append_evT, evIdx_append_stT]

private theorem evIdx_t4_of_nonSetup {p : PQXDHEvent → Bool}
    (hReg : ∀ u ik vk b, p (.IdentityRegistered u ik vk b) = false)
    (hSpk : ∀ u pk, p (.SignedPrekeyPublished u pk) = false)
    (hPq : ∀ u pk, p (.PQPrekeyPublished u pk) = false) :
    evIdx t4 p = [] := by
  rw [t4_eq, t3_eq, t2_eq, t1_eq]
  simp only [genPQPrekeyTr, genSignedPrekeyTr, registerIdentityTr,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stP, evIdx_append_ev,
    hReg, hSpk, hPq, evIdx_nil]
  rfl

private theorem trEvIdx_nil (p : TREvent → Bool) : trEvIdx Trace.nil p = [] := by
  unfold trEvIdx; rw [nil_len]; rfl

private theorem trEvIdx_append_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : TREvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT TREvent)) = none) :
    trEvIdx (tr.append x) p = trEvIdx tr p := by
  unfold trEvIdx
  rw [append_len, List.range_succ, List.filter_append,
    List.filter_cons_of_neg (by rw [getEventAt_append_self_non tr x hnone]; simp),
    List.filter_nil, List.append_nil]
  apply List.filter_congr
  intro i hi
  rw [getEventAt_append_of_lt tr x (List.mem_range.mp hi)]

private theorem trEvIdx_append_evT (tr : ExecTrace) (ev : TREvent) (p : TREvent → Bool) :
    trEvIdx (tr.append (EvT ev)) p = cond (p ev) (trEvIdx tr p ++ [tr.length]) (trEvIdx tr p) := by
  unfold trEvIdx
  rw [append_len, List.range_succ, List.filter_append]
  cases hp : p ev
  · rw [List.filter_cons_of_neg (by rw [getEventAt_append_self_ev]; dsimp only; rw [hp]; simp),
      List.filter_nil, List.append_nil]
    exact List.filter_congr fun i hi => by
      rw [getEventAt_append_of_lt tr (EvT ev) (List.mem_range.mp hi)]
  · rw [List.filter_cons_of_pos (by rw [getEventAt_append_self_ev]; dsimp only; exact hp),
      List.filter_nil]
    exact congrArg (· ++ [tr.length]) (List.filter_congr fun i hi => by
      rw [getEventAt_append_of_lt tr (EvT ev) (List.mem_range.mp hi)])

private theorem trEvIdx_append_rnd (tr : ExecTrace) (n : Nat) (p : TREvent → Bool) :
    trEvIdx (tr.append (RndE n)) p = trEvIdx tr p := trEvIdx_append_non tr _ p rfl
private theorem trEvIdx_append_net (tr : ExecTrace) (b : Bytes) (p : TREvent → Bool) :
    trEvIdx (tr.append (NetE b)) p = trEvIdx tr p := trEvIdx_append_non tr _ p rfl
private theorem trEvIdx_append_stP (tr : ExecTrace) (u : Participant) (s : PQXDHState)
    (p : TREvent → Bool) :
    trEvIdx (tr.append (StP u s)) p = trEvIdx tr p := trEvIdx_append_non tr _ p rfl
private theorem trEvIdx_append_stT (tr : ExecTrace) (u : Participant) (s : TRState)
    (p : TREvent → Bool) :
    trEvIdx (tr.append (StT u s)) p = trEvIdx tr p := trEvIdx_append_non tr _ p rfl
private theorem trEvIdx_append_evP (tr : ExecTrace) (e : PQXDHEvent) (p : TREvent → Bool) :
    trEvIdx (tr.append (EvP e)) p = trEvIdx tr p := trEvIdx_append_non tr _ p rfl
private theorem trEvIdx_append_evC (tr : ExecTrace) (e : ComposedEvent) (p : TREvent → Bool) :
    trEvIdx (tr.append (EvC e)) p = trEvIdx tr p := trEvIdx_append_non tr _ p rfl

private theorem trEvIdx_encTr_false (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState)
    (pq : Bytes) {p : TREvent → Bool}
    (hSent : ∀ a b pk ns m, p (.Sent a b pk ns m) = false)
    (hSender : ∀ s seed pq' n r pa,
      p (.MessageKey s .sender seed pq' n r pa) = false) :
    trEvIdx (encTr tr me stH st pq) p = trEvIdx tr p := by
  simp only [encTr, trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_evT, trEvIdx_append_stT,
    hSent, hSender]
  rfl

private theorem trEvIdx_t4 (p : TREvent → Bool) : trEvIdx t4 p = [] := by
  rw [t4_eq, t3_eq, t2_eq, t1_eq]
  simp only [genPQPrekeyTr, genSignedPrekeyTr, registerIdentityTr,
    trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stP, trEvIdx_append_evP, trEvIdx_nil]

private theorem t4_le_t5 : t4 ≤ t5 := aliceTr_le _ _ _ _ _ _ _
private theorem t5_le_t6 : t5 ≤ t6 := encTr_le _ _ _ _ _
private theorem t6_le_t7 : t6 ≤ t7 := encTr_le _ _ _ _ _
private theorem t5_le_t7 : t5 ≤ t7 := Trace.le_trans _ _ _ t5_le_t6 t6_le_t7
private theorem t4_le_t7 : t4 ≤ t7 := Trace.le_trans _ _ _ t4_le_t5 t5_le_t7

private theorem t7_le_t8 : t7 ≤ t8 := by
  dsimp only [t8]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le t7 _) _) _) _) _) _) _) _) _

private theorem t8_le_t9 : t8 ≤ t9 := by
  dsimp only [t9]
  exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le t8 _) _) _) _

private theorem t9_le_t10 : t9 ≤ t10 := encTr_le _ _ _ _ _
private theorem t8_le_t10 : t8 ≤ t10 := Trace.le_trans _ _ _ t8_le_t9 t9_le_t10
private theorem t5_le_t10 : t5 ≤ t10 :=
  Trace.le_trans _ _ _ t5_le_t7 (Trace.le_trans _ _ _ t7_le_t8 t8_le_t10)

private theorem t5_cur_30 : TripleRatchet.isCurrentSnapshot t5 30 = true := by
  dsimp only [t5, aliceTr, aliceTrOpt]
  apply isCurrentSnapshot_append_self
  simp only [append_len, t4_length]

private theorem t6_stA1_at : t6.at? 36 = some (StT "alice" stA1) :=
  encTr_st_at t5 "alice" 30 stA0 stA1 key0 (by rw [t5_length]; rfl) (by rw [t5_length])

private theorem t6_cur_36 : TripleRatchet.isCurrentSnapshot t6 36 = true :=
  isCurrentSnapshot_encTr_self t5 "alice" 30 stA0 key0 (by rw [t5_length])

private theorem t6_mk0_at :
    t6.at? 35 = some (EvT (.MessageKey (stA0.sessionInfo "alice") .sender
      (kdfCk stA0.cks).2 key0 0 1 30)) :=
  encTr_mk_at t5 "alice" 30 stA0 key0 (kdfCk stA0.cks).2 rfl (by rw [t5_length])

private theorem t6_msg0_at : t6.at? 37 = some (NetE (encMsg stA0 coins0 key0 m0)) :=
  encTr_msg_at t5 "alice" 30 stA0 coins0 key0 m0
    (by rw [t5_length]) (by rw [t5_length]) (by rw [t5_length])

private theorem t7_pq1_at : t7.at? 40 = some (NetE key1) :=
  encTr_pq_at t6 "alice" 36 stA1 key1 key1 (by rw [t6_length]; rfl) (by rw [t6_length])

private theorem t7_msg1_at : t7.at? 44 = some (NetE (encMsg stA1 coins1 key1 m1)) :=
  encTr_msg_at t6 "alice" 36 stA1 coins1 key1 m1
    (by rw [t6_length]) (by rw [t6_length]) (by rw [t6_length])

private theorem t8_honestDH_49_at :
    t8.at? 49 = some (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0)) := by
  dsimp only [t8]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
    (Trace.append_le _ _) _) _) _)
    (at?_append_at _ _ (by simp only [append_len, t7_length]))

private theorem t10_mkB0_at :
    t10.at? 62 = some (EvT (.MessageKey (stB2.sessionInfo "bob") .sender
      (kdfCk stB2.cks).2 key2 0 2 57)) :=
  encTr_mk_at t9 "bob" 57 stB2 key2 (kdfCk stB2.cks).2 rfl (by rw [t9_length])

private theorem t10_msg2_at : t10.at? 64 = some (NetE (encMsg stB2 coins2 key2 m2)) :=
  encTr_msg_at t9 "bob" 57 stB2 coins2 key2 m2
    (by rw [t9_length]) (by rw [t9_length]) (by rw [t9_length])

private theorem trIKB_pre_len : trIKB_pre.length = 28 := by
  simp only [trIKB_pre, forgedBundlePrefix, compIkTr, advSetup, append_len, t4_length]

private theorem trIKB_len : trIKB.length = 37 := by
  simp only [trIKB, aliceTr_len, trIKB_pre_len]

private theorem t4_le_trIKB_pre : t4 ≤ trIKB_pre := by
  dsimp only [trIKB_pre, forgedBundlePrefix, compIkTr, advSetup]
  exact le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (expose_le t4 _ _) _) _) _) _

private theorem t4_le_trIKB : t4 ≤ trIKB :=
  Trace.le_trans _ _ _ t4_le_trIKB_pre (aliceTr_le _ _ _ _ _ _ _)

private theorem trIKB_st_at :
    trIKB.at? 36 = some (StT "alice" (aliceSt "bob" trIKB_out (rnd 30 32))) :=
  aliceTr_st_at trIKB_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    (rnd 30 32) (by rw [trIKB_pre_len]) (by rw [trIKB_pre_len])

private theorem trIKB_cur_36 : TripleRatchet.isCurrentSnapshot trIKB 36 = true := by
  dsimp only [trIKB, aliceTr, aliceTrOpt]
  apply isCurrentSnapshot_append_self
  simp only [append_len, trIKB_pre_len]

private theorem trIKB_ikB_sk_at : trIKB.at? 23 = some (NetE advIkB) := by
  refine at?_mono (aliceTr_le _ _ _ _ _ _ _) ?_
  dsimp only [trIKB_pre, forgedBundlePrefix]
  exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
    (expose_net_at t4 _ advIkB (by rw [t4_length]))

private theorem trIKB_ek_at : trIKB.at? 31 = some (NetE trIKB_out.ek) :=
  aliceTr_ek_at trIKB_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    (by rw [trIKB_pre_len])

private theorem trIKB_ct_at : trIKB.at? 32 = some (NetE trIKB_out.ct) :=
  aliceTr_ct_at trIKB_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    (by rw [trIKB_pre_len])

private theorem trIKB_done_at :
    trIKB.at? 33 =
      some (EvP (.AliceDone "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk)
        (kemPk advPqSk) none trIKB_out.ek trIKB_out.ct trIKB_out.keys)) :=
  aliceTr_done_at trIKB_pre "alice" "bob" advIkA (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
    (by rw [trIKB_pre_len])

def isNonCksExposure : TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKr .. | .ExposedMK .. => true
  | _ => false

def isNonCkrExposure : TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedMK .. => true
  | _ => false

def isNonMkExposure : TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr .. => true
  | _ => false

def isNonRkExposure : TREvent → Bool
  | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr .. | .ExposedMK .. => true
  | _ => false

def isAnyAliceDone : PQXDHEvent → Bool
  | .AliceDone .. => true
  | _ => false

def isAnyBobDone : PQXDHEvent → Bool
  | .BobDone .. => true
  | _ => false

def isAnyHonestDHEv : TREvent → Bool
  | .HonestDH .. => true
  | _ => false

/-! ## Witness Trace `trCK` -/

def trCK1 : ExecTrace := exposeCksTr t5 "alice" stA0
def pqCK0 : Bytes := (Spqr.spqrSend stA0.spqr (rnd 34 32)).2.1
def trCK : ExecTrace := encTr trCK1 "alice" 30 stA0 pqCK0
abbrev mkA0 : Bytes := (kdfCk stA0.cks).2

theorem trCK_reach : trCK.Reachable reachability := by
  have r1 : trCK1.Reachable reachability := exposeCks_reach (stH := 30) t5_reach t5_stA0_at
  have hcur : TripleRatchet.isCurrentSnapshot trCK1 30 = true :=
    isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t5_cur_30)
  have hlen1 : trCK1.length = 33 := by
    simp only [trCK1, exposeCksTr, expose_len, t5_length]
  exact reach_of_runs
    (Runs.messageEncrypt (tr := trCK1) (stH := 30) (pqH := 35) (st := stA0) (pq := pqCK0)
      (at?_mono (expose_le _ _ _) t5_stA0_at) (by decide)
      (encTr_pq_pre trCK1 stA0 pqCK0 (by rw [hlen1]; rfl) (by rw [hlen1])))
    (messageEncrypt_reachable r1 hcur)

theorem trCK_msgKey : (mkTestTracePredicates trCK).MessageKey mkA0 := by
  have hlen1 : trCK1.length = 33 := by
    simp only [trCK1, exposeCksTr, expose_len, t5_length]
  exact ⟨pqCK0, stA0.sessionInfo "alice", .sender, 0, 1, 30, 37,
    eventLoggedAt_of_at?
      (encTr_mk_at trCK1 "alice" 30 stA0 pqCK0 mkA0 rfl (by rw [hlen1]))⟩

theorem trCK_knows_mkA0 : mkA0.AttackerKnows trCK :=
  ak_seed (ak_net (i := 32)
    (at?_mono (encTr_le _ _ _ _ _) (expose_net_at t5 _ stA0.cks (by rw [t5_length]))))

theorem trCK_compromise_indices : evIdx trCK isCompromise = [] := by
  simp only [trCK, evIdx_encTr, trCK1, exposeCksTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompromise]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trCK_nonCks_indices : trEvIdx trCK isNonCksExposure = [] := by
  dsimp only [trCK]
  rw [trEvIdx_encTr_false _ _ _ _ _ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  simp only [trCK1, exposeCksTr, t5, aliceTr, aliceTrOpt,
    trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
    trEvIdx_append_evC, trEvIdx_append_evT, isNonCksExposure, trEvIdx_t4]
  rfl

/-! ## Forged Message on Alice's Initial Receiving Chain -/

/-- Fake state used by the attacker to format a counter-0 message on `dhPk spkSk` under chain key
`ck` with SPQR salt `Spqr.zeroKey`. -/
def stFakeCk (ikBPk ikAPk spkSk ck : Bytes) : TRState :=
  { peer := "alice", myIk := serializedIk ikBPk, peerIk := serializedIk ikAPk,
    rk := advPlain, dhs := spkSk, cks := ck, ns := 0, pn := 0,
    sid := advPlain, initiator := false, rIdx := 1, recv := [],
    spqr := Spqr.spqrInit advPlain spqrB2A }

def msgFakeCk (ikBPk ikAPk spkSk ck : Bytes) : Bytes :=
  encMsg (stFakeCk ikBPk ikAPk spkSk ck) advCoins Spqr.zeroKey advPlain

theorem msgFakeCk_knows {tr : ExecTrace} {ikBPk ikAPk spkSk ck : Bytes}
    (hck : ck.AttackerKnows tr) (hspk : (dhPk spkSk).AttackerKnows tr)
    (hikB : ikBPk.AttackerKnows tr) (hikA : ikAPk.AttackerKnows tr) :
    (msgFakeCk ikBPk ikAPk spkSk ck).AttackerKnows tr :=
  ak_encMsg hck hspk (ak_spqrInit (ak_lit _) (ak_lit _))
    (ak_concat (ak_lit _) hikB) (ak_concat (ak_lit _) hikA)
    (ak_lit _) (ak_lit _) (ak_lit _)

/-- Trace after the attacker sends `msgFakeCk` and Alice decrypts it (without ratcheting) on her
initial state `aliceSt "bob" o dhs` at `stH`. -/
def recvInitialCkTr (tr : ExecTrace) (o : AliceHandshakeOut) (dhs : Bytes) (stH : Nat)
    (spkSk : Bytes) : ExecTrace :=
  let st := aliceSt "bob" o dhs
  let msg := msgFakeCk o.ikB o.ikA spkSk o.keys.ck
  let sig := encSig (stFakeCk o.ikB o.ikA spkSk o.keys.ck) advCoins Spqr.zeroKey advPlain
  let c : RecvChain := { ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }
  let c' : RecvChain := { c with chainKey := (kdfCk o.keys.ck).1, index := 1 }
  let seed := (kdfCk o.keys.ck).2
  let spqr' := recvSt (Spqr.spqrInit o.keys.pqr spqrA2B) sig.pqRatchet
  let stOut : TRState := { st with recv := [c'], spqr := spqr' }
  let tr0 := (tr.append (NetE msg)).append (NetE Spqr.zeroKey)
  ((tr0.append (EvT (.Received "alice" "bob" (dhPk spkSk) 0 advPlain))).append
    (EvT (.MessageKey (st.sessionInfo "alice") .receiver seed Spqr.zeroKey 0 1 stH))).append
    (StT "alice" stOut)

private theorem recvInitialCkTr_le (tr : ExecTrace) (o : AliceHandshakeOut) (dhs : Bytes)
    (stH : Nat) (spkSk : Bytes) : tr ≤ recvInitialCkTr tr o dhs stH spkSk := by
  dsimp only [recvInitialCkTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le tr _) _) _) _) _

private theorem recvInitialCkTr_mk_at (tr : ExecTrace) (o : AliceHandshakeOut) (dhs : Bytes)
    (stH : Nat) (spkSk : Bytes) {n3 : Nat}
    (h3 : tr.length + 3 = n3) :
    (recvInitialCkTr tr o dhs stH spkSk).at? n3 =
      some (EvT (.MessageKey ((aliceSt "bob" o dhs).sessionInfo "alice") .receiver
        (kdfCk o.keys.ck).2 Spqr.zeroKey 0 1 stH)) := by
  subst h3
  dsimp only [recvInitialCkTr]
  exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len]))

theorem Runs.recvInitialCk {tr : ExecTrace} {o : AliceHandshakeOut} {dhs : Bytes} {stH : Nat}
    {spkSk : Bytes}
    (hst : (tr.append (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck))).at? stH =
      some (StT "alice" (aliceSt "bob" o dhs)))
    (hspkEq : o.spk = dhPk spkSk)
    (hmsg : (tr.append (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck))).at? tr.length =
      some (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck)))
    (hpq : ((tr.append (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck))).append
      (NetE Spqr.zeroKey)).at? (tr.length + 1) = some (NetE Spqr.zeroKey)) :
    Runs (TripleRatchet.messageDecrypt "alice" stH tr.length (tr.length + 1) 0)
      (tr.append (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck)))
      (tr.length + 4)
      (recvInitialCkTr tr o dhs stH spkSk) := by
  let st := aliceSt "bob" o dhs
  let stF := stFakeCk o.ikB o.ikA spkSk o.keys.ck
  let sig := encSig stF advCoins Spqr.zeroKey advPlain
  let c : RecvChain := { ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }
  let c' : RecvChain := { c with chainKey := (kdfCk o.keys.ck).1, index := 1 }
  let spqr' := recvSt (Spqr.spqrInit o.keys.pqr spqrA2B) sig.pqRatchet
  let stOut : TRState := { st with recv := [c'], spqr := spqr' }
  have hfind : findRecvChain st.recv sig.ratchetKey = some c := by
    simp [findRecvChain, st, aliceSt, sig, encSig, stF, stFakeCk, c, hspkEq]
  have hset : setRecvChain st.recv c' = [c'] := by
    simp [setRecvChain, st, aliceSt, c', c]
  have hrecv : Spqr.spqrRecv st.spqr sig.pqRatchet 0 = some (spqr', Spqr.zeroKey) :=
    spqrRecv_init_zero o.keys.pqr sig.pqRatchet .a2b
      (bytesToLiteral_spqrSendMsg stF.spqr advCoins)
  have hrun := Runs.messageDecrypt_noRatchet (st := st) (msg := sig)
    (t := msgFakeCk o.ikB o.ikA spkSk o.keys.ck) (c := c) (c' := c')
    (pq := Spqr.zeroKey) (seed := (kdfCk o.keys.ck).2) (m := advPlain)
    hst hmsg (parse_encMsg _ _ _ _) rfl hfind rfl hrecv hpq
    (mac_ok rfl rfl rfl) (dec_ok rfl) (stOut := stOut) (by rw [hset])
  dsimp only at hrun
  rw [skipTr_zero _ _ _ _ _ _ rfl] at hrun
  have hret :
      ((tr.append (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck))).append
        (NetE Spqr.zeroKey)).length + 2 = tr.length + 4 := by
    simp only [append_len]
  exact (congrArg
    (fun n => Runs (TripleRatchet.messageDecrypt "alice" stH tr.length (tr.length + 1) 0)
      (tr.append (NetE (msgFakeCk o.ikB o.ikA spkSk o.keys.ck))) n
      (recvInitialCkTr tr o dhs stH spkSk))
    hret).mp hrun

/-! ### Witness Trace `trCKr` -/

def trCKr0 : ExecTrace := exposeCkrTr t5 "alice" stA0 cA0
def trCKr : ExecTrace := recvInitialCkTr trCKr0 o1 dhsA 30 spkB
abbrev mkCKr : Bytes := (kdfCk keys1.ck).2

theorem trCKr_reach : trCKr.Reachable reachability := by
  have r0 : trCKr0.Reachable reachability :=
    exposeCkr_reach (stH := 30) (pk := dhPk spkB) t5_reach t5_stA0_at
      (by simp [findRecvChain, stA0, aliceSt, o1, cA0]; rfl)
  have hle0 : t4 ≤ trCKr0 := Trace.le_trans _ _ _ t4_le_t5 (expose_le _ _ _)
  have r1 : (trCKr0.append (NetE (msgFakeCk o1.ikB o1.ikA spkB keys1.ck))).Reachable reachability :=
    sendAttacker_reach r0
      (msgFakeCk_knows (ak_net (i := 32) (expose_net_at t5 _ keys1.ck (by rw [t5_length])))
        (ak_net (i := 14) (at?_mono hle0 t4_spkB_at))
        (ak_net (i := 7) (at?_mono hle0 t4_ikB_at))
        (ak_net (i := 2) (at?_mono hle0 t4_ikA_at)))
  have hcur :
      TripleRatchet.isCurrentSnapshot
        (trCKr0.append (NetE (msgFakeCk o1.ikB o1.ikA spkB keys1.ck))) 30 = true :=
    isCurrentSnapshot_append_non_st _ rfl
      (isCurrentSnapshot_append_non_st _ rfl (isCurrentSnapshot_append_non_st _ rfl t5_cur_30))
  exact reach_of_runs
    (Runs.recvInitialCk
      (at?_mono (le_append_of_le (expose_le _ _ _) _) t5_stA0_at)
      rfl
      (at?_append_at trCKr0 _ rfl)
      (at?_append_at (trCKr0.append _) _ (by rw [append_len])))
    (messageDecrypt_reachable r1 hcur)

theorem trCKr_msgKey : (mkTestTracePredicates trCKr).MessageKey mkCKr := by
  have hlen0 : trCKr0.length = 33 := by
    simp only [trCKr0, exposeCkrTr, expose_len, t5_length]
  exact ⟨Spqr.zeroKey, stA0.sessionInfo "alice", .receiver, 0, 1, 30, 36,
    eventLoggedAt_of_at?
      (recvInitialCkTr_mk_at trCKr0 o1 dhsA 30 spkB (by rw [hlen0]))⟩

theorem trCKr_knows_mkCKr : mkCKr.AttackerKnows trCKr :=
  ak_seed (ak_net (i := 32)
    (at?_mono (recvInitialCkTr_le _ _ _ _ _) (expose_net_at t5 _ keys1.ck (by rw [t5_length]))))

theorem trCKr_compromise_indices : evIdx trCKr isCompromise = [] := by
  simp only [trCKr, recvInitialCkTr, trCKr0, exposeCkrTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompromise]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trCKr_nonCkr_indices : trEvIdx trCKr isNonCkrExposure = [] := by
  simp only [trCKr, recvInitialCkTr, trCKr0, exposeCkrTr, t5, aliceTr, aliceTrOpt,
    trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
    trEvIdx_append_evC, trEvIdx_append_evT, isNonCkrExposure, trEvIdx_t4]
  rfl

/-! ## Witness Trace `trMK` -/

def mhMK : PreKeyMsgHandles := { ek := 25, ct := 26, msg := 44 }
def stB00_mk : TRState := bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA1 coins1 key1 m1)
def stB0'_mk : TRState := (ratchetState stB00_mk (dhPk dhsA) dhsB1).1
def cB_mk : RecvChain := (ratchetState stB00_mk (dhPk dhsA) dhsB1).2
def cB'_mk : RecvChain :=
  { cB_mk with chainKey := (kdfCk (chainKeyAt cB_mk.chainKey 1)).1, index := 2 }
def keyB_mk : Bytes := Spqr.spqrChainKey keys1.pqr spqrA2B (Spqr.encodeSpqrIndexTerm 2)
def stB1_mk : TRState :=
  { stB0'_mk with recv := [cB'_mk], spqr := recvSt (Spqr.spqrInit keys1.pqr spqrB2A) pqm1 }

theorem recv_tMK8 : Spqr.spqrRecv stB0'_mk.spqr pqm1 2 =
    some (recvSt (Spqr.spqrInit keys1.pqr spqrB2A) pqm1, keyB_mk) :=
  spqrRecv_init_pos keys1.pqr pqm1 .b2a 2 (by decide) (bytesToLiteral_spqrSendMsg stA1.spqr coins1)

def tMK8 : ExecTrace :=
  let tr1 := (t7.append (RndE 32)).append (NetE keyB_mk)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
      (EvT (.HonestDH (stB0'_mk.sessionInfo "bob") dhsB1 0))).append
      (EvC (.HandshakeSession (stB0'_mk.sessionInfo "bob") 47))
  let trS := skipTr tr5 (stB0'_mk.sessionInfo "bob") (dhPk dhsA) cB_mk 54 1
  ((trS.append (EvT (.Received "bob" "alice" (dhPk dhsA) 1 m1))).append
    (EvT (.MessageKey (stB0'_mk.sessionInfo "bob") .receiver seedB1 key1 1 2 54))).append
    (StT "bob" stB1_mk)

theorem tMK8_runs : Runs (Composed.bobStart "bob" "alice" kh1 1 mhMK 40 2) t7 54 tMK8 := by
  have hset : setRecvChain stB0'_mk.recv cB'_mk = [cB'_mk] := by
    simp [setRecvChain, stB0'_mk, ratchetState, cB'_mk, cB_mk, stB00_mk, bobSt0, maxReceiverChains]
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA1 coins1 key1 m1))
      (encSig stA1 coins1 key1 m1).ratchetKey (rnd t7.length 32) = (stB0'_mk, cB_mk) := by
    rw [t7_length]; rfl
  have hek : t7.at? 25 = some (NetE o1.ek) :=
    at?_mono t5_le_t7
      (aliceTr_ek_at t4 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (by rw [t4_length]))
  have hct : t7.at? 26 = some (NetE o1.ct) :=
    at?_mono t5_le_t7
      (aliceTr_ct_at t4 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (by rw [t4_length]))
  have hrun := Runs.bobStart (kh := kh1) (mh := mhMK) (keys := keys1)
    (msg := encSig stA1 coins1 key1 m1)
    (t := encMsg stA1 coins1 key1 m1) (st' := stB0'_mk) (c := cB_mk) (c' := cB'_mk)
    (seed := seedB1) (pq := key1) (m := m1)
    (at?_mono t4_le_t7 t4_bobId_at)
    (at?_mono t4_le_t7 t4_bobSpk_at)
    (at?_mono t4_le_t7 t4_bobPq_at)
    rfl
    (at?_mono t4_le_t7 t4_aliceReg_at)
    hek hct (isCanonicalKey_dhPk (rnd t4.length 32))
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    t7_msg1_at (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsA) hrs rfl recv_tMK8
    (at?_mono (le_append_of_le (Trace.append_le _ _) _) t7_pq1_at)
    (mac_ok seedB1_eq rfl rfl)
    (dec_ok seedB1_eq) (stOut := stB1_mk) (by rw [hset]; rfl)
  dsimp only at hrun
  have htr1 : ((t7.append (RndE 32)).append (NetE keyB_mk)).length = 47 := by
    simp only [append_len, t7_length]
  have hchild :
      ((((((t7.append (RndE 32)).append (NetE keyB_mk)).append
        (EvP (.BobDone "bob" "alice" (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ikB
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ikA
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).spk
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).pqpk
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).opk
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ek
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ct
          (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).keys))).append
        (EvT (.DHRatchet "bob" stB0'_mk.peer (encSig stA1 coins1 key1 m1).ratchetKey
          (dhPk stB0'_mk.dhs)))).append
        (EvT (.HonestDH (stB0'_mk.sessionInfo "bob") stB0'_mk.dhs (stB0'_mk.rIdx - 2)))).append
        (EvC (.HandshakeSession (stB0'_mk.sessionInfo "bob") 47))).length +
        ((encSig stA1 coins1 key1 m1).counter.toNat - cB_mk.index.toNat) + 2 = 54 := by
    simp only [append_len, t7_length]; rfl
  rw [htr1] at hrun
  rw [hchild] at hrun
  have htrS :
      (skipTr
        ((((((t7.append (RndE 32)).append (NetE keyB_mk)).append
          (EvP (.BobDone "bob" "alice" (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ikB
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ikA
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).spk
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).pqpk
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).opk
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ek
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).ct
            (bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1).keys))).append
          (EvT (.DHRatchet "bob" stB0'_mk.peer (encSig stA1 coins1 key1 m1).ratchetKey
            (dhPk stB0'_mk.dhs)))).append
          (EvT (.HonestDH (stB0'_mk.sessionInfo "bob") stB0'_mk.dhs (stB0'_mk.rIdx - 2)))).append
          (EvC (.HandshakeSession (stB0'_mk.sessionInfo "bob") 47)))
        (stB0'_mk.sessionInfo "bob") (encSig stA1 coins1 key1 m1).ratchetKey cB_mk 54
        (encSig stA1 coins1 key1 m1).counter).length + 2 = 54 := by
    rw [skipTr_one _ _ _ _ _ _ rfl]
    simp only [append_len, t7_length]
  rw [htrS] at hrun
  exact hrun

def isReceiverMsgKeyZero : TREvent → Bool
  | .MessageKey _ .receiver _ _ n _ _ => n == 0
  | _ => false

theorem receiverKeyUsedB_false_of_no_messageKey {tr : ExecTrace} {s : SessionInfo}
    {seed : Bytes} {n : UInt32} {r : Nat}
    (hno : ∀ pq pIdx,
      ¬ tr.EventLogged (TREvent.MessageKey s .receiver seed pq n r pIdx)) :
    receiverKeyUsedB tr s seed n r = false := by
  unfold receiverKeyUsedB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
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
        exact hno pq' pa' ⟨i, eventLoggedAt_of_at? hi⟩
      | sender => simp
    | _ => simp

def trMK : ExecTrace := exposeSkippedTr tMK8 (stB0'_mk.sessionInfo "bob") seedB0 0 2

private theorem tMK8_eq :
    tMK8 =
      ((((((((((t7.append (RndE 32)).append (NetE keyB_mk)).append
        (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
          (kemPk pqskB) none o1.ek o1.ct keys1))).append
        (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
        (EvT (.HonestDH (stB0'_mk.sessionInfo "bob") dhsB1 0))).append
        (EvC (.HandshakeSession (stB0'_mk.sessionInfo "bob") 47))).append
        (EvT (.SkippedKeyStored (stB0'_mk.sessionInfo "bob") (dhPk dhsA) 0 seedB0 2 54))).append
        (EvT (.Received "bob" "alice" (dhPk dhsA) 1 m1))).append
        (EvT (.MessageKey (stB0'_mk.sessionInfo "bob") .receiver seedB1 key1 1 2 54))).append
        (StT "bob" stB1_mk)) := by
  dsimp only [tMK8]
  rw [skipTr_one _ _ _ _ _ _ rfl]
  rfl

private theorem tMK8_len : tMK8.length = 55 := by
  rw [tMK8_eq]; simp only [append_len, t7_length]

private theorem t6_le_tMK8 : t6 ≤ tMK8 := by
  rw [tMK8_eq]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le t6_le_t7 _) _) _) _) _) _) _) _) _) _

theorem trMK_reach : trMK.Reachable reachability := by
  have r8 : tMK8.Reachable reachability := reach_of_runs tMK8_runs (bobStart_reachable t7_reach)
  have hidx0 : trEvIdx tMK8 isReceiverMsgKeyZero = [] := by
    rw [tMK8_eq]
    simp only [trEvIdx_append_stT, trEvIdx_append_evT, trEvIdx_append_evC, trEvIdx_append_evP,
      trEvIdx_append_net, trEvIdx_append_rnd, isReceiverMsgKeyZero]
    have h10 : ((1 : UInt32) == 0) = false := by decide
    rw [h10]
    dsimp only [t7, t6]
    simp only [trEvIdx_encTr_false _ _ _ _ _ (p := isReceiverMsgKeyZero)
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl),
      t5, aliceTr, aliceTrOpt, trEvIdx_append_stT, trEvIdx_append_evC, trEvIdx_append_evT,
      trEvIdx_append_evP, trEvIdx_append_net, trEvIdx_append_rnd, isReceiverMsgKeyZero,
      trEvIdx_t4]
    rfl
  have hunused : (!receiverKeyUsedB tMK8 (stB0'_mk.sessionInfo "bob") seedB0 0 2) = true := by
    rw [receiverKeyUsedB_false_of_no_messageKey]
    · rfl
    · intro pq pIdx
      exact not_tr_logged hidx0 rfl
  have hsk51 :
      tMK8.at? 51 =
        some (EvT (.SkippedKeyStored (stB0'_mk.sessionInfo "bob") (dhPk dhsA) 0 seedB0 2 54)) := by
    rw [tMK8_eq]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t7_length]))
  exact exposeSkipped_reach (skH := 51) r8 hsk51 hunused

theorem trMK_msgKey : (mkTestTracePredicates trMK).MessageKey seedB0 := by
  rw [← seedB0_eq]
  exact ⟨key0, stA0.sessionInfo "alice", .sender, 0, 1, 30, 35,
    eventLoggedAt_of_at?
      (at?_mono (Trace.le_trans _ _ _ t6_le_tMK8 (expose_le _ _ _)) t6_mk0_at)⟩

theorem trMK_knows_seedB0 : seedB0.AttackerKnows trMK :=
  ak_net (i := 56) (expose_net_at tMK8 _ seedB0 (by rw [tMK8_len]))

theorem trMK_compromise_indices : evIdx trMK isCompromise = [] := by
  dsimp only [trMK, exposeSkippedTr]
  rw [evIdx_append_net, evIdx_append_evT, tMK8_eq]
  simp only [evIdx_append_stT, evIdx_append_evT, evIdx_append_evC, evIdx_append_ev,
    evIdx_append_net, evIdx_append_rnd, isCompromise,
    t7, t6, evIdx_encTr, t5, aliceTr, aliceTrOpt]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trMK_nonMk_indices : trEvIdx trMK isNonMkExposure = [] := by
  dsimp only [trMK, exposeSkippedTr]
  rw [trEvIdx_append_net, trEvIdx_append_evT, tMK8_eq]
  dsimp only [isNonMkExposure, t7, t6]
  simp only [trEvIdx_append_stT, trEvIdx_append_evT, trEvIdx_append_evC, trEvIdx_append_evP,
    trEvIdx_append_net, trEvIdx_append_rnd, isNonMkExposure,
    trEvIdx_encTr_false _ _ _ _ _ (p := isNonMkExposure)
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl),
    t5, aliceTr, aliceTrOpt, trEvIdx_t4]
  rfl

/-! ## Witness Trace `trRK` -/

def trRK1 : ExecTrace := exposeRkTr t10 "alice" stA0
def trRK : ExecTrace := exposeDhsTr trRK1 "alice" stA0
abbrev mkB0 : Bytes := (kdfCk stB2.cks).2

theorem trRK_reach : trRK.Reachable reachability := by
  have hs10 : t10.at? 30 = some (StT "alice" stA0) := at?_mono t5_le_t10 t5_stA0_at
  exact exposeDhs_reach (stH := 30)
    (exposeRk_reach (stH := 30) t10_reach hs10)
    (at?_mono (expose_le _ _ _) hs10)

theorem stB2_cks_eq : stB2.cks = (createChain stA0.rk (dhPk dhsA) dhsB1).2 := by
  show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2 =
    (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsA) dhsB1).2
  rw [createChain_comm keys1.rk dhsA spkB]

theorem trRK_msgKey : (mkTestTracePredicates trRK).MessageKey mkB0 :=
  ⟨key2, stB2.sessionInfo "bob", .sender, 0, 2, 57, 62,
    eventLoggedAt_of_at?
      (at?_mono (Trace.le_trans _ _ _ (expose_le _ _ _) (expose_le _ _ _)) t10_mkB0_at)⟩

theorem trRK_knows_mkB0 : mkB0.AttackerKnows trRK := by
  have hrk : stA0.rk.AttackerKnows trRK :=
    ak_net (i := 66) (at?_mono (expose_le _ _ _) (expose_net_at t10 _ stA0.rk (by rw [t10_length])))
  have hdhsA : dhsA.AttackerKnows trRK :=
    ak_net (i := 68)
      (expose_net_at trRK1 _ dhsA (by simp only [trRK1, exposeRkTr, expose_len, t10_length]))
  have hpkB : (dhPk dhsB1).AttackerKnows trRK :=
    knows_encMsg_ratchetKey (tr := trRK) (st := stB2) (coins := coins2) (pq := key2) (m := m2)
      (i := 64)
      (at?_mono (Trace.le_trans _ _ _ (expose_le _ _ _) (expose_le _ _ _)) t10_msg2_at)
  have hck : stB2.cks.AttackerKnows trRK := by
    rw [stB2_cks_eq]
    exact ak_chain_ck_comm hrk hpkB hdhsA
  exact ak_seed hck

theorem trRK_honestDH_dhsB1 : (mkTestTracePredicates trRK).HonestDH dhsB1 :=
  .inl ⟨stB0'.sessionInfo "bob", 0, 49,
    eventLoggedAt_of_at?
      (at?_mono
        (Trace.le_trans _ _ _ t8_le_t10 (Trace.le_trans _ _ _ (expose_le _ _ _) (expose_le _ _ _)))
        t8_honestDH_49_at)⟩

theorem trRK_honestDH_dhsA : (mkTestTracePredicates trRK).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30,
    at?_mono
      (Trace.le_trans _ _ _ t5_le_t10 (Trace.le_trans _ _ _ (expose_le _ _ _) (expose_le _ _ _)))
      t5_stA0_at,
    rfl⟩

theorem trRK_compromise_indices : evIdx trRK isCompromise = [] := by
  simp only [trRK, exposeDhsTr, trRK1, exposeRkTr, t10, evIdx_encTr, t9, t8, t7, t6,
    t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompromise]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem t10_trExposure_indices : trEvIdx t10 isAnyTRExposure = [] := by
  dsimp only [t10, t9, t8, t7, t6]
  simp only [trEvIdx_encTr_false _ _ _ _ _ (p := isAnyTRExposure)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl),
    t5, aliceTr, aliceTrOpt,
    trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
    trEvIdx_append_evC, trEvIdx_append_evT, isAnyTRExposure, trEvIdx_t4]
  rfl

theorem trRK_exposedKey {k : Bytes} (h : ExposedKey trRK k) : k = stA0.rk ∨ k = dhsA := by
  rcases exposedKey_append_expose h with h1 | rfl
  · rcases exposedKey_append_expose h1 with h0 | rfl
    · exact False.elim (not_exposedKey_of_trEvIdx t10_trExposure_indices h0)
    · exact .inl rfl
  · exact .inr rfl

/-! ## Witness Traces for `HandshakeRootCompromised` -/

theorem handshakeKeysAt_of_aliceSingleton {tr : ExecTrace} {idx : Nat}
    {a b : Participant} {ikA ikB spk pqpk ek ct : Bytes} {opk : Option Bytes}
    {keys0 : HandshakeKeys}
    (halice : evIdx tr isAnyAliceDone = [idx])
    (hbob : evIdx tr isAnyBobDone = [])
    (hat : tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys0) idx)
    {j : Nat} {keys : HandshakeKeys} (h : HandshakeKeysAt tr j keys) :
    j = idx ∧ keys = keys0 := by
  rcases h with ⟨a', b', ikA', ikB', spk', pqpk', opk', ⟨ek', ct', hj⟩ | ⟨ek', ct', hj⟩⟩
  · have hm := mem_evIdx hj (p := isAnyAliceDone) rfl
    rw [halice, List.mem_singleton] at hm
    subst hm
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj hat
    rw [hat] at hj
    cases hj
    exact ⟨rfl, rfl⟩
  · exact False.elim (not_logged hbob (e := .BobDone ..) rfl ⟨j, hj⟩)

/-! ### Witness Trace `trHrcRk` -/

abbrev dhsA_ikb : Bytes := rnd 30 32
def stA_ikb : TRState := aliceSt "bob" trIKB_out dhsA_ikb
def pqHrcRk : Bytes := (Spqr.spqrSend stA_ikb.spqr (rnd 38 32)).2.1
def trHrcRk : ExecTrace := encTr trIKB "alice" 36 stA_ikb pqHrcRk
abbrev mkHrcRk : Bytes := (kdfCk stA_ikb.cks).2

theorem trHrcRk_reach : trHrcRk.Reachable reachability :=
  reach_of_runs
    (Runs.messageEncrypt (tr := trIKB) (stH := 36) (pqH := 39) (st := stA_ikb) (pq := pqHrcRk)
      trIKB_st_at (by decide)
      (encTr_pq_pre trIKB stA_ikb pqHrcRk (by rw [trIKB_len]; rfl) (by rw [trIKB_len])))
    (messageEncrypt_reachable trIKB_reach trIKB_cur_36)

theorem trHrcRk_msgKey : (mkTestTracePredicates trHrcRk).MessageKey mkHrcRk :=
  ⟨pqHrcRk, stA_ikb.sessionInfo "alice", .sender, 0, 1, 36, 41,
    eventLoggedAt_of_at?
      (encTr_mk_at trIKB "alice" 36 stA_ikb pqHrcRk mkHrcRk rfl
        (by rw [trIKB_len]))⟩

theorem trHrcRk_knows_mkHrcRk : mkHrcRk.AttackerKnows trHrcRk := by
  have hle : trIKB ≤ trHrcRk := encTr_le _ _ _ _ _
  have ht4 : t4 ≤ trHrcRk := Trace.le_trans _ _ _ t4_le_trIKB hle
  have hrk : trIKB_out.keys.rk.AttackerKnows trHrcRk :=
    ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
      (ak_net (i := 2) (at?_mono ht4 t4_ikA_at))
      (ak_net (i := 31) (at?_mono hle trIKB_ek_at))
      (ak_net (i := 23) (at?_mono hle trIKB_ikB_sk_at))
      (ak_lit _) (ak_lit _) trivial
      (ak_net (i := 32) (at?_mono hle trIKB_ct_at)) (.inl rfl)
  have hpkA : (dhPk dhsA_ikb).AttackerKnows trHrcRk :=
    knows_encMsg_ratchetKey (tr := trHrcRk) (st := stA_ikb) (coins := rnd 38 32)
      (pq := pqHrcRk) (m := rnd 37 32) (i := 43)
      (encTr_msg_at trIKB "alice" 36 stA_ikb (rnd 38 32) pqHrcRk (rnd 37 32)
        (by rw [trIKB_len]) (by rw [trIKB_len]) (by rw [trIKB_len]))
  have hcks : stA_ikb.cks.AttackerKnows trHrcRk :=
    ak_chain_ck_comm hrk hpkA (ak_lit _)
  exact ak_seed hcks

theorem trHrcRk_trExposure_indices : trEvIdx trHrcRk isAnyTRExposure = [] := by
  dsimp only [trHrcRk]
  rw [trEvIdx_encTr_false _ _ _ _ _ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  simp only [trIKB, aliceTr, aliceTrOpt, trIKB_pre, forgedBundlePrefix, compIkTr, advSetup,
    trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
    trEvIdx_append_evC, trEvIdx_append_evT, isAnyTRExposure, trEvIdx_t4]
  rfl

theorem trHrcRk_brokenDH_indices : evIdx trHrcRk isBrokenDH = [] := by
  simp only [trHrcRk, evIdx_encTr, trIKB, aliceTr, aliceTrOpt, trIKB_pre, forgedBundlePrefix,
    compIkTr, advSetup, evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT,
    evIdx_append_evC, evIdx_append_ev, isBrokenDH]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trHrcRk_bobDone_indices : evIdx trHrcRk isAnyBobDone = [] := by
  simp only [trHrcRk, evIdx_encTr, trIKB, aliceTr, aliceTrOpt, trIKB_pre, forgedBundlePrefix,
    compIkTr, advSetup, evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT,
    evIdx_append_evC, evIdx_append_ev, isAnyBobDone]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trHrcRk_aliceDone_indices : evIdx trHrcRk isAnyAliceDone = [33] := by
  have ht4 : evIdx t4 isAnyAliceDone = [] :=
    evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  simp only [trHrcRk, evIdx_encTr, trIKB, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isAnyAliceDone, append_len, trIKB_pre_len]
  simp only [trIKB_pre, forgedBundlePrefix, compIkTr, advSetup,
    evIdx_append_net, evIdx_append_ev, isAnyAliceDone, ht4]
  rfl

theorem trHrcRk_aliceDone_at :
    trHrcRk.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
        none trIKB_out.ek trIKB_out.ct trIKB_out.keys) 33 :=
  eventLoggedAt_of_at? (at?_mono (encTr_le _ _ _ _ _) trIKB_done_at)

/-! ### Witness Trace `trHrcCk` -/

def trHrcCk : ExecTrace := recvInitialCkTr trIKB trIKB_out dhsA_ikb 36 advSpkSk
abbrev mkHrcCk : Bytes := (kdfCk trIKB_out.keys.ck).2

theorem trHrcCk_reach : trHrcCk.Reachable reachability := by
  have r1 : (trIKB.append (NetE (msgFakeCk trIKB_out.ikB trIKB_out.ikA advSpkSk
      trIKB_out.keys.ck))).Reachable reachability :=
    sendAttacker_reach trIKB_reach
      (msgFakeCk_knows (trIKB_knows_block (.inr (.inl rfl))) (ak_dhPk (ak_lit _))
        (ak_net (i := 7) (at?_mono t4_le_trIKB t4_ikB_at))
        (ak_net (i := 2) (at?_mono t4_le_trIKB t4_ikA_at)))
  exact reach_of_runs
    (Runs.recvInitialCk
      (at?_mono (Trace.append_le _ _) trIKB_st_at)
      rfl
      (at?_append_at trIKB _ rfl)
      (at?_append_at (trIKB.append _) _ (by rw [append_len])))
    (messageDecrypt_reachable r1 (isCurrentSnapshot_append_non_st _ rfl trIKB_cur_36))

theorem trHrcCk_msgKey : (mkTestTracePredicates trHrcCk).MessageKey mkHrcCk :=
  ⟨Spqr.zeroKey, stA_ikb.sessionInfo "alice", .receiver, 0, 1, 36, 40,
    eventLoggedAt_of_at?
      (recvInitialCkTr_mk_at trIKB trIKB_out dhsA_ikb 36 advSpkSk
        (by rw [trIKB_len]))⟩

theorem trHrcCk_knows_mkHrcCk : mkHrcCk.AttackerKnows trHrcCk := by
  have hle : trIKB ≤ trHrcCk := recvInitialCkTr_le _ _ _ _ _
  have ht4 : t4 ≤ trHrcCk := Trace.le_trans _ _ _ t4_le_trIKB hle
  have hck : trIKB_out.keys.ck.AttackerKnows trHrcCk :=
    ak_aliceAgreement_block_of_responderSecrets (opkSk := none)
      (ak_net (i := 2) (at?_mono ht4 t4_ikA_at))
      (ak_net (i := 31) (at?_mono hle trIKB_ek_at))
      (ak_net (i := 23) (at?_mono hle trIKB_ikB_sk_at))
      (ak_lit _) (ak_lit _) trivial
      (ak_net (i := 32) (at?_mono hle trIKB_ct_at)) (.inr (.inl rfl))
  exact ak_seed hck

theorem trHrcCk_trExposure_indices : trEvIdx trHrcCk isAnyTRExposure = [] := by
  dsimp only [trHrcCk, recvInitialCkTr]
  simp only [trIKB, aliceTr, aliceTrOpt, trIKB_pre, forgedBundlePrefix, compIkTr, advSetup,
    trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
    trEvIdx_append_evC, trEvIdx_append_evT, isAnyTRExposure, trEvIdx_t4]
  rfl

theorem trHrcCk_brokenDH_indices : evIdx trHrcCk isBrokenDH = [] := by
  dsimp only [trHrcCk, recvInitialCkTr]
  simp only [trIKB, aliceTr, aliceTrOpt, trIKB_pre, forgedBundlePrefix, compIkTr, advSetup,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isBrokenDH]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trHrcCk_bobDone_indices : evIdx trHrcCk isAnyBobDone = [] := by
  dsimp only [trHrcCk, recvInitialCkTr]
  simp only [trIKB, aliceTr, aliceTrOpt, trIKB_pre, forgedBundlePrefix, compIkTr, advSetup,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isAnyBobDone]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trHrcCk_aliceDone_indices : evIdx trHrcCk isAnyAliceDone = [33] := by
  have ht4 : evIdx t4 isAnyAliceDone = [] :=
    evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  dsimp only [trHrcCk, recvInitialCkTr]
  simp only [trIKB, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isAnyAliceDone, append_len, trIKB_pre_len]
  simp only [trIKB_pre, forgedBundlePrefix, compIkTr, advSetup,
    evIdx_append_net, evIdx_append_ev, isAnyAliceDone, ht4]
  rfl

theorem trHrcCk_aliceDone_at :
    trHrcCk.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk advIkA) (dhPk advIkB) (dhPk advSpkSk) (kemPk advPqSk)
        none trIKB_out.ek trIKB_out.ct trIKB_out.keys) 33 :=
  eventLoggedAt_of_at? (at?_mono (recvInitialCkTr_le _ _ _ _ _) trIKB_done_at)

/-! ### Helper Facts for `trIKA` -/

abbrev stB00_ika : TRState :=
  bobSt0 "alice" advIkB advSpkB (dhPk advIkA) advForgedBobKeys
    (encSig (stFakeMsg0 (dhPk advIkA) (dhPk advIkB) (dhPk advSpkB) advForgedBobKeys)
      advCoins (forgedSpqrKey advForgedBobKeys) advPlain)
abbrev stB0'_ika : TRState := (ratchetState stB00_ika (dhPk advDhsA) (rnd 27 32)).1
abbrev cB_ika : RecvChain := (ratchetState stB00_ika (dhPk advDhsA) (rnd 27 32)).2
abbrev mkIKA : Bytes := (kdfCk cB_ika.chainKey).2

private theorem trIKA_pre_len : trIKA_pre.length = 27 := by
  simp only [trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2, compIkTr, advSetup,
    append_len, t4_length]

private theorem t4_le_trIKA : t4 ≤ trIKA := by
  dsimp only [trIKA, forgedBobStartTr, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2,
    compIkTr, advSetup]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le
        (Trace.append_le t4 _) _) _) _) _) _) _) _) _) _) _) _) _) _

theorem trIKA_msgKey : (mkTestTracePredicates trIKA).MessageKey mkIKA := by
  refine ⟨forgedSpqrKey advForgedBobKeys, stB0'_ika.sessionInfo "bob", .receiver,
    0, 2, 35, 34, eventLoggedAt_of_at? ?_⟩
  dsimp only [trIKA, forgedBobStartTr]
  simp only [append_len, trIKA_pre_len]
  exact at?_mono (Trace.append_le _ _)
    (at?_append_at _ _ (by simp only [append_len, trIKA_pre_len]))

theorem trIKA_knows_mkIKA : mkIKA.AttackerKnows trIKA := by
  have hrk : advForgedBobKeys.rk.AttackerKnows trIKA := trIKA_knows_block (.inl rfl)
  have hck : cB_ika.chainKey.AttackerKnows trIKA :=
    ak_chain_ck_comm hrk (ak_net (i := 14) (at?_mono t4_le_trIKA t4_spkB_at)) (ak_lit _)
  exact ak_seed hck

theorem trIKA_brokenDH_indices : evIdx trIKA isBrokenDH = [] := by
  dsimp only [trIKA, forgedBobStartTr, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2,
    compIkTr, advSetup]
  simp only [evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT,
    evIdx_append_evC, evIdx_append_ev, isBrokenDH]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trIKA_aliceDone_indices : evIdx trIKA isAnyAliceDone = [] := by
  dsimp only [trIKA, forgedBobStartTr, trIKA_pre, forgedPreKeyPrefix, forgedPreKeyStage2,
    compIkTr, advSetup]
  simp only [evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT,
    evIdx_append_evC, evIdx_append_ev, isAnyAliceDone]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-! ## Witness Trace `trBDH` -/

def trBDH1 : ExecTrace := exposeRkTr t6 "alice" stA1
def trBDH2 : ExecTrace := trBDH1.append (NetE (dhPk dhsA))
def trBDH3 : ExecTrace := breakDHTr trBDH2
def trBDH4 : ExecTrace := invertTr trBDH3 dhsA

def stFakeBDH : TRState :=
  { peer := "alice", myIk := serializedIk (dhPk ikB), peerIk := serializedIk (dhPk ikA),
    rk := advPlain, dhs := dhsA,
    cks := (createChain stA0.rk (dhPk dhsA) dhsA).2,
    ns := 0, pn := 0, sid := advPlain, initiator := false, rIdx := 1, recv := [],
    spqr := Spqr.spqrInit advPlain spqrB2A }

def msgBDH : Bytes := encMsg stFakeBDH advCoins (dhPk ikA) advPlain
def sigBDH : TRSignalMsg := encSig stFakeBDH advCoins (dhPk ikA) advPlain
def trBDH5 : ExecTrace := trBDH4.append (NetE msgBDH)

abbrev dhsBDH : Bytes := rnd 44 32
def stBDH' : TRState := (ratchetState stA1 (dhPk dhsA) dhsBDH).1
def cBDH : RecvChain := (ratchetState stA1 (dhPk dhsA) dhsBDH).2
def cBDH' : RecvChain := { cBDH with chainKey := (kdfCk cBDH.chainKey).1, index := 1 }
def stBDH_out : TRState :=
  { stBDH' with recv := [cA0, cBDH'], spqr := recvSt stA1.spqr sigBDH.pqRatchet }
abbrev mkBDH : Bytes := (kdfCk cBDH.chainKey).2

theorem recvBDH : Spqr.spqrRecv stBDH'.spqr sigBDH.pqRatchet 1 =
    some (stBDH_out.spqr, recvKey stA1.spqr sigBDH.pqRatchet) :=
  spqrRecv_not_init _ _ _ (notInit_send stA0.spqr coins0)
    (bytesToLiteral_spqrSendMsg stFakeBDH.spqr advCoins)

def trBDH : ExecTrace :=
  let tr1 := (((trBDH5.append (RndE 32)).append
    (NetE (recvKey stA1.spqr sigBDH.pqRatchet))).append
    (EvT (.DHRatchet "alice" "bob" (dhPk dhsA) (dhPk dhsBDH)))).append
    (EvT (.HonestDH (stBDH'.sessionInfo "alice") dhsBDH 1))
  ((tr1.append (EvT (.Received "alice" "bob" (dhPk dhsA) 0 advPlain))).append
    (EvT (.MessageKey (stBDH'.sessionInfo "alice") .receiver mkBDH (dhPk ikA) 0 3 36))).append
    (StT "alice" stBDH_out)

private theorem trBDH1_len : trBDH1.length = 40 := by
  simp only [trBDH1, exposeRkTr, expose_len, t6_length]

private theorem trBDH4_len : trBDH4.length = 43 := by
  simp only [trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, append_len, trBDH1_len]

private theorem trBDH5_len : trBDH5.length = 44 := by
  simp only [trBDH5, append_len, trBDH4_len]

private theorem trBDH1_le_trBDH4 : trBDH1 ≤ trBDH4 :=
  le_append_of_le (le_append_of_le (Trace.append_le trBDH1 _) _) _

private theorem t6_le_trBDH4 : t6 ≤ trBDH4 :=
  Trace.le_trans _ _ _ (expose_le t6 _ _) trBDH1_le_trBDH4

private theorem t6_le_trBDH5 : t6 ≤ trBDH5 :=
  le_append_of_le t6_le_trBDH4 _

private theorem t4_le_trBDH4 : t4 ≤ trBDH4 :=
  Trace.le_trans _ _ _ t4_le_t5 (Trace.le_trans _ _ _ t5_le_t6 t6_le_trBDH4)

private theorem t4_le_trBDH5 : t4 ≤ trBDH5 :=
  le_append_of_le t4_le_trBDH4 _

private theorem trBDH5_le_trBDH : trBDH5 ≤ trBDH := by
  dsimp only [trBDH]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (Trace.append_le trBDH5 _) _) _) _) _) _) _

private theorem trBDH4_le_trBDH : trBDH4 ≤ trBDH :=
  Trace.le_trans _ _ _ (Trace.append_le trBDH4 _) trBDH5_le_trBDH

private theorem t6_le_trBDH : t6 ≤ trBDH :=
  Trace.le_trans _ _ _ t6_le_trBDH5 trBDH5_le_trBDH

private theorem trBDH1_rk_at : trBDH1.at? 39 = some (NetE stA0.rk) :=
  expose_net_at t6 _ stA1.rk (by rw [t6_length])

private theorem trBDH2_pk_at : trBDH2.at? 40 = some (NetE (dhPk dhsA)) :=
  at?_append_at trBDH1 (NetE (dhPk dhsA)) (by rw [trBDH1_len])

private theorem trBDH4_sk_at : trBDH4.at? 42 = some (NetE dhsA) :=
  at?_append_at trBDH3 (NetE dhsA)
    (by simp only [trBDH3, breakDHTr, trBDH2, append_len, trBDH1_len])

theorem trBDH_runs : Runs (TripleRatchet.messageDecrypt "alice" 36 43 2 1) trBDH5 50 trBDH := by
  have hne : dhPk spkB ≠ dhPk dhsA := dhPk_rnd_ne (by decide)
  have ho1 : o1.spk = dhPk spkB := rfl
  have hrs : ratchetState stA1 sigBDH.ratchetKey (rnd trBDH5.length 32) = (stBDH', cBDH) := by
    rw [trBDH5_len]; rfl
  have hset : setRecvChain stBDH'.recv cBDH' = [cA0, cBDH'] := by
    simp [setRecvChain, stBDH', ratchetState, cBDH', cBDH, stA1, encSt, stA0, aliceSt, cA0,
      ho1, hne, maxReceiverChains]
  have hfind : findRecvChain stA1.recv (dhPk dhsA) = none := by
    simp [findRecvChain, stA1, encSt, stA0, aliceSt, ho1, hne]
  have hrun := Runs.messageDecrypt_ratchet (st := stA1) (st' := stBDH') (c := cBDH) (c' := cBDH')
    (msg := sigBDH) (t := msgBDH) (pq := dhPk ikA) (seed := mkBDH) (m := advPlain)
    (at?_mono t6_le_trBDH5 t6_stA1_at)
    (at?_append_at trBDH4 (NetE msgBDH) (by rw [trBDH4_len]))
    (parse_encMsg _ _ _ _) rfl hfind (x25519LowOrder_dhPk dhsA) hrs rfl recvBDH
    (at?_mono (le_append_of_le (le_append_of_le t4_le_trBDH5 _) _) t4_ikA_at)
    (mac_ok rfl rfl rfl) (dec_ok rfl) (stOut := stBDH_out) (by rw [hset]; rfl)
  dsimp only at hrun
  rw [skipTr_zero _ _ _ _ _ _ rfl] at hrun
  have hlen :
      (((((trBDH5.append (RndE 32)).append
        (NetE (recvKey stA1.spqr sigBDH.pqRatchet))).append
        (EvT (.DHRatchet "alice" stBDH'.peer sigBDH.ratchetKey (dhPk stBDH'.dhs)))).append
        (EvT (.HonestDH (stBDH'.sessionInfo "alice") stBDH'.dhs (stBDH'.rIdx - 2))))).length + 2 =
        50 := by
    simp only [append_len, trBDH5_len]
  rw [hlen] at hrun
  exact hrun

theorem trBDH_reach : trBDH.Reachable reachability := by
  have r1 : trBDH1.Reachable reachability := exposeRk_reach (stH := 36) t6_reach t6_stA1_at
  have r2 : trBDH2.Reachable reachability :=
    sendAttacker_reach r1
      (knows_encMsg_ratchetKey (tr := trBDH1) (st := stA0) (coins := coins0) (pq := key0)
        (m := m0) (i := 37) (at?_mono (expose_le _ _ _) t6_msg0_at))
  have r3 : trBDH3.Reachable reachability := breakDHTr_reach r2
  have r4 : trBDH4.Reachable reachability :=
    invertDH_reach_sk (pkIdx := 40) r3 (brokenDHB_breakDHTr trBDH2)
      (at?_mono (Trace.append_le _ _) trBDH2_pk_at)
  have h40 : trBDH4.at? 40 = some (NetE (dhPk dhsA)) :=
    at?_mono (le_append_of_le (Trace.append_le _ _) _) trBDH2_pk_at
  have hcks : stFakeBDH.cks.AttackerKnows trBDH4 :=
    ak_chain_ck
      (ak_net (i := 39) (at?_mono trBDH1_le_trBDH4 trBDH1_rk_at))
      (ak_net (i := 40) h40)
      (ak_net (i := 42) trBDH4_sk_at)
  have r5 : trBDH5.Reachable reachability :=
    sendAttacker_reach r4
      (ak_encMsg hcks (ak_net (i := 40) h40) (ak_spqrInit (ak_lit _) (ak_lit _))
        (ak_concat (ak_lit _) (ak_net (i := 7) (at?_mono t4_le_trBDH4 t4_ikB_at)))
        (ak_concat (ak_lit _) (ak_net (i := 2) (at?_mono t4_le_trBDH4 t4_ikA_at)))
        (ak_lit _) (ak_net (i := 2) (at?_mono t4_le_trBDH4 t4_ikA_at)) (ak_lit _))
  have hcur : TripleRatchet.isCurrentSnapshot trBDH5 36 = true :=
    isCurrentSnapshot_append_non_st _ rfl
      (isCurrentSnapshot_append_non_st _ rfl
        (isCurrentSnapshot_append_non_st _ rfl
          (isCurrentSnapshot_append_non_st _ rfl
            (isCurrentSnapshot_append_non_st _ rfl
              (isCurrentSnapshot_append_non_st _ rfl t6_cur_36)))))
  exact reach_of_runs trBDH_runs (messageDecrypt_reachable r5 hcur)

theorem trBDH_msgKey : (mkTestTracePredicates trBDH).MessageKey mkBDH :=
  ⟨dhPk ikA, stBDH'.sessionInfo "alice", .receiver, 0, 3, 36, 49,
    eventLoggedAt_of_at?
      (by
        dsimp only [trBDH]
        exact at?_mono (Trace.append_le _ _)
          (at?_append_at _ _ (by simp only [append_len, trBDH5_len])))⟩

theorem trBDH_knows_mkBDH : mkBDH.AttackerKnows trBDH :=
  ak_seed (ak_chain_ck
    (ak_net (i := 39) (at?_mono (Trace.le_trans _ _ _ trBDH1_le_trBDH4 trBDH4_le_trBDH) trBDH1_rk_at))
    (ak_net (i := 40) (at?_mono (Trace.le_trans _ _ _ (le_append_of_le (Trace.append_le _ _) _) trBDH4_le_trBDH) trBDH2_pk_at))
    (ak_net (i := 42) (at?_mono trBDH4_le_trBDH trBDH4_sk_at)))

theorem trBDH_honestDH_dhsA : (mkTestTracePredicates trBDH).HonestDH dhsA :=
  .inr ⟨"alice", stA0, 30,
    at?_mono (Trace.le_trans _ _ _ t5_le_t6 t6_le_trBDH) t5_stA0_at, rfl⟩

theorem trBDH_aliceDone_indices : evIdx trBDH isAnyAliceDone = [27] := by
  have ht4 : evIdx t4 isAnyAliceDone = [] :=
    evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isAnyAliceDone, append_len, t4_length, ht4]
  rfl

theorem trBDH_bobDone_indices : evIdx trBDH isAnyBobDone = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isAnyBobDone]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trBDH_brokenDH_indices : evIdx trBDH isBrokenDH = [41] := by
  have ht4 : evIdx t4 isBrokenDH = [] :=
    evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr]
  simp only [evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT,
    evIdx_append_ev, isBrokenDH, trBDH2, append_len, trBDH1_len]
  simp only [trBDH1, exposeRkTr, t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isBrokenDH, ht4]
  rfl

theorem trBDH_compIK_indices : evIdx trBDH isCompIK = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompIK]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trBDH_compSPK_indices : evIdx trBDH isCompSPK = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompSPK]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trBDH_compPQ_indices : evIdx trBDH isCompPQ = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompPQ]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trBDH_compOPK_indices : evIdx trBDH isCompOPK = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isCompOPK]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trBDH_brokenKEM_indices : evIdx trBDH isBrokenKEM = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [t6, evIdx_encTr, t5, aliceTr, aliceTrOpt,
    evIdx_append_rnd, evIdx_append_net, evIdx_append_stT, evIdx_append_evT, evIdx_append_evC,
    evIdx_append_ev, isBrokenKEM]
  exact evIdx_t4_of_nonSetup (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem trBDH_aliceDone_at :
    trBDH.EventLoggedAt
      (PQXDHEvent.AliceDone "alice" "bob" (dhPk ikA) (dhPk ikB) (dhPk spkB) (kemPk pqskB) none
        o1.ek o1.ct keys1) 27 :=
  eventLoggedAt_of_at?
    (at?_mono (Trace.le_trans _ _ _ t5_le_t6 t6_le_trBDH)
      (aliceTr_done_at t4 "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB)
        (by rw [t4_length])))

theorem trBDH_not_handshakeExcusedAt {j : Nat} : ¬ HandshakeWasCompromisedAt trBDH j := by
  rintro (⟨a, b, ikA', ikB', spk', pqpk', opk', ek', ct', keys', hj, hexc⟩ |
      ⟨b, a, ikB', ikA', spk', pqpk', opk', ek', ct', keys', hj, _⟩)
  · have hjeq : j = 27 ∧ keys' = keys1 :=
      handshakeKeysAt_of_aliceSingleton trBDH_aliceDone_indices trBDH_bobDone_indices
        trBDH_aliceDone_at ⟨a, b, ikA', ikB', spk', pqpk', opk', .inl ⟨ek', ct', hj⟩⟩
    rcases hjeq with ⟨rfl, _⟩
    rcases hexc with ⟨k, hk, _⟩ | ⟨k, hk, hlt | hpq | hkem⟩
    · exact not_logged trBDH_compIK_indices (e := PQXDHEvent.CompromisedIK b ikB') rfl ⟨k, hk⟩
    · exact not_loggedBefore_of_singleton trBDH_brokenDH_indices
        (e := PQXDHEvent.BrokenDH) rfl (by decide) ⟨k, hk, hlt⟩
    · exact not_logged trBDH_compPQ_indices (e := PQXDHEvent.CompromisedPQSPK b pqpk') rfl hpq
    · exact not_logged trBDH_brokenKEM_indices (e := PQXDHEvent.BrokenKEM) rfl hkem
  · exact not_logged trBDH_bobDone_indices (e := PQXDHEvent.BobDone ..) rfl ⟨j, hj⟩

theorem trBDH_nonRk_indices : trEvIdx trBDH isNonRkExposure = [] := by
  dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
    trEvIdx_append_evT, isNonRkExposure]
  rw [show t6 = encTr t5 "alice" 30 stA0 key0 from rfl,
    trEvIdx_encTr_false _ _ _ _ _ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  simp only [t5, aliceTr, aliceTrOpt, trEvIdx_append_rnd, trEvIdx_append_net,
    trEvIdx_append_stT, trEvIdx_append_evP, trEvIdx_append_evC, trEvIdx_append_evT,
    isNonRkExposure, trEvIdx_t4]
  rfl

theorem trBDH_honestDHEv_indices : trEvIdx trBDH isAnyHonestDHEv = [47] := by
  dsimp only [trBDH]
  simp only [trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evT,
    isAnyHonestDHEv, append_len, trBDH5_len]
  dsimp only [trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
  simp only [trEvIdx_append_net, trEvIdx_append_evP, trEvIdx_append_evT,
    isAnyHonestDHEv]
  rw [show t6 = encTr t5 "alice" 30 stA0 key0 from rfl,
    trEvIdx_encTr_false _ _ _ _ _ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
  simp only [t5, aliceTr, aliceTrOpt, trEvIdx_append_rnd, trEvIdx_append_net,
    trEvIdx_append_stT, trEvIdx_append_evP, trEvIdx_append_evC, trEvIdx_append_evT,
    isAnyHonestDHEv, trEvIdx_t4]
  rfl

theorem trBDH_exposedRK_eq {s : SessionInfo} {k : Bytes} {r : Nat}
    (h : trBDH.EventLogged (TREvent.ExposedRK s k r)) : k = stA0.rk := by
  rcases h with ⟨i, hi⟩
  have hm := mem_trEvIdx hi (p := fun | .ExposedRK .. => true | _ => false) rfl
  have hidx : trEvIdx trBDH (fun | .ExposedRK .. => true | _ => false) = [38] := by
    dsimp only [trBDH, trBDH5, trBDH4, invertTr, trBDH3, breakDHTr, trBDH2, trBDH1, exposeRkTr]
    simp only [trEvIdx_append_rnd, trEvIdx_append_net, trEvIdx_append_stT, trEvIdx_append_evP,
      trEvIdx_append_evT, t6_length]
    rw [show t6 = encTr t5 "alice" 30 stA0 key0 from rfl,
      trEvIdx_encTr_false _ _ _ _ _ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)]
    simp only [t5, aliceTr, aliceTrOpt, trEvIdx_append_rnd, trEvIdx_append_net,
      trEvIdx_append_stT, trEvIdx_append_evP, trEvIdx_append_evC, trEvIdx_append_evT,
      trEvIdx_t4]
    rfl
  rw [hidx, List.mem_singleton] at hm
  subst hm
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
  have hat38 :
      trBDH.at? 38 = some (EvT (.ExposedRK (stA1.sessionInfo "alice") stA1.rk 1)) :=
    at?_mono (Trace.le_trans _ _ _ trBDH1_le_trBDH4 trBDH4_le_trBDH)
      (expose_ev_at t6 _ _ (by rw [t6_length]))
  rw [hat38] at hi
  injection hi with hi'
  injection hi' with hi''
  injection hi'' with _ hk _
  exact hk.symm

theorem trBDH_honestDHEv_eq {s : SessionInfo} {d : Bytes} {r : Nat}
    (h : trBDH.EventLogged (TREvent.HonestDH s d r)) : d = dhsBDH := by
  rcases h with ⟨i, hi⟩
  have hm := mem_trEvIdx hi (p := isAnyHonestDHEv) rfl
  rw [trBDH_honestDHEv_indices, List.mem_singleton] at hm
  subst hm
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hi
  have hat47 :
      trBDH.at? 47 = some (EvT (.HonestDH (stBDH'.sessionInfo "alice") dhsBDH 1)) := by
    dsimp only [trBDH]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, trBDH5_len]))
  rw [hat47] at hi
  injection hi with hi'
  injection hi' with hi''
  injection hi'' with _ hd _
  exact hd.symm

/-! ## Reachability Invariants for DH Ratchet Secrets and Key Shapes -/

open DY.Libsignal.PQXDH (KeyKind AliceHandshakeOut BobHandshakeOut getKey lookupIdentity
  aliceAgreement bobAgreement aliceHandshake bobHandshake registerIdentity
  registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK
  compromiseSPK compromisePQSPK compromiseOPK breakDH breakKEM invertDH invertKEM)

/-- A valid root key on a reachable trace is either a PQXDH handshake root `(pqxdhKdf ikm).rk`
or a DH-ratchet root step `(createChain rk pk sk).1` from a valid root key. -/
inductive ValidRoot : Bytes → Prop
  | pqxdh (ikm : Bytes) : ValidRoot (pqxdhKdf ikm).rk
  | step {rk : Bytes} (pk sk : Bytes) : ValidRoot rk → ValidRoot (createChain rk pk sk).1

/-- A valid chain root on a reachable trace is either a PQXDH handshake chain key
`(pqxdhKdf ikm).ck` or a DH-ratchet chain output `(createChain rk pk sk).2` from a `ValidRoot`. -/
inductive ValidChainRoot : Bytes → Prop
  | pqxdh (ikm : Bytes) : ValidChainRoot (pqxdhKdf ikm).ck
  | chain {rk : Bytes} (pk sk : Bytes) : ValidRoot rk → ValidChainRoot (createChain rk pk sk).2

/-- A valid chain key is `chainKeyAt ck₀ n` for some `ValidChainRoot ck₀`. -/
def ValidChain (ck : Bytes) : Prop :=
  ∃ ck₀ n, ValidChainRoot ck₀ ∧ ck = chainKeyAt ck₀ n

/-- A valid message-key seed is `(kdfCk ck).2` for some `ValidChain ck`. -/
def ValidSeed (mk : Bytes) : Prop :=
  ∃ ck, ValidChain ck ∧ mk = (kdfCk ck).2

theorem ValidRoot.saltDepth_ge_two {r : Bytes} (h : ValidRoot r) : 2 ≤ saltDepth r := by
  cases h with
  | pqxdh ikm => simp
  | step pk sk _ => simp

theorem ValidRoot.of_createChain_fst {rk pk sk : Bytes}
    (h : ValidRoot (createChain rk pk sk).1) : ValidRoot rk := by
  generalize heq : (createChain rk pk sk).1 = x at h
  cases h with
  | pqxdh ikm => exact False.elim (pqxdhKdf_rk_ne_createChain_fst ikm rk pk sk heq.symm)
  | step pk' sk' hrk =>
    have := createChain_fst_inj heq.symm
    subst this
    exact hrk

theorem ValidRoot.of_rootDescends {a b : Bytes} (hd : RootDescends a b) (hb : ValidRoot b) :
    ValidRoot a := by
  induction hd with
  | refl => exact hb
  | step _ ih => exact ih (ValidRoot.of_createChain_fst hb)

theorem ValidChainRoot.isChainRoot {ck₀ : Bytes} (h : ValidChainRoot ck₀) : IsChainRoot ck₀ := by
  cases h with
  | pqxdh ikm => exact isChainRoot_pqxdhKdf_ck ikm
  | chain pk sk _ => exact isChainRoot_createChain_snd _ pk sk

theorem ValidChainRoot.saltDepth_ge_two {ck₀ : Bytes} (h : ValidChainRoot ck₀) :
    2 ≤ saltDepth ck₀ := by
  cases h with
  | pqxdh ikm => simp
  | chain pk sk _ => simp

theorem ValidChain.of_root {ck₀ : Bytes} (h : ValidChainRoot ck₀) : ValidChain ck₀ :=
  ⟨ck₀, 0, h, rfl⟩

theorem ValidChain.kdfCk_fst {ck : Bytes} (h : ValidChain ck) : ValidChain (kdfCk ck).1 := by
  rcases h with ⟨ck₀, n, h₀, rfl⟩
  exact ⟨ck₀, n + 1, h₀, (chainKeyAt_succ_eq_kdfCk_fst ck₀ n).symm⟩

theorem ValidChain.chainKeyAt {ck : Bytes} (h : ValidChain ck) (m : Nat) :
    ValidChain (chainKeyAt ck m) := by
  rcases h with ⟨ck₀, n, h₀, rfl⟩
  exact ⟨ck₀, n + m, h₀, (chainKeyAt_add ck₀ n m).symm⟩

theorem ValidSeed.of_chain {ck : Bytes} (h : ValidChain ck) : ValidSeed (kdfCk ck).2 :=
  ⟨ck, h, rfl⟩

/-- No term `d` with `saltDepth d = 0` can excuse a `ValidSeed mk` in any of the three
`FSQuery` disjuncts (direct, chain, or root). -/
theorem not_excused_of_validSeed_of_saltDepth_zero {mk d : Bytes}
    (hmk : ValidSeed mk) (hd : saltDepth d = 0) :
    mk ≠ d ∧ ¬ DerivesMsgKey d mk ∧ ∀ ck, ¬ (DerivesChain d ck ∧ DerivesMsgKey ck mk) := by
  rcases hmk with ⟨ck_m, ⟨ck₀, n, hroot, rfl⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hsd := congrArg saltDepth heq
    simp only [saltDepth_kdfCk_snd, saltDepth_chainKeyAt, hd] at hsd
    omega
  · rintro ⟨steps, heq⟩
    exact not_chainKeyAt_eq_of_root hroot.isChainRoot
      (by have := hroot.saltDepth_ge_two; omega) (kdfCk_snd_inj heq)
  · rintro ck ⟨⟨rk', pk, sk, hdesc, rfl⟩, ⟨steps, heq⟩⟩
    have hck₀ := (chainKeyAt_root_inj hroot.isChainRoot
      (isChainRoot_createChain_snd rk' pk sk) (kdfCk_snd_inj heq)).1
    cases hroot with
    | pqxdh ikm => exact pqxdhKdf_ck_ne_createChain_snd ikm rk' pk sk hck₀
    | chain pk₀ sk₀ hrk₀ =>
      have hrk' : ValidRoot rk' := (createChain_snd_inj hck₀) ▸ hrk₀
      have hd_valid : ValidRoot d := ValidRoot.of_rootDescends hdesc hrk'
      have := hd_valid.saltDepth_ge_two
      omega

abbrev TRStEntry : Type :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

abbrev TRStateStoredAt (p : Participant) (st : TRState) (i : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? i : Option TRStEntry) = some (StT p st)

private theorem trStateStoredAt_append_same {tr : ExecTrace} {p₀ p : Participant}
    {st₀ st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j (tr.append (StT p₀ st₀))) :
    (j < tr.length ∧ TRStateStoredAt p st j tr) ∨ (j = tr.length ∧ p₀ = p ∧ st₀ = st) := by
  rcases at?_append_cases h with ⟨hj, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hj, h⟩
  · rw [proj_inj] at hp; injection hp with hp; injection hp with hp; injection hp with hp1 hp2
    exact .inr ⟨rfl, hp1, hp2⟩

private theorem trStateStoredAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    {p : Participant} {st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j (tr.append e)) :
    TRStateStoredAt p st j tr := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

private theorem trStateStoredAt_mono_append {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E} {p : Participant} {st : TRState} {j : Nat}
    (h : TRStateStoredAt p st j tr) :
    TRStateStoredAt p st j (tr.append e) := by
  have hj : j < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr j
    rw [h] at this; exact this
  rw [TRStateStoredAt, at?_append_of_lt tr e hj]
  exact h

private theorem trStateStoredAt_append_self (tr : ExecTrace) (p : Participant) (st : TRState) :
    TRStateStoredAt p st tr.length (tr.append (StT p st)) := by
  have hlt : tr.length < (tr.append (StT p st)).length := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  dsimp only [TRStateStoredAt]
  simp only [Trace.at?, hlt, ↓reduceDIte]
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte, proj_inj]

/-- Well-formedness of a stored `TRState` snapshot. -/
structure StoredValid (st : TRState) : Prop where
  rkValid : ValidRoot st.rk
  cksValid : ValidChain st.cks
  recvValid : ∀ c ∈ st.recv, ValidChain c.chainKey
  dhsZero : saltDepth st.dhs = 0

/-- Reachable-trace key-shape invariant for stored snapshots and logged events. -/
structure ShapeInv (tr : ExecTrace) : Prop where
  storedOK : ∀ p st j, TRStateStoredAt p st j tr → StoredValid st
  exposedDHsZero : ∀ s d r, tr.EventLogged (TREvent.ExposedDHs s d r) → saltDepth d = 0
  honestDHZero : ∀ s d r, tr.EventLogged (TREvent.HonestDH s d r) → saltDepth d = 0
  skippedSeedValid :
    ∀ s pk n seed r src,
      tr.EventLogged (TREvent.SkippedKeyStored s pk n seed r src) → ValidSeed seed
  msgKeySeedValid :
    ∀ s dir seed pq n r p,
      tr.EventLogged (TREvent.MessageKey s dir seed pq n r p) → ValidSeed seed

/-- Every `HonestDH` event secret is stored as `st.dhs` in some `TRState` snapshot on the trace. -/
def HonestDHInv (tr : ExecTrace) : Prop :=
  ∀ s d r, tr.EventLogged (TREvent.HonestDH s d r) →
    ∃ p st j, TRStateStoredAt p st j tr ∧ st.dhs = d

/-- Intermediate version of `HonestDHInv` holding between `logEvent (TREvent.HonestDH _ d₀ _)`
and the subsequent `storeLocalState` in `bobStart` or `messageDecrypt`. -/
def HonestDHInvExcept (d₀ : Bytes) (tr : ExecTrace) : Prop :=
  ∀ s d r, tr.EventLogged (TREvent.HonestDH s d r) →
    d = d₀ ∨ ∃ p st j, TRStateStoredAt p st j tr ∧ st.dhs = d

def CompInv (tr : ExecTrace) : Prop :=
  HonestDHInv tr ∧ ShapeInv tr

def CompInvExcept (d₀ : Bytes) (tr : ExecTrace) : Prop :=
  HonestDHInvExcept d₀ tr ∧ ShapeInv tr

private theorem not_eventLogged_nil {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (ev : Ev) : ¬ Trace.nil.EventLogged ev := by
  rintro ⟨i, hi⟩
  have hlt := Trace.EventLoggedAt_implies_i_le_length ev i Trace.nil hi
  exact Symbolic.DYBridge.DY.Trace.nil_length_not_lt i hlt

private theorem ShapeInv.nil : ShapeInv Trace.nil where
  storedOK _ _ j h := by
    have hj := Trace.at?_eq_some_implies_length_le (α := ExecTrace.Entry) (EntryT := TRStEntry) Trace.nil j
    rw [h] at hj
    exact False.elim (Symbolic.DYBridge.DY.Trace.nil_length_not_lt j hj)
  exposedDHsZero _ _ _ h := False.elim (not_eventLogged_nil _ h)
  honestDHZero _ _ _ h := False.elim (not_eventLogged_nil _ h)
  skippedSeedValid _ _ _ _ _ _ h := False.elim (not_eventLogged_nil _ h)
  msgKeySeedValid _ _ _ _ _ _ _ h := False.elim (not_eventLogged_nil _ h)

private theorem CompInv.nil : CompInv Trace.nil :=
  ⟨fun _ _ _ h => False.elim (not_eventLogged_nil _ h), ShapeInv.nil⟩

private theorem ShapeInv.append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : ShapeInv tr) : ShapeInv (tr.append e) where
  storedOK p st j hst := h.storedOK p st j (trStateStoredAt_append_other hnone_st hst)
  exposedDHsZero s d r hev := h.exposedDHsZero s d r (eventLogged_append_other hnone_tr hev)
  honestDHZero s d r hev := h.honestDHZero s d r (eventLogged_append_other hnone_tr hev)
  skippedSeedValid s pk n seed r src hev :=
    h.skippedSeedValid s pk n seed r src (eventLogged_append_other hnone_tr hev)
  msgKeySeedValid s dir seed pq n r p hev :=
    h.msgKeySeedValid s dir seed pq n r p (eventLogged_append_other hnone_tr hev)

private theorem HonestDHInv.append_nonTR {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : HonestDHInv tr) : HonestDHInv (tr.append e) := by
  intro s d r hev
  obtain ⟨p, st, j, hst, hd⟩ := h s d r (eventLogged_append_other hnone_tr hev)
  exact ⟨p, st, j, trStateStoredAt_mono_append hst, hd⟩

private theorem HonestDHInvExcept.append_nonTR {E : Type} [ExecTraceTypes.Has E]
    {d₀ : Bytes} {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : HonestDHInvExcept d₀ tr) : HonestDHInvExcept d₀ (tr.append e) := by
  intro s d r hev
  rcases h s d r (eventLogged_append_other hnone_tr hev) with rfl | ⟨p, st, j, hst, hd⟩
  · exact .inl rfl
  · exact .inr ⟨p, st, j, trStateStoredAt_mono_append hst, hd⟩

private theorem CompInv.append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : CompInv tr) : CompInv (tr.append e) :=
  ⟨h.1.append_nonTR hnone_tr, h.2.append_other hnone_tr hnone_st⟩

private theorem CompInvExcept.append_other {E : Type} [ExecTraceTypes.Has E]
    {d₀ : Bytes} {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : CompInvExcept d₀ tr) : CompInvExcept d₀ (tr.append e) :=
  ⟨h.1.append_nonTR hnone_tr, h.2.append_other hnone_tr hnone_st⟩

private theorem ShapeInv.append_trEv {tr : ExecTrace} {ev : TREvent}
    (hdhs : ∀ s d r, ev = .ExposedDHs s d r → saltDepth d = 0)
    (hhdh : ∀ s d r, ev = .HonestDH s d r → saltDepth d = 0)
    (hskip : ∀ s pk n seed r src, ev = .SkippedKeyStored s pk n seed r src → ValidSeed seed)
    (hmk : ∀ s dir seed pq n r p, ev = .MessageKey s dir seed pq n r p → ValidSeed seed)
    (h : ShapeInv tr) : ShapeInv (tr.append (EvT ev)) where
  storedOK p st j hst := h.storedOK p st j (trStateStoredAt_append_other rfl hst)
  exposedDHsZero s d r hev := by
    rcases eventLogged_append_ev hev with hev | heq
    · exact h.exposedDHsZero s d r hev
    · exact hdhs s d r heq
  honestDHZero s d r hev := by
    rcases eventLogged_append_ev hev with hev | heq
    · exact h.honestDHZero s d r hev
    · exact hhdh s d r heq
  skippedSeedValid s pk n seed r src hev := by
    rcases eventLogged_append_ev hev with hev | heq
    · exact h.skippedSeedValid s pk n seed r src hev
    · exact hskip s pk n seed r src heq
  msgKeySeedValid s dir seed pq n r p hev := by
    rcases eventLogged_append_ev hev with hev | heq
    · exact h.msgKeySeedValid s dir seed pq n r p hev
    · exact hmk s dir seed pq n r p heq

private theorem HonestDHInv.append_tr_nonHonestDH {tr : ExecTrace} {ev : TREvent}
    (hne : ∀ s d r, ev ≠ .HonestDH s d r)
    (h : HonestDHInv tr) : HonestDHInv (tr.append (EvT ev)) := by
  intro s d r hev
  rcases eventLogged_append_ev hev with hev | heq
  · obtain ⟨p, st, j, hst, hd⟩ := h s d r hev
    exact ⟨p, st, j, trStateStoredAt_mono_append hst, hd⟩
  · exact absurd heq (hne s d r)

private theorem HonestDHInvExcept.append_tr_nonHonestDH {d₀ : Bytes} {tr : ExecTrace} {ev : TREvent}
    (hne : ∀ s d r, ev ≠ .HonestDH s d r)
    (h : HonestDHInvExcept d₀ tr) : HonestDHInvExcept d₀ (tr.append (EvT ev)) := by
  intro s d r hev
  rcases eventLogged_append_ev hev with hev | heq
  · rcases h s d r hev with rfl | ⟨p, st, j, hst, hd⟩
    · exact .inl rfl
    · exact .inr ⟨p, st, j, trStateStoredAt_mono_append hst, hd⟩
  · exact absurd heq (hne s d r)

private theorem ShapeInv.append_storeTR {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hst₀ : StoredValid st₀) (h : ShapeInv tr) : ShapeInv (tr.append (StT p₀ st₀)) where
  storedOK p st j hst := by
    rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
    · exact h.storedOK p st j hst
    · exact hst₀
  exposedDHsZero s d r hev := h.exposedDHsZero s d r (eventLogged_append_other rfl hev)
  honestDHZero s d r hev := h.honestDHZero s d r (eventLogged_append_other rfl hev)
  skippedSeedValid s pk n seed r src hev :=
    h.skippedSeedValid s pk n seed r src (eventLogged_append_other rfl hev)
  msgKeySeedValid s dir seed pq n r p hev :=
    h.msgKeySeedValid s dir seed pq n r p (eventLogged_append_other rfl hev)

private theorem CompInv.append_storeTR {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hst₀ : StoredValid st₀) (h : CompInv tr) : CompInv (tr.append (StT p₀ st₀)) :=
  ⟨h.1.append_nonTR rfl, h.2.append_storeTR hst₀⟩

private theorem CompInvExcept.resolve_storeTR {d₀ : Bytes} {tr : ExecTrace}
    {p₀ : Participant} {st₀ : TRState}
    (hst₀ : StoredValid st₀) (hdhs : st₀.dhs = d₀)
    (h : CompInvExcept d₀ tr) : CompInv (tr.append (StT p₀ st₀)) := by
  refine ⟨?_, h.2.append_storeTR hst₀⟩
  intro s d r hev
  rcases h.1 s d r (eventLogged_append_other rfl hev) with rfl | ⟨p, st, j, hst, hd⟩
  · exact ⟨p₀, st₀, tr.length, trStateStoredAt_append_self tr p₀ st₀, hdhs⟩
  · exact ⟨p, st, j, trStateStoredAt_mono_append hst, hd⟩

/-! ### `Preserves` and `PreservesWith` combinators -/

private def Preserves (Inv : ExecTrace → Prop) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val

private def PreservesWith (Inv : ExecTrace → Prop) {α : Type} (Post : α → Prop)
    (m : Traceful α) : Prop :=
  ∀ tr, Inv tr → Inv (m.run tr).2.val ∧ ∀ a, (m.run tr).1 = some a → Post a

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]; rcases x.run tr with ⟨_ | a, tr1⟩ <;> rfl

private theorem Preserves.of_id {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : ∀ tr, (x.run tr).2.val = tr) : Preserves Inv x := by
  intro tr h; rw [hx]; exact h

private theorem Preserves.pure {Inv : ExecTrace → Prop} {α : Type} (a : α) :
    Preserves Inv (Pure.pure a : Traceful α) :=
  Preserves.of_id fun _ => by simp only [Traceful.run_pure]

private theorem Preserves.failure {Inv : ExecTrace → Prop} {α : Type} :
    Preserves Inv (failure : Traceful α) :=
  Preserves.of_id fun _ => by simp only [Traceful.run_failure]

private theorem Preserves.guardP {Inv : ExecTrace → Prop} (p : Prop) {_ : Decidable p} :
    Preserves Inv (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split
  · exact Preserves.pure _
  · exact Preserves.failure

private theorem Preserves.requireTracePredicate {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (PQXDH.guardTrace p) :=
  Preserves.of_id fun _ => by unfold PQXDH.guardTrace; simp only [Traceful.run_mk]

private theorem Preserves.guardTrace {Inv : ExecTrace → Prop} (p : ExecTrace → Bool) :
    Preserves Inv (guardTrace p) :=
  Preserves.of_id fun _ => by
    unfold DY.Libsignal.TripleRatchet.guardTrace
    simp only [Traceful.run_mk]

private theorem Preserves.monadLiftErr {Inv : ExecTrace → Prop} {α : Type} (x : Err α) :
    Preserves Inv (monadLift x : Traceful α) :=
  Preserves.of_id fun _ => by
    cases x <;> simp only [monadLift, MonadLift.monadLift, Traceful.run_mk]

private theorem Preserves.traceLength {Inv : ExecTrace → Prop} :
    Preserves Inv traceLength :=
  Preserves.of_id fun _ => by unfold DY.Libsignal.TripleRatchet.traceLength; simp only [Traceful.run_mk]

private theorem Preserves.getEntry {Inv : ExecTrace → Prop} {E : Type} [ExecTraceTypes.Has E]
    (h : Nat) : Preserves Inv (DY.getEntry h : Traceful E) :=
  Preserves.of_id fun _ => by simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]

private theorem Preserves.bind {Inv : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves Inv x) (hf : ∀ a, Preserves Inv (f a)) : Preserves Inv (x >>= f) := by
  intro tr hInv; rw [Traceful.run_bind]; rcases h : x.run tr with ⟨o, trMid, _⟩
  have hMid : Inv trMid := by have := hx tr hInv; rw [h] at this; exact this
  cases o with
  | none => exact hMid
  | some a => exact hf a trMid hMid

private theorem PreservesWith.of_preserves {Inv : ExecTrace → Prop} {α : Type} {x : Traceful α}
    (hx : Preserves Inv x) : PreservesWith Inv (fun _ => True) x :=
  fun tr hInv => ⟨hx tr hInv, fun _ _ => trivial⟩

private theorem PreservesWith.pure {Inv : ExecTrace → Prop} {α : Type} {P : α → Prop}
    (a : α) (ha : P a) : PreservesWith Inv P (Pure.pure a : Traceful α) :=
  fun _ hInv => by
    simp only [Traceful.run_pure]
    exact ⟨hInv, fun _ h => Option.some.inj h ▸ ha⟩

private theorem PreservesWith.failure {Inv : ExecTrace → Prop} {α : Type} {P : α → Prop} :
    PreservesWith Inv P (failure : Traceful α) :=
  fun _ hInv => by
    simp only [Traceful.run_failure]
    exact ⟨hInv, fun _ h => nomatch h⟩

private theorem PreservesWith.bind {Inv : ExecTrace → Prop} {α β : Type}
    {P : α → Prop} {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : PreservesWith Inv P x) (hf : ∀ a, P a → PreservesWith Inv Q (f a)) :
    PreservesWith Inv Q (x >>= f) := by
  intro tr hInv
  rw [Traceful.run_bind]
  obtain ⟨h1, h2⟩ := hx tr hInv
  rcases hrun : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [hrun] at h1; exact ⟨h1, fun _ h => nomatch h⟩
  · rw [hrun] at h1
    exact hf a (h2 a (congrArg Prod.fst hrun)) trMid h1

private theorem PreservesWith.bind_preserves {Inv : ExecTrace → Prop} {α β : Type}
    {Q : β → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves Inv x) (hf : ∀ a, PreservesWith Inv Q (f a)) :
    PreservesWith Inv Q (x >>= f) :=
  PreservesWith.bind (PreservesWith.of_preserves hx) fun a _ => hf a

private theorem Preserves.bind_with {Inv : ExecTrace → Prop} {α β : Type}
    {P : α → Prop} {x : Traceful α} {f : α → Traceful β}
    (hx : PreservesWith Inv P x) (hf : ∀ a, P a → Preserves Inv (f a)) :
    Preserves Inv (x >>= f) := by
  intro tr hInv
  rw [Traceful.run_bind]
  obtain ⟨h1, h2⟩ := hx tr hInv
  rcases hrun : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [hrun] at h1; exact h1
  · rw [hrun] at h1
    exact hf a (h2 a (congrArg Prod.fst hrun)) trMid h1

private theorem Preserves.receiveMessage {Inv : ExecTrace → Prop} (h : Nat) :
    Preserves Inv (Network.receiveMessage h) := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _

private theorem Preserves.getLocalState_tr {Inv : ExecTrace → Prop} (p : Participant) (h : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p h : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Preserves.bind (Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem Preserves.getLocalState_pq {Inv : ExecTrace → Prop} (p : Participant) (h : Nat) :
    Preserves Inv (PersistentLocalState.getLocalState p h : Traceful PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  refine Preserves.bind (Preserves.bind (Preserves.getEntry _) fun _ => Preserves.pure _) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem getLocalState_tr_fst (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 =
      match (tr.at? stH : Option TRStEntry) with
      | some ⟨⟨p, st⟩⟩ => if p = me then some st else none
      | none => none := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1,
    Symbolic.DYBridge.DY.getEntry_eq_1, _root_.guard]
  rw [run_bind_fst, run_bind_fst, run_bind_snd, Traceful.run_mk]
  rcases (tr.at? stH : Option TRStEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    rw [Traceful.run_pure]
    change (((if p = me then pure () else failure : Traceful Unit) >>= fun _ => pure st).run tr).1 =
      if p = me then some st else none
    by_cases hp : p = me
    · rw [ite_eq_left_iff.mpr fun h => absurd hp h, ite_eq_left_iff.mpr fun h => absurd hp h]
      simp only [Traceful.run_bind, Traceful.run_pure]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hp, ite_eq_right_iff.mpr fun h => absurd h hp]
      simp only [Traceful.run_bind, Traceful.run_failure]

private theorem getLocalState_tr_snd (me : Participant) (stH : Nat) (tr : ExecTrace) :
    ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr :=
  Preserves.getLocalState_tr (Inv := fun t => t = tr) me stH tr rfl

private theorem Preserves.receiveSignalMsg {Inv : ExecTrace → Prop} (msgH : Nat) :
    Preserves Inv (receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem Preserves.verifyMacAndDecrypt {Inv : ExecTrace → Prop}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes) :
    Preserves Inv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.monadLiftErr _

private theorem Preserves.getKey {Inv : ExecTrace → Prop} (p : Participant) (stateIdx : Nat)
    (kind : KeyKind) : Preserves Inv (getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem Preserves.lookupIdentity {Inv : ExecTrace → Prop} (p : Participant)
    (regIdx : Nat) : Preserves Inv (lookupIdentity p regIdx) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry _) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev <;> try exact Preserves.failure
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

/-! ### Step-level `Preserves CompInv` combinators -/

private theorem sendMessage_snd (m : Bytes) (tr : ExecTrace) :
    ((Network.sendMessage m).run tr).2.val = tr.append (NetE m) := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]

private theorem genRand_fst (n : Nat) (tr : ExecTrace) :
    ((Random.genRand n).run tr).1 = some (rnd tr.length n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, rnd]

private theorem genRand_snd (n : Nat) (tr : ExecTrace) :
    ((Random.genRand n).run tr).2.val = tr.append (RndE n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]

private theorem storeTR_snd (p : Participant) (st : TRState) (tr : ExecTrace) :
    ((PersistentLocalState.storeLocalState p st).run tr).2.val = tr.append (StT p st) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem storePQX_snd (p : Participant) (st : PQXDHState) (tr : ExecTrace) :
    ((PersistentLocalState.storeLocalState p st).run tr).2.val = tr.append (StP p st) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem logEvent_fst {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (ev : Ev) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev).run tr).1 = some () := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]

private theorem logEvent_snd {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (ev : Ev) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev).run tr).2.val = tr.append (ProtocolEvent.ExecEntryT.mk ev) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]

private theorem preserves_sendMessage (m : Bytes) : Preserves CompInv (Network.sendMessage m) :=
  fun tr h => by rw [sendMessage_snd]; exact h.append_other rfl rfl

private theorem preserves_genRand (n : Nat) : Preserves CompInv (Random.genRand n) :=
  fun tr h => by rw [genRand_snd]; exact h.append_other rfl rfl

private theorem preservesWith_genRand (n : Nat) :
    PreservesWith CompInv (fun b : Bytes => saltDepth b = 0) (Random.genRand n) := by
  intro tr hInv
  refine ⟨preserves_genRand n tr hInv, fun b hb => ?_⟩
  rw [genRand_fst] at hb
  cases hb
  exact saltDepth_rnd tr.length n

private theorem preserves_storePQX (p : Participant) (st : PQXDHState) :
    Preserves CompInv (PersistentLocalState.storeLocalState p st) :=
  fun tr h => by rw [storePQX_snd]; exact h.append_other rfl rfl

private theorem preserves_logPQX (ev : PQXDHEvent) : Preserves CompInv (ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd]; exact h.append_other rfl rfl

private theorem preserves_logCEv (ev : ComposedEvent) : Preserves CompInv (ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd]; exact h.append_other rfl rfl

private theorem preservesExcept_logCEv (d₀ : Bytes) (ev : ComposedEvent) :
    Preserves (CompInvExcept d₀) (ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd]; exact h.append_other rfl rfl

private theorem preserves_logTR_inert (ev : TREvent)
    (hdhs : ∀ s d r, ev ≠ .ExposedDHs s d r)
    (hhdh : ∀ s d r, ev ≠ .HonestDH s d r)
    (hskip : ∀ s pk n seed r src, ev ≠ .SkippedKeyStored s pk n seed r src)
    (hmk : ∀ s dir seed pq n r p, ev ≠ .MessageKey s dir seed pq n r p) :
    Preserves CompInv (ProtocolEvent.logEvent ev) :=
  fun tr h => by
    rw [logEvent_snd]
    exact ⟨h.1.append_tr_nonHonestDH hhdh,
      h.2.append_trEv
        (fun s d r he => absurd he (hdhs s d r))
        (fun s d r he => absurd he (hhdh s d r))
        (fun s pk n seed r src he => absurd he (hskip s pk n seed r src))
        (fun s dir seed pq n r p he => absurd he (hmk s dir seed pq n r p))⟩

private theorem preservesExcept_logTR_inert (d₀ : Bytes) (ev : TREvent)
    (hdhs : ∀ s d r, ev ≠ .ExposedDHs s d r)
    (hhdh : ∀ s d r, ev ≠ .HonestDH s d r)
    (hskip : ∀ s pk n seed r src, ev ≠ .SkippedKeyStored s pk n seed r src)
    (hmk : ∀ s dir seed pq n r p, ev ≠ .MessageKey s dir seed pq n r p) :
    Preserves (CompInvExcept d₀) (ProtocolEvent.logEvent ev) :=
  fun tr h => by
    rw [logEvent_snd]
    exact ⟨h.1.append_tr_nonHonestDH hhdh,
      h.2.append_trEv
        (fun s d r he => absurd he (hdhs s d r))
        (fun s d r he => absurd he (hhdh s d r))
        (fun s pk n seed r src he => absurd he (hskip s pk n seed r src))
        (fun s dir seed pq n r p he => absurd he (hmk s dir seed pq n r p))⟩

private theorem preserves_storeTR (p : Participant) (st : TRState) (hst : StoredValid st) :
    Preserves CompInv (PersistentLocalState.storeLocalState p st) :=
  fun tr h => by rw [storeTR_snd]; exact h.append_storeTR hst

private theorem preserves_logSkippedKeys (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat),
      ValidChain ck → Preserves CompInv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0, _ => Preserves.pure ()
  | ck, n, k + 1, hck =>
    Preserves.bind
      (fun tr h => by
        rw [logEvent_snd]
        exact ⟨h.1.append_tr_nonHonestDH (fun _ _ _ he => by cases he),
          h.2.append_trEv
            (fun _ _ _ he => by cases he)
            (fun _ _ _ he => by cases he)
            (fun _ _ _ _ _ _ he => by cases he; exact ValidSeed.of_chain hck)
            (fun _ _ _ _ _ _ _ he => by cases he)⟩)
      fun _ => preserves_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k hck.kdfCk_fst

private theorem preservesExcept_logSkippedKeys (d₀ : Bytes) (s : SessionInfo) (pk : Bytes)
    (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat),
      ValidChain ck → Preserves (CompInvExcept d₀) (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0, _ => Preserves.pure ()
  | ck, n, k + 1, hck =>
    Preserves.bind
      (fun tr h => by
        rw [logEvent_snd]
        exact ⟨h.1.append_tr_nonHonestDH (fun _ _ _ he => by cases he),
          h.2.append_trEv
            (fun _ _ _ he => by cases he)
            (fun _ _ _ he => by cases he)
            (fun _ _ _ _ _ _ he => by cases he; exact ValidSeed.of_chain hck)
            (fun _ _ _ _ _ _ _ he => by cases he)⟩)
      fun _ => preservesExcept_logSkippedKeys d₀ s pk rIdx src (kdfCk ck).1 (n + 1) k hck.kdfCk_fst

private theorem preserves_logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hseed : ValidSeed seed) (hst : StoredValid st) :
    Preserves CompInv (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine Preserves.bind
    (fun tr h => by
      rw [logEvent_snd]
      exact ⟨h.1.append_tr_nonHonestDH (fun _ _ _ he => by cases he),
        h.2.append_trEv
          (fun _ _ _ he => by cases he)
          (fun _ _ _ he => by cases he)
          (fun _ _ _ _ _ _ he => by cases he)
          (fun _ _ _ _ _ _ _ he => by cases he; exact hseed)⟩)
    fun _ => ?_
  exact preserves_storeTR me st hst

private theorem resolve_logMessageKeyAndStore (d₀ : Bytes) (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hseed : ValidSeed seed) (hst : StoredValid st) (hdhs : st.dhs = d₀)
    (tr : ExecTrace) (hInv : CompInvExcept d₀ tr) :
    CompInv ((logMessageKeyAndStore me s dir seed pqSalt n rIdx par st).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  simp only [Traceful.run_bind, logEvent_fst, logEvent_snd, storeTR_snd]
  have h1 : CompInvExcept d₀
      (tr.append (EvT (TREvent.MessageKey s dir seed pqSalt n rIdx par))) :=
    ⟨hInv.1.append_tr_nonHonestDH (fun _ _ _ he => by cases he),
      hInv.2.append_trEv
        (fun _ _ _ he => by cases he)
        (fun _ _ _ he => by cases he)
        (fun _ _ _ _ _ _ he => by cases he)
        (fun _ _ _ _ _ _ _ he => by cases he; exact hseed)⟩
  exact h1.resolve_storeTR (p₀ := me) hst hdhs

private theorem enter_honestDH (s₀ : SessionInfo) (d₀ : Bytes) (r₀ : Nat)
    (hd₀ : saltDepth d₀ = 0) (tr : ExecTrace) (hInv : CompInv tr) :
    CompInvExcept d₀ ((ProtocolEvent.logEvent (TREvent.HonestDH s₀ d₀ r₀)).run tr).2.val := by
  rw [logEvent_snd]
  refine ⟨?_, ?_⟩
  · intro s d r hev
    rcases eventLogged_append_ev hev with hev | heq
    · obtain ⟨p, st, j, hst, hd⟩ := hInv.1 s d r hev
      exact .inr ⟨p, st, j, trStateStoredAt_mono_append hst, hd⟩
    · injection heq with _ hd _; exact .inl hd.symm
  · exact hInv.2.append_trEv
      (fun _ _ _ he => by cases he)
      (fun _ _ _ he => by cases he; exact hd₀)
      (fun _ _ _ _ _ _ he => by cases he)
      (fun _ _ _ _ _ _ _ he => by cases he)

private theorem preservesWith_getLocalState_tr (me : Participant) (stH : Nat) :
    PreservesWith CompInv StoredValid
      (PersistentLocalState.getLocalState me stH : Traceful TRState) := by
  intro tr hInv
  rw [getLocalState_tr_fst, getLocalState_tr_snd]
  refine ⟨hInv, fun st h => ?_⟩
  rcases he : (tr.at? stH : Option TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at h; nomatch h
  · rw [he] at h; dsimp only at h
    split at h
    · next hp => subst hp; cases h; exact hInv.2.storedOK p st stH he
    · nomatch h

private theorem preservesWith_getEntry_trEv (h : Nat) :
    PreservesWith CompInv
      (fun e : TREntry =>
        ∀ s pk n seed r src, e.ev = .SkippedKeyStored s pk n seed r src → ValidSeed seed)
      (DY.getEntry h : Traceful TREntry) := by
  intro tr hInv
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
  refine ⟨hInv, fun e he s pk n seed r src hev => ?_⟩
  have hat : tr.EventLogged e.ev :=
    ⟨h, by rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact he⟩
  rw [hev] at hat
  exact hInv.2.skippedSeedValid s pk n seed r src hat

private theorem preservesWith_dhRatchetStep (st₀ : TRState) (theirPk : Bytes)
    (hrk₀ : ValidRoot st₀.rk) (hrecv₀ : ∀ x ∈ st₀.recv, ValidChain x.chainKey) :
    PreservesWith CompInv (fun p : TRState × RecvChain => StoredValid p.1 ∧ ValidChain p.2.chainKey)
      (dhRatchetStep st₀ theirPk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PreservesWith.bind_preserves (Preserves.guardP _) fun _ => ?_
  refine PreservesWith.bind (preservesWith_genRand 32) fun dhs hdhs => ?_
  have hrk1 : ValidRoot (createChain st₀.rk theirPk st₀.dhs).1 :=
    ValidRoot.step theirPk st₀.dhs hrk₀
  have hckr : ValidChain (createChain st₀.rk theirPk st₀.dhs).2 :=
    ValidChain.of_root (ValidChainRoot.chain theirPk st₀.dhs hrk₀)
  have hrk2 : ValidRoot (createChain (createChain st₀.rk theirPk st₀.dhs).1 theirPk dhs).1 :=
    ValidRoot.step theirPk dhs hrk1
  have hcks : ValidChain (createChain (createChain st₀.rk theirPk st₀.dhs).1 theirPk dhs).2 :=
    ValidChain.of_root (ValidChainRoot.chain theirPk dhs hrk1)
  refine PreservesWith.pure _ ⟨⟨hrk2, hcks, ?_, hdhs⟩, hckr⟩
  intro y hy
  have hy' := List.mem_of_mem_drop hy
  rcases List.mem_append.mp hy' with hy_old | hy_new
  · exact hrecv₀ y hy_old
  · rw [List.mem_singleton] at hy_new
    subst hy_new
    exact hckr

private theorem preservesWith_ensureReceiverChain (st₀ : TRState) (theirPk : Bytes)
    (h₀ : StoredValid st₀ ∨ (ValidRoot st₀.rk ∧ st₀.recv = [])) :
    PreservesWith CompInv
      (fun p : TRState × RecvChain × Bool => StoredValid p.1 ∧ ValidChain p.2.1.chainKey)
      (ensureReceiverChain st₀ theirPk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  rcases hrec : recvChainFor st₀.toDRState theirPk with _ | ⟨c, _ | _⟩ <;> dsimp only
  · exact PreservesWith.failure
  · unfold DY.Libsignal.TripleRatchet.recvChainFor at hrec
    rcases hfind : findRecvChain st₀.recv theirPk with _ | c_found
    · rw [hfind] at hrec
      by_cases hlo : x25519LowOrder theirPk = true <;> simp only [hlo] at hrec <;> nomatch hrec
    · rw [hfind] at hrec
      injection hrec with hp; injection hp with hc _
      subst hc
      have hmem : c_found ∈ st₀.recv := List.mem_of_find?_eq_some hfind
      rcases h₀ with hst₀ | ⟨_, hnil⟩
      · exact PreservesWith.pure (st₀, c_found, false) ⟨hst₀, hst₀.recvValid c_found hmem⟩
      · rw [hnil] at hmem; nomatch hmem
  · have hbase : ValidRoot st₀.rk ∧ ∀ x ∈ st₀.recv, ValidChain x.chainKey := by
      rcases h₀ with hst₀ | ⟨hrk, hnil⟩
      · exact ⟨hst₀.rkValid, hst₀.recvValid⟩
      · exact ⟨hrk, fun _ hx => by rw [hnil] at hx; nomatch hx⟩
    refine PreservesWith.bind (preservesWith_dhRatchetStep st₀ theirPk hbase.1 hbase.2)
      fun p hp => ?_
    rcases p with ⟨st, c'⟩
    exact PreservesWith.pure (st, c', true) hp

private theorem consumeMessageKey_valid {c c' : RecvChain} {counter : UInt32} {seed : Bytes}
    (hc : ValidChain c.chainKey) (h : consumeMessageKey c counter = some (seed, c')) :
    ValidSeed seed ∧ ValidChain c'.chainKey := by
  unfold DY.Libsignal.TripleRatchet.consumeMessageKey at h
  split at h
  · nomatch h
  · split at h
    · nomatch h
    · split at h
      · nomatch h
      · injection h with hp
        injection hp with hseed hc'
        have hck : ValidChain (chainKeyAt c.chainKey (counter.toNat - c.index.toNat)) :=
          hc.chainKeyAt _
        refine ⟨?_, ?_⟩
        · rw [← hseed]; exact ValidSeed.of_chain hck
        · rw [← hc']; exact hck.kdfCk_fst

private theorem setRecvChain_valid {recv : List RecvChain} {c : RecvChain}
    (hrecv : ∀ x ∈ recv, ValidChain x.chainKey) (hc : ValidChain c.chainKey) :
    ∀ y ∈ setRecvChain recv c, ValidChain y.chainKey := by
  intro y hy
  rw [setRecvChain, List.mem_map] at hy
  rcases hy with ⟨x, hx, rfl⟩
  split
  · exact hc
  · exact hrecv x hx

private theorem preservesWith_aliceHandshake (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    PreservesWith CompInv (fun o : AliceHandshakeOut => ∃ ikm, o.keys = pqxdhKdf ikm)
      (aliceHandshake a b idStateIdx regIdxB bh) :=
  HandshakePreserves.aliceHandshake_preserves CompInv
    (fun _ _ h => h.append_other rfl rfl) a b idStateIdx regIdxB bh

private theorem bobAgreement_eq_pqxdhKdf {ikB spkSk pqsk : Bytes} {opkSk : Option Bytes}
    {ikA ek ct : Bytes} {keys : HandshakeKeys}
    (h : bobAgreement ikB spkSk pqsk opkSk ikA ek ct = some keys) :
    ∃ ikm, keys = pqxdhKdf ikm := by
  unfold DY.Libsignal.PQXDH.bobAgreement at h
  change some (pqxdhKdf _) = some keys at h
  injection h with h
  exact ⟨_, h.symm⟩

set_option maxHeartbeats 800000 in
private theorem preservesWith_bobHandshake (b a : Participant) (kh : BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) :
    PreservesWith CompInv (fun o : BobHandshakeOut => ∃ ikm, o.keys = pqxdhKdf ikm)
      (bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
  refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
  rcases kh.opk with _ | idx <;> dsimp only
  · refine PreservesWith.bind_preserves (Preserves.pure _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.lookupIdentity _ _) fun p => ?_
    rcases p with ⟨ikA, vkA⟩
    dsimp only
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.guardP _) fun _ => ?_
    split
    · next keys hagree => exact PreservesWith.pure _ (bobAgreement_eq_pqxdhKdf hagree)
    · exact PreservesWith.failure
  · refine PreservesWith.bind_preserves (Preserves.getKey _ _ _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.pure _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.lookupIdentity _ _) fun p => ?_
    rcases p with ⟨ikA, vkA⟩
    dsimp only
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.receiveMessage _) fun _ => ?_
    refine PreservesWith.bind_preserves (Preserves.guardP _) fun _ => ?_
    split
    · next keys hagree => exact PreservesWith.pure _ (bobAgreement_eq_pqxdhKdf hagree)
    · exact PreservesWith.failure

/-! ### Preservation of `CompInv` across all 23 transitions -/

private theorem preserves_registerIdentity (p : Participant) :
    Preserves CompInv (registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact preserves_storePQX p _

private theorem preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves CompInv (registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  exact preserves_logPQX _

private theorem preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves CompInv (genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  refine Preserves.bind (preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

private theorem preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves CompInv (genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (preserves_genRand 64) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  refine Preserves.bind (preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

private theorem preserves_genOneTimePrekey (b : Participant) :
    Preserves CompInv (genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  refine Preserves.bind (preserves_storePQX b _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact Preserves.pure _

private theorem preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) : Preserves CompInv (aliceStart a b idStateIdx regIdxB bh) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Preserves.bind_with (preservesWith_aliceHandshake a b idStateIdx regIdxB bh)
    fun o hkdf => ?_
  rcases hkdf with ⟨ikm, hkeys⟩
  refine Preserves.bind_with (preservesWith_genRand 32) fun dhsA hdhsA => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind Preserves.traceLength fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  refine Preserves.bind
    (preserves_logTR_inert _
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
    fun _ => ?_
  refine Preserves.bind (preserves_logCEv _) fun _ => ?_
  have hrk0 : ValidRoot o.keys.rk := hkeys ▸ ValidRoot.pqxdh ikm
  have hck0 : ValidChain o.keys.ck :=
    ValidChain.of_root (hkeys ▸ ValidChainRoot.pqxdh ikm)
  refine preserves_storeTR a _
    ⟨ValidRoot.step o.spk dhsA hrk0,
      ValidChain.of_root (ValidChainRoot.chain o.spk dhsA hrk0), ?_, hdhsA⟩
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  exact hck0

private theorem Preserves.bind_enter {Inv₁ Inv₂ : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : ∀ tr, Inv₁ tr → (x.run tr).1.isSome = true ∧ Inv₂ (x.run tr).2.val)
    (hf : ∀ a tr, Inv₂ tr → Inv₁ ((f a).run tr).2.val) :
    Preserves Inv₁ (x >>= f) := by
  intro tr hInv
  rw [Traceful.run_bind]
  obtain ⟨hsome, hMid⟩ := hx tr hInv
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [h] at hsome; cases hsome
  · rw [h] at hMid; exact hf a trMid hMid

private theorem Preserves.bind_step {Inv₁ Inv₂ : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hx : ∀ tr, Inv₂ tr → (x.run tr).1.isSome = true ∧ Inv₂ (x.run tr).2.val)
    (hf : ∀ a tr, Inv₂ tr → Inv₁ ((f a).run tr).2.val) :
    ∀ tr, Inv₂ tr → Inv₁ ((x >>= f).run tr).2.val := by
  intro tr hInv
  rw [Traceful.run_bind]
  obtain ⟨hsome, hMid⟩ := hx tr hInv
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [h] at hsome; cases hsome
  · rw [h] at hMid; exact hf a trMid hMid

private theorem logSkippedKeys_isSome (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      ((logSkippedKeys s pk rIdx src ck n k).run tr).1.isSome = true
  | _, _, 0, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; simp only [Traceful.run_pure]; rfl
  | ck, n, k + 1, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [run_bind_fst, logEvent_fst]
    exact logSkippedKeys_isSome s pk rIdx src (kdfCk ck).1 (n + 1) k _

private theorem preserves_bobStart_afterOpk (b a : Participant) (o : BobHandshakeOut)
    (st : TRState) (hst : StoredValid st)
    (msg : TRSignalMsg) (c c' : RecvChain) (hc : ValidChain c.chainKey) (hc' : ValidChain c'.chainKey)
    (ratcheted : Bool) (seed pqSalt m : Bytes) (hseed : ValidSeed seed) (spqr' : Bytes) :
    Preserves CompInv (do
      let doneIdx ← traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
      if ratcheted then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← traceLength) + skipped + 2
      logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) := by
  have hst' : StoredValid { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
    ⟨hst.rkValid, hst.cksValid, setRecvChain_valid hst.recvValid hc', hst.dhsZero⟩
  refine Preserves.bind Preserves.traceLength fun doneIdx => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  cases ratcheted <;> dsimp only
  · refine Preserves.bind (preserves_logCEv _) fun _ => ?_
    refine Preserves.bind Preserves.traceLength fun _ => ?_
    refine Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _ hc) fun _ => ?_
    refine Preserves.bind
      (preserves_logTR_inert _
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
      fun _ => ?_
    exact preserves_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hseed hst'
  · refine Preserves.bind
      (preserves_logTR_inert _
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
      fun _ => ?_
    refine Preserves.bind_enter
      (fun tr hInv =>
        ⟨by rw [logEvent_fst]; rfl,
          enter_honestDH (st.sessionInfo b) st.dhs (st.rIdx - 2) hst.dhsZero tr hInv⟩)
      fun _ => ?_
    refine Preserves.bind_step
      (fun tr hInv => ⟨by rw [logEvent_fst]; rfl, preservesExcept_logCEv st.dhs _ tr hInv⟩)
      fun _ => ?_
    refine Preserves.bind_step
      (fun tr hInv => by
        unfold DY.Libsignal.TripleRatchet.traceLength
        simp only [Traceful.run_mk]
        exact ⟨rfl, hInv⟩)
      fun _ => ?_
    refine Preserves.bind_step
      (fun tr hInv =>
        ⟨logSkippedKeys_isSome _ _ _ _ _ _ _ tr,
          preservesExcept_logSkippedKeys st.dhs _ _ _ _ _ _ _ hc tr hInv⟩)
      fun _ => ?_
    refine Preserves.bind_step
      (fun tr hInv =>
        ⟨by rw [logEvent_fst]; rfl, preservesExcept_logTR_inert st.dhs _
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
          (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h) tr hInv⟩)
      fun _ => ?_
    exact resolve_logMessageKeyAndStore st.dhs b _ _ _ _ _ _ _ _ hseed hst' rfl

private theorem preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Preserves.bind_with (preservesWith_bobHandshake b a kh regIdxA mh.ek mh.ct)
    fun o hkdf => ?_
  rcases hkdf with ⟨ikm, hkeys⟩
  refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
  have hrk0 : ValidRoot o.keys.rk := hkeys ▸ ValidRoot.pqxdh ikm
  refine Preserves.bind_with
    (preservesWith_ensureReceiverChain _ msg.ratchetKey (.inr ⟨hrk0, rfl⟩))
    fun p hp => ?_
  rcases p with ⟨st, c, ratcheted⟩
  rcases hp with ⟨hst, hc⟩
  dsimp only
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩ <;> dsimp only
  · exact Preserves.failure
  · obtain ⟨hseed, hc'⟩ := consumeMessageKey_valid hc hcons
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩ <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      rcases hopk : o.opk with _ | opk <;> dsimp only
      · rw [← hopk]
        exact preserves_bobStart_afterOpk b a o st hst msg c c' hc hc' ratcheted seed pqSalt m hseed spqr'
      · refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
        refine Preserves.bind (preserves_logPQX _) fun _ => ?_
        rw [← hopk]
        exact preserves_bobStart_afterOpk b a o st hst msg c c' hc hc' ratcheted seed pqSalt m hseed spqr'

private theorem preserves_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves CompInv (messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st hst => ?_
  refine Preserves.bind (Preserves.guardP _) fun _ => ?_
  refine Preserves.bind (preserves_genRand 32) fun _ => ?_
  refine Preserves.bind (preserves_genRand coinsLen) fun _ => ?_
  refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind
    (preserves_logTR_inert _
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
    fun _ => ?_
  refine Preserves.bind
    (preserves_logMessageKeyAndStore me _ .sender _ _ _ _ _ _
      (ValidSeed.of_chain hst.cksValid)
      ⟨hst.rkValid, hst.cksValid.kdfCk_fst, hst.recvValid, hst.dhsZero⟩)
    fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves CompInv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  exact Preserves.bind (preserves_genRand 32) fun _ => Preserves.failure

private theorem preserves_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves CompInv (messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st₀ hst₀ => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg => ?_
  refine Preserves.bind_with
    (preservesWith_ensureReceiverChain st₀ msg.ratchetKey (.inl hst₀))
    fun p hp => ?_
  rcases p with ⟨st, c, ratcheted⟩
  rcases hp with ⟨hst, hc⟩
  dsimp only
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩ <;> dsimp only
  · exact Preserves.failure
  · obtain ⟨hseed, hc'⟩ := consumeMessageKey_valid hc hcons
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩ <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      cases ratcheted
      · refine Preserves.bind (preserves_logSkippedKeys _ _ _ _ _ _ _ hc) fun _ => ?_
        refine Preserves.bind
          (preserves_logTR_inert _
            (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
            (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
          fun _ => ?_
        exact preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hseed
          ⟨hst.rkValid, hst.cksValid, setRecvChain_valid hst.recvValid hc', hst.dhsZero⟩
      · refine Preserves.bind
          (preserves_logTR_inert _
            (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
            (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
          fun _ => ?_
        refine Preserves.bind_enter
          (fun tr hInv =>
            ⟨by rw [logEvent_fst]; rfl,
              enter_honestDH (st.sessionInfo me) st.dhs (st.rIdx - 2) hst.dhsZero tr hInv⟩)
          fun _ => ?_
        refine Preserves.bind_step
          (fun tr hInv =>
            ⟨logSkippedKeys_isSome _ _ _ _ _ _ _ tr,
              preservesExcept_logSkippedKeys st.dhs _ _ _ _ _ _ _ hc tr hInv⟩)
          fun _ => ?_
        refine Preserves.bind_step
          (fun tr hInv =>
            ⟨by rw [logEvent_fst]; rfl, preservesExcept_logTR_inert st.dhs _
              (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
              (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h) tr hInv⟩)
          fun _ => ?_
        exact resolve_logMessageKeyAndStore st.dhs me _ _ _ _ _ _ _ _ hseed
          ⟨hst.rkValid, hst.cksValid, setRecvChain_valid hst.recvValid hc', hst.dhsZero⟩ rfl

private theorem preserves_messageDecryptSkipped (me : Participant) (stH msgH evH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves CompInv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st hst => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg => ?_
  refine Preserves.bind_with (preservesWith_getEntry_trEv evH) fun e he => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    have hseed : ValidSeed seed := he s pk n seed rIdx src rfl
    dsimp only
    refine Preserves.bind (Preserves.guardP _) fun _ => ?_
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩ <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
      refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
      refine Preserves.bind
        (preserves_logTR_inert _
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
          (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
        fun _ => ?_
      refine Preserves.bind
        (preserves_logTR_inert _
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
          (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
        fun _ => ?_
      exact preserves_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hseed
        ⟨hst.rkValid, hst.cksValid, hst.recvValid, hst.dhsZero⟩
  | _ => exact Preserves.failure

private theorem preserves_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    Preserves CompInv (exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind_with (preservesWith_getLocalState_tr me stH) fun st hst => ?_
  cases k <;> dsimp only
  case rk =>
    refine Preserves.bind
      (preserves_logTR_inert _
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
      fun _ => preserves_sendMessage _
  case dhs =>
    refine Preserves.bind ?_ fun _ => preserves_sendMessage _
    exact fun tr hInv => by
      rw [logEvent_snd]
      exact ⟨hInv.1.append_tr_nonHonestDH (fun _ _ _ h => by cases h),
        hInv.2.append_trEv
          (fun _ _ _ he => by cases he; exact hst.dhsZero)
          (fun _ _ _ h => by cases h)
          (fun _ _ _ _ _ _ h => by cases h)
          (fun _ _ _ _ _ _ _ h => by cases h)⟩
  case cks =>
    refine Preserves.bind
      (preserves_logTR_inert _
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
      fun _ => preserves_sendMessage _
  case ckr pk =>
    rcases findRecvChain st.recv pk with _ | c <;> dsimp only
    · exact Preserves.failure
    · refine Preserves.bind
        (preserves_logTR_inert _
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
          (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
        fun _ => preserves_sendMessage _

private theorem preserves_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves CompInv (exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  refine Preserves.bind
    (preserves_logTR_inert _
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
    fun _ => preserves_sendMessage _

private theorem preserves_exposeSkipped (evH : Nat) :
    Preserves CompInv (exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine Preserves.bind (Preserves.getEntry evH) fun e => ?_
  rcases e with ⟨ev⟩
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    refine Preserves.bind
      (preserves_logTR_inert _
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ h => by cases h))
      fun _ => preserves_sendMessage _
  | _ => exact Preserves.failure

private theorem preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves CompInv (compromiseIK p stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves CompInv (compromiseSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves CompInv (compromisePQSPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves CompInv (compromiseOPK b stateIdx) := by
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine Preserves.bind (Preserves.getKey _ _ _) fun _ => ?_
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (preserves_logPQX _) fun _ => ?_
  exact preserves_sendMessage _

private theorem preserves_breakDH : Preserves CompInv breakDH :=
  preserves_logPQX _

private theorem preserves_breakKEM : Preserves CompInv breakKEM :=
  preserves_logPQX _

private theorem preserves_invertDH (pkIdx : Nat) : Preserves CompInv (invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact preserves_sendMessage _
  · exact Preserves.failure

private theorem preserves_invertKEM (pkIdx : Nat) : Preserves CompInv (invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.monadLiftErr _) fun _ => ?_
  exact preserves_sendMessage _

private theorem Preserves.composed_step
    (input : reachability.Input) (tr : ExecTrace)
    (hInv : CompInv tr) :
    CompInv (((reachability.step input).snd).run tr).2.val := by
  rcases input with ⟨⟨i, hi⟩, inp⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact preserves_sendMessage inp tr hInv
  · exact preserves_registerIdentity inp tr hInv
  · rcases inp with ⟨p, skIdx⟩; exact preserves_registerCorruptIdentity p skIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩; exact preserves_genSignedPrekey b idStateIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩; exact preserves_genPQPrekey b idStateIdx tr hInv
  · exact preserves_genOneTimePrekey inp tr hInv
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact preserves_aliceStart a b idStateIdx regIdxB bh tr hInv
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩
    exact preserves_messageEncrypt me stH coinsLen pqIdx tr hInv
  · rcases inp with ⟨me, stH⟩; exact preserves_messageEncryptAbort me stH tr hInv
  · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩
    exact preserves_messageDecrypt me stH msgH pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩
    exact preserves_messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stH, k⟩; exact preserves_exposeKey me stH k tr hInv
  · rcases inp with ⟨me, stH⟩; exact preserves_exposeSpqr me stH tr hInv
  · exact preserves_exposeSkipped inp tr hInv
  · rcases inp with ⟨p, stateIdx⟩; exact preserves_compromiseIK p stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩; exact preserves_compromiseSPK b stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩; exact preserves_compromisePQSPK b stateIdx tr hInv
  · rcases inp with ⟨b, stateIdx⟩; exact preserves_compromiseOPK b stateIdx tr hInv
  · exact preserves_breakDH tr hInv
  · exact preserves_breakKEM tr hInv
  · exact preserves_invertDH inp tr hInv
  · exact preserves_invertKEM inp tr hInv
  · omega

theorem compInv_reachable {tr : ExecTrace} (hReach : tr.Reachable reachability) : CompInv tr := by
  induction hReach with
  | Base => exact CompInv.nil
  | Step input _ _ ih => exact Preserves.composed_step input _ ih

/-- On every reachable trace, any `TREvent.HonestDH s d r` event implies that `d` is stored as
`st.dhs` in some `TRState` snapshot on `tr`. -/
theorem honestDH_event_imp_stored {tr : ExecTrace} (hReach : tr.Reachable reachability)
    {s : SessionInfo} {d : Bytes} {r : Nat} (h : tr.EventLogged (TREvent.HonestDH s d r)) :
    ∃ me st j, StateStoredAt me st j tr ∧ st.dhs = d :=
  (compInv_reachable hReach).1 s d r h

/-- On every reachable trace, if `mk` is a logged `MessageKey` seed and `d` is either exposed via
`ExposedDHs` or satisfies `HonestDH`, then `d` cannot excuse `mk` in `FSQuery`. -/
theorem not_dhs_excuses_msgKey {tr : ExecTrace} {Knows : Bytes → Prop}
    (hReach : tr.Reachable reachability)
    {mk : Bytes}
    (hmk : (mkTestTracePredicates tr Knows).MessageKey mk)
    {d : Bytes}
    (hd : (∃ s' i', tr.EventLogged (TREvent.ExposedDHs s' d i')) ∨
      (mkTestTracePredicates tr Knows).HonestDH d) :
    mk ≠ d ∧ ¬ DerivesMsgKey d mk ∧ ∀ ck, ¬ (DerivesChain d ck ∧ DerivesMsgKey ck mk) := by
  have hShape := (compInv_reachable hReach).2
  rcases hmk with ⟨pq, s, dir, n, i, p, hev⟩
  have hseed : ValidSeed mk := hShape.msgKeySeedValid s dir mk pq n i p hev
  have hd0 : saltDepth d = 0 := by
    rcases hd with ⟨s', i', he⟩ | ⟨s', i', hh⟩ | ⟨me, st, j, hst, rfl⟩
    · exact hShape.exposedDHsZero s' d i' he
    · exact hShape.honestDHZero s' d i' hh
    · exact (hShape.storedOK me st j hst).dhsZero
  exact not_excused_of_validSeed_of_saltDepth_zero hseed hd0

end

end Symbolic.Proofs.Tests.Shared.ExplanationTightness.CompromisedTraces

