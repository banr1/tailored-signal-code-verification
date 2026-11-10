/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Stored Root-Key and Ratchet-Secret Uniqueness

Proves `RkPairUniqInv` across reachable traces of `DY.Libsignal.Composed`: every stored `TRState`
draws its ratchet secret `st.dhs = randTerm t 32` at a timestamp strictly greater than any peer DH
key in its parent `createChain`, and any two stored states sharing `dhs` agree on `rk` and
participant (`trStateStoredAt_rk_eq_of_dhs_eq`, `stored_dhs_ne_spkSk`, `stored_peer_lt`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey findRecvChain setRecvChain kdfCk)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles
  PreKeyMsgHandles opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey
  genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH invertKEM)
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompPresPQXDH
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable EvE)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

unseal DY.Bytes in
theorem randTerm_timestamp_inj {t₁ t₂ n₁ n₂ : Nat}
    (h : randTerm t₁ n₁ = randTerm t₂ n₂) : t₁ = t₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.Random.Random) { timestamp := t₁, size := n₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.Random.Random) { timestamp := t₂, size := n₂ }
  change DY.Bytes.view? (randTerm t₁ n₁) _ = _ at h1
  change DY.Bytes.view? (randTerm t₂ n₂) _ = _ at h2
  rw [h, h2] at h1
  injection h1 with h1
  injection h1 with ht _
  exact ht.symm

/-- Every DH public key timestamp occurring as `X25519.normalizeX25519Key pk = dhPk (randTerm c 32)` is `< t`. -/
def PeerLtAt (t : Nat) (pk : DY.Bytes) : Prop :=
  ∀ c : Nat, X25519.normalizeX25519Key pk = DiffieHellman.dhPk (randTerm c 32) → c < t

theorem peerLtAt_mono {t₁ t₂ : Nat} {pk : DY.Bytes} (hle : t₁ ≤ t₂) (h : PeerLtAt t₁ pk) :
    PeerLtAt t₂ pk :=
  fun c hc => Nat.lt_of_lt_of_le (h c hc) hle

theorem randAt_lt_len {tr : ExecTrace} {c n : Nat} (h : CompInv.RandAt tr c n) : c < tr.length := by
  unfold CompInv.RandAt Trace.at? at h
  split at h <;> [assumption; cases h]

theorem lt_of_dhClass_rand32 {tr : ExecTrace} {c : Nat} (h : CompInv.DhClass tr (randTerm c 32)) :
    c < tr.length := by
  rcases h with ⟨_, t, heq, hr, _⟩ | ⟨_, t, heq, hr, _⟩ | ⟨_, t, heq, hr, _⟩ |
    ⟨t, heq, hr, _⟩ | ⟨t, heq, _, _, hr, _⟩ | ⟨t, _, heq, hr, _⟩ <;>
  (obtain ⟨rfl, _⟩ := CompInv.rnd_inj heq; exact randAt_lt_len hr)

theorem lt_of_pqClass_rand32 {tr : ExecTrace} {c : Nat} (h : CompInv.PQClass tr (randTerm c 32)) :
    c < tr.length := by
  rcases h with ⟨_, t, heq, hr, _⟩
  obtain ⟨rfl, _⟩ := CompInv.rnd_inj heq
  exact randAt_lt_len hr

theorem lt_of_msgEncRandAt_rand32 {tr : ExecTrace} {c : Nat}
    (h : CompInv.MsgEncRandAt tr (randTerm c 32)) : c < tr.length := by
  rcases h with ⟨t, _, _, heq, hr, _⟩ | ⟨t, _, _, heq, _, hr, _⟩ <;>
  (obtain ⟨rfl, _⟩ := CompInv.rnd_inj heq; exact randAt_lt_len hr)

theorem lt_of_randExposed_rand32 {tr : ExecTrace} {c : Nat}
    (h : CompInv.RandExposed tr (randTerm c 32)) : c < tr.length := by
  rcases h with ⟨p, h, _⟩ | ⟨b, h, _⟩ | ⟨b, h, _⟩ | ⟨b, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h | h, _⟩ | h
  · exact lt_of_dhClass_rand32 (.inl ⟨p, h⟩)
  · exact lt_of_dhClass_rand32 (.inr (.inl ⟨b, h⟩))
  · exact lt_of_pqClass_rand32 ⟨b, h⟩
  · exact lt_of_dhClass_rand32 (.inr (.inr (.inl ⟨b, h⟩)))
  · exact lt_of_dhClass_rand32 h
  · exact lt_of_pqClass_rand32 h
  · exact lt_of_dhClass_rand32 (.inr (.inr (.inr (.inr (.inl h)))))
  · exact lt_of_dhClass_rand32 (.inr (.inr (.inr (.inr (.inr h)))))
  · exact lt_of_msgEncRandAt_rand32 h

theorem peerLtAt_of_pub {tr : ExecTrace} (hinv : SpqrInv tr) {pk : DY.Bytes}
    (hpub : CompInv.Pub tr pk) : PeerLtAt tr.length pk := by
  intro c hk
  have hx : CompInv.Pub tr (DiffieHellman.dhPk (randTerm c 32)) :=
    hk ▸ CompInv.CompPubInv.Pub.normalizeX25519Key hinv hpub
  rcases CompInv.CompPubInv.Pub.inv_dhPk hinv hx with hdh | hr
  · exact lt_of_dhClass_rand32 hdh
  · exact lt_of_randExposed_rand32 (CompInv.CompPubInv.Pub.inv_rand hinv hr)

theorem peerLtAt_of_attackerKnows {tr : ExecTrace} (hinv : SpqrInv tr) {pk : DY.Bytes}
    (hak : pk.AttackerKnows tr) : PeerLtAt tr.length pk :=
  peerLtAt_of_pub hinv (CompInv.CompPubInv.Pub.of_attackerKnows hinv hak)

theorem pub_ratchetKey_of_parseTrSignalMsg {tr : ExecTrace} (hinv : SpqrInv tr)
    {raw : DY.Bytes} {msg : TRSignalMsg} (hraw : CompInv.Pub tr raw)
    (hparse : parseTrSignalMsg raw = some msg) :
    CompInv.Pub tr msg.ratchetKey := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hparse
  dsimp only [bind, Option.bind] at hparse
  rcases hsplit : Concat.split raw (raw.length - Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsplit] at hparse; cases hparse
  · rw [hsplit] at hparse
    dsimp only at hparse
    have hraw_eq : raw = Concat.concat wire mac :=
      (Concat.concat_split raw (raw.length - Trunc.trunc8Length) wire mac hsplit).symm
    have hwire_pub : CompInv.Pub tr wire := (CompInv.CompPubInv.Pub.inv_cat hinv (hraw_eq ▸ hraw)).1
    rcases hfields : TrWire.trWireMsgFields? wire with _ | x
    · rw [hfields] at hparse; cases hparse
    · rw [hfields] at hparse
      dsimp only [pure] at hparse
      injection hparse with hmsg_eq
      have hrk_eq : msg.ratchetKey = x.senderRatchetKey := by rw [← hmsg_eq]
      rw [hrk_eq]
      have hwire_eq := TrWire.trWireMsg_of_fields? hfields
      rw [hwire_eq] at hwire_pub
      exact (CompInv.CompPubInv.Pub.inv_trWire hinv hwire_pub).1

/-- Trace invariant for stored `(rk, dhs)` pairs:
1. Every stored `TRState` at `tr` has `st.dhs = randTerm t 32` for some `t < tr.length` and
   `st.rk = (createChain rk_p pk_p (randTerm t 32)).1` with `PeerLtAt t pk_p`.
2. Any two stored `TRState`s at `tr` with the same `dhs` have the same `rk` and participant `p`. -/
structure RkPairUniqInv (tr : ExecTrace) : Prop where
  dhs_bound : ∀ p st idx, TRStateStoredAt p st idx tr →
    ∃ t < tr.length, st.dhs = randTerm t 32 ∧
      ∃ rk_p pk_p, PeerLtAt t pk_p ∧ st.rk = (createChain rk_p pk_p (randTerm t 32)).1
  pair_uniq : ∀ p₁ st₁ idx₁ p₂ st₂ idx₂,
    TRStateStoredAt p₁ st₁ idx₁ tr → TRStateStoredAt p₂ st₂ idx₂ tr →
    st₁.dhs = st₂.dhs → st₁.rk = st₂.rk ∧ p₁ = p₂

theorem rkPairUniqInv_nil : RkPairUniqInv Trace.nil where
  dhs_bound := by
    intro _ _ _ hst
    unfold TRStateStoredAt Trace.at? at hst
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hst
  pair_uniq := by
    intro _ _ _ _ _ _ hst₁ _ _
    unfold TRStateStoredAt Trace.at? at hst₁
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1] at hst₁

theorem rkPairUniqInv_append_other {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none := by rfl)
    (h : RkPairUniqInv tr) : RkPairUniqInv (tr.append e) where
  dhs_bound := by
    intro p st idx hs
    obtain ⟨t, ht, hdhs, hrk⟩ := h.dhs_bound p st idx (CompTrace.trStateStoredAt_append_other hst hs)
    exact ⟨t, Nat.lt_of_lt_of_le ht (Trace.length_le _ _ (Trace.append_le _ _)), hdhs, hrk⟩
  pair_uniq := by
    intro p₁ st₁ idx₁ p₂ st₂ idx₂ hs₁ hs₂ heq
    exact h.pair_uniq p₁ st₁ idx₁ p₂ st₂ idx₂
      (CompTrace.trStateStoredAt_append_other hst hs₁)
      (CompTrace.trStateStoredAt_append_other hst hs₂) heq

theorem rkPairUniqInv_append_st_copy {tr : ExecTrace} (p : Participant) {st st₀ : TRState} {idx₀ : Nat}
    (hst₀ : TRStateStoredAt p st₀ idx₀ tr) (hdhs : st.dhs = st₀.dhs) (hrk : st.rk = st₀.rk)
    (h : RkPairUniqInv tr) : RkPairUniqInv (tr.append (TRStE p st)) where
  dhs_bound := by
    intro p' st' idx hs
    rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs'⟩ | ⟨_, rfl, rfl⟩
    · obtain ⟨t, ht, hd, hr⟩ := h.dhs_bound p' st' idx hs'
      exact ⟨t, Nat.lt_of_lt_of_le ht (Trace.length_le _ _ (Trace.append_le _ _)), hd, hr⟩
    · obtain ⟨t, ht, hd, rk_p, pk_p, hplt, hr⟩ := h.dhs_bound p st₀ idx₀ hst₀
      exact ⟨t, Nat.lt_of_lt_of_le ht (Trace.length_le _ _ (Trace.append_le _ _)), hdhs.trans hd, rk_p, pk_p, hplt, hrk.trans hr⟩
  pair_uniq := by
    intro p₁ st₁ idx₁ p₂ st₂ idx₂ hs₁ hs₂ heq
    rcases CompTrace.trStateStoredAt_append_same hs₁ with ⟨_, hs₁'⟩ | ⟨_, rfl, rfl⟩ <;>
      rcases CompTrace.trStateStoredAt_append_same hs₂ with ⟨_, hs₂'⟩ | ⟨_, rfl, rfl⟩
    · exact h.pair_uniq p₁ st₁ idx₁ p₂ st₂ idx₂ hs₁' hs₂' heq
    · have ⟨hrk_eq, hp_eq⟩ := h.pair_uniq p₁ st₁ idx₁ p st₀ idx₀ hs₁' hst₀ (heq.trans hdhs)
      exact ⟨hrk_eq.trans hrk.symm, hp_eq⟩
    · have ⟨hrk_eq, hp_eq⟩ := h.pair_uniq p st₀ idx₀ p₂ st₂ idx₂ hst₀ hs₂' (hdhs.symm.trans heq)
      exact ⟨hrk.trans hrk_eq, hp_eq⟩
    · exact ⟨rfl, rfl⟩

theorem rkPairUniqInv_append_st_fresh {tr : ExecTrace} (p : Participant) {st : TRState} {t_new : Nat}
    (ht_lt : t_new < tr.length)
    (ht_fresh : ∀ p' st' idx', TRStateStoredAt p' st' idx' tr → st'.dhs ≠ randTerm t_new 32)
    (hdhs : st.dhs = randTerm t_new 32)
    (hrk : ∃ rk_p pk_p, PeerLtAt t_new pk_p ∧ st.rk = (createChain rk_p pk_p (randTerm t_new 32)).1)
    (h : RkPairUniqInv tr) : RkPairUniqInv (tr.append (TRStE p st)) where
  dhs_bound := by
    intro p' st' idx hs
    rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs'⟩ | ⟨_, rfl, rfl⟩
    · obtain ⟨t, ht, hd, hr⟩ := h.dhs_bound p' st' idx hs'
      exact ⟨t, Nat.lt_of_lt_of_le ht (Trace.length_le _ _ (Trace.append_le _ _)), hd, hr⟩
    · exact ⟨t_new, Nat.lt_of_lt_of_le ht_lt (Trace.length_le _ _ (Trace.append_le _ _)), hdhs, hrk⟩
  pair_uniq := by
    intro p₁ st₁ idx₁ p₂ st₂ idx₂ hs₁ hs₂ heq
    rcases CompTrace.trStateStoredAt_append_same hs₁ with ⟨_, hs₁'⟩ | ⟨_, rfl, rfl⟩ <;>
      rcases CompTrace.trStateStoredAt_append_same hs₂ with ⟨_, hs₂'⟩ | ⟨_, rfl, rfl⟩
    · exact h.pair_uniq p₁ st₁ idx₁ p₂ st₂ idx₂ hs₁' hs₂' heq
    · exact False.elim (ht_fresh p₁ st₁ idx₁ hs₁' (heq.trans hdhs))
    · exact False.elim (ht_fresh p₂ st₂ idx₂ hs₂' (heq.symm.trans hdhs))
    · exact ⟨rfl, rfl⟩

theorem dhs_ne_randTerm_of_ge {tr₀ : ExecTrace} (h : RkPairUniqInv tr₀) {t_new : Nat}
    (hle : tr₀.length ≤ t_new) :
    ∀ p' st' idx', TRStateStoredAt p' st' idx' tr₀ → st'.dhs ≠ randTerm t_new 32 := by
  intro p' st' idx' hs heq
  obtain ⟨t, ht, hdhs, _⟩ := h.dhs_bound p' st' idx' hs
  have := randTerm_timestamp_inj (hdhs.symm.trans heq)
  omega

def PQRkUAt (tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  RkPairUniqInv tr → RkPairUniqInv (x.run tr).2.val ∧
    ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a

def NoNewStore (tr₀ tr₁ : ExecTrace) : Prop :=
  ∀ p st idx, TRStateStoredAt p st idx tr₁ → TRStateStoredAt p st idx tr₀

theorem noNewStore_refl (tr : ExecTrace) : NoNewStore tr tr := fun _ _ _ h => h

theorem noNewStore_trans {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : NoNewStore tr₀ tr₁) (h12 : NoNewStore tr₁ tr₂) : NoNewStore tr₀ tr₂ :=
  fun p st idx h => h01 p st idx (h12 p st idx h)

theorem noNewStore_append_other {tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none := by rfl) :
    NoNewStore tr (tr.append e) :=
  fun _ _ _ h => CompTrace.trStateStoredAt_append_other hst h

theorem PQRkUAt.bind {tr : ExecTrace} {α β : Type}
    {Q : ExecTrace → α → Prop} {R : ExecTrace → β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : PQRkUAt tr Q x) (hf : ∀ tr1 a, tr ≤ tr1 → Q tr1 a → PQRkUAt tr1 R (f a)) :
    PQRkUAt tr R (x >>= f) := by
  intro hJ
  rw [Traceful.run_bind]
  have hx0 := hx hJ
  rcases h : x.run tr with ⟨_ | a, trMid, hmid⟩ <;> rw [h] at hx0
  · exact ⟨hx0.1, fun _ hb => by cases hb⟩
  · exact hf trMid a hmid (hx0.2 a rfl) hx0.1

theorem PQRkUAt.of_id {tr : ExecTrace} {α : Type} {x : Traceful α}
    (hx : (x.run tr).2.val = tr) : PQRkUAt tr (fun tr1 _ => tr1 = tr) x := by
  intro hJ; rw [hx]; exact ⟨hJ, fun _ _ => rfl⟩

theorem PQRkUAt.pure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop}
    (a : α) (ha : Q tr a) : PQRkUAt tr Q (Pure.pure a : Traceful α) := by
  unfold PQRkUAt
  rw [Traceful.run_pure]
  intro hJ
  refine ⟨hJ, fun b hb => ?_⟩; cases hb; exact ha

theorem PQRkUAt.failure {tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} :
    PQRkUAt tr Q (Alternative.failure : Traceful α) := by
  unfold PQRkUAt
  rw [Traceful.run_failure]
  exact fun hJ => ⟨hJ, fun _ hb => by cases hb⟩

theorem PQRkUAt.guardP {tr : ExecTrace} (p : Prop) [Decidable p] :
    PQRkUAt tr (fun tr1 _ => tr1 = tr ∧ p) (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard
  split
  · rename_i hp; exact PQRkUAt.pure () ⟨rfl, hp⟩
  · exact PQRkUAt.failure

theorem PQRkUAt.guardTrace {tr : ExecTrace} (p : ExecTrace → Bool) :
    PQRkUAt tr (fun tr1 _ => tr1 = tr) (DY.Libsignal.TripleRatchet.guardTrace p) := by
  apply PQRkUAt.of_id
  unfold DY.Libsignal.TripleRatchet.guardTrace
  rw [Traceful.run_mk]

theorem PQRkUAt.traceLength {tr : ExecTrace} :
    PQRkUAt tr (fun tr1 _ => tr1 = tr) DY.Libsignal.TripleRatchet.traceLength := by
  apply PQRkUAt.of_id
  unfold DY.Libsignal.TripleRatchet.traceLength
  rw [Traceful.run_mk]

theorem PQRkUAt.genRand {tr : ExecTrace} (n : Nat) :
    PQRkUAt tr (fun tr1 r => r = randTerm tr.length n ∧ tr.length < tr1.length ∧ NoNewStore tr tr1)
      (Random.genRand n) := by
  intro hJ
  have hg1 : ((Random.genRand n).run tr).1 = some (randTerm tr.length n) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_fst, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]; rfl
  have hg2 : ((Random.genRand n).run tr).2.val = tr.append (RndE n) := by
    rw [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  rw [hg2, hg1]
  have hlt : tr.length < (tr.append (RndE n)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  refine ⟨rkPairUniqInv_append_other rfl hJ, fun b hb => ?_⟩
  cases hb
  exact ⟨rfl, hlt, noNewStore_append_other rfl⟩

theorem PQRkUAt.sendMessage {tr : ExecTrace} (m : DY.Bytes) :
    PQRkUAt tr (fun tr1 _ => NoNewStore tr tr1) (Network.sendMessage m) := by
  intro hJ
  rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨rkPairUniqInv_append_other rfl hJ, fun _ _ => noNewStore_append_other rfl⟩

theorem PQRkUAt.logEvent {tr : ExecTrace} (ev : TREvent) :
    PQRkUAt tr (fun tr1 _ => NoNewStore tr tr1) (ProtocolEvent.logEvent ev) := by
  intro hJ
  have hg : ((ProtocolEvent.logEvent ev).run tr).2.val = tr.append (TREvE ev) := by
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  rw [hg]
  exact ⟨rkPairUniqInv_append_other rfl hJ, fun _ _ => noNewStore_append_other rfl⟩

theorem PQRkUAt.getLocalState {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkUAt tr (fun tr1 st => tr1 = tr ∧ TRStateStoredAt me st stH tr)
      (PersistentLocalState.getLocalState me stH) := by
  intro hJ
  rw [CompTrace.getLocalState_tr_snd]
  refine ⟨hJ, fun st hst => ?_⟩
  rw [CompTrace.getLocalState_tr_fst] at hst
  rcases he : (tr.at? stH : Option CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at hst; cases hst
  · rw [he] at hst; dsimp only at hst
    by_cases hp : p = me
    · subst hp; simp only [↓reduceIte] at hst; cases hst; exact ⟨rfl, he⟩
    · simp only [hp, ↓reduceIte] at hst; cases hst

theorem PQRkUAt.getEntryTR {tr : ExecTrace} (evH : Nat) :
    PQRkUAt tr (fun tr1 _ => tr1 = tr) (DY.getEntry evH : Traceful CompTrace.TREntry) := by
  apply PQRkUAt.of_id
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]

theorem PQRkUAt.receiveMessage {tr : ExecTrace} (msgH : Nat) :
    PQRkUAt tr (fun tr1 b => tr1 = tr ∧ b.AttackerKnows tr) (Network.receiveMessage msgH) := by
  intro hJ
  rw [CompTrace.receiveMessage_snd]
  refine ⟨hJ, fun a ha => ?_⟩
  rw [CompTrace.receiveMessage_fst] at ha
  rcases hat : (tr.at? msgH : Option CompTrace.NetEntry) with _ | ⟨⟨b⟩⟩ <;> rw [hat] at ha
  · cases ha
  · injection ha with ha
    subst ha
    exact ⟨rfl, Trace.MessageSentAt_implies_AttackerKnows tr b msgH
      ((Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1 tr b msgH).mpr hat)⟩

theorem PQRkUAt.receiveSignalMsg {tr : ExecTrace} (msgH : Nat) :
    PQRkUAt tr (fun tr1 msg => tr1 = tr ∧ ∃ raw : DY.Bytes, raw.AttackerKnows tr ∧ parseTrSignalMsg raw = some msg)
      (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine PQRkUAt.bind (PQRkUAt.receiveMessage msgH) fun tr1 t _ ⟨ht, hraw_ak⟩ => ?_
  subst tr1
  rcases hp : parseTrSignalMsg t with _ | msg
  · exact PQRkUAt.failure
  · exact PQRkUAt.bind (PQRkUAt.guardP _) fun _ _ _ ⟨ht1, _⟩ => PQRkUAt.pure msg ⟨ht1, t, hraw_ak, hp⟩

theorem PQRkUAt.verifyMacAndDecrypt {tr : ExecTrace} (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) :
    PQRkUAt tr (fun tr1 _ => tr1 = tr)
      (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) :=
  PQRkUAt.of_id (CompTrace.verifyMacAndDecrypt_trace st msg pqSalt seed tr)

theorem PQRkUAt.sendMessage_true {tr : ExecTrace} (m : DY.Bytes) :
    PQRkUAt tr (fun _ _ => True) (Network.sendMessage m) := by
  intro hJ
  rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨rkPairUniqInv_append_other rfl hJ, fun _ _ => trivial⟩

theorem PQRkUAt.logSkippedKeys {tr : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (k : Nat) (ck : DY.Bytes) (n : UInt32) :
    PQRkUAt tr (fun tr1 _ => NoNewStore tr tr1)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing tr ck n with
  | zero =>
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact PQRkUAt.pure () (noNewStore_refl tr)
  | succ k ih =>
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    refine PQRkUAt.bind (PQRkUAt.logEvent _) fun tr1 _ _ h1 hJ1 => ?_
    have ⟨hJ2, h2⟩ := ih (kdfCk ck).1 (n + 1) hJ1
    exact ⟨hJ2, fun a ha => noNewStore_trans h1 (h2 a ha)⟩

theorem PQRkUAt.logMessageKeyAndStore_copy {tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat)
    {st st₀ : TRState} {idx₀ : Nat}
    (hst₀ : TRStateStoredAt me st₀ idx₀ tr) (hdhs : st.dhs = st₀.dhs) (hrk : st.rk = st₀.rk) :
    PQRkUAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine PQRkUAt.bind (PQRkUAt.logEvent _) fun tr2 _ hle2 _ => ?_
  intro hJ2
  have hstore : ((PersistentLocalState.storeLocalState me st).run tr2).2.val = tr2.append (TRStE me st) := by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  rw [hstore]
  exact ⟨rkPairUniqInv_append_st_copy me (trStateStoredAt_mono hle2 hst₀) hdhs hrk hJ2,
    fun _ _ => trivial⟩

theorem PQRkUAt.logMessageKeyAndStore_fresh {tr₀ tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat)
    {st : TRState} {t_new : Nat}
    (hJ₀ : RkPairUniqInv tr₀) (hnns : NoNewStore tr₀ tr)
    (ht_ge : tr₀.length ≤ t_new) (ht_lt : t_new < tr.length)
    (hdhs : st.dhs = randTerm t_new 32)
    (hrk : ∃ rk_p pk_p, PeerLtAt t_new pk_p ∧ st.rk = (createChain rk_p pk_p (randTerm t_new 32)).1) :
    PQRkUAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  refine PQRkUAt.bind (PQRkUAt.logEvent _) fun tr2 _ hle2 hnns2 => ?_
  intro hJ2
  have hstore : ((PersistentLocalState.storeLocalState me st).run tr2).2.val = tr2.append (TRStE me st) := by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  rw [hstore]
  have hnns_all : NoNewStore tr₀ tr2 := noNewStore_trans hnns hnns2
  have ht_lt2 : t_new < tr2.length := Nat.lt_of_lt_of_le ht_lt (Trace.length_le _ _ hle2)
  exact ⟨rkPairUniqInv_append_st_fresh me ht_lt2
    (fun p' st' idx' hs => dhs_ne_randTerm_of_ge hJ₀ ht_ge p' st' idx' (hnns_all p' st' idx' hs))
    hdhs hrk hJ2, fun _ _ => trivial⟩

def EnsureChainU (tr tr1 : ExecTrace) (st0 st : TRState) : Prop :=
  NoNewStore tr tr1 ∧
    ((st.dhs = st0.dhs ∧ st.rk = st0.rk) ∨
      ∃ t_new, tr.length ≤ t_new ∧ t_new < tr1.length ∧
        st.dhs = randTerm t_new 32 ∧
        ∃ rk_p pk_p, PeerLtAt t_new pk_p ∧ st.rk = (createChain rk_p pk_p (randTerm t_new 32)).1)

theorem PQRkUAt.dhRatchetStep {tr : ExecTrace} (st0 : TRState) (pk : DY.Bytes)
    (hpk : PeerLtAt tr.length pk) :
    PQRkUAt tr (fun tr1 (r : TRState × RecvChain) => EnsureChainU tr tr1 st0 r.1)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PQRkUAt.bind (PQRkUAt.guardP _) fun tr1 _ _ ⟨ht1, _⟩ => ?_
  subst tr1
  rcases hc1 : createChain st0.rk pk st0.dhs with ⟨rk1, ckr⟩
  dsimp only
  refine PQRkUAt.bind (PQRkUAt.genRand 32) fun tr2 dhs _ ⟨hdhs_eq, ht2_lt, hnns2⟩ => ?_
  rcases hc2 : createChain rk1 pk dhs with ⟨rk2, cks⟩
  dsimp only
  have hrk2_eq : rk2 = (createChain rk1 pk (randTerm tr.length 32)).1 := by rw [← hdhs_eq, hc2]
  exact PQRkUAt.pure _ ⟨hnns2, .inr ⟨tr.length, Nat.le_refl _, ht2_lt, hdhs_eq, rk1, pk, hpk, hrk2_eq⟩⟩

theorem PQRkUAt.ensureReceiverChain {tr : ExecTrace} (st0 : TRState) (pk : DY.Bytes)
    (hpk : PeerLtAt tr.length pk) :
    PQRkUAt tr (fun tr1 (r : TRState × RecvChain × Bool) => EnsureChainU tr tr1 st0 r.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact PQRkUAt.pure _ ⟨noNewStore_refl tr, .inl ⟨rfl, rfl⟩⟩
  · exact PQRkUAt.bind (PQRkUAt.dhRatchetStep st0 pk hpk) fun _ ⟨st', c⟩ _ hr => PQRkUAt.pure _ hr
  · exact PQRkUAt.failure

theorem PQRkUAt.messageEncryptAbort {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkUAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact PQRkUAt.bind (PQRkUAt.getLocalState me stH) fun _ _ _ _ =>
    PQRkUAt.bind (PQRkUAt.genRand 32) fun _ _ _ _ => PQRkUAt.failure

theorem PQRkUAt.messageEncrypt {tr : ExecTrace} (me : Participant) (stH coinsLen pqIdx : Nat) :
    PQRkUAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine PQRkUAt.bind (PQRkUAt.getLocalState me stH) fun tr1 st _ ⟨ht1, hstored⟩ => ?_
  subst tr1
  refine PQRkUAt.bind (PQRkUAt.guardP _) fun tr2 _ hle2 _ =>
    PQRkUAt.bind (PQRkUAt.genRand 32) fun tr3 _ hle3 _ =>
    PQRkUAt.bind (PQRkUAt.genRand coinsLen) fun tr4 coins hle4 _ => ?_
  rcases Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩
  dsimp only
  refine PQRkUAt.bind (PQRkUAt.sendMessage key) fun tr5 _ hle5 _ => ?_
  rcases kdfCk st.cks with ⟨ck', seed⟩
  dsimp only
  refine PQRkUAt.bind (PQRkUAt.receiveMessage pqIdx) fun tr6 _ hle6 _ =>
    PQRkUAt.bind (PQRkUAt.logEvent _) fun tr7 _ hle7 _ => ?_
  have hle17 : tr ≤ tr7 :=
    Trace.le_trans _ _ _ hle2 (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4
      (Trace.le_trans _ _ _ hle5 (Trace.le_trans _ _ _ hle6 hle7))))
  refine PQRkUAt.bind
    (PQRkUAt.logMessageKeyAndStore_copy me _ _ _ _ _ _ _
      (trStateStoredAt_mono hle17 hstored) rfl rfl)
    fun _ _ _ _ => PQRkUAt.sendMessage_true _

theorem PQRkUAt.exposeKey {tr : ExecTrace} (me : Participant) (stH : Nat) (k : KeyComponent) :
    PQRkUAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine PQRkUAt.bind (PQRkUAt.getLocalState me stH) fun _ st _ _ => ?_
  cases k with
  | rk => exact PQRkUAt.bind (PQRkUAt.logEvent _) fun _ _ _ _ => PQRkUAt.sendMessage_true _
  | dhs => exact PQRkUAt.bind (PQRkUAt.logEvent _) fun _ _ _ _ => PQRkUAt.sendMessage_true _
  | cks => exact PQRkUAt.bind (PQRkUAt.logEvent _) fun _ _ _ _ => PQRkUAt.sendMessage_true _
  | ckr pk =>
    dsimp only
    rcases findRecvChain st.recv pk with _ | c
    · exact PQRkUAt.failure
    · exact PQRkUAt.bind (PQRkUAt.logEvent _) fun _ _ _ _ => PQRkUAt.sendMessage_true _

theorem PQRkUAt.exposeSpqr {tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkUAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact PQRkUAt.bind (PQRkUAt.getLocalState me stH) fun _ _ _ _ =>
    PQRkUAt.bind (PQRkUAt.logEvent _) fun _ _ _ _ =>
    PQRkUAt.sendMessage_true _

theorem PQRkUAt.exposeSkipped {tr : ExecTrace} (evH : Nat) :
    PQRkUAt tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine PQRkUAt.bind (PQRkUAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    exact PQRkUAt.bind (PQRkUAt.guardTrace _) fun _ _ _ _ =>
      PQRkUAt.bind (PQRkUAt.logEvent _) fun _ _ _ _ =>
      PQRkUAt.sendMessage_true _
  | _ => exact PQRkUAt.failure

theorem PQRkUAt.messageDecryptSkipped {tr : ExecTrace} (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkUAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine PQRkUAt.bind (PQRkUAt.getLocalState me stH) fun tr1 st _ ⟨ht1, hstored⟩ => ?_
  subst tr1
  refine PQRkUAt.bind (PQRkUAt.receiveSignalMsg msgH) fun tr2 msg hle2 _ =>
    PQRkUAt.bind (PQRkUAt.getEntryTR evH) fun tr3 ⟨ev⟩ hle3 _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine PQRkUAt.bind (PQRkUAt.guardP _) fun tr4 _ hle4 _ =>
      PQRkUAt.bind (PQRkUAt.guardTrace _) fun tr5 _ hle5 _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQRkUAt.failure
    · refine PQRkUAt.bind (PQRkUAt.sendMessage key) fun tr6 _ hle6 _ =>
        PQRkUAt.bind (PQRkUAt.receiveMessage pqIdx) fun tr7 pqSalt hle7 _ =>
        PQRkUAt.bind (PQRkUAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr8 _ hle8 _ =>
        PQRkUAt.bind (PQRkUAt.logEvent _) fun tr9 _ hle9 _ =>
        PQRkUAt.bind (PQRkUAt.logEvent _) fun tr10 _ hle10 _ => ?_
      have hle1_10 : tr ≤ tr10 :=
        Trace.le_trans _ _ _ hle2 (Trace.le_trans _ _ _ hle3 (Trace.le_trans _ _ _ hle4
          (Trace.le_trans _ _ _ hle5 (Trace.le_trans _ _ _ hle6 (Trace.le_trans _ _ _ hle7
            (Trace.le_trans _ _ _ hle8 (Trace.le_trans _ _ _ hle9 hle10)))))))
      exact PQRkUAt.logMessageKeyAndStore_copy me _ _ _ _ _ _ _
        (trStateStoredAt_mono hle1_10 hstored) rfl rfl
  | _ => exact PQRkUAt.failure

theorem PQRkUAt.messageDecrypt {tr : ExecTrace} (hinv : SpqrInv tr) (me : Participant)
    (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkUAt tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  intro hJ_init
  refine (?_ : PQRkUAt tr (fun _ _ => True)
    (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx)) hJ_init
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine PQRkUAt.bind (PQRkUAt.getLocalState me stH) fun tr1 st0 _ ⟨ht1, hstored0⟩ => ?_
  subst tr1
  refine PQRkUAt.bind (PQRkUAt.receiveSignalMsg msgH) fun tr2 msg _ ⟨ht2, raw, hraw_ak, hparse⟩ => ?_
  subst tr2
  have hpk_lt : PeerLtAt tr.length msg.ratchetKey :=
    peerLtAt_of_pub hinv (pub_ratchetKey_of_parseTrSignalMsg hinv
      (CompInv.CompPubInv.Pub.of_attackerKnows hinv hraw_ak) hparse)
  refine PQRkUAt.bind (PQRkUAt.ensureReceiverChain st0 msg.ratchetKey hpk_lt)
    fun tr3 ⟨st, c, ratcheted⟩ hle3 ⟨hnns3, hcases⟩ => ?_
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact PQRkUAt.failure
  · dsimp only
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQRkUAt.failure
    · refine PQRkUAt.bind (PQRkUAt.sendMessage key) fun tr4 _ hle4 hnns4 =>
        PQRkUAt.bind (PQRkUAt.receiveMessage pqIdx) fun tr5 pqSalt _ ⟨ht5, _⟩ => ?_
      subst tr5
      refine PQRkUAt.bind (PQRkUAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr6 m _ ht6 => ?_
      subst tr6
      have hnns36 : NoNewStore tr tr4 := noNewStore_trans hnns3 hnns4
      have htail : ∀ {tr_t : ExecTrace}, tr4 ≤ tr_t → NoNewStore tr tr_t →
          PQRkUAt tr_t (fun _ _ => True) (do
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index (msg.counter.toNat - c.index.toNat)
            ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) KeyDir.receiver seed pqSalt msg.counter c.rIdx stH
              { st with recv := setRecvChain st.recv c', spqr := spqr' }) :=
        fun {tr_t} hle_t hnns_t =>
          PQRkUAt.bind (PQRkUAt.logSkippedKeys _ _ _ _ _ _ _) fun tr_a _ hle_a hnns_a =>
            PQRkUAt.bind (PQRkUAt.logEvent _) fun tr_b _ hle_b hnns_b => by
              have hle3_b : tr3 ≤ tr_b :=
                Trace.le_trans _ _ _ hle4 (Trace.le_trans _ _ _ hle_t (Trace.le_trans _ _ _ hle_a hle_b))
              have hnns_b_all : NoNewStore tr tr_b :=
                noNewStore_trans hnns_t (noNewStore_trans hnns_a hnns_b)
              rcases hcases with ⟨hdhs_eq, hrk_eq⟩ | ⟨t_new, ht_ge, ht_lt, hdhs_eq, hrk_ex⟩
              · exact PQRkUAt.logMessageKeyAndStore_copy me _ _ _ _ _ _ _
                  (trStateStoredAt_mono (Trace.le_trans _ _ _ hle3 hle3_b) hstored0) hdhs_eq hrk_eq
              · exact PQRkUAt.logMessageKeyAndStore_fresh me _ _ _ _ _ _ _
                  hJ_init hnns_b_all ht_ge (Nat.lt_of_lt_of_le ht_lt (Trace.length_le _ _ hle3_b))
                  hdhs_eq hrk_ex
      split
      · refine PQRkUAt.bind (PQRkUAt.logEvent _) fun tr7 _ hle7 hnns7 =>
          PQRkUAt.bind (PQRkUAt.logEvent _) fun tr8 _ hle8 hnns8 =>
            htail (Trace.le_trans _ _ _ hle7 hle8)
              (noNewStore_trans hnns36 (noNewStore_trans hnns7 hnns8))
      · exact htail (Trace.le_refl _) hnns36

theorem rkPairUniqInv_preserves_aliceStart {tr : ExecTrace} (hinv : SpqrInv tr)
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) (hJ : RkPairUniqInv tr) :
    RkPairUniqInv ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hJ
    (rkPairUniqInv_append_other rfl hJ)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ hspk _ _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (f : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= f).run t).2.val = ((f t.length).run t).2.val := by
    intro α f t; unfold DY.Libsignal.TripleRatchet.traceLength
    rw [CompTrace.run_bind_snd, Traceful.run_mk]
  have hstore : ∀ (me : Participant) (st : TRState) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState me st).run t).2.val = t.append (TRStE me st) := by
    intro me st t
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  let hs := CompTrace.aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := randTerm tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32)
  let tr4 := tr3.append (NetE hs.ek)
  let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  rw [CompTrace.run_genRand_bind_snd]
  dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
    htl, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd, hstore]
  change RkPairUniqInv (tr8.append (TRStE a stA))
  have hJ8 : RkPairUniqInv tr8 :=
    rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
      (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
        (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl hJ)))))))
  have hnns8 : NoNewStore tr tr8 :=
    noNewStore_trans (noNewStore_append_other rfl) (noNewStore_trans (noNewStore_append_other rfl)
      (noNewStore_trans (noNewStore_append_other rfl) (noNewStore_trans (noNewStore_append_other rfl)
        (noNewStore_trans (noNewStore_append_other rfl) (noNewStore_trans (noNewStore_append_other rfl)
          (noNewStore_trans (noNewStore_append_other rfl) (noNewStore_append_other rfl)))))))
  have hge : tr.length ≤ tr2.length := by simp [tr2, tr1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hlt : tr2.length < tr8.length := by simp [tr8, tr7, tr6, tr5, tr4, tr3, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hspk_lt : PeerLtAt tr2.length hs.spk :=
    peerLtAt_mono hge (peerLtAt_of_attackerKnows hinv (CompTrace.NetMsgAt.attackerKnows hspk))
  exact rkPairUniqInv_append_st_fresh a hlt
    (fun p' st' idx' hs => dhs_ne_randTerm_of_ge hJ hge p' st' idx' (hnns8 p' st' idx' hs))
    rfl ⟨hs.keys.rk, hs.spk, hspk_lt, rfl⟩ hJ8

theorem rkPairUniqInv_logSkippedKeys_preserves (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32) (tr : ExecTrace),
      RkPairUniqInv tr →
        RkPairUniqInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val ∧
          NoNewStore tr ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k).run tr).2.val
  | 0, ck, n, tr, hJ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Traceful.run_pure]
    exact ⟨hJ, noNewStore_refl tr⟩
  | k + 1, ck, n, tr, hJ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    let e : CompTrace.TREntry := TREvE (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)
    have ⟨hJ', hnns'⟩ :=
      rkPairUniqInv_logSkippedKeys_preserves s pk rIdx src k (kdfCk ck).1 (n + 1) (tr.append e)
        (rkPairUniqInv_append_other (e := e) rfl hJ)
    exact ⟨hJ', noNewStore_trans (noNewStore_append_other (e := e) rfl) hnns'⟩

theorem rkPairUniqInv_bobStart_commit {tr₀ tr : ExecTrace}
    (hJ₀ : RkPairUniqInv tr₀) (hJ : RkPairUniqInv tr) (hnns : NoNewStore tr₀ tr)
    (ht_lt : tr₀.length < tr.length)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes)
    (keys : HandshakeKeys) (msg : TRSignalMsg) (spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hpk_lt : PeerLtAt tr₀.length msg.ratchetKey) :
    let dhs := randTerm tr₀.length 32
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    RkPairUniqInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro dhs st c
  have htl : ∀ {α : Type} (f : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= f).run t).2.val = ((f t.length).run t).2.val := by
    intro α f t; unfold DY.Libsignal.TripleRatchet.traceLength
    rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let doneIdx := tr.length
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hJ₄ : RkPairUniqInv tr₄ :=
    rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
      (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl hJ)))
  have hnns₄ : NoNewStore tr₀ tr₄ :=
    noNewStore_trans hnns (noNewStore_trans (noNewStore_append_other rfl)
      (noNewStore_trans (noNewStore_append_other rfl)
        (noNewStore_trans (noNewStore_append_other rfl) (noNewStore_append_other rfl))))
  have hle₀₄ : tr ≤ tr₄ :=
    Trace.le_trans _ _ _ (Trace.append_le tr _) (Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }
  simp only [↓reduceIte]
  rw [htl, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
    CompPresTRExp.run_logEvent_bind_snd, htl]
  change RkPairUniqInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have ⟨hJ₅, hnns₄₅⟩ := rkPairUniqInv_logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c.chainKey c.index tr₄ hJ₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  let tr₇ := tr₆.append (TREvE (.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx))
  have hJ₇ : RkPairUniqInv tr₇ :=
    rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl hJ₅)
  have hnns₇ : NoNewStore tr₀ tr₇ :=
    noNewStore_trans hnns₄ (noNewStore_trans hnns₄₅
      (noNewStore_trans (noNewStore_append_other rfl) (noNewStore_append_other rfl)))
  have hle₀₇ : tr ≤ tr₇ :=
    Trace.le_trans _ _ _ hle₀₄ (Trace.le_trans _ _ _ hle₄₅
      (Trace.le_trans _ _ _ (Trace.append_le tr₅ _) (Trace.append_le tr₆ _)))
  have ht_lt₇ : tr₀.length < tr₇.length := Nat.lt_of_lt_of_le ht_lt (Trace.length_le _ _ hle₀₇)
  dsimp only [restAct]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logMessageKeyAndStore_snd]
  exact rkPairUniqInv_append_st_fresh b ht_lt₇
    (fun p' st' idx' hs => dhs_ne_randTerm_of_ge hJ₀ (Nat.le_refl _) p' st' idx' (hnns₇ p' st' idx' hs))
    rfl ⟨_, msg.ratchetKey, hpk_lt, rfl⟩ hJ₇

theorem rkPairUniqInv_preserves_bobStart {tr : ExecTrace} (hinv : SpqrInv tr)
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles)
    (pqIdx : Nat) (spqrMsgIdx : UInt32) (hJ : RkPairUniqInv tr) :
    RkPairUniqInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hJ
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ _ _ _ _ => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at mh.msg tr hJ fun raw _ hraw_ak => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · dsimp only
    change RkPairUniqInv (((failure : Traceful TRSignalMsg) >>= _).run tr).2.val
    rw [CompTrace.run_bind_snd, Traceful.run_failure]
    exact hJ
  · dsimp only
    rw [CompTrace.run_bind_assoc_snd]
    refine CompTrace.bind_guardP_at _ tr hJ fun _ => ?_
    refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hJ fun _ => ?_
    let dhs := CompKeyInversion.rnd tr.length 32
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    let tr₁ := tr.append (RndE 32)
    have hJ₁ : RkPairUniqInv tr₁ := rkPairUniqInv_append_other rfl hJ
    rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only
      change RkPairUniqInv ((failure : Traceful Nat).run tr₁).2.val
      rw [Traceful.run_failure]
      exact hJ₁
    · dsimp only
      rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only
        change RkPairUniqInv ((failure : Traceful Nat).run tr₁).2.val
        rw [Traceful.run_failure]
        exact hJ₁
      · dsimp only
        let tr₂ := tr₁.append (NetE key)
        have hJ₂ : RkPairUniqInv tr₂ := rkPairUniqInv_append_other rfl hJ₁
        have hnns₂ : NoNewStore tr tr₂ :=
          noNewStore_trans (noNewStore_append_other rfl) (noNewStore_append_other rfl)
        have hlen₂ : tr.length < tr₂.length := by simp [tr₂, tr₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        have hpk_lt : PeerLtAt tr.length msg.ratchetKey :=
          peerLtAt_of_pub hinv (pub_ratchetKey_of_parseTrSignalMsg hinv
            (CompInv.CompPubInv.Pub.of_attackerKnows hinv hraw_ak) hparse)
        rw [CompPresTRExp.run_sendMessage_bind_snd]
        refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hJ₂ fun pqSalt _ _ =>
          CompInv.CompPresBob.bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hJ₂ fun m _ => ?_
        cases o with
        | none =>
          dsimp only [Option.map]
          exact rkPairUniqInv_bobStart_commit hJ hJ₂ hnns₂ hlen₂ b a sB sS sQ none ikA ek ct keys msg spqr' seed pqSalt m c' hpk_lt
        | some oSk =>
          dsimp only [Option.map]
          rw [CompTrace.run_bind_snd]
          unfold DY.Libsignal.PQXDH.guardTrace
          rw [Traceful.run_mk]
          dsimp only
          by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
          · rw [ite_eq_left_iff.mpr fun h => absurd hused h, CompPresTRExp.run_logEvent_bind_snd]
            exact rkPairUniqInv_bobStart_commit hJ (rkPairUniqInv_append_other rfl hJ₂)
              (noNewStore_trans hnns₂ (noNewStore_append_other rfl))
              (Nat.lt_of_lt_of_le hlen₂ (Trace.length_le _ _ (Trace.append_le _ _)))
              b a sB sS sQ (some oSk) ikA ek ct keys msg spqr' seed pqSalt m c' hpk_lt
          · rw [ite_eq_right_iff.mpr fun h => absurd h hused]
            exact hJ₂

theorem rkPairUniqInv_reachable {tr : ExecTrace} (hreach : ReachableTrace tr) :
    RkPairUniqInv tr := by
  have hLogEv : ∀ {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
      (ev : Ev) (t : ExecTrace),
      ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev) := by
    intro Ev _ ev t
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      CompTrace.run_bind_snd, Traceful.run_mk]
    dsimp only; rw [Traceful.run_pure]
  have hStorePQ_snd : ∀ (me : Participant) (st : PQXDHState) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState me st).run t).2.val = t.append (PQStE me st) := by
    intro me st t
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  have hStorePQ_bind : ∀ {α : Type} (me : Participant) (st : PQXDHState)
      (f : Nat → Traceful α) (t : ExecTrace),
      ((PersistentLocalState.storeLocalState me st >>= f).run t).2.val =
        ((f t.length).run (t.append (PQStE me st))).2.val := by
    intro α me st f t
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, Traceful.run_mk]
  induction hreach with
  | Base => exact rkPairUniqInv_nil
  | @Step tr_prev input _ hReachPre ih =>
    have hinv : SpqrInv tr_prev := spqrInv_of_reachable _ hReachPre
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · let msg : DY.Bytes := inp
      change RkPairUniqInv ((Network.sendMessage msg).run tr_prev).2.val
      rw [CompPresTRExp.run_sendMessage_snd]
      exact rkPairUniqInv_append_other rfl ih
    · let p : Participant := inp
      change RkPairUniqInv ((registerIdentity p).run _).2.val
      unfold registerIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, hStorePQ_snd]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
        (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih))))
    · rcases inp with ⟨p, skIdx⟩
      change RkPairUniqInv ((registerCorruptIdentity p skIdx).run _).2.val
      unfold registerCorruptIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at skIdx _ ih fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hLogEv]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)
    · rcases inp with ⟨b, idStateIdx⟩
      change RkPairUniqInv ((genSignedPrekey b idStateIdx).run _).2.val
      unfold genSignedPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ ih fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, hStorePQ_bind,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
        Traceful.run_pure]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
        (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
          (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)))))
    · rcases inp with ⟨b, idStateIdx⟩
      change RkPairUniqInv ((genPQPrekey b idStateIdx).run _).2.val
      unfold genPQPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ ih fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, hStorePQ_bind,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd,
        Traceful.run_pure]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
        (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
          (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)))))
    · let b : Participant := inp
      change RkPairUniqInv ((genOneTimePrekey b).run _).2.val
      unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd,
        CompPresTRExp.run_logEvent_bind_snd, hStorePQ_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl
        (rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
      exact rkPairUniqInv_preserves_aliceStart hinv a b idStateIdx regIdxB bh ih
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
      exact rkPairUniqInv_preserves_bobStart hinv b a kh regIdxA mh pqIdx spqrMsgIdx ih
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
      exact (PQRkUAt.messageEncrypt me stateIdx coinsLen pqIdx ih).1
    · rcases inp with ⟨me, stateIdx⟩
      exact (PQRkUAt.messageEncryptAbort me stateIdx ih).1
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
      exact (PQRkUAt.messageDecrypt hinv me stateIdx msgIdx pqIdx spqrMsgIdx ih).1
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
      exact (PQRkUAt.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx ih).1
    · rcases inp with ⟨me, stateIdx, k⟩
      exact (PQRkUAt.exposeKey me stateIdx k ih).1
    · rcases inp with ⟨me, stateIdx⟩
      exact (PQRkUAt.exposeSpqr me stateIdx ih).1
    · exact (PQRkUAt.exposeSkipped inp ih).1
    · rcases inp with ⟨p, stateIdx⟩
      change RkPairUniqInv ((compromiseIK p stateIdx).run _).2.val
      unfold compromiseIK
      refine CompPresPQXDH.bind_getKey_at p stateIdx .identity _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)
    · rcases inp with ⟨b, stateIdx⟩
      change RkPairUniqInv ((compromiseSPK b stateIdx).run _).2.val
      unfold compromiseSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .signedPrekey _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)
    · rcases inp with ⟨b, stateIdx⟩
      change RkPairUniqInv ((compromisePQSPK b stateIdx).run _).2.val
      unfold compromisePQSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .pqPrekey _ ih fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)
    · rcases inp with ⟨b, stateIdx⟩
      change RkPairUniqInv ((compromiseOPK b stateIdx).run _).2.val
      unfold compromiseOPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .oneTimePrekey _ ih fun _ _ => ?_
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact rkPairUniqInv_append_other rfl (rkPairUniqInv_append_other rfl ih)
    · change RkPairUniqInv ((ProtocolEvent.logEvent PQXDHEvent.BrokenDH).run tr_prev).2.val
      rw [hLogEv]
      exact rkPairUniqInv_append_other rfl ih
    · change RkPairUniqInv ((ProtocolEvent.logEvent PQXDHEvent.BrokenKEM).run tr_prev).2.val
      rw [hLogEv]
      exact rkPairUniqInv_append_other rfl ih
    · let pkIdx : Nat := inp
      change RkPairUniqInv ((invertDH pkIdx).run _).2.val
      unfold invertDH
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at pkIdx tr_prev ih fun pk _ _ => ?_
      rcases DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only
        change RkPairUniqInv ((failure : Traceful Nat).run tr_prev).2.val
        rw [Traceful.run_failure]
        exact ih
      · dsimp only
        rw [CompPresTRExp.run_sendMessage_snd]
        exact rkPairUniqInv_append_other rfl ih
    · let pkIdx : Nat := inp
      change RkPairUniqInv ((invertKEM pkIdx).run _).2.val
      unfold invertKEM
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ ih fun _ =>
        CompTrace.bind_receiveMessage_at pkIdx tr_prev ih fun pk _ _ => ?_
      rcases PQKem.invertKemPublicKey pk with _ | sk
      · dsimp [liftM, monadLift, MonadLift.monadLift]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
        exact ih
      · dsimp [liftM, monadLift, MonadLift.monadLift]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
        rw [CompPresTRExp.run_sendMessage_snd]
        exact rkPairUniqInv_append_other rfl ih
    · omega

/-- On any reachable trace `tr`, if `st₁` and `st₂` are stored states with `st₁.dhs = st₂.dhs`,
then `st₁.rk = st₂.rk` and `p₁ = p₂`. -/
theorem trStateStoredAt_rk_eq_of_dhs_eq {tr : ExecTrace} (hreach : ReachableTrace tr)
    {p₁ p₂ : Participant} {st₁ st₂ : TRState} {idx₁ idx₂ : Nat}
    (hst₁ : TRStateStoredAt p₁ st₁ idx₁ tr) (hst₂ : TRStateStoredAt p₂ st₂ idx₂ tr)
    (hdhs : st₁.dhs = st₂.dhs) :
    st₁.rk = st₂.rk ∧ p₁ = p₂ :=
  (rkPairUniqInv_reachable hreach).pair_uniq p₁ st₁ idx₁ p₂ st₂ idx₂ hst₁ hst₂ hdhs

theorem trStateStoredAt_rk_createChain {tr : ExecTrace} (hreach : ReachableTrace tr)
    {p : Participant} {st : TRState} {idx : Nat}
    (hst : TRStateStoredAt p st idx tr) :
    ∃ t < tr.length, st.dhs = randTerm t 32 ∧
      ∃ rk_p pk_p, PeerLtAt t pk_p ∧ st.rk = (createChain rk_p pk_p (randTerm t 32)).1 :=
  (rkPairUniqInv_reachable hreach).dhs_bound p st idx hst

/-! ## Stored-State Root-Key Corollaries -/

abbrev _root_.Symbolic.Swarm.COMPOSED.CompTrace.PQXDHStateStoredAt
    (b : Participant) (st : PQXDHState) (idx : Nat) (tr : ExecTrace) : Prop :=
  CompTrace.PQXDHStoredAt tr b st idx

theorem stored_rk_eq_of_dhs_eq {T : ExecTrace} (hT : ReachableTrace T)
    {p₁ p₂ : Participant} {st₁ st₂ : TRState} {i₁ i₂ : Nat}
    (h₁ : TRStateStoredAt p₁ st₁ i₁ T) (h₂ : TRStateStoredAt p₂ st₂ i₂ T)
    (hd : st₁.dhs = st₂.dhs) : st₁.rk = st₂.rk :=
  (trStateStoredAt_rk_eq_of_dhs_eq hT h₁ h₂ hd).1

/-- A stored ratchet secret `st.dhs` is never a signed-prekey secret. -/
theorem stored_dhs_ne_spkSk {T : ExecTrace} (hT : ReachableTrace T)
    {p b : Participant} {st : TRState} {i idx t : Nat}
    (h : TRStateStoredAt p st i T)
    (hspk : CompTrace.PQXDHStateStoredAt b { kind := .signedPrekey, sk := randTerm t 32 } idx T) :
    st.dhs ≠ randTerm t 32 := by
  intro hdhs
  have hinv : SpqrInv T := spqrInv_of_reachable T hT
  obtain ⟨_, _, _, _, _, hdhs_cls, _⟩ := hinv.trStOK p st i h
  have hspk_at : CompInv.SPKAt T b (randTerm t 32) :=
    hinv.stOK b { kind := .signedPrekey, sk := randTerm t 32 } idx hspk
  obtain ⟨t_s, heq_s, _, hr64, _⟩ := hspk_at
  obtain ⟨rfl, _⟩ := CompInv.rnd_inj heq_s
  rcases hdhs_cls with ⟨t_a, heq_a, _, _, _, a, b', ikA, ikB, spk, pqpk, opk, ek, ct, keys, hnet_ek, _⟩ |
      ⟨t_r, msg, heq_r, _, hnet_msg⟩
  · rw [hdhs] at heq_a
    obtain ⟨rfl, _⟩ := CompInv.rnd_inj heq_a
    exact CompInv.HsClassHelpers.randAt_not_netAt hr64 hnet_ek
  · rw [hdhs] at heq_r
    obtain ⟨rfl, _⟩ := CompInv.rnd_inj heq_r
    exact CompInv.HsClassHelpers.randAt_not_netAt hr64 hnet_msg

/-- The peer key of a stored state's root was received before its own `dhs` was drawn. -/
theorem stored_peer_lt {T : ExecTrace} (hT : ReachableTrace T)
    {p : Participant} {st : TRState} {i : Nat}
    (h : TRStateStoredAt p st i T) {rk1 k : DY.Bytes} {c s : Nat}
    (hdhs : st.dhs = randTerm s 32) (hrk : st.rk = (createChain rk1 k st.dhs).1)
    (hk : X25519.normalizeX25519Key k = DiffieHellman.dhPk (randTerm c 32)) : c < s := by
  obtain ⟨t, _, hdhs_t, rk_p, pk_p, hpeer_lt, hrk_t⟩ := trStateStoredAt_rk_createChain hT h
  have hst_eq : s = t := randTerm_timestamp_inj (hdhs.symm.trans hdhs_t)
  subst hst_eq
  rw [hdhs] at hrk
  have hchain_eq : (createChain rk_p pk_p (randTerm s 32)).1 = (createChain rk1 k (randTerm s 32)).1 :=
    hrk_t.symm.trans hrk
  have hagree : DY.Libsignal.PQXDH.agree pk_p (randTerm s 32) =
      DY.Libsignal.PQXDH.agree k (randTerm s 32) :=
    (CompTermAlgebra.createChain_fst_inj hchain_eq).2
  unfold DY.Libsignal.PQXDH.agree at hagree
  rw [hk] at hagree
  rcases CompTermAlgebra.dh_eq_dh_dhPk_cases hagree with ⟨hpk_eq, _⟩ | ⟨hpk_eq, hsk_eq⟩
  · exact hpeer_lt c hpk_eq
  · rw [hsk_eq] at hpk_eq
    exact hpeer_lt c hpk_eq

end Symbolic.Swarm.CREF.TR.G1
