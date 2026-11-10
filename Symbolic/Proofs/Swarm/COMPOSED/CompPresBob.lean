/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompCikOK
import all DY.ALaCarte.Basic
import all DY.ALaCarte.Ordering
import all DY.Bytes.Basic
import all DY.Bytes.AttackerKnowledge
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.EquationalTheory.Concat
import all DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.KdfExtract
import all DY.EquationalTheory.Literal
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import all Init.Data.String.Defs
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra

/-!
# `bobStart` Preservation and Composed MAC Origin

Proves `comp_mac_origin`, showing that Bob's MAC verification inside `bobStart` on an
attacker-known message yields `AliceMatch` or an authentication compromise excuse, and deduces
that `bobStart` preserves `SpqrInv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.PQKem DY.Signature DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion
open Symbolic.Swarm.COMPOSED.CompInv.CompPubInv

namespace CompPresBob

/-! ## Trace Entry Append and Disjointness Helpers -/

theorem proj_inj_eq {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by simp [Trace.append, Trace.length]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_here {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    ((tr.append e).at? tr.length : Option E) = some e :=
  Trace.at?_append tr e

theorem at?_append_cases {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    {tr : ExecTrace} {e : E1} {x : E2} {i : Nat}
    (h : ((tr.append e).at? i : Option E2) = some x) :
    (i < tr.length ∧ (tr.at? i : Option E2) = some x) ∨
    (i = tr.length ∧
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = some x) := by
  have hlt : i < (tr.append e).length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := E2) (tr.append e) i
    rw [h] at this; exact this
  have hlen : (tr.append e).length = tr.length + 1 := rfl
  rcases (show i < tr.length ∨ i = tr.length by omega) with hi | rfl
  · rw [at?_append_of_lt tr e hi] at h
    exact .inl ⟨hi, h⟩
  · simp only [Trace.at?, hlt, ↓reduceDIte] at h
    simp only [Trace.append, Trace.at, ↓reduceDIte] at h
    exact .inr ⟨rfl, h⟩

theorem eventLoggedAt_here {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev tr.length :=
  Trace.at?_append tr (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)

theorem eventLogged_here {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev)).EventLogged ev :=
  ⟨tr.length, eventLoggedAt_here tr ev⟩

theorem eventLoggedAt_append_same {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {ev₀ ev : Ev} {i : Nat}
    (h : (tr.append (⟨ev₀⟩ : ProtocolEvent.ExecEntryT Ev)).EventLoggedAt ev i) :
    (i < tr.length ∧ tr.EventLoggedAt ev i) ∨ (i = tr.length ∧ ev₀ = ev) := by
  rcases at?_append_cases h with ⟨hi, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hi, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp
    exact .inr ⟨rfl, hp⟩

theorem eventLoggedAt_append_other {E Ev : Type}
    [ExecTraceTypes.Has E] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT Ev)) = none)
    {ev : Ev} {i : Nat} (h : (tr.append e).EventLoggedAt ev i) :
    tr.EventLoggedAt ev i := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

theorem storedAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    {me : Participant} {st : PQXDHState} {idx : Nat}
    (h : StoredAt (tr.append e) me st idx) :
    StoredAt tr me st idx := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

theorem trStoredAt_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    {me : Participant} {st : TRState} {idx : Nat}
    (h : TRStoredAt (tr.append e) me st idx) :
    TRStoredAt tr me st idx := by
  rcases at?_append_cases h with ⟨_, h⟩ | ⟨_, hp⟩
  · exact h
  · rw [hnone] at hp; cases hp

theorem trStoredAt_append_same {tr : ExecTrace} {p₀ p : Participant}
    {st₀ st : TRState} {j : Nat}
    (h : TRStoredAt (tr.append (TRStE p₀ st₀)) p st j) :
    (j < tr.length ∧ TRStoredAt tr p st j) ∨ (j = tr.length ∧ p₀ = p ∧ st₀ = st) := by
  rcases at?_append_cases h with ⟨hj, h⟩ | ⟨rfl, hp⟩
  · exact .inl ⟨hj, h⟩
  · rw [proj_inj_eq] at hp; injection hp with hp; injection hp with hp; injection hp with hp1 hp2
    exact .inr ⟨rfl, hp1, hp2⟩

@[scoped simp] theorem baseAttackerKnows_append_net (tr : ExecTrace) (msg b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (NetE msg)) b ↔
      b = msg ∨ Trace.BaseAttackerKnows tr b := Iff.rfl

@[scoped simp] theorem baseAttackerKnows_append_ev (tr : ExecTrace) (ev : PQXDHEvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (EvE ev)) b ↔ Trace.BaseAttackerKnows tr b :=
  iff_of_eq (false_or _)

@[scoped simp] theorem baseAttackerKnows_append_cEv (tr : ExecTrace) (ev : ComposedEvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (CEvE ev)) b ↔ Trace.BaseAttackerKnows tr b :=
  iff_of_eq (false_or _)

theorem loggedBefore_of_eventLogged {tr : ExecTrace} {ev : PQXDHEvent}
    (h : tr.EventLogged ev) : LoggedBefore ev tr.length tr := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, hj, Trace.EventLoggedAt_implies_i_le_length ev j tr hj⟩

theorem AliceMatch.mono_idx {tr : ExecTrace} {ikA ikB pqpk ek ct : Bytes}
    {keys : HandshakeKeys} {i i' : Nat} (h : AliceMatch tr ikA ikB pqpk ek ct keys i)
    (hle : i ≤ i') : AliceMatch tr ikA ikB pqpk ek ct keys i' := by
  obtain ⟨j, a', b', spk', opk', hj, hev⟩ := h
  exact ⟨j, a', b', spk', opk', by omega, hev⟩

theorem loggedBefore_mono_idx {tr : ExecTrace} {ev : PQXDHEvent} {i i' : Nat}
    (h : LoggedBefore ev i tr) (hle : i ≤ i') : LoggedBefore ev i' tr := by
  obtain ⟨j, hj, hlt⟩ := h
  exact ⟨j, hj, by omega⟩

theorem BobDoneFacts.mono_idx {tr : ExecTrace} {b a : Participant}
    {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {ek ct : Bytes} {keys : HandshakeKeys}
    {i i' : Nat} (h : BobDoneFacts tr b a ikB ikA spk pqpk opk ek ct keys i) (hle : i ≤ i') :
    BobDoneFacts tr b a ikB ikA spk pqpk opk ek ct keys i' := by
  obtain ⟨sB, sS, sQ, o, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨r, vkA, hon, hr, hir⟩, hm⟩ := h
  refine ⟨sB, sS, sQ, o, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨r, vkA, hon, by omega, hir⟩, ?_⟩
  rcases hm with h | h | h | h
  · exact .inl (AliceMatch.mono_idx h hle)
  · exact .inr (.inl (loggedBefore_mono_idx h hle))
  · exact .inr (.inr (.inl (loggedBefore_mono_idx h hle)))
  · exact .inr (.inr (.inr (loggedBefore_mono_idx h hle)))

/-! ## Single-Entry Append Preservation -/

theorem spqrInv_append_rnd {tr : ExecTrace} (hinv : SpqrInv tr) (n : Nat) :
    SpqrInv (tr.append (RndE n)) :=
  CompPresTRExp.append_rnd n hinv

theorem spqrInv_append_net {tr : ExecTrace} (hinv : SpqrInv tr) {msg : Bytes}
    (hpub : Pub (tr.append (NetE msg)) msg) :
    SpqrInv (tr.append (NetE msg)) :=
  CompPresTRExp.append_net hinv hpub

theorem spqrInv_append_opkUsed {tr : ExecTrace} (hinv : SpqrInv tr) (b : Participant) (opk : Bytes) :
    SpqrInv (tr.append (EvE (.OPKUsed b opk))) := by
  have hle : tr ≤ tr.append (EvE (.OPKUsed b opk)) := Trace.append_le tr _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hinv.opkOrder.append_ev nofun nofun⟩
  · intro x hx
    exact Pub.mono hle (hinv.netPub x ((baseAttackerKnows_append_ev tr _ x).mp hx))
  · intro me st idx hst
    exact KindOK.mono hle (hinv.stOK me st idx (storedAt_append_other rfl hst))
  · intro me st idx hst
    exact TRStateOK.mono hle (hinv.trStOK me st idx (trStoredAt_append_other rfl hst))
  · intro s rPk ctr seed rIdx src idx hsk
    exact SkippedKeyOK.mono hle
      (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other rfl hsk))
  · intro p ik vkp r hr
    rcases eventLoggedAt_append_same hr with ⟨_, hr⟩ | ⟨_, hEq⟩
    · obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r hr
      exact ⟨s, hs.mono hle, h1, h2⟩
    · cases hEq
  · intro p ik vkp r hr
    rcases eventLoggedAt_append_same hr with ⟨_, hr⟩ | ⟨_, hEq⟩
    · exact evAt_mono hle (hinv.irCorrupt p ik vkp r hr)
    · cases hEq
  · intro a' b' ikA ikB spk pqpk opk' ek ct keys i hi
    rcases eventLoggedAt_append_same hi with ⟨_, hi⟩ | ⟨_, hEq⟩
    · exact (hinv.aliceDone a' b' ikA ikB spk pqpk opk' ek ct keys i hi).mono hle
    · cases hEq
  · intro b' a' ikB ikA spk pqpk opk' ek ct keys i hi
    rcases eventLoggedAt_append_same hi with ⟨_, hi⟩ | ⟨_, hEq⟩
    · exact (hinv.bobDone b' a' ikB ikA spk pqpk opk' ek ct keys i hi).mono hle
    · cases hEq

theorem spqrInv_append_bobDone {tr : ExecTrace} (hinv : SpqrInv tr)
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes} {ek ct : Bytes}
    {keys : HandshakeKeys}
    (hFacts : BobDoneFacts tr b a ikB ikA spk pqpk opk ek ct keys tr.length)
    (hopkUsed : ∀ o, opk = some o → LoggedBefore (PQXDHEvent.OPKUsed b o) tr.length tr) :
    SpqrInv (tr.append (EvE (.BobDone b a ikB ikA spk pqpk opk ek ct keys))) := by
  have hle : tr ≤ tr.append (EvE (.BobDone b a ikB ikA spk pqpk opk ek ct keys)) :=
    Trace.append_le tr _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hinv.opkOrder.append_ev
      (fun _ _ _ _ _ _ o' _ _ _ hEq => by cases hEq; exact hopkUsed o' rfl)
      nofun⟩
  · intro x hx
    exact Pub.mono hle (hinv.netPub x ((baseAttackerKnows_append_ev tr _ x).mp hx))
  · intro me st idx hst
    exact KindOK.mono hle (hinv.stOK me st idx (storedAt_append_other rfl hst))
  · intro me st idx hst
    exact TRStateOK.mono hle (hinv.trStOK me st idx (trStoredAt_append_other rfl hst))
  · intro s rPk ctr seed rIdx src idx hsk
    exact SkippedKeyOK.mono hle
      (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other rfl hsk))
  · intro p ik vkp r hr
    rcases eventLoggedAt_append_same hr with ⟨_, hr⟩ | ⟨_, hEq⟩
    · obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r hr
      exact ⟨s, hs.mono hle, h1, h2⟩
    · cases hEq
  · intro p ik vkp r hr
    rcases eventLoggedAt_append_same hr with ⟨_, hr⟩ | ⟨_, hEq⟩
    · exact evAt_mono hle (hinv.irCorrupt p ik vkp r hr)
    · cases hEq
  · intro a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hi
    rcases eventLoggedAt_append_same hi with ⟨_, hi⟩ | ⟨_, hEq⟩
    · exact (hinv.aliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hi).mono hle
    · cases hEq
  · intro b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hi
    rcases eventLoggedAt_append_same hi with ⟨_, hi⟩ | ⟨hi_eq, hEq⟩
    · exact (hinv.bobDone b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hi).mono hle
    · cases hi_eq
      cases hEq
      exact hFacts.mono hle

theorem spqrInv_append_trEv_nonSkip {tr : ExecTrace} (hinv : SpqrInv tr) {ev : TREvent}
    (hns : ∀ s pk n seed rIdx src, ev ≠ .SkippedKeyStored s pk n seed rIdx src) :
    SpqrInv (tr.append (TREvE ev)) :=
  CompPresTRExp.append_trEv_nonSkip hinv hns

theorem spqrInv_append_trEv_skip {tr : ExecTrace} (hinv : SpqrInv tr)
    {s : SessionInfo} {pk : Bytes} {n : UInt32} {seed : Bytes} {rIdx src : Nat}
    (hskip : SkippedKeyOK tr seed) :
    SpqrInv (tr.append (TREvE (.SkippedKeyStored s pk n seed rIdx src))) :=
  CompPresTRExp.append_trEv hinv fun _ _ _ _ _ _ hEq => by cases hEq; exact hskip

theorem spqrInv_append_cEv {tr : ExecTrace} (hinv : SpqrInv tr) (ev : ComposedEvent) :
    SpqrInv (tr.append (CEvE ev)) := by
  have hle : tr ≤ tr.append (CEvE ev) := Trace.append_le tr _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.opkOrder.append_other rfl⟩
  · intro x hx
    exact Pub.mono hle (hinv.netPub x ((baseAttackerKnows_append_cEv tr ev x).mp hx))
  · intro me st idx hst
    exact KindOK.mono hle (hinv.stOK me st idx (storedAt_append_other rfl hst))
  · intro me st idx hst
    exact TRStateOK.mono hle (hinv.trStOK me st idx (trStoredAt_append_other rfl hst))
  · intro s rPk ctr seed rIdx src idx hsk
    exact SkippedKeyOK.mono hle
      (hinv.skipOK s rPk ctr seed rIdx src idx (eventLoggedAt_append_other rfl hsk))
  · intro p ik vkp r hr
    obtain ⟨s, hs, h1, h2⟩ := hinv.irHonest p ik vkp r (eventLoggedAt_append_other rfl hr)
    exact ⟨s, hs.mono hle, h1, h2⟩
  · intro p ik vkp r hr
    exact evAt_mono hle (hinv.irCorrupt p ik vkp r (eventLoggedAt_append_other rfl hr))
  · intro a' b' ikA ikB spk pqpk opk ek ct keys i hi
    exact (hinv.aliceDone a' b' ikA ikB spk pqpk opk ek ct keys i
      (eventLoggedAt_append_other rfl hi)).mono hle
  · intro b' a' ikB ikA spk pqpk opk ek ct keys i hi
    exact (hinv.bobDone b' a' ikB ikA spk pqpk opk ek ct keys i
      (eventLoggedAt_append_other rfl hi)).mono hle

theorem spqrInv_append_trSt {tr : ExecTrace} (hinv : SpqrInv tr)
    {me : Participant} {st : TRState} (hst : TRStateOK tr me st) :
    SpqrInv (tr.append (TRStE me st)) :=
  CompPresTRExp.append_trSt hinv hst

/-! ## `Pub` Inversion Along the Confirmation Key Schedule -/

theorem chainKeyAt_succ_right (ck : Bytes) (n : Nat) :
    chainKeyAt ck (n + 1) = (kdfCk (chainKeyAt ck n)).1 := by
  induction n generalizing ck with
  | zero => rfl
  | succ m ih => exact ih (kdfCk ck).1

open Symbolic.Swarm.COMPOSED.CompTermAlgebra (concat_inj hmac_inj hkdfBlock2_inj
  hkdfBlock1_ne_hkdfBlock2 hkdfBlock2_ne_hkdfBlock3 pqxdhKdf_rk_inj pqxdhLabel_ne_whisperMessageKeys
  lit_whisperRatchet_ne_whisperMessageKeys createChain_snd_inj pqxdhKdf_rk_ne_createChain_fst
  pqxdhKdf_ck_ne_createChain_snd kdfCk_snd_inj kdfCk_fst_ne_snd hkdfBlock1_ne_kdfCk_fst
  hkdfBlock1_ne_kdfCk_snd hkdfBlock2_ne_kdfCk_fst hkdfBlock2_ne_kdfCk_snd hkdfBlock3_ne_kdfCk_fst
  hkdfBlock3_ne_kdfCk_snd chainKeyAt_createChain_snd_inj
  chainKeyAt_createChain_snd_ne_chainKeyAt_pqxdhKdf_ck trMsgKeys_macKey_inj kemPk_inj
  kemDecap_eq_some_iff pqxdhIkm_inj_kem dhPk_inj x25519Key_dhPk x25519Key_of_isCanonicalKey
  agree_eq_of_sk_ne sameDHKey_of_agree_right_eq consumeMessageKey_seed_eq
  bobAgreement_rk_eq_aliceAgreement_rk)

section KdfChainInversion
unseal Bytes

private theorem agree_view_dh_isSome (pk sk : Bytes) :
    ((agree pk sk).view? DiffieHellman.Dh.SubF).isSome = true := by
  dsimp only [agree, DiffieHellman.dh, DiffieHellman.CanDH.dh]
  rcases (X25519.normalizeX25519Key pk).view? DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
  · rfl
  · dsimp only
    split <;> rfl

theorem not_compExposure_hmac_agree {tr : ExecTrace} (hinv : SpqrInv tr) {rk pk sk : Bytes}
    (h : CompExposure tr (hmac rk (agree pk sk))) : False := by
  generalize hkm : hmac rk (agree pk sk) = km at h
  cases h with
  | pqr hexp | ck0 hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    have hv := congrArg (fun b : Bytes => (b.view? DiffieHellman.Dh.SubF).isSome) (hmac_inj hkm).2
    rw [agree_view_dh_isSome] at hv; cases hv
  | ckStep _ _ =>
    rw [chainKeyAt_succ_right] at hkm
    have hv := congrArg (fun b : Bytes => (b.view? DiffieHellman.Dh.SubF).isSome) (hmac_inj hkm).2
    rw [agree_view_dh_isSome] at hv; cases hv
  | rkRatchet _ _ _ | seedCk _ _ | seedRatchet _ _ _ =>
    have hv := congrArg (fun b : Bytes => (b.view? DiffieHellman.Dh.SubF).isSome) (hmac_inj hkm).2
    rw [agree_view_dh_isSome] at hv; cases hv
  | @chainRatchet keys j n rkChain pk' sk' _ _ _ =>
    cases n with
    | zero =>
      have hv := congrArg (fun b : Bytes => (b.view? DiffieHellman.Dh.SubF).isSome) (hmac_inj hkm).2
      rw [agree_view_dh_isSome] at hv; cases hv
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      have hv := congrArg (fun b : Bytes => (b.view? DiffieHellman.Dh.SubF).isSome) (hmac_inj hkm).2
      rw [agree_view_dh_isSome] at hv; cases hv

theorem not_compExposure_hmac_trMac {tr : ExecTrace} (hinv : SpqrInv tr)
    {pqSalt seed ikA ikB wire : Bytes}
    (h : CompExposure tr (hmac (trMsgKeys pqSalt seed).macKey
      (Concat.concat (serializedIk ikA) (Concat.concat (serializedIk ikB) wire)))) : False := by
  generalize hkm : hmac (trMsgKeys pqSalt seed).macKey
      (Concat.concat (serializedIk ikA) (Concat.concat (serializedIk ikB) wire)) = km at h
  cases h with
  | pqr hexp | ck0 hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    cases congrArg (fun b : Bytes => b.view? KdfExtract.SubF) (hmac_inj (hmac_inj hkm).1).1
  | ckStep _ _ =>
    rw [chainKeyAt_succ_right] at hkm
    cases congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) (hmac_inj hkm).2
  | rkRatchet _ _ _ =>
    cases congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) (concat_inj (hmac_inj hkm).2).1
  | @chainRatchet keys j n rkChain pk sk _ _ _ =>
    cases n with
    | zero =>
      cases congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) (concat_inj (hmac_inj hkm).2).1
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      cases congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) (hmac_inj hkm).2
  | seedCk _ _ | seedRatchet _ _ _ =>
    cases congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) (hmac_inj hkm).2

theorem not_compExposure_trMacKey {tr : ExecTrace} (hinv : SpqrInv tr) {pqSalt seed : Bytes}
    (h : CompExposure tr (trMsgKeys pqSalt seed).macKey) : False := by
  generalize hkm : (trMsgKeys pqSalt seed).macKey = km at h
  cases h with
  | pqr hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    exact hkdfBlock2_ne_hkdfBlock3 _ _ _ _ hkm
  | ck0 hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    exact pqxdhLabel_ne_whisperMessageKeys (hkdfBlock2_inj hkm).2.symm
  | ckStep _ _ =>
    rw [chainKeyAt_succ_right] at hkm; exact hkdfBlock2_ne_kdfCk_fst _ _ _ hkm
  | rkRatchet _ _ _ => exact hkdfBlock1_ne_hkdfBlock2 _ _ _ _ hkm.symm
  | @chainRatchet keys j n rkChain pk sk _ _ _ =>
    cases n with
    | zero => exact lit_whisperRatchet_ne_whisperMessageKeys (hkdfBlock2_inj hkm).2.symm
    | succ m => rw [chainKeyAt_succ_right] at hkm; exact hkdfBlock2_ne_kdfCk_fst _ _ _ hkm
  | seedCk _ _ | seedRatchet _ _ _ => exact hkdfBlock2_ne_kdfCk_snd _ _ _ hkm

theorem not_compExposure_hmac_seed {tr : ExecTrace} (hinv : SpqrInv tr) {pqSalt ck : Bytes}
    (h : CompExposure tr (hmac pqSalt (kdfCk ck).2)) : False := by
  generalize hkm : hmac pqSalt (kdfCk ck).2 = km at h
  cases h with
  | pqr hexp | ck0 hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    cases congrArg (fun b : Bytes => b.view? KdfExtract.SubF) (hmac_inj hkm).2
  | ckStep _ _ =>
    rw [chainKeyAt_succ_right] at hkm
    cases congrArg (fun b : Bytes => b.view? KdfExtract.SubF) (hmac_inj hkm).2
  | rkRatchet _ _ _ | seedCk _ _ | seedRatchet _ _ _ =>
    cases congrArg (fun b : Bytes => b.view? KdfExtract.SubF) (hmac_inj hkm).2
  | @chainRatchet keys j n rkChain pk sk _ _ _ =>
    cases n with
    | zero => cases congrArg (fun b : Bytes => b.view? KdfExtract.SubF) (hmac_inj hkm).2
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      cases congrArg (fun b : Bytes => b.view? KdfExtract.SubF) (hmac_inj hkm).2

/-- What `CompExposure` on a ratchet-chain message seed `(kdfCk (chainKeyAt (createChain rk rt sS).2 n)).2`
or intermediate chain key `chainKeyAt (createChain rk rt sS).2 n` yields: an honest handshake
rooting `rkChain` with `rk = rkChain` and `agree rt sS = agree pk sk`. -/
def RatchetChainExposed (tr : ExecTrace) (rk rt sS : Bytes) : Prop :=
  ∃ j keys₀ rkChain pk sk,
    j < tr.length ∧ HandshakeKeysAt tr j keys₀ ∧
    (rkChain = keys₀.rk ∨ ∃ r₀ p₀ s₀, rkChain = (createChain r₀ p₀ s₀).1) ∧
    rk = rkChain ∧ agree rt sS = agree pk sk

theorem compExposure_kdfCk_snd_inv {tr : ExecTrace} (hinv : SpqrInv tr) {rk rt sS : Bytes} {n : Nat}
    (h : CompExposure tr (kdfCk (chainKeyAt (createChain rk rt sS).2 n)).2) :
    RatchetChainExposed tr rk rt sS := by
  generalize hkm : (kdfCk (chainKeyAt (createChain rk rt sS).2 n)).2 = km at h
  cases h with
  | pqr hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    exact False.elim (hkdfBlock3_ne_kdfCk_snd _ _ _ hkm.symm)
  | ck0 hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    exact False.elim (hkdfBlock2_ne_kdfCk_snd _ _ _ hkm.symm)
  | ckStep _ _ =>
    rw [chainKeyAt_succ_right] at hkm
    exact False.elim (kdfCk_fst_ne_snd _ _ hkm.symm)
  | rkRatchet _ _ _ =>
    exact False.elim (hkdfBlock1_ne_kdfCk_snd _ _ _ hkm.symm)
  | @chainRatchet keys j m rkChain pk sk _ _ _ =>
    cases m with
    | zero => exact False.elim (hkdfBlock2_ne_kdfCk_snd _ _ _ hkm.symm)
    | succ m' =>
      rw [chainKeyAt_succ_right] at hkm
      exact False.elim (kdfCk_fst_ne_snd _ _ hkm.symm)
  | seedCk hj hkeys =>
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    exact False.elim
      (chainKeyAt_createChain_snd_ne_chainKeyAt_pqxdhKdf_ck rk rt sS ikm _ _ (kdfCk_snd_inj hkm))
  | @seedRatchet keys₀ j m rkChain pk sk hj hkeys hrk =>
    obtain ⟨hcc, _⟩ := chainKeyAt_createChain_snd_inj (kdfCk_snd_inj hkm)
    obtain ⟨hrk_eq, hagr⟩ := createChain_snd_inj hcc
    exact ⟨j, keys₀, rkChain, pk, sk, hj, hkeys, hrk, hrk_eq, hagr⟩

theorem compExposure_chainKeyAt_createChain_inv {tr : ExecTrace} (hinv : SpqrInv tr)
    {rk rt sS : Bytes} {n : Nat}
    (h : CompExposure tr (chainKeyAt (createChain rk rt sS).2 n)) :
    RatchetChainExposed tr rk rt sS := by
  generalize hkm : chainKeyAt (createChain rk rt sS).2 n = km at h
  cases h with
  | pqr hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    cases n with
    | zero => exact False.elim (hkdfBlock2_ne_hkdfBlock3 _ _ _ _ hkm)
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      exact False.elim (hkdfBlock3_ne_kdfCk_fst _ _ _ hkm.symm)
  | ck0 hexp =>
    obtain ⟨_, _, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    cases n with
    | zero => exact False.elim (pqxdhKdf_ck_ne_createChain_snd ikm rk rt sS hkm.symm)
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      exact False.elim (hkdfBlock2_ne_kdfCk_fst _ _ _ hkm.symm)
  | @ckStep keys₀ j m hj hkeys =>
    obtain ⟨ikm, hEq⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys; rw [hEq] at hkm
    exact False.elim
      (chainKeyAt_createChain_snd_ne_chainKeyAt_pqxdhKdf_ck rk rt sS ikm n (m + 1) hkm)
  | rkRatchet _ _ _ =>
    cases n with
    | zero => exact False.elim (hkdfBlock1_ne_hkdfBlock2 _ _ _ _ hkm.symm)
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      exact False.elim (hkdfBlock1_ne_kdfCk_fst _ _ _ hkm.symm)
  | @chainRatchet keys₀ j m rkChain pk sk hj hkeys hrk =>
    obtain ⟨hcc, _⟩ := chainKeyAt_createChain_snd_inj hkm
    obtain ⟨hrk_eq, hagr⟩ := createChain_snd_inj hcc
    exact ⟨j, keys₀, rkChain, pk, sk, hj, hkeys, hrk, hrk_eq, hagr⟩
  | seedCk _ _ | seedRatchet _ _ _ =>
    cases n with
    | zero => exact False.elim (hkdfBlock2_ne_kdfCk_snd _ _ _ hkm)
    | succ m =>
      rw [chainKeyAt_succ_right] at hkm
      exact False.elim (kdfCk_fst_ne_snd _ _ hkm)

theorem pub_chainKeyAt_createChain_inv {tr : ExecTrace} (hinv : SpqrInv tr) {rk rt sS : Bytes} :
    ∀ {n : Nat}, Pub tr (chainKeyAt (createChain rk rt sS).2 n) →
      Pub tr rk ∨ RatchetChainExposed tr rk rt sS
  | 0, h => by
    rcases Pub.inv_kdf h with hexp | ⟨hprk, _⟩
    · exact .inr (compExposure_chainKeyAt_createChain_inv hinv (n := 0) hexp)
    · rcases Pub.inv_kdf hprk with hexp' | ⟨hrk, _⟩
      · exact False.elim (not_compExposure_hmac_agree hinv hexp')
      · exact .inl hrk
  | n + 1, h => by
    rw [chainKeyAt_succ_right] at h
    rcases Pub.inv_kdf h with hexp | ⟨hck, _⟩
    · change CompExposure tr (kdfCk (chainKeyAt (createChain rk rt sS).2 n)).1 at hexp
      rw [← chainKeyAt_succ_right] at hexp
      exact .inr (compExposure_chainKeyAt_createChain_inv hinv (n := n + 1) hexp)
    · exact pub_chainKeyAt_createChain_inv hinv hck

theorem pub_hmac_trMac_inv {tr : ExecTrace} (hinv : SpqrInv tr)
    {rk rt sS pqSalt seed ikA ikB wire : Bytes} {n : Nat}
    (hseed : seed = (kdfCk (chainKeyAt (createChain rk rt sS).2 n)).2)
    (hhmac : Pub tr (hmac (trMsgKeys pqSalt seed).macKey
      (Concat.concat (serializedIk ikA) (Concat.concat (serializedIk ikB) wire)))) :
    Pub tr rk ∨ RatchetChainExposed tr rk rt sS := by
  rcases Pub.inv_kdf hhmac with hexp | ⟨hmk, _⟩
  · exact False.elim (not_compExposure_hmac_trMac hinv hexp)
  · rcases Pub.inv_kdf hmk with hexp | ⟨hprk, _⟩
    · exact False.elim (not_compExposure_trMacKey hinv hexp)
    · rw [hseed] at hprk
      rcases Pub.inv_kdf hprk with hexp | ⟨_, hpub_seed⟩
      · exact False.elim (not_compExposure_hmac_seed hinv hexp)
      · rcases Pub.inv_kdf hpub_seed with hexp | ⟨hckn, _⟩
        · exact .inr (compExposure_kdfCk_snd_inv hinv hexp)
        · exact pub_chainKeyAt_createChain_inv hinv hckn

end KdfChainInversion

/-! ## Composed MAC Origin -/

theorem evAt_unique {tr : ExecTrace} {ev ev' : PQXDHEvent} {i : Nat}
    (h : tr.EventLoggedAt ev i) (h' : tr.EventLoggedAt ev' i) : ev = ev' := by
  unfold Trace.EventLoggedAt at h h'; rw [h] at h'; cases h'; rfl

theorem randAt_unique {tr : ExecTrace} {t n n' : Nat} (h : RandAt tr t n) (h' : RandAt tr t n') :
    n = n' := by
  unfold RandAt at h h'; rw [h] at h'; cases h'; rfl

theorem randAt_not_evAt {tr : ExecTrace} {t n : Nat} {ev : PQXDHEvent} (h : RandAt tr t n)
    (h' : tr.EventLoggedAt ev t) : False := by
  unfold RandAt at h; unfold Trace.EventLoggedAt at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h; obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := ProtocolEvent.ExecEntryT PQXDHEvent)) h'
  rw [proj_inj_eq] at hc; cases hc

theorem HandshakeKeysAt.lt_length {tr : ExecTrace} {j : Nat} {keys : HandshakeKeys}
    (h : HandshakeKeysAt tr j keys) : j < tr.length := by
  rcases h with ⟨_, _, _, _, _, _, _, ⟨_, _, hA⟩ | ⟨_, _, hB⟩⟩
  · exact Trace.EventLoggedAt_implies_i_le_length _ j tr hA
  · exact Trace.EventLoggedAt_implies_i_le_length _ j tr hB

theorem sS_ne_alice_ek {tr : ExecTrace} {b : Participant} {sS : Bytes} {t : Nat}
    (hS : SPKAt tr b sS) (hslot : AliceSlot tr t) : sS ≠ rnd t 32 := by
  intro hEq
  obtain ⟨ts, rfl, _, hr64, _⟩ := hS
  obtain ⟨_, hr32, _⟩ := hslot
  have hts : ts = t := (rnd_inj hEq).1; subst hts
  have := randAt_unique hr64 hr32; omega

theorem sB_ne_alice_ek {tr : ExecTrace} {b : Participant} {sB : Bytes} {t : Nat}
    (hB : IKAt tr b sB) (hslot : AliceSlot tr t) : sB ≠ rnd t 32 := by
  intro hEq
  obtain ⟨tb, rfl, _, hev⟩ := hB
  obtain ⟨_, hr32, _⟩ := hslot
  have htb : tb = t := (rnd_inj hEq).1; subst htb
  exact randAt_not_evAt hr32 hev

theorem sA_ne_spk {tr : ExecTrace} {a b : Participant} {sA sS : Bytes}
    (hA : IKAt tr a sA) (hS : SPKAt tr b sS) : sA ≠ sS := by
  intro hEq
  obtain ⟨ta, rfl, _, hev⟩ := hA
  obtain ⟨ts, rfl, _, hr64, _⟩ := hS
  have hta : ta = ts := (rnd_inj hEq).1; subst hta
  exact randAt_not_evAt hr64 hev

theorem eq_dhPk_of_sameDHKey_of_isCanonicalKey {ek sk : Bytes}
    (hsame : SameDHKey ek (DiffieHellman.dhPk sk)) (hcan : isCanonicalKey ek = true) :
    ek = DiffieHellman.dhPk sk := by
  unfold SameDHKey at hsame
  rw [x25519Key_of_isCanonicalKey hcan, x25519Key_dhPk] at hsame
  exact hsame

theorem eq_dhPk_of_sameDHKey_dhPk {sk₁ sk₂ : Bytes}
    (hsame : SameDHKey (DiffieHellman.dhPk sk₁) (DiffieHellman.dhPk sk₂)) :
    sk₁ = sk₂ := by
  unfold SameDHKey at hsame
  rw [x25519Key_dhPk, x25519Key_dhPk] at hsame
  exact dhPk_inj hsame

theorem bobAgreement_of_kemDecap {sB sS sQ : Bytes} {o : Option Bytes} {ikA ek ct e : Bytes}
    (hdec : PQKem.kemDecap sQ ct = some e) :
    bobAgreement sB sS sQ o ikA ek ct =
      some (pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e)) := by
  unfold bobAgreement; rw [hdec]; rfl

theorem kemDecap_of_bobAgreement {sB sS sQ : Bytes} {o : Option Bytes} {ikA ek ct : Bytes}
    {keys : HandshakeKeys} (hbob : bobAgreement sB sS sQ o ikA ek ct = some keys) :
    ∃ e, e = (DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct) ∧
      keys = pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e) :=
  ⟨_, rfl, bobAgreement_eq_some_iff.mp hbob⟩

theorem origin_of_aliceDone_rk_eq {tr : ExecTrace} (hinv : SpqrInv tr) (hcik : CikOK tr)
    {b a : Participant} {sB sS sQ sA : Bytes} {o : Option Bytes} {ek ct e : Bytes} {i j : Nat}
    {a' b' : Participant} {ikA' ikB' spk' pqpk' : Bytes} {opk' : Option Bytes}
    {ek' ct' : Bytes} {keys₀ : HandshakeKeys}
    (hB : IKAt tr b sB) (hS : SPKAt tr b sS) (hA : IKAt tr a sA)
    (hek : isCanonicalKey ek = true)
    (hdec : e = (DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct))
    (hj : j < i)
    (hAlice : tr.EventLoggedAt (PQXDHEvent.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys₀) j)
    (hrk : (pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS) (agree ek sB) (agree ek sS)
      (o.map (agree ek ·)) e)).rk = keys₀.rk) :
    AliceMatch tr (DiffieHellman.dhPk sA) (DiffieHellman.dhPk sB) (PQKem.kemPk sQ) ek ct
      (pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS) (agree ek sB) (agree ek sS)
        (o.map (agree ek ·)) e)) i ∨
    tr.EventLogged (PQXDHEvent.CompromisedIK a (DiffieHellman.dhPk sA)) ∨
    tr.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk sS)) ∨
    tr.EventLogged PQXDHEvent.BrokenDH := by
  have _ := hA
  obtain ⟨t, sA', rfl, hslot, hA', hikA', rfl, hAliceAgree, hbundle⟩ :=
    hinv.aliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys₀ j hAlice
  have hbob : bobAgreement sB sS sQ o (DiffieHellman.dhPk sA) ek ct =
      some (pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS) (agree ek sB) (agree ek sS)
        (o.map (agree ek ·)) e)) := by
    rw [bobAgreement_eq_some, ← hdec]
  have hrk' := hrk.trans (congrArg HandshakeKeys.rk (congrArg Prod.snd hAliceAgree))
  obtain ⟨hdh1, hdh2, hdh3, _, hpq, hct, hkeys⟩ := bobAgreement_rk_eq_aliceAgreement_rk hbob hrk'
  have hct_eq : ct = ct' := hct.trans (congrArg Prod.fst hAliceAgree).symm
  have hkeys_eq :
      pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS) (agree ek sB) (agree ek sS)
        (o.map (agree ek ·)) e) = keys₀ :=
    hkeys.trans (congrArg Prod.snd hAliceAgree).symm
  have hsA_eq : sA = sA' :=
    eq_dhPk_of_sameDHKey_dhPk (agree_eq_of_sk_ne (sA_ne_spk hA' hS).symm hdh1).1
  have hikA_eq : DiffieHellman.dhPk sA = ikA' := by rw [hsA_eq, hikA']
  have hek_eq : ek = DiffieHellman.dhPk (rnd t 32) :=
    eq_dhPk_of_sameDHKey_of_isCanonicalKey (agree_eq_of_sk_ne (sS_ne_alice_ek hS hslot) hdh3).1 hek
  have hikB_same : SameDHKey ikB' (DiffieHellman.dhPk sB) :=
    (agree_eq_of_sk_ne (sB_ne_alice_ek hB hslot) hdh2).2
  rcases hbundle with ⟨sB', sS', sQ', _, hikB', _, _, _, _⟩ | ⟨rc, hrc, _⟩ | ⟨rd, hrd, _⟩
  · rw [hikB'] at hikB_same
    have hikB_eq : DiffieHellman.dhPk sB = ikB' := by
      rw [hikB', eq_dhPk_of_sameDHKey_dhPk hikB_same]
    refine .inl ⟨t + 5, a', b', spk', opk', hj, ?_⟩
    rw [hkeys_eq, hikA_eq, hikB_eq, ← hpq, hek_eq, hct_eq]
    exact hAlice
  · obtain ⟨sB', _, hikB'⟩ := cik_pub hinv hcik hrc
    rw [hikB'] at hikB_same
    have hikB_eq : DiffieHellman.dhPk sB = ikB' := by
      rw [hikB', eq_dhPk_of_sameDHKey_dhPk hikB_same]
    refine .inl ⟨t + 5, a', b', spk', opk', hj, ?_⟩
    rw [hkeys_eq, hikA_eq, hikB_eq, ← hpq, hek_eq, hct_eq]
    exact hAlice
  · exact .inr (.inr (.inr ⟨rd, hrd⟩))

theorem origin_of_handshakeKeysAt_rk_eq {tr : ExecTrace} (hinv : SpqrInv tr) (hcik : CikOK tr)
    {b a : Participant} {sB sS sQ sA : Bytes} {o : Option Bytes} {ek ct e : Bytes} {i j : Nat}
    {keys₀ : HandshakeKeys}
    (hB : IKAt tr b sB) (hS : SPKAt tr b sS) (hQ : PQAt tr b sQ) (hA : IKAt tr a sA)
    (hek : isCanonicalKey ek = true)
    (hdec : e = (DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct))
    (hj : j < i) (hkeys₀ : HandshakeKeysAt tr j keys₀)
    (hrk : (pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS) (agree ek sB) (agree ek sS)
      (o.map (agree ek ·)) e)).rk = keys₀.rk) :
    AliceMatch tr (DiffieHellman.dhPk sA) (DiffieHellman.dhPk sB) (PQKem.kemPk sQ) ek ct
      (pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS) (agree ek sB) (agree ek sS)
        (o.map (agree ek ·)) e)) i ∨
    tr.EventLogged (PQXDHEvent.CompromisedIK a (DiffieHellman.dhPk sA)) ∨
    tr.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk sS)) ∨
    tr.EventLogged PQXDHEvent.BrokenDH := by
  have _ := hQ
  rcases hkeys₀ with ⟨a', b', ikA', ikB', spk', pqpk', opk', ⟨ek', ct', hAlice⟩ | ⟨ek', ct', hBob⟩⟩
  · exact origin_of_aliceDone_rk_eq hinv hcik hB hS hA hek hdec hj hAlice hrk
  · obtain ⟨sB', sS', sQ', o', e', _, rfl, hS', rfl, _, rfl, _, rfl, _, _, hkeys₀_eq, _, horigin'⟩ :=
      hinv.bobDone b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys₀ j hBob
    have hrk₀ := hrk
    rw [hkeys₀_eq] at hrk₀
    have hdh1 := (pqxdhIkm_inj_parts (pqxdhKdf_rk_inj hrk₀)).1
    have hsS : sS = sS' :=
      Classical.byContradiction fun hne =>
        sA_ne_spk hA hS' (eq_dhPk_of_sameDHKey_dhPk (agree_eq_of_sk_ne hne hdh1).1)
    subst hsS
    have hb : b = b' := SPKAt.owner_unique hS hS'; subst hb
    have hikA'_same : SameDHKey ikA' (DiffieHellman.dhPk sA) :=
      sameDHKey_of_agree_right_eq hdh1.symm
    rcases horigin' with ⟨j₀, a'', b'', spk'', opk'', hj₀, hAlice₀⟩ | ⟨rc, hrc, _⟩ | ⟨rc, hrc, _⟩ | ⟨rd, hrd, _⟩
    · exact origin_of_aliceDone_rk_eq hinv hcik hB hS hA hek hdec (Nat.lt_trans hj₀ hj) hAlice₀ hrk
    · obtain ⟨sk, hpub_sk, hikA'_eq⟩ := cik_pub hinv hcik hrc
      rw [hikA'_eq] at hikA'_same
      have hsk : sk = sA := eq_dhPk_of_sameDHKey_dhPk hikA'_same; subst hsk
      rcases pub_IK hinv hA hpub_sk with ⟨jc, hjc⟩ | ⟨jd, hjd⟩
      · exact .inr (.inl ⟨jc, hjc⟩)
      · exact .inr (.inr (.inr ⟨jd, hjd⟩))
    · exact .inr (.inr (.inl ⟨rc, hrc⟩))
    · exact .inr (.inr (.inr ⟨rd, hrd⟩))

/-- Bob's key confirmation on an attacker-known `TRSignalMsg` inside `bobStart` yields
`AliceMatch` or one of `CompromisedIK a ikA`, `CompromisedSPK b (dhPk sS)`, or `BrokenDH`. -/
theorem comp_mac_origin {tr : ExecTrace} (hinv : SpqrInv tr) (hcik : CikOK tr) {b a : Participant}
    {sB sS sQ : Bytes} {o : Option Bytes} {ikA vkA ek ct e : Bytes} {hon : Bool} {r : Nat}
    (hB : IKAt tr b sB) (hS : SPKAt tr b sS) (hQ : PQAt tr b sQ)
    (hreg : tr.EventLoggedAt (PQXDHEvent.IdentityRegistered a ikA vkA hon) r)
    (hek : isCanonicalKey ek = true)
    (hdec : e = (DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct))
    {msg : TRSignalMsg} {pqSalt seed : Bytes} {rcIdx : Nat} {c' : RecvChain}
    (hmac : msg.mac.AttackerKnows tr)
    (hConsume : consumeMessageKey
      { ratchetKey := msg.ratchetKey,
        chainKey := (createChain
          (pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e)).rk
          msg.ratchetKey sS).2,
        index := 0,
        rIdx := rcIdx } msg.counter = some (seed, c'))
    (hMac : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (serializedIk ikA) (serializedIk (DiffieHellman.dhPk sB)) msg.wire) :
    AliceMatch tr ikA (DiffieHellman.dhPk sB) (PQKem.kemPk sQ) ek ct
      (pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e))
      tr.length ∨
    tr.EventLogged (PQXDHEvent.CompromisedIK a ikA) ∨
    tr.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk sS)) ∨
    tr.EventLogged PQXDHEvent.BrokenDH := by
  cases hon with
  | false => exact .inr (.inl ⟨r + 1, hinv.irCorrupt a ikA vkA r hreg⟩)
  | true =>
    obtain ⟨sA, hA, rfl, _⟩ := hinv.irHonest a ikA vkA r hreg
    let keys := pqxdhKdf (pqxdhIkm (agree (DiffieHellman.dhPk sA) sS)
      (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e)
    have hseed := consumeMessageKey_seed_eq hConsume
    have hpub_mac : Pub tr msg.mac := pub_of_knows hinv hmac
    rw [hMac] at hpub_mac
    rcases Pub.inv_trunc hinv hpub_mac with hpub_hmac | hhonest
    · rcases pub_hmac_trMac_inv hinv hseed hpub_hmac with
        hpub_rk | ⟨j, keys₀, rkChain, _, _, hj, hkeys₀, hrkChain, hrk_eq, _⟩
      · have hblk : IsHandshakeBlock keys keys.rk := .inl rfl
        rcases pub_handshakeBlock_inv hinv (keys := keys) (k := keys.rk) rfl hblk hpub_rk with
          ⟨hpub_dh1, _, _, _, _⟩ | ⟨_, j, _, hkeys₀, _⟩
        · rcases pub_agree_dhPk hinv hpub_dh1 with hsA | hsS
          · rcases pub_IK hinv hA hsA with hcik_ev | hbdh
            · exact .inr (.inl hcik_ev)
            · exact .inr (.inr (.inr hbdh))
          · rcases pub_SPK hinv hS hsS with hcspk | hbdh
            · exact .inr (.inr (.inl hcspk))
            · exact .inr (.inr (.inr hbdh))
        · exact origin_of_handshakeKeysAt_rk_eq hinv hcik hB hS hQ hA hek hdec (HandshakeKeysAt.lt_length hkeys₀) hkeys₀ rfl
      · rcases hrkChain with rfl | ⟨r₀, p₀, s₀, rfl⟩
        · exact origin_of_handshakeKeysAt_rk_eq hinv hcik hB hS hQ hA hek hdec hj hkeys₀ hrk_eq
        · exact False.elim (pqxdhKdf_rk_ne_createChain_fst _ _ _ _ hrk_eq)
    · obtain ⟨j, keys₀, rkChain, pk, sk, counter, pqSalt', ikA', ikB', wire',
        hj, hkeys₀, hrkChain, hhmac_eq⟩ := hhonest
      have hmk := (hmac_inj hhmac_eq).1
      have hseed_eq := (trMsgKeys_macKey_inj hmk).2
      have hck_at := kdfCk_snd_inj (hseed.symm.trans hseed_eq)
      obtain ⟨hcc, _⟩ := chainKeyAt_createChain_snd_inj hck_at
      obtain ⟨hrk_eq, _⟩ := createChain_snd_inj hcc
      rcases hrkChain with rfl | ⟨r₀, p₀, s₀, rfl⟩
      · exact origin_of_handshakeKeysAt_rk_eq hinv hcik hB hS hQ hA hek hdec hj hkeys₀ hrk_eq
      · exact False.elim (pqxdhKdf_rk_ne_createChain_fst _ _ _ _ hrk_eq)

/-! ## `bobStart` Preservation -/

open Symbolic.Swarm.COMPOSED.CompTrace (run_bind_fst run_bind_snd run_bind_assoc_snd bind_guardP_at
  bind_receiveMessage_at bind_bobHandshake_at)

theorem attackerKnows_of_parseTrSignalMsg {tr : ExecTrace} (hinv : SpqrInv tr)
    {raw : Bytes} {msg : TRSignalMsg}
    (hraw : raw.AttackerKnows tr) (hparse : parseTrSignalMsg raw = some msg) :
    msg.mac.AttackerKnows tr ∧ Pub tr msg.pqRatchet := by
  unfold parseTrSignalMsg at hparse
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at hparse
  rcases hparse with ⟨⟨wire, mac⟩, hsplit, ⟨v, rk, c, pc, ct, pq, enc⟩, hx, rfl⟩
  have hmac : mac.AttackerKnows tr :=
    Bytes.AttackerKnows.prove Concat.attackerKnowledge mac tr
      ⟨⟨2, by decide⟩, raw, wire, raw.length - Trunc.trunc8Length, hsplit.symm, hraw⟩
  have hwire : wire.AttackerKnows tr :=
    Bytes.AttackerKnows.prove Concat.attackerKnowledge wire tr
      ⟨⟨1, by decide⟩, raw, mac, raw.length - Trunc.trunc8Length, hsplit.symm, hraw⟩
  have hpub_wire : Pub tr wire := pub_of_knows hinv hwire
  have hpack := Bytes.pack_view? TrWire.TrWireMsg.SubF wire
  unfold TrWire.trWireMsgFields? at hx
  rw [hx] at hpack
  have htr : wire = TrWire.trWireMsg v rk c pc ct pq enc := hpack.symm
  rw [htr] at hpub_wire
  exact ⟨hmac, (CompPubInv.Pub.inv_trWire hinv hpub_wire).2.2⟩

theorem consumeMessageKey_out {rk pk : Bytes} {rcIdx : Nat} {counter : UInt32}
    {seed : Bytes} {c' : RecvChain}
    (h : consumeMessageKey { ratchetKey := rk, chainKey := pk, index := 0, rIdx := rcIdx } counter =
      some (seed, c')) :
    seed = (kdfCk (chainKeyAt pk counter.toNat)).2 ∧
    c' = { ratchetKey := rk,
           chainKey := (kdfCk (chainKeyAt pk counter.toNat)).1,
           index := counter + 1,
           rIdx := rcIdx } := by
  unfold consumeMessageKey at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · injection h with hpair
        have h1 := congrArg Prod.fst hpair
        have h2 := congrArg Prod.snd hpair
        dsimp only at h1 h2
        have hsub : counter.toNat - (0 : UInt32).toNat = counter.toNat := Nat.sub_zero counter.toNat
        rw [hsub] at h1 h2
        exact ⟨h1.symm, h2.symm⟩

theorem run_logSkippedKeys_fst (s : SessionInfo) (pk : Bytes) (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : Bytes) (idx : UInt32) (tr : ExecTrace),
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).1 = some ()
  | 0, _, _, _ => rfl
  | k + 1, ck, idx, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [run_bind_fst]
    exact run_logSkippedKeys_fst s pk rIdx srcIdx k (kdfCk ck).1 (idx + 1) _

theorem run_logSkippedKeys_bind_snd {α : Type} (s : SessionInfo) (pk : Bytes) (rIdx srcIdx : Nat)
    (ck : Bytes) (idx : UInt32) (k : Nat) (f : Unit → Traceful α) (tr : ExecTrace) :
    ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k >>= f).run tr).2.val =
      ((f ()).run ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val).2.val := by
  rw [run_bind_snd, run_logSkippedKeys_fst]

theorem run_logEvent_bind_snd {Ev α : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    (ev : Ev) (f : Unit → Traceful α) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev >>= f).run tr).2.val =
      ((f ()).run (tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT Ev))).2.val :=
  by rfl

theorem spqrInv_logSkippedKeys {tr : ExecTrace} (hinv : SpqrInv tr)
    {j : Nat} {keys : HandshakeKeys} (hj : j < tr.length) (hkeys : HandshakeKeysAt tr j keys)
    (s : SessionInfo) (rt : Bytes) (rIdx srcIdx : Nat) (sS : Bytes) :
    ∀ (k m : Nat) (idx : UInt32),
      SpqrInv ((DY.Libsignal.TripleRatchet.logSkippedKeys s rt rIdx srcIdx
        (chainKeyAt (createChain keys.rk rt sS).2 m) idx k).run tr).2.val
  | 0, _, _ => hinv
  | k + 1, m, idx => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [run_logEvent_bind_snd (Ev := TREvent)]
    let ev := TREvent.SkippedKeyStored s rt idx
      (kdfCk (chainKeyAt (createChain keys.rk rt sS).2 m)).2 rIdx srcIdx
    let tr₁ := tr.append (TREvE ev)
    have hle : tr ≤ tr₁ := Trace.append_le tr _
    have hok : SkippedKeyOK tr (kdfCk (chainKeyAt (createChain keys.rk rt sS).2 m)).2 :=
      ⟨j, keys, hj, hkeys, .inr ⟨keys.rk, rt, sS, m, .inl rfl, rfl⟩⟩
    have hinv₁ : SpqrInv tr₁ := spqrInv_append_trEv_skip hinv hok
    have hj₁ : j < tr₁.length := Nat.lt_of_lt_of_le hj (Nat.le_succ _)
    have hkeys₁ : HandshakeKeysAt tr₁ j keys := handshakeKeysAt_mono hle hkeys
    rw [← chainKeyAt_succ_right]
    exact spqrInv_logSkippedKeys hinv₁ hj₁ hkeys₁ s rt rIdx srcIdx sS k (m + 1) (idx + 1)

theorem bind_receiveSignalMsg_at {tr : ExecTrace} (hinv : SpqrInv tr) {α : Type}
    (msgIdx : Nat) {f : TRSignalMsg → Traceful α}
    (hf : ∀ msg, msg.mac.AttackerKnows tr → Pub tr msg.pqRatchet →
      SpqrInv ((f msg).run tr).2.val) :
    SpqrInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [run_bind_assoc_snd]
  refine bind_receiveMessage_at msgIdx tr hinv fun raw _ hraw => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg
  · exact hinv
  · dsimp only
    rw [run_bind_assoc_snd]
    refine bind_guardP_at _ tr hinv fun _ => ?_
    obtain ⟨hmac, hpq⟩ := attackerKnows_of_parseTrSignalMsg hinv hraw hparse
    exact hf msg hmac hpq

theorem bind_verifyMacAndDecrypt_at {Inv : ExecTrace → Prop} {α : Type}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes)
    {f : Bytes → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ m, msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire →
      Inv ((f m).run tr).2.val) :
    Inv (((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  rw [run_bind_assoc_snd]
  refine bind_guardP_at _ tr hInv fun hMac => ?_
  rcases SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext with _ | m
  · exact hInv
  · exact hf m hMac

def bobInitSt (a : Participant) (ikB ikA : Bytes) (keys : HandshakeKeys) (sS rt : Bytes) : TRState :=
  { peer := a, myIk := serializedIk ikB, peerIk := serializedIk ikA, rk := keys.rk,
    dhs := sS, cks := keys.ck, ns := 0, pn := 0, sid := Concat.concat (X25519.normalizeX25519Key rt) keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit keys.pqr spqrB2A }

def bobRatchetedChain (keys : HandshakeKeys) (rt sS : Bytes) : RecvChain :=
  { ratchetKey := rt, chainKey := (createChain keys.rk rt sS).2, index := 0, rIdx := 2 }

def bobRatchetedSt (a : Participant) (ikB ikA : Bytes) (keys : HandshakeKeys)
    (sS rt dhs : Bytes) : TRState :=
  let (rk1, _) := createChain keys.rk rt sS
  let (rk2, cks) := createChain rk1 rt dhs
  { peer := a, myIk := serializedIk ikB, peerIk := serializedIk ikA, rk := rk2,
    dhs := dhs, cks := cks, ns := 0, pn := 0, sid := Concat.concat (X25519.normalizeX25519Key rt) keys.rk,
    initiator := false, rIdx := 2, recv := [bobRatchetedChain keys rt sS],
    spqr := Spqr.spqrInit keys.pqr spqrB2A }

theorem bind_ensureReceiverChain_bobInitSt {Inv : ExecTrace → Prop} {α : Type}
    (a : Participant) (ikB ikA : Bytes) (keys : HandshakeKeys) (sS rt : Bytes)
    {f : TRState × RecvChain × Bool → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (hf : (!x25519LowOrder rt) = true →
      Inv ((f (bobRatchetedSt a ikB ikA keys sS rt (rnd tr.length 32),
        bobRatchetedChain keys rt sS, true)).run (tr.append (RndE 32))).2.val) :
    Inv (((DY.Libsignal.TripleRatchet.ensureReceiverChain (bobInitSt a ikB ikA keys sS rt) rt >>= f).run tr).2.val) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor findRecvChain
  dsimp only [bobInitSt, List.find?_nil]
  rcases hlo : x25519LowOrder rt with _ | _
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    rw [run_bind_assoc_snd, run_bind_assoc_snd]
    refine bind_guardP_at _ tr hInv fun hlo' => ?_
    exact hf hlo'
  · simp only [↓reduceIte]
    exact hInv

theorem spqrInv_bobStart_commit {tr : ExecTrace} (hinv : SpqrInv tr)
    {b a : Participant} {sB sS sQ : Bytes} {o : Option Bytes}
    {ikA ek ct : Bytes} {keys : HandshakeKeys}
    {msg : TRSignalMsg} {dhs spqr' seed pqSalt m : Bytes} {c' : RecvChain}
    (hFacts : BobDoneFacts tr b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS)
      (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys tr.length)
    (hopkUsed : ∀ o_pk, o.map DiffieHellman.dhPk = some o_pk →
      LoggedBefore (PQXDHEvent.OPKUsed b o_pk) tr.length tr)
    (hdhs : TRRatchetAt tr dhs)
    (hspqr : SpqrStateFrom tr keys.pqr spqr')
    (hConsume : consumeMessageKey (bobRatchetedChain keys msg.ratchetKey sS) msg.counter = some (seed, c')) :
    let st := bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := bobRatchetedChain keys msg.ratchetKey sS
    SpqrInv (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA
        (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat
      let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c
  obtain ⟨_, hc'⟩ := consumeMessageKey_out hConsume
  let doneIdx := tr.length
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA
    (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  have hinv₁ : SpqrInv tr₁ := spqrInv_append_bobDone hinv hFacts hopkUsed
  have hkeys₁ : HandshakeKeysAt tr₁ doneIdx keys :=
    ⟨a, b, _, _, _, _, _, .inr ⟨_, _, eventLoggedAt_here tr _⟩⟩
  have hj₁ : doneIdx < tr₁.length := Nat.lt_succ_self _
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  have hinv₂ : SpqrInv tr₂ := spqrInv_append_trEv_nonSkip hinv₁ (by intros; rintro ⟨⟩)
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  have hinv₃ : SpqrInv tr₃ := spqrInv_append_trEv_nonSkip hinv₂ (by intros; rintro ⟨⟩)
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hinv₄ : SpqrInv tr₄ := spqrInv_append_cEv hinv₃ _
  have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
  have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
  have hle₂₃ : tr₂ ≤ tr₃ := Trace.append_le tr₂ _
  have hle₃₄ : tr₃ ≤ tr₄ := Trace.append_le tr₃ _
  have hle₁₄ : tr₁ ≤ tr₄ := Trace.le_trans _ _ _ hle₁₂ (Trace.le_trans _ _ _ hle₂₃ hle₃₄)
  have hle₀₄ : tr ≤ tr₄ := Trace.le_trans _ _ _ hle₀₁ hle₁₄
  have hj₄ : doneIdx < tr₄.length := Nat.lt_of_lt_of_le hj₁ (Trace.length_le _ _ hle₁₄)
  have hkeys₄ : HandshakeKeysAt tr₄ doneIdx keys := handshakeKeysAt_mono hle₁₄ hkeys₁
  have hhs₄ : tr₄.EventLogged (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx) :=
    eventLogged_here tr₃ _
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx
    c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
      msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }
  change SpqrInv (((skipAct >>= restAct).run tr₄).2.val)
  rw [run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hle₄₅ : tr₄ ≤ tr₅ := (skipAct.run tr₄).2.property
  have hinv₅ : SpqrInv tr₅ :=
    spqrInv_logSkippedKeys hinv₄ hj₄ hkeys₄ (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx sS skipped 0 0
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  have hinv₆ : SpqrInv tr₆ := spqrInv_append_trEv_nonSkip hinv₅ (by intros; rintro ⟨⟩)
  let tr₇ := tr₆.append (TREvE (.MessageKey (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx))
  have hinv₇ : SpqrInv tr₇ := spqrInv_append_trEv_nonSkip hinv₆ (by intros; rintro ⟨⟩)
  have hle₅₆ : tr₅ ≤ tr₆ := Trace.append_le tr₅ _
  have hle₆₇ : tr₆ ≤ tr₇ := Trace.append_le tr₆ _
  have hle₄₇ : tr₄ ≤ tr₇ := Trace.le_trans _ _ _ hle₄₅ (Trace.le_trans _ _ _ hle₅₆ hle₆₇)
  have hle₀₇ : tr ≤ tr₇ := Trace.le_trans _ _ _ hle₀₄ hle₄₇
  have hst_ok : TRStateOK tr₇ b { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
    refine ⟨doneIdx, keys, Nat.lt_of_lt_of_le hj₄ (Trace.length_le _ _ hle₄₇),
      handshakeKeysAt_mono hle₄₇ hkeys₄, ev_mono hle₄₇ hhs₄,
      .inr (hdhs.mono hle₀₇), hspqr.mono hle₀₇,
      ⟨(createChain keys.rk msg.ratchetKey sS).1, msg.ratchetKey, dhs, rfl⟩,
      ⟨(createChain keys.rk msg.ratchetKey sS).1, msg.ratchetKey, dhs, 0,
        .inr ⟨keys.rk, msg.ratchetKey, sS, rfl⟩, rfl⟩, ?_⟩
    intro rc hrc
    simp only [st, bobRatchetedSt, setRecvChain, List.map_cons, List.map_nil, List.mem_singleton] at hrc
    split at hrc <;> subst hrc
    · rw [hc', ← chainKeyAt_succ_right]
      exact .inr (.inr ⟨keys.rk, msg.ratchetKey, sS, msg.counter.toNat + 1, .inl rfl, rfl⟩)
    · exact .inr (.inr ⟨keys.rk, msg.ratchetKey, sS, 0, .inl rfl, rfl⟩)
  exact spqrInv_append_trSt hinv₇ hst_ok

end CompPresBob

open CompPresBob
open Symbolic.Swarm.COMPOSED.CompTrace (
  run_bind_snd bind_receiveMessage_at bind_bobHandshake_at)

/-- `bobStart` preserves `SpqrInv` on traces satisfying `CikOK`. -/
theorem preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    ∀ (tr : ExecTrace), SpqrInv tr → CikOK tr →
      SpqrInv ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  intro tr hinv hcik
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hinv
    fun sB sS sQ o ikA vkA ek ct hon keys hstB hstS hstQ hopk hregA _ _ hek hbob => ?_
  refine bind_receiveSignalMsg_at hinv mh.msg fun msg hmac hpq => ?_
  dsimp only
  refine bind_ensureReceiverChain_bobInitSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey
    tr hinv fun _ => ?_
  let dhs := rnd tr.length 32
  let st := bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32)
  have hinv₁ : SpqrInv tr₁ := spqrInv_append_rnd hinv 32
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact hinv₁
  · dsimp only
    rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with
      _ | ⟨spqr', key⟩
    · exact hinv₁
    · dsimp only
      have hle₀₁ : tr ≤ tr₁ := Trace.append_le tr _
      have hpub_pq₁ : Pub tr₁ msg.pqRatchet := hpq.mono hle₀₁
      have hkey₁ : Pub tr₁ key := CompPubInv.Pub.spqrRecvKey_of hSpqr
      have hspqr₁ : SpqrStateFrom tr₁ keys.pqr spqr' :=
        CompPubInv.SpqrStateFrom.of_spqrRecv hSpqr (.init (.literal _)) hpub_pq₁
      let tr₂ := tr₁.append (NetE key)
      have hle₁₂ : tr₁ ≤ tr₂ := Trace.append_le tr₁ _
      have hle₀₂ : tr ≤ tr₂ := Trace.le_trans _ _ _ hle₀₁ hle₁₂
      have hinv₂ : SpqrInv tr₂ := spqrInv_append_net hinv₁ (hkey₁.mono hle₁₂)
      have hdhs₂ : TRRatchetAt tr₂ dhs :=
        ⟨tr.length, key, rfl, RandAt.mono hle₁₂ (at?_append_here tr (RndE 32)), at?_append_here tr₁ (NetE key)⟩
      have hspqr₂ : SpqrStateFrom tr₂ keys.pqr spqr' := hspqr₁.mono hle₁₂
      change SpqrInv (((Network.receiveMessage pqIdx >>= fun pqSalt =>
        DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
      refine bind_receiveMessage_at pqIdx tr₂ hinv₂ fun pqSalt _ _ => ?_
      refine bind_verifyMacAndDecrypt_at st msg pqSalt seed tr₂ hinv₂ fun m hMac => ?_
      have hB : IKAt tr b sB := hinv.stOK b { kind := .identity, sk := sB } kh.ik hstB
      have hS : SPKAt tr b sS := hinv.stOK b { kind := .signedPrekey, sk := sS } kh.spk hstS
      have hQ : PQAt tr b sQ := hinv.stOK b { kind := .pqPrekey, sk := sQ } kh.pqspk hstQ
      have ho : ∀ x, o = some x → OPKAt tr b x := by
        intro x hx
        rcases hopk with ⟨_, rfl⟩ | ⟨idx, o', _, rfl, hstO⟩
        · cases hx
        · injection hx with hx_eq; subst hx_eq
          exact hinv.stOK b { kind := .oneTimePrekey, sk := o' } idx hstO
      obtain ⟨e, hdec, hkeys⟩ := kemDecap_of_bobAgreement hbob
      have hConsume' :
          consumeMessageKey
            { ratchetKey := msg.ratchetKey,
              chainKey := (createChain
                (pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) e)).rk
                msg.ratchetKey sS).2,
              index := 0,
              rIdx := 2 } msg.counter = some (seed, c') := by
        rw [← hkeys]; exact hConsume
      have horigin := comp_mac_origin hinv hcik hB hS hQ hregA hek hdec hmac hConsume' hMac
      have hr_lt : regIdxA < tr.length :=
        Trace.EventLoggedAt_implies_i_le_length _ regIdxA tr hregA
      have hFacts :
          BobDoneFacts tr b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS)
            (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys tr.length := by
        refine ⟨sB, sS, sQ, o, e, hB, rfl, hS, rfl, hQ, rfl, ho, rfl, hek, hdec, hkeys,
          ⟨regIdxA, vkA, hon, hr_lt, hregA⟩, ?_⟩
        rcases horigin with hmatch | hcik_ev | hcspk | hbdh
        · rw [← hkeys] at hmatch; exact .inl hmatch
        · exact .inr (.inl (loggedBefore_of_eventLogged hcik_ev))
        · exact .inr (.inr (.inl (loggedBefore_of_eventLogged hcspk)))
        · exact .inr (.inr (.inr (loggedBefore_of_eventLogged hbdh)))
      have hFacts₂ :
          BobDoneFacts tr₂ b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS)
            (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys tr₂.length :=
        BobDoneFacts.mono_idx (hFacts.mono hle₀₂) (Trace.length_le _ _ hle₀₂)
      cases o with
      | none =>
        dsimp only [Option.map]
        exact spqrInv_bobStart_commit hinv₂ hFacts₂ nofun hdhs₂ hspqr₂ hConsume
      | some oSk =>
        dsimp only [Option.map]
        rw [run_bind_snd]
        unfold DY.Libsignal.PQXDH.guardTrace
        rw [Traceful.run_mk]
        dsimp only
        by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
        · rw [ite_eq_left_iff.mpr fun h => absurd hused h]
          let tr₃ := tr₂.append (EvE (.OPKUsed b (DiffieHellman.dhPk oSk)))
          have hle₂₃ : tr₂ ≤ tr₃ := Trace.append_le tr₂ _
          have hinv₃ : SpqrInv tr₃ := spqrInv_append_opkUsed hinv₂ b (DiffieHellman.dhPk oSk)
          have hFacts₃ :
              BobDoneFacts tr₃ b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS)
                (PQKem.kemPk sQ) ((some oSk).map DiffieHellman.dhPk) ek ct keys tr₃.length :=
            BobDoneFacts.mono_idx (hFacts₂.mono hle₂₃) (Trace.length_le _ _ hle₂₃)
          have hopkUsed₃ : ∀ o_pk, (some oSk).map DiffieHellman.dhPk = some o_pk →
              LoggedBefore (PQXDHEvent.OPKUsed b o_pk) tr₃.length tr₃ := by
            intro o_pk hEq
            injection hEq with hEq; subst hEq
            exact ⟨tr₂.length, eventLoggedAt_here tr₂ _, Nat.lt_succ_self _⟩
          exact spqrInv_bobStart_commit (o := some oSk) hinv₃ hFacts₃ hopkUsed₃ (hdhs₂.mono hle₂₃) (hspqr₂.mono hle₂₃) hConsume
        · rw [ite_eq_right_iff.mpr fun h => absurd h hused]
          exact hinv₂

end Symbolic.Swarm.COMPOSED.CompInv
