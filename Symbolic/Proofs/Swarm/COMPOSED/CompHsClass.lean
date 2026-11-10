/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Prekey Class Secrecy and Encapsulation Coin Unobservability

Proves trace-entry disjointness and owner uniqueness for prekey records (`SPKAt.owner_unique`,
`PQAt.owner_unique`, `OPKAt.owner_unique`), class secrecy under `SpqrInv` (`pub_SPK`, `pub_PQ`,
`pub_OPK`, `pub_EK`), Diffie-Hellman shared-secret inversion in `Pub` (`pub_agree_dhPk`), and
unobservability of Alice's KEM encapsulation coins (`not_pub_coins`).
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

/-! ## Trace-entry exclusivity and prekey owner uniqueness -/

namespace HsClassHelpers

theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem evAt_unique {tr : ExecTrace} {ev ev' : PQXDHEvent} {i : Nat}
    (h : tr.EventLoggedAt ev i) (h' : tr.EventLoggedAt ev' i) : ev = ev' := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h h'
  rw [h] at h'
  cases h'
  rfl

theorem randAt_unique {tr : ExecTrace} {t n n' : Nat} (h : RandAt tr t n) (h' : RandAt tr t n') :
    n = n' := by
  unfold RandAt at h h'
  rw [h] at h'
  cases h'
  rfl

theorem randAt_not_evAt {tr : ExecTrace} {t n : Nat} {ev : PQXDHEvent} (h : RandAt tr t n)
    (h' : tr.EventLoggedAt ev t) : False := by
  unfold RandAt at h
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := EvEntry)) h'
  rw [proj_inj] at hc
  cases hc

theorem netAt_not_evAt {tr : ExecTrace} {t : Nat} {msg : Bytes} {ev : PQXDHEvent}
    (h : NetAt tr msg t) (h' : tr.EventLoggedAt ev t) : False := by
  unfold NetAt at h
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := EvEntry)) h'
  rw [proj_inj] at hc
  cases hc

theorem randAt_not_netAt {tr : ExecTrace} {t n : Nat} {msg : Bytes}
    (h : RandAt tr t n) (h' : NetAt tr msg t) : False := by
  unfold RandAt at h
  unfold NetAt at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := NetEntry)) h'
  rw [proj_inj] at hc
  cases hc

theorem netAt_not_trEvAt {tr : ExecTrace} {t : Nat} {msg : Bytes} {ev : TREvent}
    (h : NetAt tr msg t) (h' : tr.EventLoggedAt ev t) : False := by
  unfold NetAt at h
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := TREvEntry)) h'
  rw [proj_inj] at hc
  cases hc

theorem pqAt_ne_rnd32 {tr : ExecTrace} {b : Participant} {t : Nat}
    (hq : PQAt tr b (rnd t 32)) : False := by
  obtain ⟨t', hr, _⟩ := hq
  have := (rnd_inj hr).2
  omega

end HsClassHelpers

open HsClassHelpers

theorem SPKAt.owner_unique {tr : ExecTrace} {b b' : Participant} {r : Bytes} (h : SPKAt tr b r)
    (h' : SPKAt tr b' r) : b = b' := by
  obtain ⟨t, hr, _, _, hev⟩ := h
  obtain ⟨t', hr', _, _, hev'⟩ := h'
  have ht : t = t' := (rnd_inj (hr.symm.trans hr')).1
  subst ht
  have heq := evAt_unique hev hev'
  cases heq
  rfl

theorem PQAt.owner_unique {tr : ExecTrace} {b b' : Participant} {r : Bytes} (h : PQAt tr b r)
    (h' : PQAt tr b' r) : b = b' := by
  obtain ⟨t, hr, _, _, hev⟩ := h
  obtain ⟨t', hr', _, _, hev'⟩ := h'
  have ht : t = t' := (rnd_inj (hr.symm.trans hr')).1
  subst ht
  have heq := evAt_unique hev hev'
  cases heq
  rfl

theorem OPKAt.owner_unique {tr : ExecTrace} {b b' : Participant} {r : Bytes}
    (h : OPKAt tr b r) (h' : OPKAt tr b' r) : b = b' := by
  obtain ⟨t, hr, _, hev⟩ := h
  obtain ⟨t', hr', _, hev'⟩ := h'
  have ht : t = t' := (rnd_inj (hr.symm.trans hr')).1
  subst ht
  have heq := evAt_unique hev hev'
  cases heq
  rfl

/-! ## Prekey class secrecy and `pub_agree_dhPk` -/

theorem pub_SPK_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hspk : SPKAt tr b r) (hpub : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk r)) ∨
    (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j) := by
  have hs₀ := hspk
  obtain ⟨t, rfl, _, hr64, hev⟩ := hspk
  rcases Pub.inv_rand hinv hpub with
    ⟨p, hik, _⟩ | ⟨b', hspk', he⟩ | ⟨b', hpq, _⟩ | ⟨b', hopk, _⟩ |
    ⟨_, hbdh⟩ | ⟨⟨b', hpq⟩, _⟩ | ⟨hrat, _⟩ | hmsg
  · obtain ⟨t', ht', _, hev'⟩ := hik
    cases (rnd_inj ht').1
    exact (randAt_not_evAt hr64 hev').elim
  · cases SPKAt.owner_unique hs₀ hspk'
    exact .inl he
  · exact (pqAt_ne_rnd32 hpq).elim
  · obtain ⟨t', ht', _, hev'⟩ := hopk
    cases (rnd_inj ht').1
    exact (randAt_not_evAt hr64 hev').elim
  · exact .inr hbdh
  · exact (pqAt_ne_rnd32 hpq).elim
  · rcases hrat with ⟨t', ht', _, _, _, a, b', ikA, ikB, spk, pqpk, opk, ek, ct, keys, hn3, _, _⟩ |
      ⟨t', msg, ht', _, hn⟩
    · have ht : t = t' + 2 := (rnd_inj ht').1
      have hidx : t' + 3 = t + 1 := by omega
      rw [hidx] at hn3
      exact (randAt_not_netAt hr64 hn3).elim
    · cases (rnd_inj ht').1
      exact (randAt_not_netAt hr64 hn).elim
  · rcases hmsg with ⟨t', n, msg, ht', _, _, hn2, _⟩ | ⟨t', n, msg, ht', _, _, hn2, _⟩
    · cases (rnd_inj ht').1
      exact (netAt_not_evAt hn2 hev).elim
    · have ht : t = t' + 1 := (rnd_inj ht').1
      have hidx : t' + 2 = t + 1 := by omega
      rw [hidx] at hn2
      exact (randAt_not_netAt hr64 hn2).elim

theorem pub_SPK {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hspk : SPKAt tr b r) (hpub : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedSPK b (DiffieHellman.dhPk r)) ∨
    (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j) :=
  pub_SPK_of_spqrInv hinv hspk hpub

theorem pub_PQ_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hpq : PQAt tr b r) (hpub : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk r)) ∨
    tr.EventLogged PQXDHEvent.BrokenKEM := by
  have hq₀ := hpq
  obtain ⟨t, rfl, _, hr64, _⟩ := hpq
  rcases Pub.inv_rand hinv hpub with
    ⟨p, ⟨_, ht, _⟩, _⟩ | ⟨b', ⟨_, ht, _⟩, _⟩ | ⟨b', hpq', he⟩ | ⟨b', ⟨_, ht, _⟩, _⟩ |
    ⟨hdh, _⟩ | ⟨_, hbkem⟩ | ⟨hrat, _⟩ | hmsg
  · have := (rnd_inj ht).2; omega
  · have := (rnd_inj ht).2; omega
  · cases PQAt.owner_unique hq₀ hpq'
    exact .inl he
  · have := (rnd_inj ht).2; omega
  · rcases hdh with ⟨_, _, ht, _⟩ | ⟨_, _, ht, _⟩ | ⟨_, _, ht, _⟩ |
      ⟨_, ht, _⟩ | ⟨_, ht, _⟩ | ⟨_, _, ht, _⟩ <;>
      (have := (rnd_inj ht).2; omega)
  · exact .inr hbkem
  · rcases hrat with ⟨_, ht, _⟩ | ⟨_, _, ht, _⟩ <;> (have := (rnd_inj ht).2; omega)
  · rcases hmsg with ⟨_, _, _, ht, _⟩ | ⟨t', n, msg, ht', _, _, hn2, _⟩
    · have := (rnd_inj ht).2; omega
    · have ht : t = t' + 1 := (rnd_inj ht').1
      have hidx : t' + 2 = t + 1 := by omega
      rw [hidx] at hn2
      exact (randAt_not_netAt hr64 hn2).elim

theorem pub_PQ {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hpq : PQAt tr b r) (hpub : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk r)) ∨
    tr.EventLogged PQXDHEvent.BrokenKEM :=
  pub_PQ_of_spqrInv hinv hpq hpub

theorem pub_OPK_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hopk : OPKAt tr b r) (hpub : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedOPK b (DiffieHellman.dhPk r)) ∨
    tr.EventLogged PQXDHEvent.BrokenDH := by
  have ho₀ := hopk
  obtain ⟨t, rfl, _, hev⟩ := hopk
  rcases Pub.inv_rand hinv hpub with
    ⟨p, hik, _⟩ | ⟨b', hspk, _⟩ | ⟨b', hpq, _⟩ | ⟨b', hopk', he⟩ |
    ⟨_, hbdh⟩ | ⟨⟨b', hpq⟩, _⟩ | ⟨hrat, _⟩ | hmsg
  · obtain ⟨t', ht', _, hev'⟩ := hik
    cases (rnd_inj ht').1
    cases evAt_unique hev hev'
  · obtain ⟨t', ht', _, hr64, _⟩ := hspk
    cases (rnd_inj ht').1
    exact (randAt_not_evAt hr64 hev).elim
  · exact (pqAt_ne_rnd32 hpq).elim
  · cases OPKAt.owner_unique ho₀ hopk'
    exact .inl he
  · exact .inr hbdh
  · exact (pqAt_ne_rnd32 hpq).elim
  · rcases hrat with ⟨t', ht', _, _, _, a, b', ikA, ikB, spk, pqpk, opk, ek, ct, keys, hn3, _, _⟩ |
      ⟨t', msg, ht', _, hn⟩
    · have ht : t = t' + 2 := (rnd_inj ht').1
      have hidx : t' + 3 = t + 1 := by omega
      rw [hidx] at hn3
      exact (netAt_not_evAt hn3 hev).elim
    · cases (rnd_inj ht').1
      exact (netAt_not_evAt hn hev).elim
  · rcases hmsg with ⟨t', n, msg, ht', _, hr1, _, _⟩ | ⟨t', n, msg, ht', _, _, hn2, _⟩
    · cases (rnd_inj ht').1
      exact (randAt_not_evAt hr1 hev).elim
    · have ht : t = t' + 1 := (rnd_inj ht').1
      have hidx : t' + 2 = t + 1 := by omega
      rw [hidx] at hn2
      exact (netAt_not_evAt hn2 hev).elim

theorem pub_OPK {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hopk : OPKAt tr b r) (hpub : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedOPK b (DiffieHellman.dhPk r)) ∨
    tr.EventLogged PQXDHEvent.BrokenDH :=
  pub_OPK_of_spqrInv hinv hopk hpub

theorem pub_EK_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {t : Nat}
    (h : AliceSlot tr t) (hpub : Pub tr (rnd t 32)) :
    ∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j := by
  obtain ⟨_, hr1, hr2, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h
  rcases Pub.inv_rand hinv hpub with
    ⟨p, ⟨t', ht', _, hev⟩, _⟩ | ⟨b, ⟨t', ht', _, hr64, _⟩, _⟩ | ⟨b, hpq, _⟩ |
    ⟨b, ⟨t', ht', _, hev⟩, _⟩ | ⟨_, hbdh⟩ | ⟨⟨b, hpq⟩, _⟩ | ⟨hrat, _⟩ | hmsg
  · cases (rnd_inj ht').1
    exact (randAt_not_evAt hr1 hev).elim
  · cases (rnd_inj ht').1
    have := randAt_unique hr1 hr64
    omega
  · exact (pqAt_ne_rnd32 hpq).elim
  · cases (rnd_inj ht').1
    exact (randAt_not_evAt hr1 hev).elim
  · exact hbdh
  · exact (pqAt_ne_rnd32 hpq).elim
  · rcases hrat with ⟨t', ht', _, _, _, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, hn3, _, _⟩ |
      ⟨t', msg, ht', _, hn⟩
    · have ht : t = t' + 2 := (rnd_inj ht').1
      have hidx : t' + 3 = t + 1 := by omega
      rw [hidx] at hn3
      exact (randAt_not_netAt hr1 hn3).elim
    · cases (rnd_inj ht').1
      exact (randAt_not_netAt hr1 hn).elim
  · rcases hmsg with ⟨t', n, msg, ht', _, _, hn2, _⟩ | ⟨t', n, msg, ht', _, _, hn2, _⟩
    · cases (rnd_inj ht').1
      exact (randAt_not_netAt hr2 hn2).elim
    · have ht : t = t' + 1 := (rnd_inj ht').1
      have hidx : t' + 2 = t + 1 := by omega
      rw [hidx] at hn2
      exact (randAt_not_netAt hr1 hn2).elim

theorem pub_EK {tr : ExecTrace} (hinv : SpqrInv tr) {t : Nat}
    (h : AliceSlot tr t) (hpub : Pub tr (rnd t 32)) :
    ∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j :=
  pub_EK_of_spqrInv hinv h hpub

theorem pub_agree_dhPk_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {s1 s2 : Bytes}
    (h : Pub tr (agree (DiffieHellman.dhPk s1) s2)) :
    Pub tr s1 ∨ Pub tr s2 := by
  unfold agree at h
  rw [x25519Key_dhPk] at h
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh, DiffieHellman.dhPk,
    DiffieHellman.CanDH.dhPk] at h
  simp only [BytesView.view_pack] at h
  split at h
  · rcases Pub.inv_dhPack hinv h with hs2 | ⟨s, heq, hs⟩
    · exact .inr hs2
    · obtain rfl := dhPk_inj heq
      exact .inl hs
  · rcases Pub.inv_dhPack hinv h with hs1 | ⟨s, heq, hs⟩
    · exact .inl hs1
    · obtain rfl := dhPk_inj heq
      exact .inr hs

theorem pub_agree_dhPk {tr : ExecTrace} (hinv : SpqrInv tr) {s1 s2 : Bytes}
    (h : Pub tr (agree (DiffieHellman.dhPk s1) s2)) :
    Pub tr s1 ∨ Pub tr s2 :=
  pub_agree_dhPk_of_spqrInv hinv h

/-! ## Unobservability of KEM encapsulation coins -/

namespace HsClassHelpers

theorem not_ikAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    {p : Participant} (h : IKAt tr p (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, hr2, _⟩ := hs
  obtain ⟨t', ht', _, hev⟩ := h
  have : t' = t + 1 := (rnd_inj ht').1.symm
  subst this
  exact randAt_not_evAt hr2 hev

theorem not_spkAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    {b : Participant} (h : SPKAt tr b (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, hr2, _⟩ := hs
  obtain ⟨t', ht', _, hr64, _⟩ := h
  have : t' = t + 1 := (rnd_inj ht').1.symm
  subst this
  have := randAt_unique hr2 hr64
  omega

theorem not_opkAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    {b : Participant} (h : OPKAt tr b (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, hr2, _⟩ := hs
  obtain ⟨t', ht', _, hev⟩ := h
  have : t' = t + 1 := (rnd_inj ht').1.symm
  subst this
  exact randAt_not_evAt hr2 hev

theorem not_ekAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    (h : EKAt tr (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, _, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, hn3, _, _⟩ := hs
  obtain ⟨t', ht', _, _, hr2', _⟩ := h
  have ht : t' = t + 1 := (rnd_inj ht').1.symm
  have hidx : t' + 2 = t + 3 := by omega
  rw [hidx] at hr2'
  exact randAt_not_netAt hr2' hn3

theorem not_ratchetAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    (h : RatchetAt tr (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, hr2, _⟩ := hs
  obtain ⟨t', ht', _, _, _, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, hn3', _, _⟩ := h
  have ht : t + 1 = t' + 2 := (rnd_inj ht').1
  have hidx : t' + 3 = t + 2 := by omega
  rw [hidx] at hn3'
  exact randAt_not_netAt hr2 hn3'

theorem not_trRatchetAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    (h : TRRatchetAt tr (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, hr2, _⟩ := hs
  obtain ⟨t', msg, ht', _, hn1'⟩ := h
  have ht : t' = t + 1 := (rnd_inj ht').1.symm
  subst ht
  exact randAt_not_netAt hr2 hn1'

theorem not_msgEncRandAt_coins {tr : ExecTrace} {t : Nat} (hs : AliceSlot tr t)
    (h : MsgEncRandAt tr (rnd (t + 1) 32)) : False := by
  obtain ⟨_, _, hr2, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, _, hn4, _⟩ := hs
  rcases h with ⟨t', n, msg, ht', _, _, _, ev, hev3⟩ |
    ⟨t', n, msg, ht', _, _, hn2, _⟩
  · have ht : t' = t + 1 := (rnd_inj ht').1.symm
    have hidx : t' + 3 = t + 4 := by omega
    rw [hidx] at hev3
    exact netAt_not_trEvAt hn4 hev3
  · have ht : t' = t := by have := (rnd_inj ht').1; omega
    subst ht
    exact randAt_not_netAt hr2 hn2

end HsClassHelpers

theorem not_pub_coins_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {t : Nat}
    (hs : AliceSlot tr t) :
    ¬ Pub tr (rnd (t + 1) 32) := by
  intro h
  rcases Pub.inv_rand hinv h with
    ⟨p, hik, _⟩ | ⟨b, hspk, _⟩ | ⟨b, hpq, _⟩ | ⟨b, hopk, _⟩ |
    ⟨hdh, _⟩ | ⟨⟨b, hpq⟩, _⟩ | ⟨hrat, _⟩ | hmsg
  · exact not_ikAt_coins hs hik
  · exact not_spkAt_coins hs hspk
  · exact pqAt_ne_rnd32 hpq
  · exact not_opkAt_coins hs hopk
  · rcases hdh with ⟨p, hik⟩ | ⟨b, hspk⟩ | ⟨b, hopk⟩ | hek | hrat | htrrat
    · exact not_ikAt_coins hs hik
    · exact not_spkAt_coins hs hspk
    · exact not_opkAt_coins hs hopk
    · exact not_ekAt_coins hs hek
    · exact not_ratchetAt_coins hs hrat
    · exact not_trRatchetAt_coins hs htrrat
  · exact pqAt_ne_rnd32 hpq
  · rcases hrat with hrat | htrrat
    · exact not_ratchetAt_coins hs hrat
    · exact not_trRatchetAt_coins hs htrrat
  · exact not_msgEncRandAt_coins hs hmsg

/-- Under `SpqrInv tr`, the KEM encapsulation coins `rnd (t + 1) 32` of an `AliceSlot` are never in
`Pub tr`. -/
theorem not_pub_coins {tr : ExecTrace} (hinv : SpqrInv tr) {t : Nat}
    (h : AliceSlot tr t) :
    ¬ Pub tr (rnd (t + 1) 32) :=
  not_pub_coins_of_spqrInv hinv h

end Symbolic.Swarm.COMPOSED.CompInv
