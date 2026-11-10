/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Specifications.Refinement.TraceExplanation
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompRatchet
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Responder Session Identifier Freshness

Proves `bobStart_sid_fresh_of_link`: if a fresh `bobHandshake` output has base key
`o.ek ∉ bobDoneBaseKeys T`, then no prior receiver event or stored `TRState` on a reachable
trace `T` shares the responder session identifier `concat (normalizeX25519Key rkey) o.keys.rk`.
Equal root keys imply equal PQXDH DH2 and DH3 shared secrets, pinning `ek` on symbolic terms
since an identity secret never coincides with a signed-prekey secret of the same participant.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm agree isCanonicalKey)
open Symbolic.Swarm.COMPOSED.CompTermAlgebra (dhPk_inj dh_eq_dh_dhPk_cases dh_eq_of_sk_ne
  pqxdhKdf_rk_inj pqxdhIkm_inj_parts x25519Key_of_isCanonicalKey)
open Symbolic.Swarm.COMPOSED.CompInv (BobDoneFacts IKAt SPKAt RandAt rnd_inj)
open DY.Libsignal.TripleRatchet (SessionInfo)
open DY.Libsignal.TripleRatchet (TRState TREvent)

/-- `fun pk => dh pk sk` is injective on symbolic terms. -/
theorem dh_pk_inj_of_sk {pk₁ pk₂ sk : Bytes} (h : dh pk₁ sk = dh pk₂ sk) : pk₁ = pk₂ := by
  have hpack₂ := Bytes.pack_view? DiffieHellman.DhPk.SubF pk₂
  rcases hpk₂ : pk₂.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
  · have hpack₁ := Bytes.pack_view? DiffieHellman.DhPk.SubF pk₁
    rcases hpk₁ : pk₁.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨b⟩⟩
    · have hview := congrArg (fun x : Bytes => x.view? DiffieHellman.Dh.SubF) h
      dsimp only [dh, CanDH.dh] at hview
      rw [hpk₁, hpk₂] at hview
      simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hview
      exact hview.1
    · rw [hpk₁] at hpack₁
      have hpk₁_eq : pk₁ = dhPk b := hpack₁.symm
      subst hpk₁_eq
      rcases dh_eq_dh_dhPk_cases h.symm with ⟨hpk, _⟩ | ⟨hpk, _⟩ <;>
      · rw [hpk] at hpk₂
        simp only [dhPk, CanDH.dhPk, BytesView.view_pack] at hpk₂
        cases hpk₂
  · rw [hpk₂] at hpack₂
    have hpk₂_eq : pk₂ = dhPk a := hpack₂.symm
    subst hpk₂_eq
    rcases dh_eq_dh_dhPk_cases h with ⟨hpk, _⟩ | ⟨hpk, rfl⟩
    · exact hpk
    · exact hpk

/-- Equal DH2 and DH3 shared secrets pin the base key whenever `sB₁ ≠ sS₁`. -/
theorem ek_eq_of_dh2_dh3 {ek₁ ek₂ sB₁ sB₂ sS₁ sS₂ : Bytes} (hBS : sB₁ ≠ sS₁)
    (h2 : dh ek₁ sB₁ = dh ek₂ sB₂) (h3 : dh ek₁ sS₁ = dh ek₂ sS₂) : ek₁ = ek₂ := by
  by_cases hB : sB₁ = sB₂
  · subst hB
    exact dh_pk_inj_of_sk h2
  · obtain ⟨he₁, he₂⟩ := dh_eq_of_sk_ne hB h2
    rw [he₁, he₂] at h3
    rcases dh_eq_dh_dhPk_cases h3 with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd (dhPk_inj h).symm hB
    · exact absurd h.symm hBS

theorem ikAt_spkAt_ne {T : ExecTrace} {b : Participant} {sB sS : Bytes}
    (hI : IKAt T b sB) (hS : SPKAt T b sS) : sB ≠ sS := by
  rintro rfl
  obtain ⟨t, rfl, -, hev⟩ := hI
  obtain ⟨t', ht', -, hr, -⟩ := hS
  obtain ⟨rfl, -⟩ := rnd_inj ht'
  unfold RandAt at hr
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  rw [Trace.at?_eq_some] at hr hev
  obtain ⟨_, hr⟩ := hr
  obtain ⟨_, hev⟩ := hev
  rw [hr] at hev
  cases hev

theorem bobHandshake_run_snd (b a : Participant) (kh : PQXDH.BobKeyHandles)
    (regIdxA ekIdx ctIdx : Nat) (tr : ExecTrace) :
    ((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run tr).2.val = tr := by
  have hpure : (((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx >>=
      fun _ => (pure () : Traceful Unit))).run tr).2.val =
      ((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run tr).2.val := by
    rw [Traceful.run_bind]; rcases (PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run tr with
      ⟨_ | _, _⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
  rw [← hpure]
  exact Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at (Inv := fun t => t = tr)
    b a kh regIdxA ekIdx ctIdx tr rfl fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl

theorem bobHandshake_run_keys {T : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regIdxA ekIdx ctIdx : Nat} {o : PQXDH.BobHandshakeOut}
    (ho : ((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run T).1 = some o) :
    isCanonicalKey o.ek = true ∧ ∃ (sB sS dh1 ss : Bytes) (dh4 : Option Bytes),
      o.keys = pqxdhKdf (pqxdhIkm dh1 (agree o.ek sB) (agree o.ek sS) dh4 ss) := by
  classical
  let Goal : Prop := isCanonicalKey o.ek = true ∧ ∃ (sB sS dh1 ss : Bytes) (dh4 : Option Bytes),
      o.keys = pqxdhKdf (pqxdhIkm dh1 (agree o.ek sB) (agree o.ek sS) dh4 ss)
  let Inv (t : ExecTrace) : Prop := t = T ∨ Goal
  let f (o' : PQXDH.BobHandshakeOut) : Traceful Unit :=
    if o' = o then Random.genRand 32 >>= fun _ => pure () else pure ()
  have hstep : Inv (((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx >>= f).run T).2.val) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at b a kh regIdxA ekIdx ctIdx T
      (Or.inl rfl) (fun ikB spkSk pqsk opkSk ikA _vkA ek ct _hon keys _ _ _ _ _ _ _ hcan hagree => ?_)
    dsimp only [f]; split
    · next heq =>
      refine Or.inr ?_
      subst heq
      refine ⟨hcan, ?_⟩
      unfold PQXDH.bobAgreement at hagree
      dsimp only at hagree
      refine ⟨ikB, spkSk, agree ikA spkSk,
        (PQXDH.errToOption (PQKem.kemDecap pqsk ct)).getD (PQKem.kemRejKey pqsk ct),
        opkSk.map (agree ek ·), ?_⟩
      exact (Option.some.inj hagree).symm
    · exact Or.inl (by rw [Symbolic.DYBridge.DY.Traceful.run_eq_1]; rfl)
  have htr_eq : (((Random.genRand 32 >>= fun _ => pure () : Traceful Unit).run T).2.val) =
      T.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32) := by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
    rfl
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, ho] at hstep
  dsimp only at hstep
  rw [bobHandshake_run_snd] at hstep
  dsimp only [f] at hstep
  rw [ite_eq_left_iff.mpr fun h => absurd rfl h, htr_eq] at hstep
  rcases hstep with heq | hgoal
  · have hlen := congrArg Trace.length heq
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hlen
  · exact hgoal

/-- A logged `BobDone` event and a fresh `bobHandshake` output with equal root key `rk` have
equal base keys. -/
theorem bobDone_ek_eq_of_rk_eq_out {T : ExecTrace} {b a₁ : Participant}
    {ikB₁ ikA₁ spk₁ pq₁ ek₁ ct₁ ek₂ sB₂ sS₂ dh1₂ ss₂ : Bytes} {opk₁ dh4₂ : Option Bytes}
    {keys₁ keys₂ : HandshakeKeys} {i₁ : Nat}
    (h₁ : BobDoneFacts T b a₁ ikB₁ ikA₁ spk₁ pq₁ opk₁ ek₁ ct₁ keys₁ i₁)
    (hc₂ : isCanonicalKey ek₂ = true)
    (hk₂ : keys₂ = pqxdhKdf (pqxdhIkm dh1₂ (agree ek₂ sB₂) (agree ek₂ sS₂) dh4₂ ss₂))
    (hrk : keys₁.rk = keys₂.rk) : ek₁ = ek₂ := by
  obtain ⟨sB₁, sS₁, _sQ₁, _o₁, _e₁, hI₁, -, hS₁, -, -, -, -, -, hc₁, -, hk₁, -, -⟩ := h₁
  rw [hk₁, hk₂] at hrk
  obtain ⟨-, h2, h3, -⟩ := pqxdhIkm_inj_parts (pqxdhKdf_rk_inj hrk)
  unfold agree at h2 h3
  rw [x25519Key_of_isCanonicalKey hc₁, x25519Key_of_isCanonicalKey hc₂] at h2 h3
  exact ek_eq_of_dh2_dh3 (ikAt_spkAt_ne hI₁ hS₁) h2 h3

/-- Every responder `HandshakeSession s d` on `tr` corresponds to a `BobDone` event at `d`
whose root key `keys.rk` is the second component of `s.sid`. -/
def BobSidLink (tr : ExecTrace) : Prop :=
  ∀ (s : SessionInfo) (d : Nat), tr.EventLogged (ComposedEvent.HandshakeSession s d) →
    s.initiator = false → ∃ (pk : Bytes) (a : Participant) (ikB ikA spk pqpk ek ct : Bytes)
      (opk : Option Bytes) (keys : HandshakeKeys),
      tr.EventLoggedAt (PQXDHEvent.BobDone s.me a ikB ikA spk pqpk opk ek ct keys) d ∧
      s.sid = DY.Concat.concat (X25519.normalizeX25519Key pk) keys.rk

theorem concat_inj_parts {a₁ b₁ a₂ b₂ : Bytes}
    (h : DY.Concat.concat a₁ b₁ = DY.Concat.concat a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 := congrArg (fun x => x.view? DY.Concat.Concat.SubF) h
  change Bytes.view? (({ lhs := a₁, rhs := b₁ } : DY.Concat.Concat.SubF DY.Bytes).pack)
      DY.Concat.Concat.SubF =
    Bytes.view? (({ lhs := a₂, rhs := b₂ } : DY.Concat.Concat.SubF DY.Bytes).pack)
      DY.Concat.Concat.SubF at h1
  rw [BytesView.view_pack, BytesView.view_pack, Option.some.injEq] at h1
  cases h1
  exact ⟨rfl, rfl⟩

theorem mem_bobDoneBaseKeys_of {T : ExecTrace} {b a : Participant}
    {ikB ikA spk pqpk ek ct : Bytes} {opk : Option Bytes} {keys : HandshakeKeys} {d : Nat}
    (h : T.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) d) :
    ek ∈ DY.Libsignal.Composed.Refinement.bobDoneBaseKeys T := by
  simp only [DY.Libsignal.Composed.Refinement.bobDoneBaseKeys, List.mem_filterMap,
    List.mem_range]
  have hlt : d < T.length := by
    have h' := h
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h'
    rw [Trace.at?_eq_some] at h'
    exact h'.1
  refine ⟨d, hlt, ?_⟩
  have hget : T.getEventAt PQXDHEvent d =
      some (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) := by
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
    rw [h]
  rw [hget]

theorem bobStart_no_handshakeSession {T : ExecTrace}
    (hreach : T.Reachable DY.Libsignal.Composed.reachability) (hlink : BobSidLink T)
    {b a : Participant} {kh : PQXDH.BobKeyHandles} {regIdxA ekIdx ctIdx : Nat}
    {o : PQXDH.BobHandshakeOut}
    (ho : ((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run T).1 = some o)
    (hek : o.ek ∉ DY.Libsignal.Composed.Refinement.bobDoneBaseKeys T)
    (rkey : Bytes) (d : Nat) :
    ¬ T.EventLogged (ComposedEvent.HandshakeSession
      ⟨DY.Concat.concat (X25519.normalizeX25519Key rkey) o.keys.rk, false, b, a⟩ d) := by
  intro hhs
  obtain ⟨pk, a', ikB, ikA, spk, pqpk, ek, ct, opk, keys, hbd, hsid⟩ := hlink _ d hhs rfl
  have hrk : o.keys.rk = keys.rk := (concat_inj_parts hsid).2
  obtain ⟨hcan, sB, sS, dh1, ss, dh4, hk⟩ := bobHandshake_run_keys ho
  have hfacts := (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach).bobDone
    _ _ _ _ _ _ _ _ _ _ _ hbd
  have hek' : ek = o.ek := bobDone_ek_eq_of_rk_eq_out hfacts hcan hk hrk.symm
  exact hek (hek' ▸ mem_bobDoneBaseKeys_of hbd)

/-- Session-identifier freshness for `bobStart` from `BobSidLink` and `o.ek ∉ bobDoneBaseKeys T`. -/
theorem bobStart_sid_fresh_of_link {T : ExecTrace}
    (hreach : T.Reachable DY.Libsignal.Composed.reachability) (hlink : BobSidLink T)
    {b a : Participant} {kh : PQXDH.BobKeyHandles} {regIdxA ekIdx ctIdx : Nat}
    {o : PQXDH.BobHandshakeOut}
    (ho : ((PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run T).1 = some o)
    (hek : o.ek ∉ DY.Libsignal.Composed.Refinement.bobDoneBaseKeys T)
    (rkey : Bytes) :
    let s : SessionInfo := ⟨DY.Concat.concat (X25519.normalizeX25519Key rkey) o.keys.rk, false, b, a⟩
    ((∀ seed pqSalt n r pIdx i, ¬ T.EventLoggedAt
        (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i) ∧
      (∀ pk n seed r srcIdx i, ¬ T.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed r srcIdx) i)) ∧
    (∀ q j st, ((PersistentLocalState.getLocalState q j : Traceful TRState).run T).1 = some st →
      st.sessionInfo q ≠ s) := by
  intro s
  have hno := bobStart_no_handshakeSession hreach hlink ho hek rkey
  have horig := Symbolic.Swarm.COMPOSED.CompRatchet.compSessionOriginInv_reachable hreach
  refine ⟨⟨fun seed pqSalt n r pIdx i hev => ?_,
    fun pk n seed r srcIdx i hev => ?_⟩, fun q j st hst hs => ?_⟩
  · obtain ⟨d, keys, hhs, -⟩ := horig.mkSession _ _ _ _ _ _ _ ⟨i, hev⟩
    exact hno d hhs
  · obtain ⟨-, d, keys, hhs, -⟩ := horig.skippedOK _ _ _ _ _ _ ⟨i, hev⟩
    exact hno d hhs
  · have hst' : DY.Libsignal.TripleRatchet.Cheval.StateStoredAt q st j T := by
      rw [Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_fst] at hst
      unfold DY.Libsignal.TripleRatchet.Cheval.StateStoredAt
      rcases hat : (T.at? j : Option Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩
      · rw [hat] at hst; cases hst
      · rw [hat] at hst
        dsimp only at hst
        by_cases hp : p = q
        · subst hp
          simp only [ite_true, Option.some.injEq] at hst
          subst hst
          rfl
        · simp only [hp, ite_false, reduceCtorEq] at hst
    obtain ⟨-, -, ⟨d, keys, hhs, -⟩, -⟩ := horig.storedOK q st j hst'
    rw [hs] at hhs
    exact hno d hhs

end Symbolic.Swarm.CREF.TR
