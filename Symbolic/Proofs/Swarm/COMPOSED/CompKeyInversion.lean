/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra

/-!
# Composed Key-Schedule Inversion and Secrecy Query Reductions

Proves generic `pqxdhIkm` and per-block `pqxdhKdf` inversion lemmas over an arbitrary closure
and atomic exposure set, and reduces `AliceInitiatorSecrecyQuery` and `BobResponderSecrecyQuery`
in the composed model to invariant contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompKeyInversion

open DY DY.Comparse DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTermAlgebra

/-! ## Generic `pqxdhKdf` and `pqxdhIkm` Inversion -/

section GenericInversion

variable {C E : Bytes → Prop}

theorem pqxdhIkm_inv_generic
    (hcat : ∀ {l r : Bytes}, C (concat l r) → C l ∧ C r)
    {dh1 dh2 dh3 : Bytes} {dh4 : Option Bytes} {ss : Bytes}
    (h : C (pqxdhIkm dh1 dh2 dh3 dh4 ss)) :
    C dh1 ∧ C dh2 ∧ C dh3 ∧ (∀ d, dh4 = some d → C d) ∧ C ss := by
  unfold pqxdhIkm at h
  obtain ⟨_, h1⟩ := hcat h
  obtain ⟨hdh1, h2⟩ := hcat h1
  obtain ⟨hdh2, h3⟩ := hcat h2
  obtain ⟨hdh3, htail⟩ := hcat h3
  refine ⟨hdh1, hdh2, hdh3, ?_⟩
  cases dh4 with
  | none =>
    exact ⟨(by intro d hd; cases hd), htail⟩
  | some d₀ =>
    obtain ⟨hd₀, hss⟩ := hcat htail
    refine ⟨?_, hss⟩
    rintro d ⟨rfl⟩
    exact hd₀

/-- If `k` is a block of `pqxdhKdf ikm` in `C` and `hmac zeroSalt ikm` is not in `E`, then
`C ikm` or `E k` holds. -/
theorem pqxdhKdf_block_inv_generic
    (hkdf : ∀ {s m : Bytes}, C (kdfExtract s m) → E (kdfExtract s m) ∨ (C s ∧ C m))
    {ikm k : Bytes}
    (hnot_prk : ¬ E (hmac zeroSalt ikm))
    (hblk : IsHandshakeBlock (pqxdhKdf ikm) k)
    (hCk : C k) :
    C ikm ∨ E k := by
  rcases hblk with rfl | rfl | rfl
  · rcases hkdf hCk with hE | ⟨hprk, _⟩
    · exact .inr hE
    · rcases hkdf hprk with hE_prk | ⟨_, hikm⟩
      · exact False.elim (hnot_prk hE_prk)
      · exact .inl hikm
  · rcases hkdf hCk with hE | ⟨hprk, _⟩
    · exact .inr hE
    · rcases hkdf hprk with hE_prk | ⟨_, hikm⟩
      · exact False.elim (hnot_prk hE_prk)
      · exact .inl hikm
  · rcases hkdf hCk with hE | ⟨hprk, _⟩
    · exact .inr hE
    · rcases hkdf hprk with hE_prk | ⟨_, hikm⟩
      · exact False.elim (hnot_prk hE_prk)
      · exact .inl hikm

theorem keyKnown_block_inv_generic {tr : ExecTrace}
    (hkdf : ∀ {s m : Bytes}, C (kdfExtract s m) → E (kdfExtract s m) ∨ (C s ∧ C m))
    (hcat : ∀ {l r : Bytes}, C (concat l r) → C l ∧ C r)
    {dh1 dh2 dh3 : Bytes} {dh4 : Option Bytes} {ss ikm : Bytes}
    {keys : HandshakeKeys} {k : Bytes}
    (hikm : ikm = pqxdhIkm dh1 dh2 dh3 dh4 ss)
    (hkeys : keys = pqxdhKdf ikm)
    (hnot_prk : ¬ E (hmac zeroSalt ikm))
    (hexp : E k → SessionStateExposed tr keys k)
    (hblk : IsHandshakeBlock keys k)
    (hCk : C k) :
    (C dh1 ∧ C dh2 ∧ C dh3 ∧ (∀ d, dh4 = some d → C d) ∧ C ss) ∨
      SessionStateExposed tr keys k := by
  subst hkeys
  rcases pqxdhKdf_block_inv_generic hkdf hnot_prk hblk hCk with hikmC | hEk
  · rw [hikm] at hikmC
    exact .inl (pqxdhIkm_inv_generic hcat hikmC)
  · exact .inr (hexp hEk)

end GenericInversion

/-! ## Handshake Secrecy Query Reductions -/

abbrev rnd (t n : Nat) : Bytes :=
  ({ timestamp := t, size := n } : Random.Random Bytes).pack

section SecrecyReductions

variable {tr : ExecTrace} {Pub : Bytes → Prop}
variable {IKAt : Participant → Bytes → Prop}
variable {SPKAt : Participant → Bytes → Prop}
variable {PQAt : Participant → Bytes → Prop}
variable {OPKAt : Participant → Bytes → Prop}
variable {CompAliceSlot : Nat → Prop}

/-- Reduces `AliceInitiatorSecrecyQuery` to closure, key-classification, and `AliceDone` contracts. -/
theorem responderSecrecyQuery_of_contracts
    (hpub_of_knows : ∀ {x : Bytes}, x.AttackerKnows tr → Pub x)
    (hpub_block_inv : ∀ {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss : Bytes}
      {keys : HandshakeKeys} {k : Bytes},
      keys = pqxdhKdf (pqxdhIkm d1 d2 d3 d4 ss) →
      IsHandshakeBlock keys k → Pub k →
      (Pub d1 ∧ Pub d2 ∧ Pub d3 ∧ (∀ d, d4 = some d → Pub d) ∧ Pub ss) ∨
        SessionStateExposed tr keys k)
    (hpub_agree_dhPk : ∀ {s1 s2 : Bytes}, Pub (agree (dhPk s1) s2) → Pub s1 ∨ Pub s2)
    (hinv_ss : ∀ {pk e : Bytes}, Pub (kemEncap pk e).2 →
      (Pub pk ∧ Pub e) ∨ (∃ sk, pk = kemPk sk ∧ Pub sk))
    (hnot_pub_coins : ∀ {t : Nat}, CompAliceSlot t → ¬ Pub (rnd (t + 1) 32))
    (hpub_IK : ∀ {p : Participant} {r : Bytes}, IKAt p r → Pub r →
      (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK p (dhPk r)) j) ∨
      (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j))
    (hpub_SPK : ∀ {b : Participant} {r : Bytes}, SPKAt b r → Pub r →
      tr.EventLogged (PQXDHEvent.CompromisedSPK b (dhPk r)) ∨
      (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j))
    (hpub_PQ : ∀ {b : Participant} {r : Bytes}, PQAt b r → Pub r →
      tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (kemPk r)) ∨
      tr.EventLogged PQXDHEvent.BrokenKEM)
    (hpub_EK : ∀ {t : Nat}, CompAliceSlot t → Pub (rnd t 32) →
      ∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j)
    (haliceDone : ∀ a b ikA ikB spk pqpk opk ek ct keys i,
      tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
      ∃ t sA, i = t + 5 ∧ CompAliceSlot t ∧ IKAt a sA ∧ ikA = dhPk sA ∧ ek = dhPk (rnd t 32) ∧
        (ct, keys) = aliceAgreement sA (rnd t 32) ikB spk pqpk opk (rnd (t + 1) 32) ∧
        ((∃ sB sS sQ, IKAt b sB ∧ ikB = dhPk sB ∧ SPKAt b sS ∧ spk = dhPk sS ∧
            PQAt b sQ ∧ pqpk = kemPk sQ) ∨
         LoggedBefore (PQXDHEvent.CompromisedIK b ikB) i tr ∨
         LoggedBefore PQXDHEvent.BrokenDH i tr)) :
    DY.Libsignal.PQXDH.AliceInitiatorSecrecyQuery tr (fun t => t.AttackerKnows tr) := by
  intro a b ikA ikB spk pqpk opk ek ct keys i hev k hblk hkk
  obtain ⟨t, sA, rfl, hslot, _hA, _hikA, _hek, hagr, hbundle⟩ :=
    haliceDone a b ikA ikB spk pqpk opk ek ct keys i hev
  rcases hbundle with ⟨sB, sS, sQ, hB, rfl, hS, rfl, hQ, rfl⟩ | ⟨j, hj, hlt⟩ | ⟨j, hj, hlt⟩
  rotate_left
  · exact .inl (.inl ⟨j, hj, .inl hlt⟩)
  · exact .inl (.inr ⟨j, hj, .inl hlt⟩)
  have hkeys : keys = pqxdhKdf (pqxdhIkm (agree (dhPk sS) sA) (agree (dhPk sB) (rnd t 32))
      (agree (dhPk sS) (rnd t 32)) (opk.map (agree · (rnd t 32)))
      (kemEncap (kemPk sQ) (rnd (t + 1) 32)).2) := by
    rcases hE : kemEncap (kemPk sQ) (rnd (t + 1) 32) with ⟨c, s⟩
    simp only [aliceAgreement, hE, Prod.mk.injEq] at hagr
    exact hagr.2
  rcases hpub_block_inv hkeys hblk (hpub_of_knows hkk) with
    ⟨_, hd2, hd3, _, hss⟩ | hexp
  · have hPQ : tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (kemPk sQ)) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM := by
      rcases hinv_ss hss with ⟨_, hc⟩ | ⟨sk, hsk, hpk⟩
      · exact absurd hc (hnot_pub_coins hslot)
      · obtain rfl := kemPk_inj hsk
        exact hpub_PQ hQ hpk
    rcases hpub_agree_dhPk hd2 with h2 | h2
    · rcases hpub_IK hB h2 with ⟨j, hj⟩ | ⟨j, hj⟩
      · rcases hpub_agree_dhPk hd3 with h3 | h3
        · rcases hpub_SPK hS h3 with hcs | ⟨j', hj'⟩
          · exact .inl (.inl ⟨j, hj, .inr ⟨hcs, hPQ⟩⟩)
          · exact .inl (.inr ⟨j', hj', .inr hPQ⟩)
        · obtain ⟨j', hj'⟩ := hpub_EK hslot h3
          exact .inl (.inr ⟨j', hj', .inr hPQ⟩)
      · exact .inl (.inr ⟨j, hj, .inr hPQ⟩)
    · obtain ⟨j, hj⟩ := hpub_EK hslot h2
      exact .inl (.inr ⟨j, hj, .inr hPQ⟩)
  · exact .inr hexp

/-- Reduces `BobResponderSecrecyQuery` to closure, key-classification, `AliceDone`/`BobDone`, and
OPK-ordering contracts. -/
theorem initiatorSecrecyQuery_of_contracts
    (hpub_of_knows : ∀ {x : Bytes}, x.AttackerKnows tr → Pub x)
    (hpub_block_inv : ∀ {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss : Bytes}
      {keys : HandshakeKeys} {k : Bytes},
      keys = pqxdhKdf (pqxdhIkm d1 d2 d3 d4 ss) →
      IsHandshakeBlock keys k → Pub k →
      (Pub d1 ∧ Pub d2 ∧ Pub d3 ∧ (∀ d, d4 = some d → Pub d) ∧ Pub ss) ∨
        SessionStateExposed tr keys k)
    (hpub_agree_dhPk : ∀ {s1 s2 : Bytes}, Pub (agree (dhPk s1) s2) → Pub s1 ∨ Pub s2)
    (hinv_ss : ∀ {pk e : Bytes}, Pub (kemEncap pk e).2 →
      (Pub pk ∧ Pub e) ∨ (∃ sk, pk = kemPk sk ∧ Pub sk))
    (hnot_pub_coins : ∀ {t : Nat}, CompAliceSlot t → ¬ Pub (rnd (t + 1) 32))
    (hpub_IK : ∀ {p : Participant} {r : Bytes}, IKAt p r → Pub r →
      tr.EventLogged (PQXDHEvent.CompromisedIK p (dhPk r)) ∨
      tr.EventLogged PQXDHEvent.BrokenDH)
    (hpub_SPK : ∀ {b : Participant} {r : Bytes}, SPKAt b r → Pub r →
      tr.EventLogged (PQXDHEvent.CompromisedSPK b (dhPk r)) ∨
      tr.EventLogged PQXDHEvent.BrokenDH)
    (hpub_PQ : ∀ {b : Participant} {r : Bytes}, PQAt b r → Pub r →
      tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (kemPk r)) ∨
      tr.EventLogged PQXDHEvent.BrokenKEM)
    (hpub_OPK : ∀ {b : Participant} {r : Bytes}, OPKAt b r → Pub r →
      tr.EventLogged (PQXDHEvent.CompromisedOPK b (dhPk r)) ∨
      tr.EventLogged PQXDHEvent.BrokenDH)
    (hpub_EK : ∀ {t : Nat}, CompAliceSlot t → Pub (rnd t 32) →
      tr.EventLogged PQXDHEvent.BrokenDH)
    (haliceDone : ∀ a b ikA ikB spk pqpk opk ek ct keys i,
      tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
      ∃ t sA, i = t + 5 ∧ CompAliceSlot t ∧ IKAt a sA ∧ ikA = dhPk sA ∧ ek = dhPk (rnd t 32) ∧
        (ct, keys) = aliceAgreement sA (rnd t 32) ikB spk pqpk opk (rnd (t + 1) 32))
    (hbobDone : ∀ b a ikB ikA spk pqpk opk ek ct keys i,
      tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
      ∃ sB sS sQ o ss,
        IKAt b sB ∧ ikB = dhPk sB ∧
        SPKAt b sS ∧ spk = dhPk sS ∧
        PQAt b sQ ∧ pqpk = kemPk sQ ∧
        (∀ x, o = some x → OPKAt b x) ∧ opk = o.map dhPk ∧
        ss = (DY.Libsignal.PQXDH.errToOption (kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct) ∧
        keys = pqxdhKdf (pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) ss) ∧
        ((∃ j a' b' spk' opk', j < i ∧
            tr.EventLoggedAt (PQXDHEvent.AliceDone a' b' ikA ikB spk' pqpk opk' ek ct keys) j) ∨
         LoggedBefore (PQXDHEvent.CompromisedIK a ikA) i tr ∨
         LoggedBefore (PQXDHEvent.CompromisedSPK b spk) i tr ∨
         LoggedBefore PQXDHEvent.BrokenDH i tr))
    (hcompOpk_before : ∀ {b a ikB ikA spk pqpk o ek ct keys i},
      tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk (some o) ek ct keys) i →
      tr.EventLogged (PQXDHEvent.CompromisedOPK b o) →
      LoggedBefore (PQXDHEvent.CompromisedOPK b o) i tr) :
    DY.Libsignal.PQXDH.BobResponderSecrecyQuery tr (fun t => t.AttackerKnows tr) := by
  intro b a ikB ikA spk pqpk opk ek ct keys i hBob k hblk hKnown
  obtain ⟨sB, sS, sQ, o, ss,
    hsB, hikB, hsS, hspk, hsQ, hpqpk, ho, hopk,
    hdec, hkeys, hauth⟩ := hbobDone b a ikB ikA spk pqpk opk ek ct keys i hBob
  rcases hauth with hmatch | hCIK | hCSPK | hBDH
  · obtain ⟨j, a', b', spk', opk', _, hAlice⟩ := hmatch
    obtain ⟨t, sA, _, hSlot, _, _, hek_eq, hAliceAgree⟩ :=
      haliceDone a' b' ikA ikB spk' pqpk opk' ek ct keys j hAlice
    have hct : ct = (kemEncap (kemPk sQ) (rnd (t + 1) 32)).1 := by
      have h1 := congrArg Prod.fst hAliceAgree
      simpa [aliceAgreement, hpqpk] using h1
    have hss_eq : ss = (kemEncap (kemPk sQ) (rnd (t + 1) 32)).2 := by
      have hkd : DY.Libsignal.PQXDH.errToOption
          (kemDecap sQ (kemEncap (kemPk sQ) (rnd (t + 1) 32)).1) =
          some (kemEncap (kemPk sQ) (rnd (t + 1) 32)).2 := kemDecap_kemEncap sQ (rnd (t + 1) 32)
      rw [hdec, hct, hkd]
      rfl
    rcases hpub_block_inv hkeys hblk (hpub_of_knows hKnown) with
      ⟨_, hdh2, hdh3, hdh4, hssPub⟩ | hexp
    · rw [hss_eq] at hssPub
      have hpqPub : Pub sQ := by
        rcases hinv_ss hssPub with ⟨_, hcoins⟩ | ⟨sk, heq, hsk⟩
        · exact False.elim (hnot_pub_coins hSlot hcoins)
        · obtain rfl := kemPk_inj heq
          exact hsk
      have hpqLeak : tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
          tr.EventLogged PQXDHEvent.BrokenKEM := by
        rw [hpqpk]
        exact hpub_PQ hsQ hpqPub
      by_cases hBDH : tr.EventLogged PQXDHEvent.BrokenDH
      · exact .inl (.inr (.inr ⟨hBDH, hpqLeak⟩))
      · have hnotEk : ¬ Pub (rnd t 32) := fun hekPub => hBDH (hpub_EK hSlot hekPub)
        rw [hek_eq] at hdh2 hdh3 hdh4
        have hsBPub : Pub sB := (hpub_agree_dhPk hdh2).resolve_left hnotEk
        have hsSPub : Pub sS := (hpub_agree_dhPk hdh3).resolve_left hnotEk
        have hikBComp : tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) := by
          rw [hikB]
          exact (hpub_IK hsB hsBPub).resolve_right hBDH
        have hspkComp : tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) := by
          rw [hspk]
          exact (hpub_SPK hsS hsSPub).resolve_right hBDH
        have hopkExc : OPKAbsentOrCompromised b opk i tr := by
          cases o with
          | none =>
            subst hopk
            exact .inl rfl
          | some sO =>
            subst hopk
            have hd4 : Pub (agree (dhPk (rnd t 32)) sO) :=
              hdh4 (agree (dhPk (rnd t 32)) sO) rfl
            have hsOPub : Pub sO := (hpub_agree_dhPk hd4).resolve_left hnotEk
            have hsOComp : tr.EventLogged (PQXDHEvent.CompromisedOPK b (dhPk sO)) :=
              (hpub_OPK (ho sO rfl) hsOPub).resolve_right hBDH
            exact .inr ⟨dhPk sO, rfl, hcompOpk_before hBob hsOComp⟩
        exact .inl (.inr (.inl ⟨hikBComp, hspkComp, hopkExc, hpqLeak⟩))
    · exact .inr hexp
  · exact .inl (.inl (.inl hCIK))
  · exact .inl (.inl (.inr (.inl hCSPK)))
  · exact .inl (.inl (.inr (.inr hBDH)))

end SecrecyReductions

end Symbolic.Swarm.COMPOSED.CompKeyInversion
