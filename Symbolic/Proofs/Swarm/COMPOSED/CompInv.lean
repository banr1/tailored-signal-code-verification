/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompPresBob
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Composed Trace Invariant and PQXDH Security Theorems

Proves that `SpqrInv` holds on every reachable trace of `Composed.reachability`
(`spqrInv_of_reachable`) and derives initiator secrecy (`alice_initiator_secrecy`), responder
secrecy (`bob_responder_secrecy`), and handshake authentication (`authentication`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion

private theorem composed_reachable_induction' {Inv : ExecTrace → Prop}
    (hBase : Inv Trace.nil)
    (hStep : ∀ (input : DY.Libsignal.Composed.reachability.Input) (tr : ExecTrace),
      tr.Reachable DY.Libsignal.Composed.reachability →
      DY.Libsignal.Composed.reachability.PreCond input tr → Inv tr →
      Inv (((DY.Libsignal.Composed.reachability.step input).snd).run tr).2.val)
    (tr : ExecTrace) (hReach : tr.Reachable DY.Libsignal.Composed.reachability) : Inv tr := by
  induction hReach with
  | Base => exact hBase
  | Step input hPre hReachPre ih => exact hStep input _ hReachPre hPre ih

/-- `SpqrInv` holds on every trace reachable under `Composed.reachability`. -/
theorem spqrInv_of_reachable (tr : ExecTrace)
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) :
    SpqrInv tr := by
  refine composed_reachable_induction' spqrInv_nil (fun input tr hReachPre hPre hInv => ?_) tr hreach
  rcases input with ⟨⟨i, hi⟩, inp⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact preserves_net inp tr hPre hInv
  · exact preserves_registerIdentity inp tr hInv
  · rcases inp with ⟨p, skIdx⟩; exact preserves_registerCorruptIdentity p skIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩; exact preserves_genSignedPrekey b idStateIdx tr hInv
  · rcases inp with ⟨b, idStateIdx⟩; exact preserves_genPQPrekey b idStateIdx tr hInv
  · exact preserves_genOneTimePrekey inp tr hInv
  · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
    exact preserves_aliceStart a b idStateIdx regIdxB bh tr hInv
  · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
    exact preserves_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx tr hInv (cikOK_of_reachable hReachPre hInv)
  · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
    exact preserves_messageEncrypt me stateIdx coinsLen pqIdx tr hInv
  · rcases inp with ⟨me, stateIdx⟩
    exact preserves_messageEncryptAbort me stateIdx tr hInv
  · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
    exact preserves_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
    exact preserves_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx tr hInv
  · rcases inp with ⟨me, stateIdx, k⟩
    exact preserves_exposeKey me stateIdx k tr hInv
  · rcases inp with ⟨me, stateIdx⟩
    exact preserves_exposeSpqr me stateIdx tr hInv
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

theorem responderSecrecyQuery_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) :
    DY.Libsignal.PQXDH.AliceInitiatorSecrecyQuery tr (fun t => t.AttackerKnows tr) :=
  responderSecrecyQuery_of_contracts
    (Pub := Pub tr)
    (IKAt := IKAt tr)
    (SPKAt := SPKAt tr)
    (PQAt := PQAt tr)
    (CompAliceSlot := AliceSlot tr)
    (fun hk => pub_of_knows hinv hk)
    (fun hkeys hblk hpub => pub_handshakeBlock_inv hinv hkeys hblk hpub)
    (fun h => pub_agree_dhPk hinv h)
    (fun h => Pub.inv_ss hinv h)
    (fun h => not_pub_coins hinv h)
    (fun hik hpub => pub_IK hinv hik hpub)
    (fun hspk hpub => pub_SPK hinv hspk hpub)
    (fun hpq hpub => pub_PQ hinv hpq hpub)
    (fun hslot hpub => pub_EK hinv hslot hpub)
    (fun a b ikA ikB spk pqpk opk ek ct keys i hev =>
      hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i hev)

theorem initiatorSecrecyQuery_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) :
    DY.Libsignal.PQXDH.BobResponderSecrecyQuery tr (fun t => t.AttackerKnows tr) :=
  initiatorSecrecyQuery_of_contracts
    (Pub := Pub tr)
    (IKAt := IKAt tr)
    (SPKAt := SPKAt tr)
    (PQAt := PQAt tr)
    (OPKAt := OPKAt tr)
    (CompAliceSlot := AliceSlot tr)
    (fun hk => pub_of_knows hinv hk)
    (fun hkeys hblk hpub => pub_handshakeBlock_inv hinv hkeys hblk hpub)
    (fun h => pub_agree_dhPk hinv h)
    (fun h => Pub.inv_ss hinv h)
    (fun h => not_pub_coins hinv h)
    (fun hik hpub => (pub_IK hinv hik hpub).imp
      (fun ⟨j, hj⟩ => ⟨j, hj⟩) (fun ⟨j, hj⟩ => ⟨j, hj⟩))
    (fun hspk hpub => (pub_SPK hinv hspk hpub).imp id (fun ⟨j, hj⟩ => ⟨j, hj⟩))
    (fun hpq hpub => pub_PQ hinv hpq hpub)
    (fun hopk hpub => pub_OPK hinv hopk hpub)
    (fun hslot hpub => let ⟨j, hj⟩ := pub_EK hinv hslot hpub; ⟨j, hj⟩)
    (fun a b ikA ikB spk pqpk opk ek ct keys i hev => by
      obtain ⟨t, sA, hi, hslot, hA, hikA, hek, hagr, _⟩ :=
        hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys i hev
      exact ⟨t, sA, hi, hslot, hA, hikA, hek, hagr⟩)
    (fun b a ikB ikA spk pqpk opk ek ct keys i hBob => by
      obtain ⟨sB, sS, sQ, o, e, hB, hikB, hS, hspk, hQ, hpqpk, ho, hopk,
        _hcan, hdec, hkeys, _hreg, hauth⟩ :=
        hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i hBob
      exact ⟨sB, sS, sQ, o, e, hB, hikB, hS, hspk, hQ, hpqpk, ho, hopk, hdec, hkeys, hauth⟩)
    (fun hBob hsOComp => hinv.compOpk_loggedBefore hBob hsOComp)

theorem authenticationQuery_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) :
    AuthenticationQuery tr := by
  intro b a ikB ikA spk pqpk opk ek ct keys i hBob
  obtain ⟨sB, sS, sQ, o, e, _, h_ikB, _, h_spk, _, h_pqpk, _, h_opk, _, hdec, hkeys,
    ⟨r, vkA, hon, hr_lt, hreg⟩, hor⟩ :=
    hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i hBob
  subst h_ikB h_spk h_pqpk h_opk
  rcases hor with ⟨j, a', b', spk', opk', hj, hAlice⟩ | hcik | hcspk | hbdh
  · obtain ⟨t, sA, rfl, _, hA, hikA, _, hAliceAgree, _⟩ :=
      hinv.aliceDone a' b' ikA (DiffieHellman.dhPk sB) spk' (PQKem.kemPk sQ) opk' ek ct keys j hAlice
    have hbob7 : bobAgreement sB sS sQ o ikA ek ct = some keys := by
      rw [bobAgreement_eq_some_iff, ← hdec]
      exact hkeys
    have hrk :
        keys.rk =
          (aliceAgreement sA (rnd t 32) (DiffieHellman.dhPk sB) spk' (PQKem.kemPk sQ) opk' (rnd (t + 1) 32)).2.rk :=
      congrArg HandshakeKeys.rk (congrArg Prod.snd hAliceAgree)
    obtain ⟨hdh1, _, hdh3, hdh4, _, _, _⟩ := bobAgreement_rk_eq_aliceAgreement_rk hbob7 hrk
    rw [hikA] at hdh1
    have hSameSpk : SameDHKey (DiffieHellman.dhPk sS) spk' :=
      sameDHKey_of_agree_eq_uncond hdh1
    have hdh3' : agree ek sS = agree (DiffieHellman.dhPk (rnd t 32)) sS := by
      rw [hdh3, ← agree_of_sameDHKey hSameSpk (rnd t 32), agree_comm]
    have hSameEk : SameDHKey ek (DiffieHellman.dhPk (rnd t 32)) :=
      sameDHKey_of_agree_right_eq hdh3'
    have hmap_eq :
        o.map (agree (DiffieHellman.dhPk (rnd t 32)) ·) = opk'.map (agree · (rnd t 32)) := by
      rw [← hdh4]
      congr 1
      funext x
      exact (agree_of_sameDHKey hSameEk x).symm
    have hSameOpk : SameOPK (o.map DiffieHellman.dhPk) opk' :=
      sameOPK_of_map_agree_eq_uncond hmap_eq
    cases hon with
    | false =>
      have hcomp : tr.EventLoggedAt (PQXDHEvent.CompromisedIK a ikA) (r + 1) :=
        hinv.irCorrupt a ikA vkA r hreg
      have hne : r + 1 ≠ i := by
        intro hEq
        have hcomp' := hcomp
        have hBob' := hBob
        rw [hEq, Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hcomp'
        rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hBob'
        have hSameEv : (some (EvE (PQXDHEvent.CompromisedIK a ikA)) : Option EvEntry) =
            some (EvE (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS)
              (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)) := hcomp'.symm.trans hBob'
        cases hSameEv
      exact .inr (.inl ⟨r + 1, hcomp, by omega⟩)
    | true =>
      obtain ⟨sA₀, hA₀, hikA₀, _⟩ := hinv.irHonest a ikA vkA r hreg
      have hsA : sA = sA₀ := dhPk_inj (hikA.symm.trans hikA₀)
      subst hsA
      have ha : a' = a := ikAt_owner_unique hA hA₀
      subst ha
      exact .inl ⟨b', ikA, DiffieHellman.dhPk sB, spk', opk', ek,
        ct, keys, t + 5,
        hAlice, hj, hSameSpk, hSameOpk⟩
  · exact .inr (.inl hcik)
  · exact .inr (.inr (.inl hcspk))
  · exact .inr (.inr (.inr hbdh))

/-- Alice initiator handshake secrecy on all reachable traces of the composed protocol. -/
theorem alice_initiator_secrecy : Security.AliceInitiatorSecrecy :=
  fun tr hreach => responderSecrecyQuery_of_spqrInv (spqrInv_of_reachable tr hreach)

/-- Bob responder handshake secrecy on all reachable traces of the composed protocol. -/
theorem bob_responder_secrecy : Security.BobResponderSecrecy :=
  fun tr hreach => initiatorSecrecyQuery_of_spqrInv (spqrInv_of_reachable tr hreach)

/-- Handshake authentication on all reachable traces of the composed protocol. -/
theorem authentication : Security.Authentication :=
  fun tr hreach => authenticationQuery_of_spqrInv (spqrInv_of_reachable tr hreach)

end Symbolic.Swarm.COMPOSED.CompInv
