/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Trace
public import Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.PubClosure
import Init.Data.String.Defs
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
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace

/-!
# Secrecy of Alice's Initial Message Key on the Replay Trace `fTr`

Proves `fTr_not_knows_mkA : ¬ (mkTestTracePredicates fTr).AttackerKnows mkA`. Every network message
of `fTr` lies in `Pub SecL` (`fTr_netPub`), where `SecL` excludes Alice's base key (`t = 22`) and
Bob's identity secret (`t = 5`), so no key derived from `DH2 = DH(EK_A, IK_B)` is attacker-known on
`fTr`.
-/

@[expose] public section

set_option autoImplicit false

open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (TestTracePredicates mkTestTracePredicates FSQueryP PCSQueryP fsQuery_iff_test pcsQuery_iff_test)

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Secrecy

open Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.PubClosure (Pub Pub.not_agree
  Pub.not_createChain_snd Pub.not_kdfCk_snd Pub.not_pqxdhIkm Pub.not_pqxdhKdf_rk Pub.not_rand
  Pub.not_trMsgKeys_cipherKey Pub.of_attackerKnows Pub.rand Pub.spqrSendKey_of
  baseAttackerKnows_append_cEv baseAttackerKnows_append_ev baseAttackerKnows_append_net
  baseAttackerKnows_append_rnd baseAttackerKnows_append_trEv)
open Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Trace (fTr tC)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (coins0 dhsA ikA ikB keys1 o1 pqskB spkB
  stA0 t1 t1_length t2 t3 t4 t4_length t5 t5_length t6 t6_length t7 t8)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs.genPQPrekey
  Runs.genSignedPrekey Runs.registerIdentity StP StT aliceOutOpt aliceTr encMsg encTr
  genPQPrekeyTr genSignedPrekeyTr registerIdentityTr rnd)

open DY DY.Comparse DY.DiffieHellman DY.PQKem
open DY.Libsignal.Composed
open DY.Libsignal.TripleRatchet (kdfCk TRState TREvent)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (mkTestTracePredicates)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState pqxdhKdf pqxdhIkm agree)

/-- Every random value except Bob's identity secret (5) and Alice's base key (22). -/
abbrev SecL (t : Nat) : Prop := t ≠ 22 ∧ t ≠ 5

/-- Every network message of `tr` is in `Pub SecL`. -/
def NetPub (tr : ExecTrace) : Prop := ∀ y, tr.BaseAttackerKnows y → Pub SecL y

/-! ## Appending entries -/

theorem baseAttackerKnows_append_stT (tr : ExecTrace) (me : Participant) (st : TRState)
    (b : Bytes) : Trace.BaseAttackerKnows (tr.append (StT me st)) b ↔ Trace.BaseAttackerKnows tr b :=
  Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_trSt tr me st b

theorem baseAttackerKnows_append_stP (tr : ExecTrace) (me : Participant) (st : PQXDHState)
    (b : Bytes) : Trace.BaseAttackerKnows (tr.append (StP me st)) b ↔ Trace.BaseAttackerKnows tr b :=
  Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_pqSt tr me st b

theorem NetPub.nil : NetPub Trace.nil := fun _ h => by
  rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1] at h
  exact False.elim h

theorem NetPub.net {tr : ExecTrace} {m : Bytes} (h : NetPub tr) (hm : Pub SecL m) :
    NetPub (tr.append (NetE m)) := by
  intro y hy
  rcases (baseAttackerKnows_append_net tr m y).1 hy with rfl | hy
  · exact hm
  · exact h y hy

theorem NetPub.rand {tr : ExecTrace} {n : Nat} (h : NetPub tr) : NetPub (tr.append (RndE n)) :=
  fun y hy => h y ((baseAttackerKnows_append_rnd tr n y).1 hy)

theorem NetPub.trEv {tr : ExecTrace} {e : TREvent} (h : NetPub tr) : NetPub (tr.append (EvT e)) :=
  fun y hy => h y ((baseAttackerKnows_append_trEv tr e y).1 hy)

theorem NetPub.pqEv {tr : ExecTrace} {e : PQXDHEvent} (h : NetPub tr) :
    NetPub (tr.append (EvP e)) :=
  fun y hy => h y ((baseAttackerKnows_append_ev tr e y).1 hy)

theorem NetPub.cEv {tr : ExecTrace} {e : ComposedEvent} (h : NetPub tr) : NetPub (tr.append (EvC e)) :=
  fun y hy => h y ((baseAttackerKnows_append_cEv tr e y).1 hy)

theorem NetPub.stT {tr : ExecTrace} {me : Participant} {st : TRState} (h : NetPub tr) :
    NetPub (tr.append (StT me st)) :=
  fun y hy => h y ((baseAttackerKnows_append_stT tr me st y).1 hy)

theorem NetPub.stP {tr : ExecTrace} {me : Participant} {st : PQXDHState} (h : NetPub tr) :
    NetPub (tr.append (StP me st)) :=
  fun y hy => h y ((baseAttackerKnows_append_stP tr me st y).1 hy)

/-! ## The protocol steps of `fTr` send only `Pub SecL` messages -/

theorem NetPub.registerIdentityTr {tr : ExecTrace} {p : Participant} (h : NetPub tr) :
    NetPub (registerIdentityTr tr p) :=
  NetPub.stP (NetPub.net (NetPub.net (NetPub.pqEv (NetPub.rand h)) (.dhPub _)) (.vkPub _))

theorem NetPub.genSignedPrekeyTr {tr : ExecTrace} {b : Participant} {ik : Bytes} (h : NetPub tr) :
    NetPub (genSignedPrekeyTr tr b ik) :=
  NetPub.net (NetPub.net (NetPub.stP (NetPub.pqEv (NetPub.rand (NetPub.rand h)))) (.dhPub _))
    (.sig _ _ _)

theorem NetPub.genPQPrekeyTr {tr : ExecTrace} {b : Participant} {ik : Bytes} (h : NetPub tr) :
    NetPub (genPQPrekeyTr tr b ik) :=
  NetPub.net (NetPub.net (NetPub.stP (NetPub.pqEv (NetPub.rand (NetPub.rand h)))) (.kemPub _))
    (.sig _ _ _)

theorem pub_aliceOut_ct (tr : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (opk : Option Bytes) :
    Pub SecL (aliceOutOpt tr ikA ikBPk spkPk pqPk opk).ct :=
  .encap pqPk (rnd (tr.length + 1) 32)

theorem NetPub.aliceTr {tr : ExecTrace} {a b : Participant} {ikA ikBPk spkPk pqPk : Bytes}
    (h : NetPub tr) : NetPub (aliceTr tr a b ikA ikBPk spkPk pqPk) :=
  NetPub.stT (NetPub.cEv (NetPub.trEv (NetPub.pqEv
    (NetPub.net (NetPub.net (NetPub.rand (NetPub.rand (NetPub.rand h))) (.dhPub _))
      (pub_aliceOut_ct tr ikA ikBPk spkPk pqPk none)))))

theorem pub_encMsg (st : TRState) (coins pq : Bytes) {t : Nat} (ht : SecL t) :
    Pub SecL (encMsg st coins pq (rnd t 32)) :=
  .cat (.trWire (.dhPub _) (.enc (.rand ht)) (.spqrSendMsg _ _)) (.trunc _)

theorem NetPub.encTr {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState} {pq : Bytes}
    (h : NetPub tr) (hm : SecL tr.length) : NetPub (encTr tr me stH st pq) :=
  NetPub.net (NetPub.stT (NetPub.trEv (NetPub.trEv
    (NetPub.net (NetPub.rand (NetPub.rand h)) (Pub.spqrSendKey_of _ _)))))
    (pub_encMsg st (rnd (tr.length + 1) 32) pq hm)

theorem t1_eq : t1 = registerIdentityTr Trace.nil "alice" :=
  (Runs.registerIdentity (tr := Trace.nil) (p := "alice") (by
    simp only [DY.Libsignal.PQXDH.isRegisteredB, DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl)).2

theorem t2_eq : t2 = registerIdentityTr t1 "bob" := by
  have hat_none : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
      (hi : i = tr.length)
      (_ : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by rfl),
      ((tr.append e).at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
    intro E _ tr e i hi hproj
    subst hi
    have hlt : tr.length < (tr.append e).length := by
      simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    simp only [DY.Trace.at?, hlt, ↓reduceDIte]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2,
      ↓reduceDIte]
    exact hproj
  let ik0 := rnd (Trace.nil : ExecTrace).length 32
  let p1 := (Trace.nil : ExecTrace).append (RndE 32)
  let p2 := p1.append (EvP (.IdentityRegistered "alice" (dhPk ik0) (DY.Signature.vk ik0) true))
  let p3 := p2.append (NetE (dhPk ik0))
  let p4 := p3.append (NetE (DY.Signature.vk ik0))
  let p5 := p4.append (StP "alice" { kind := .identity, sk := ik0 })
  have hp5 : t1 = p5 := t1_eq
  have h0 : (p5.at? 0 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p4 _
        (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p3 _
        (by simp [p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p2 _
        (by simp [p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p1 _
        (by simp [p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])]
    exact hat_none Trace.nil (RndE 32) (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h1 : (p5.at? 1 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
      some (EvP (.IdentityRegistered "alice" (dhPk ik0) (DY.Signature.vk ik0) true)) := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p4 _
        (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p3 _
        (by simp [p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p2 _
        (by simp [p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])]
    have hp1_len : p1.length = 1 := by
      simp [p1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1]
    exact hp1_len ▸ DY.Trace.at?_append p1
      (EvP (.IdentityRegistered "alice" (dhPk ik0) (DY.Signature.vk ik0) true))
  have h2 : (p5.at? 2 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p4 _
        (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p3 _
        (by simp [p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])]
    exact hat_none p2 (NetE (dhPk ik0))
      (by simp [p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h3 : (p5.at? 3 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p4 _
        (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])]
    exact hat_none p3 (NetE (DY.Signature.vk ik0))
      (by simp [p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h4 : (p5.at? 4 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none :=
    hat_none p4 (StP "alice" { kind := .identity, sk := ik0 })
      (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob") = true := by
    have hne : (("alice" : Participant) == "bob") = false := beq_false_of_ne (by decide)
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    rw [t1_length, show List.range 5 = [0, 1, 2, 3, 4] from rfl, hp5]
    simp only [List.any_cons, List.any_nil, Bool.or_false, h0, h1, h2, h3, h4, hne]
    rfl
  exact (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2

theorem t3_eq : t3 = genSignedPrekeyTr t2 "bob" ikB := by
  have hik2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq]
    unfold registerIdentityTr
    dsimp only
    rw [t1_length]
    let q := ((((t1.append (RndE 32)).append
      (EvP (.IdentityRegistered "bob" (dhPk ikB) (DY.Signature.vk ikB) true))).append
      (NetE (dhPk ikB))).append (NetE (DY.Signature.vk ikB)))
    have hq_len : q.length = 9 := by
      simp [q, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length]
    exact hq_len ▸ DY.Trace.at?_append q (StP "bob" { kind := .identity, sk := ikB })
  exact (Runs.genSignedPrekey (tr := t2) (b := "bob") (idH := 9) (ik := ikB) hik2).2

theorem t4_eq : t4 = genPQPrekeyTr t3 "bob" ikB := by
  have hik2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t2_eq]
    unfold registerIdentityTr
    dsimp only
    rw [t1_length]
    let q := ((((t1.append (RndE 32)).append
      (EvP (.IdentityRegistered "bob" (dhPk ikB) (DY.Signature.vk ikB) true))).append
      (NetE (dhPk ikB))).append (NetE (DY.Signature.vk ikB)))
    have hq_len : q.length = 9 := by
      simp [q, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length]
    exact hq_len ▸ DY.Trace.at?_append q (StP "bob" { kind := .identity, sk := ikB })
  have hle23 : t2 ≤ t3 := ((DY.Libsignal.PQXDH.genSignedPrekey "bob" 9).run t2).2.property
  exact (Runs.genPQPrekey (tr := t3) (b := "bob") (idH := 9) (ik := ikB)
    (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle23 hik2)).2

theorem t4_netPub : NetPub t4 := by
  rw [t4_eq, t3_eq, t2_eq, t1_eq]
  exact NetPub.genPQPrekeyTr (NetPub.genSignedPrekeyTr
    (NetPub.registerIdentityTr (NetPub.registerIdentityTr NetPub.nil)))

theorem t7_netPub : NetPub t7 := by
  have h5 : NetPub t5 := NetPub.aliceTr t4_netPub
  have h6 : NetPub t6 := NetPub.encTr h5 (by rw [t5_length]; decide)
  exact NetPub.encTr h6 (by rw [t6_length]; decide)

theorem t8_netPub : NetPub t8 :=
  NetPub.stT (NetPub.trEv (NetPub.trEv (NetPub.cEv (NetPub.trEv (NetPub.trEv (NetPub.pqEv
    (NetPub.net (NetPub.rand t7_netPub) (Pub.spqrSendKey_of stA0.spqr coins0))))))))

theorem tC_netPub : NetPub tC :=
  NetPub.net (NetPub.pqEv t8_netPub) (Pub.rand (n := 32) (show SecL 10 by decide))

/-- Every network message of `fTr` lies in `Pub SecL`. -/
theorem fTr_netPub : NetPub fTr :=
  NetPub.stT (NetPub.trEv (NetPub.trEv (NetPub.cEv (NetPub.trEv (NetPub.trEv (NetPub.pqEv
    (NetPub.net (NetPub.rand tC_netPub) (Pub.spqrSendKey_of stA0.spqr coins0))))))))

/-! ## Alice's message-0 key is not in `Pub SecL` -/

/-- Alice's message-0 seed. -/
abbrev mkA : Bytes := (kdfCk stA0.cks).2

theorem not_secL_22 : ¬ SecL 22 := fun h => h.1 rfl
theorem not_secL_5 : ¬ SecL 5 := fun h => h.2 rfl

theorem not_pub_dh2 : ¬ Pub SecL (agree (dhPk ikB) (rnd 22 32)) :=
  Pub.not_agree (Pub.not_rand not_secL_22) (Pub.not_rand not_secL_5)

theorem not_pub_rk : ¬ Pub SecL keys1.rk := by
  have hkeys : keys1 = pqxdhKdf (pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) (rnd 22 32))
      (agree (dhPk spkB) (rnd 22 32)) none (kemEncap (kemPk pqskB) (rnd 23 32)).2) := by
    unfold keys1 o1 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt
      DY.Libsignal.PQXDH.aliceAgreement
    rw [t4_length]
    rfl
  rw [hkeys]
  exact Pub.not_pqxdhKdf_rk (ikm := pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) (rnd 22 32))
    (agree (dhPk spkB) (rnd 22 32)) none (kemEncap (kemPk pqskB) (rnd 23 32)).2)
    (Pub.not_pqxdhIkm not_pub_dh2)

theorem not_pub_cks : ¬ Pub SecL stA0.cks :=
  Pub.not_createChain_snd (rk := keys1.rk) (dhPk spkB) dhsA not_pub_rk

theorem not_pub_mkA : ¬ Pub SecL mkA := Pub.not_kdfCk_snd not_pub_cks

/-- Neither `mkA` nor its hybrid cipher key under any logged salt is attacker-known on `fTr`. -/
theorem fTr_not_knows_mkA : ¬ (mkTestTracePredicates fTr).AttackerKnows mkA := by
  rintro ⟨pqSalt, _, hk | hk⟩
  · exact not_pub_mkA (Pub.of_attackerKnows fTr_netPub hk)
  · exact Pub.not_trMsgKeys_cipherKey pqSalt not_pub_mkA (Pub.of_attackerKnows fTr_netPub hk)

end Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.Secrecy
