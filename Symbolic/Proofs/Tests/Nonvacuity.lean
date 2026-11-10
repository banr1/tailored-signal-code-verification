/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Tests.Nonvacuity.SetupTrace
public import Symbolic.Tests.Nonvacuity.HonestHandshakeWithoutOpk
public import Symbolic.Tests.Nonvacuity.HonestHandshakeWithOpk
public import Symbolic.Tests.Nonvacuity.HonestSession
public import Symbolic.Tests.Nonvacuity.ExposedSession
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
import Mathlib.Algebra.Group.Nat.Defs
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
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace

/-!
# Execution and Reachability of Nonvacuity Example Traces

Proves that each example protocol trace in `Symbolic.Tests.Nonvacuity` runs to completion without
aborting and is reachable in `DY.Libsignal.Composed.reachability`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Nonvacuity

open Symbolic.Tests.Nonvacuity (keySetupTrace honestHandshakeWithoutOpkTrace
  honestHandshakeWithOpkTrace honestSessionTrace exposedSessionTrace setupTrace_reachable)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (bh1 bhOpk cB cB' coins0 dhsA ikA ikB key0
  keys1 kh1 khOpk m0 mh1 mhOpk o1 pqm0 pqskB recv8 seedB0 seedB0_eq spkB stA0 stB0' stB00 stB1 t1
  t1_length t2 t2_length t3 t3_length t4 t4_length t4Opk_runs t5 t5_length t5_runs t5Opk_runs t6
  t6_length t6_reach t6_runs t6Opk_runs t7_runs t7Opk_runs t8_runs t9_runs t10_runs t11 t11_reach
  t11_runs t12_runs t13_runs t14_runs t15_runs wTr wTr_reach wTrOpk wTrOpk_reach)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (EvC EvP EvT NetE RndE Runs Runs.bind Runs.bobStart
  Runs.genPQPrekey Runs.genSignedPrekey Runs.pure Runs.receiveMessage Runs.registerIdentity StP StT
  aliceTr aliceTrOpt bobSt0 bobStart_reachable bobAgreement_honest dec_ok encTr genPQPrekeyTr
  genSignedPrekeyTr mac_ok parse_encMsg ratchetState reach_of_runs registerIdentityTr rnd skipTr)

open DY
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.PQXDH (registerIdentity genSignedPrekey genPQPrekey)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (ProtocolSetup setupTrace)
open DY.Libsignal.TripleRatchet (RecvChain TRState kdfCk setRecvChain spqrB2A maxReceiverChains)

/-! ## Shared prekey setup -/

private theorem runs_step1 : Runs (registerIdentity "alice") Trace.nil 4 t1 := by
  have hunreg : (!DY.Libsignal.PQXDH.isRegisteredB (Trace.nil : ExecTrace) "alice") = true := by
    simp only [DY.Libsignal.PQXDH.isRegisteredB, DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  have h := Runs.registerIdentity (tr := (Trace.nil : ExecTrace)) (p := "alice") hunreg
  exact ⟨by simpa only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.zero_add] using h.1, rfl⟩

private theorem runs_step2 : Runs (registerIdentity "bob") t1 9 t2 := by
  have hunregA : (!DY.Libsignal.PQXDH.isRegisteredB (Trace.nil : ExecTrace) "alice") = true := by
    simp only [DY.Libsignal.PQXDH.isRegisteredB, DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (tr := (Trace.nil : ExecTrace)) (p := "alice") hunregA).2
  have hat_none : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
      (hi : i = tr.length)
      (_ : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by rfl),
      ((tr.append e).at? i :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
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
  have hp5 : t1 = p5 := ht1
  have h0 : (p5.at? 0 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      none := by
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
    exact hat_none Trace.nil (RndE 32)
      (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h1 : (p5.at? 1 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
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
  have h2 : (p5.at? 2 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      none := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p4 _
        (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p3 _
        (by simp [p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])]
    exact hat_none p2 (NetE (dhPk ik0))
      (by simp [p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h3 : (p5.at? 3 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      none := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt p4 _
        (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])]
    exact hat_none p3 (NetE (DY.Signature.vk ik0))
      (by simp [p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have h4 : (p5.at? 4 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      none :=
    hat_none p4 (StP "alice" { kind := .identity, sk := ik0 })
      (by simp [p4, p3, p2, p1, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob") = true := by
    have hne : (("alice" : Participant) == "bob") = false := beq_false_of_ne (by decide)
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    rw [t1_length, show List.range 5 = [0, 1, 2, 3, 4] from rfl, hp5]
    simp only [List.any_cons, List.any_nil, Bool.or_false, h0, h1, h2, h3, h4, hne]
    rfl
  have h := Runs.registerIdentity (tr := t1) (p := "bob") hunregB
  exact ⟨by simpa only [t1_length] using h.1, rfl⟩

private theorem runs_step3 : Runs (genSignedPrekey "bob" 9) t2 13 t3 := by
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob") = true := by
    have h1 := runs_step2.1
    unfold DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.guardTrace at h1
    rw [DY.Traceful.run_bind, DY.Traceful.run_mk] at h1
    cases h : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob")
    · simp [h] at h1
    · rfl
  have ht2 : t2 = registerIdentityTr t1 "bob" :=
    (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2
  have hik2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]
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
  have h := Runs.genSignedPrekey (tr := t2) (b := "bob") (idH := 9) hik2
  exact ⟨by simpa only [t2_length] using h.1, rfl⟩

private theorem runs_step4 : Runs (genPQPrekey "bob" 9) t3 19 t4 := by
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob") = true := by
    have h1 := runs_step2.1
    unfold DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.guardTrace at h1
    rw [DY.Traceful.run_bind, DY.Traceful.run_mk] at h1
    cases h : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob")
    · simp [h] at h1
    · rfl
  have ht2 : t2 = registerIdentityTr t1 "bob" :=
    (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2
  have hik2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]
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
  have hle23 : t2 ≤ t3 := ((genSignedPrekey "bob" 9).run t2).2.property
  have hik3 := Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle23 hik2
  have h := Runs.genPQPrekey (tr := t3) (b := "bob") (idH := 9) hik3
  exact ⟨by simpa only [t3_length] using h.1, rfl⟩

private def defaultSetupRecords : ProtocolSetup where
  alice := "alice"
  bob := "bob"
  withOpk := false
  regIdA := 0
  regIdB := 0
  spkId := 0
  kpkId := 0
  opkId := 0
  kyberSecB := []
  fresh := fun _ _ => []
  opaqueBytes := fun _ => []

theorem keySetupTrace_eq : keySetupTrace = t4 := by
  unfold keySetupTrace DY.Libsignal.Composed.Refinement.setupAct
  refine (?_ : Runs _ Trace.nil () t4).2
  refine Runs.bind runs_step1 ?_
  refine Runs.bind runs_step2 ?_
  refine Runs.bind runs_step3 ?_
  refine Runs.bind runs_step4 ?_
  exact Runs.pure () _

theorem keySetupTrace_reachable : keySetupTrace.Reachable reachability :=
  setupTrace_reachable defaultSetupRecords

/-! ## Handshake and session traces -/

abbrev dhsB0 : Bytes := rnd 38 32
def stB0NoOpk' : TRState := (ratchetState stB00 (dhPk dhsA) dhsB0).1
def cBNoOpk : RecvChain := (ratchetState stB00 (dhPk dhsA) dhsB0).2
def cBNoOpk' : RecvChain :=
  { cBNoOpk with chainKey := (kdfCk cBNoOpk.chainKey).1, index := 1 }
def stB1NoOpk : TRState :=
  { stB0NoOpk' with
      recv := [cBNoOpk']
      spqr := Symbolic.Proofs.Tests.Shared.Composed.Runs.recvSt
        (DY.Spqr.spqrInit keys1.pqr spqrB2A) pqm0 }

/-- Explicit 47-entry trace after `Composed.bobStart` accepts message 0 directly on `t6`. -/
def tHandshakeNoOpk : ExecTrace :=
  let tr1 := (t6.append (RndE 32)).append (NetE key0)
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0)))).append
      (EvT (.HonestDH (stB0NoOpk'.sessionInfo "bob") dhsB0 0))).append
      (EvC (.HandshakeSession (stB0NoOpk'.sessionInfo "bob") 40))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
    (EvT (.MessageKey (stB0NoOpk'.sessionInfo "bob") .receiver seedB0 key0 0 2 46))).append
    (StT "bob" stB1NoOpk)

private theorem tHandshakeNoOpk_bobStart_runs :
    Runs (bobStart "bob" "alice" kh1 1 mh1 33 1) t6 46 tHandshakeNoOpk := by
  have hset : setRecvChain stB0NoOpk'.recv cBNoOpk' = [cBNoOpk'] := by
    simp [setRecvChain, stB0NoOpk', ratchetState, cBNoOpk', cBNoOpk, stB00, bobSt0,
      maxReceiverChains]
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig stA0 coins0 key0 m0))
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig stA0 coins0 key0 m0).ratchetKey (rnd t6.length 32) =
      (stB0NoOpk', cBNoOpk) := by
    rw [t6_length]; rfl
  have hat_here : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
      (hi : i = tr.length), ((tr.append e).at? i : Option E) = some e := by
    intro E _ tr e i hi; subst hi; exact DY.Trace.at?_append tr e
  have hle_of_runs : ∀ {α : Type} {x : Traceful α} {tr tr' : ExecTrace} {a : α},
      Runs x tr a tr' → tr ≤ tr' :=
    fun {_} {x} {tr} {_} {_} h => h.2 ▸ (x.run tr).2.property
  have hle45 : t4 ≤ t5 := hle_of_runs t5_runs
  have hle56 : t5 ≤ t6 := hle_of_runs t6_runs
  have hle46 : t4 ≤ t6 := DY.Trace.le_trans _ _ _ hle45 hle56
  have hle36 : t3 ≤ t6 := DY.Trace.le_trans _ _ _ (hle_of_runs runs_step4) hle46
  have hle26 : t2 ≤ t6 := DY.Trace.le_trans _ _ _ (hle_of_runs runs_step3) hle36
  have hle16 : t1 ≤ t6 := DY.Trace.le_trans _ _ _ (hle_of_runs runs_step2) hle26
  have hunregA : (!DY.Libsignal.PQXDH.isRegisteredB (Trace.nil : ExecTrace) "alice") = true := by
    simp only [DY.Libsignal.PQXDH.isRegisteredB, DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (tr := (Trace.nil : ExecTrace)) (p := "alice") hunregA).2
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob") = true := by
    have h1 := runs_step2.1
    unfold DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.guardTrace at h1
    rw [DY.Traceful.run_bind, DY.Traceful.run_mk] at h1
    cases h : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob")
    · simp [h] at h1
    · rfl
  have ht2 : t2 = registerIdentityTr t1 "bob" :=
    (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2
  have hik2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]
    unfold registerIdentityTr
    dsimp only
    rw [t1_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length])
  have hik : t6.at? kh1.ik = some (StP "bob" { kind := .identity, sk := ikB }) :=
    Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle26 hik2
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey (tr := t2) (b := "bob") (idH := 9) hik2).2
  have hspk : t6.at? kh1.spk = some (StP "bob" { kind := .signedPrekey, sk := spkB }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle36 ?_
    change t3.at? 13 = _
    rw [ht3]
    unfold genSignedPrekeyTr
    dsimp only
    rw [t2_length]
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t2_length])
  have hik3 := Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (hle_of_runs runs_step3) hik2
  have ht4 : t4 = genPQPrekeyTr t3 "bob" ikB :=
    (Runs.genPQPrekey (tr := t3) (b := "bob") (idH := 9) hik3).2
  have hpqk : t6.at? kh1.pqspk = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change t4.at? 19 = _
    rw [ht4]
    unfold genPQPrekeyTr
    dsimp only
    rw [t3_length]
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t3_length])
  have hreg : t6.at? 1 =
      some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle16 ?_
    rw [ht1]
    unfold registerIdentityTr
    dsimp only
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    iterate 3 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hek : t6.at? mh1.ek = some (NetE o1.ek) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle56 ?_
    change t5.at? 25 = _
    unfold t5 aliceTr aliceTrOpt
    dsimp only
    iterate 5 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t4_length])
  have hct : t6.at? mh1.ct = some (NetE o1.ct) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle56 ?_
    change t5.at? 26 = _
    unfold t5 aliceTr aliceTrOpt
    dsimp only
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t4_length])
  have hv_var : ∀ sk : Bytes, ((dhPk sk).view? DY.X25519.Variant.SubF) = none := fun sk => by
    simp only [dhPk, DY.DiffieHellman.CanDH.dhPk]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
  have hlow_dhPk : ∀ sk : Bytes, DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false :=
    fun sk => by
      have hv_lit : ((dhPk sk).view? DY.Literal.Literal.SubF) = none := by
        simp only [dhPk, DY.DiffieHellman.CanDH.dhPk]
        exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
          ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
      simp only [DY.Libsignal.TripleRatchet.x25519LowOrder, DY.X25519.normalizeX25519Key,
        hv_var, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have hcan : DY.Libsignal.PQXDH.isCanonicalKey o1.ek = true := by
    simp only [DY.Libsignal.PQXDH.isCanonicalKey, o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt, hv_var]
    change (Option.isNone none && !DY.Libsignal.TripleRatchet.x25519LowOrder
      (dhPk (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd t4.length 32))) = true
    rw [hlow_dhPk]
    rfl
  have hmsg : t6.at? mh1.msg =
      some (NetE (Symbolic.Proofs.Tests.Shared.Composed.Runs.encMsg stA0 coins0 key0 m0)) := by
    change t6.at? 37 = _
    unfold t6 encTr
    dsimp only
    rw [t5_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t5_length])
  have hpq : ((t6.append (RndE 32)).append (NetE key0)).at? 33 = some (NetE key0) := by
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    unfold t6 encTr
    dsimp only
    rw [t5_length]
    iterate 4 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t5_length])
  have hbs := Runs.bobStart (keys := keys1)
    (msg := Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig stA0 coins0 key0 m0)
    (t := Symbolic.Proofs.Tests.Shared.Composed.Runs.encMsg stA0 coins0 key0 m0)
    (st' := stB0NoOpk') (c := cBNoOpk) (c' := cBNoOpk') (seed := seedB0)
    (pq := key0) (m := m0)
    hik hspk hpqk rfl hreg hek hct hcan
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (hlow_dhPk dhsA) hrs rfl recv8 hpq (mac_ok seedB0_eq rfl rfl)
    (dec_ok seedB0_eq) (stOut := stB1NoOpk) (by rw [hset]; rfl)
  dsimp -failIfUnchanged only [Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOutOpt] at hbs
  have htr1_len : ((t6.append (RndE 32)).append (NetE key0)).length = 40 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      t6_length]
  rw [htr1_len] at hbs
  have hskip : ∀ (tr : ExecTrace) (n : Nat),
      skipTr tr (stB0NoOpk'.sessionInfo "bob")
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig stA0 coins0 key0 m0).ratchetKey
        cBNoOpk n
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig stA0 coins0 key0 m0).counter = tr :=
    fun tr _ => by
      change ((Pure.pure () : Traceful Unit).run tr).2.val = tr
      rw [DY.Traceful.run_pure]
  rw [hskip] at hbs
  let tr5 := (((((t6.append (RndE 32)).append (NetE key0)).append
    (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB0)))).append
      (EvT (.HonestDH (stB0NoOpk'.sessionInfo "bob") dhsB0 0))).append
      (EvC (.HandshakeSession (stB0NoOpk'.sessionInfo "bob") 40))
  have htr5_len : tr5.length = 44 := by
    simp [tr5, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
      t6_length]
  change Runs (bobStart "bob" "alice" kh1 1 mh1 33 1) t6 (tr5.length + 2)
    (((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 m0))).append
      (EvT (.MessageKey (stB0NoOpk'.sessionInfo "bob") .receiver seedB0 key0 0 2
        (tr5.length + 0 + 2)))).append
      (StT "bob" stB1NoOpk)) at hbs
  rw [htr5_len] at hbs
  exact hbs

private theorem runs_trace_eq {x : Traceful Unit} {tr tr' : ExecTrace} (h : Runs x tr () tr') :
    (x.run tr).2.val = tr' := h.2

theorem honestHandshakeWithoutOpkTrace_eq :
    honestHandshakeWithoutOpkTrace = tHandshakeNoOpk := by
  unfold honestHandshakeWithoutOpkTrace
  refine runs_trace_eq ?_
  refine Runs.bind runs_step1 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step2 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step3 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind runs_step4 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t5_runs ?_; dsimp only [Nat.reduceAdd, Nat.reduceSub]
  refine Runs.bind t6_runs ?_
  exact Runs.bind tHandshakeNoOpk_bobStart_runs (Runs.pure () _)

theorem honestHandshakeWithoutOpkTrace_reachable :
    honestHandshakeWithoutOpkTrace.Reachable reachability := by
  rw [honestHandshakeWithoutOpkTrace_eq]
  exact reach_of_runs tHandshakeNoOpk_bobStart_runs (bobStart_reachable t6_reach)

theorem honestHandshakeWithOpkTrace_eq : honestHandshakeWithOpkTrace = wTrOpk := by
  unfold honestHandshakeWithOpkTrace
  refine runs_trace_eq ?_
  refine Runs.bind runs_step1 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step2 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step3 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind runs_step4 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t4Opk_runs ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t5Opk_runs ?_; dsimp only [Nat.reduceAdd, Nat.reduceSub]
  refine Runs.bind t6Opk_runs ?_
  exact Runs.bind t7Opk_runs (Runs.pure () _)

theorem honestHandshakeWithOpkTrace_reachable :
    honestHandshakeWithOpkTrace.Reachable reachability := by
  rw [honestHandshakeWithOpkTrace_eq]
  exact wTrOpk_reach

theorem honestSessionTrace_eq : honestSessionTrace = t11 := by
  unfold honestSessionTrace
  refine runs_trace_eq ?_
  refine Runs.bind runs_step1 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step2 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step3 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind runs_step4 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t5_runs ?_; dsimp only [Nat.reduceAdd, Nat.reduceSub]
  refine Runs.bind t6_runs ?_; dsimp only [Nat.reduceAdd, Nat.reduceSub]
  refine Runs.bind t7_runs ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind t8_runs ?_
  refine Runs.bind t9_runs ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t10_runs ?_
  exact Runs.bind t11_runs (Runs.pure () _)

theorem honestSessionTrace_reachable : honestSessionTrace.Reachable reachability := by
  rw [honestSessionTrace_eq]
  exact t11_reach

private theorem runs_recv_spkBPk :
    Runs (Network.receiveMessage 14) t11 (dhPk spkB) t11 := by
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob") = true := by
    have h1 := runs_step2.1
    unfold DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.guardTrace at h1
    rw [DY.Traceful.run_bind, DY.Traceful.run_mk] at h1
    cases h : (!DY.Libsignal.PQXDH.isRegisteredB t1 "bob")
    · simp [h] at h1
    · rfl
  have ht2 : t2 = registerIdentityTr t1 "bob" :=
    (Runs.registerIdentity (tr := t1) (p := "bob") hunregB).2
  have hat_here : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
      (hi : i = tr.length), ((tr.append e).at? i : Option E) = some e := by
    intro E _ tr e i hi; subst hi; exact DY.Trace.at?_append tr e
  have hik2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]
    unfold registerIdentityTr
    dsimp only
    rw [t1_length]
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t1_length])
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey (tr := t2) (b := "bob") (idH := 9) hik2).2
  have ht3_14 : t3.at? 14 = some (NetE (dhPk spkB)) := by
    rw [ht3]
    unfold genSignedPrekeyTr
    dsimp only
    rw [t2_length]
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact hat_here _ _
      (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        t2_length])
  have hle_of_runs : ∀ {α : Type} {x : Traceful α} {tr tr' : ExecTrace} {a : α},
      Runs x tr a tr' → tr ≤ tr' :=
    fun {_} {x} {tr} {_} {_} h => h.2 ▸ (x.run tr).2.property
  have hle3_11 : t3 ≤ t11 :=
    DY.Trace.le_trans _ _ _ (hle_of_runs runs_step4)
      (DY.Trace.le_trans _ _ _ (hle_of_runs t5_runs)
        (DY.Trace.le_trans _ _ _ (hle_of_runs t6_runs)
          (DY.Trace.le_trans _ _ _ (hle_of_runs t7_runs)
            (DY.Trace.le_trans _ _ _ (hle_of_runs t8_runs)
              (DY.Trace.le_trans _ _ _ (hle_of_runs t9_runs)
                (DY.Trace.le_trans _ _ _ (hle_of_runs t10_runs) (hle_of_runs t11_runs)))))))
  exact Runs.receiveMessage (Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle3_11 ht3_14)

theorem exposedSessionTrace_eq : exposedSessionTrace = wTr := by
  unfold exposedSessionTrace
  refine runs_trace_eq ?_
  refine Runs.bind runs_step1 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step2 ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind runs_step3 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind runs_step4 ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t5_runs ?_; dsimp only [Nat.reduceAdd, Nat.reduceSub]
  refine Runs.bind t6_runs ?_; dsimp only [Nat.reduceAdd, Nat.reduceSub]
  refine Runs.bind t7_runs ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind t8_runs ?_
  refine Runs.bind t9_runs ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t10_runs ?_; dsimp only [Nat.reduceSub]
  refine Runs.bind t11_runs ?_
  refine Runs.bind runs_recv_spkBPk ?_
  refine Runs.bind t12_runs ?_
  refine Runs.bind t13_runs ?_; dsimp only [Nat.reduceAdd]
  refine Runs.bind t14_runs ?_
  exact Runs.bind t15_runs (Runs.pure () _)

theorem exposedSessionTrace_reachable : exposedSessionTrace.Reachable reachability := by
  rw [exposedSessionTrace_eq]
  exact wTr_reach

theorem nonvacuity_examples_reachable_proof :
    keySetupTrace.Reachable reachability ∧
    honestHandshakeWithoutOpkTrace.Reachable reachability ∧
    honestHandshakeWithOpkTrace.Reachable reachability ∧
    honestSessionTrace.Reachable reachability ∧
    exposedSessionTrace.Reachable reachability ∧
    (∀ r : ProtocolSetup, (setupTrace r).Reachable reachability) :=
  ⟨keySetupTrace_reachable, honestHandshakeWithoutOpkTrace_reachable,
    honestHandshakeWithOpkTrace_reachable, honestSessionTrace_reachable,
    exposedSessionTrace_reachable, setupTrace_reachable⟩

end Symbolic.Proofs.Tests.Nonvacuity
