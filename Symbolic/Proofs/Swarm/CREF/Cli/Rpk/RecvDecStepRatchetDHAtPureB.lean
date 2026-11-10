/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.Random
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.Swarm.CREF.TR.SpqrSemDef
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHAtPureA
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc uOf_leBytes uOf_lt

cref_open
cref_open_tr
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3 Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (at?_append_of_lt)

section AliceCoinsLen32

open Symbolic.Swarm.CREF.XplSteps

private def NoAliceDoneFrom (n : Nat) (t : ExecTrace) : Prop :=
  ∀ i ev, n ≤ i → t.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev →
    DY.Libsignal.Composed.Refinement.isAliceDone ev = false

private def NoAliceDone {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, NoAliceDoneFrom tr.length (x.run tr).2.val

private theorem noAliceDone_of_quiet {α : Type} {x : Traceful α} (hx : XQuiet x) : NoAliceDone x := by
  intro tr i ev hi hev
  have hnone := (hx tr i hi).2.1
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
  rw [hnone] at hev; cases hev

private theorem noAliceDoneFrom_trans {n : Nat} {t t' : ExecTrace} (hle : t ≤ t')
    (h1 : NoAliceDoneFrom n t) (h2 : NoAliceDoneFrom t.length t') : NoAliceDoneFrom n t' := by
  intro i ev hi hev
  by_cases hlt : i < t.length
  · refine h1 i ev hi ?_
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev ⊢
    rwa [← xat?_le_eq hle hlt]
  · exact h2 i ev (by omega) hev

private theorem noAliceDone_bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoAliceDone x) (hf : ∀ a, NoAliceDone (f a)) : NoAliceDone (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · exact noAliceDoneFrom_trans (xrun_le _ _) (hx tr) (hf _ _)
  · exact hx tr

private theorem noAliceDone_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (h : ∀ x : DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent,
      ((tr.append e).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = some x →
      DY.Libsignal.Composed.Refinement.isAliceDone x.ev = false) :
    NoAliceDoneFrom tr.length (tr.append e) := by
  intro i ev hi hev
  have hlt : tr.length < (tr.append e).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  rcases Nat.lt_or_ge tr.length i with hgt | hle
  · have hn := (xnone_of_ge (t := tr.append e) (i := i)
      (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)).2.1
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev; rw [hn] at hev; cases hev
  · obtain rfl : i = tr.length := by omega
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
    rcases hx : ((tr.append e).at? tr.length :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | x
    · rw [hx] at hev; cases hev
    · rw [hx] at hev; injection hev with hev_eq; subst hev_eq; exact h x hx

private theorem NoAliceDoneFrom.elim {n : Nat} {t : ExecTrace} (h : NoAliceDoneFrom n t)
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent} (hi : n ≤ i)
    (hev : t.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev) :
    DY.Libsignal.Composed.Refinement.isAliceDone ev = false :=
  h i ev hi hev

attribute [irreducible] NoAliceDoneFrom

private theorem noAliceDone_logEvent_pq (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (h : DY.Libsignal.Composed.Refinement.isAliceDone ev = false) :
    NoAliceDone (DY.ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1]
  refine noAliceDone_append tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent) fun x hx => ?_
  rw [DY.Trace.at?_append] at hx; injection hx with hx'; cases hx'; exact h

private theorem noAliceDone_logEvent_tr (ev : TREvent) :
    NoAliceDone (DY.ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1]
  refine noAliceDone_append tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT TREvent) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT TREvent)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

private theorem noAliceDone_logEvent_c (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoAliceDone (DY.ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1]
  refine noAliceDone_append tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

private theorem noAliceDone_storeTR (p : Participant) (st : TRState) :
    NoAliceDone (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1]
  refine noAliceDone_append tr (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState)) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState))).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

private theorem noAliceDone_storePQ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    NoAliceDone (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk,
    ← Symbolic.DYBridge.DY.Trace.append_eq_1]
  refine noAliceDone_append tr (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState))).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

private theorem noAliceDone_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (r src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (n : UInt32), NoAliceDone (DY.Libsignal.TripleRatchet.logSkippedKeys s pk r src ck n k)
  | 0, _, _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | k + 1, ck, n => by
    rw [DY.Libsignal.TripleRatchet.logSkippedKeys]
    exact noAliceDone_bind (noAliceDone_logEvent_tr _) fun _ => noAliceDone_logSkippedKeys s pk r src k _ _

private theorem noAliceDone_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r p : Nat) (st : TRState) :
    NoAliceDone (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact noAliceDone_bind (noAliceDone_logEvent_tr _) fun _ => noAliceDone_storeTR _ _

local macro "nad_step_1" : tactic =>
  `(tactic| first
    | with_reducible refine noAliceDone_bind ?_ fun _ => ?_
    | with_reducible exact noAliceDone_logEvent_tr _
    | with_reducible refine noAliceDone_logEvent_pq _ ?_
    | with_reducible exact noAliceDone_logEvent_c _
    | with_reducible exact noAliceDone_storeTR _ _
    | with_reducible exact noAliceDone_storePQ _ _)

local macro "nad_step_2" : tactic =>
  `(tactic| first
    | with_reducible exact noAliceDone_logSkippedKeys _ _ _ _ _ _ _
    | with_reducible exact noAliceDone_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    | with_reducible exact noAliceDone_of_quiet (xquiet_bobHandshake _ _ _ _ _ _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_receiveSignalMsg _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_ensureReceiverChain _ _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_verifyMacAndDecrypt _ _ _ _))

local macro "nad_step_3" : tactic =>
  `(tactic| first
    | with_reducible exact noAliceDone_of_quiet (xquiet_genRand _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_sendMessage _)
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_receiveMessage _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_getLocalState _ _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_getEntry _)))

local macro "nad_step_4" : tactic =>
  `(tactic| first
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_guard _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix xfix_traceLength)
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_guardTrace _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    | with_reducible exact noAliceDone_of_quiet (xquiet_of_fix xfix_failure)
    | split)

local macro "nad_step" : tactic =>
  `(tactic| first | nad_step_1 | nad_step_2 | nad_step_3 | nad_step_4)

private theorem noAliceDone_setup (a b : Participant) (w : Bool) :
    NoAliceDone (Move.setup a b w).act := by
  dsimp only [Move.act]
  unfold setupAct
    DY.Libsignal.PQXDH.registerIdentity DY.Libsignal.PQXDH.genSignedPrekey
    DY.Libsignal.PQXDH.genPQPrekey DY.Libsignal.PQXDH.genOneTimePrekey
  repeat' nad_step
  all_goals rfl

private theorem noAliceDone_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (r : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pq : Nat) (sp : UInt32) :
    NoAliceDone (DY.Libsignal.Composed.bobStart b a kh r mh pq sp) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  dsimp only
  repeat' nad_step
  all_goals rfl

private theorem noAliceDone_messageEncrypt (me : Participant) (si cl pq : Nat) :
    NoAliceDone (DY.Libsignal.TripleRatchet.messageEncrypt me si cl pq) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  repeat' nad_step

private theorem noAliceDone_messageDecrypt (me : Participant) (si mi pq : Nat) (sp : UInt32) :
    NoAliceDone (DY.Libsignal.TripleRatchet.messageDecrypt me si mi pq sp) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  repeat' nad_step

private theorem noAliceDone_messageDecryptSkipped (me : Participant) (si mi k pq : Nat) (sp : UInt32) :
    NoAliceDone (DY.Libsignal.TripleRatchet.messageDecryptSkipped me si mi k pq sp) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  repeat' nad_step

private theorem noAliceDone_nonAlice {m : Move}
    (hnotA : ∀ a b i r h s, m ≠ .aliceStart a b i r h s) :
    NoAliceDone m.act := by
  cases m with
  | setup a b w => exact noAliceDone_setup a b w
  | aliceStart a b i r h s => exact absurd rfl (hnotA a b i r h s)
  | bobStart b a kh r mh pq sp sh =>
    exact noAliceDone_bind (noAliceDone_bobStart b a kh r mh pq sp) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | encrypt me si cl pq wr =>
    exact noAliceDone_bind (noAliceDone_messageEncrypt me si cl pq) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | encryptAbort me si =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
    repeat' nad_step
  | encryptFail me si cl =>
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix xfix_traceLength)) fun _ =>
      noAliceDone_bind (noAliceDone_messageEncrypt me si cl _) fun _ =>
        noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | decrypt me si mi pq sp wr =>
    exact noAliceDone_bind (noAliceDone_messageDecrypt me si mi pq sp) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | decryptSkipped me si mi k pq sp wr =>
    exact noAliceDone_bind (noAliceDone_messageDecryptSkipped me si mi k pq sp) fun _ =>
      noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
  | compromiseIK p si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromiseIK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | compromiseSPK b si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromiseSPK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | compromiseOPK b si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromiseOPK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_guardOnTrace _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | compromisePQSPK b si =>
    dsimp only [Move.act]
    refine noAliceDone_bind ?_ fun _ => noAliceDone_of_quiet (xquiet_of_fix (xfix_pure _))
    unfold DY.Libsignal.PQXDH.compromisePQSPK
    exact noAliceDone_bind (noAliceDone_of_quiet (xquiet_of_fix (xfix_getKey _ _ _))) fun _ =>
      noAliceDone_bind (noAliceDone_logEvent_pq _ rfl) fun _ =>
        noAliceDone_of_quiet (xquiet_sendMessage _)
  | exposeKey me si k =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeKey
    repeat' nad_step
  | exposeSpqr me si =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeSpqr
    repeat' nad_step
  | exposeSkipped k =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeSkipped
    repeat' nad_step
  | attackerSend msg =>
    dsimp only [Move.act]
    repeat' nad_step
  | brkDH =>
    exact noAliceDone_logEvent_pq .BrokenDH rfl
  | brkKEM =>
    exact noAliceDone_logEvent_pq .BrokenKEM rfl
  | reject dr =>
    dsimp only [Move.act]
    repeat' nad_step

private theorem pqEv_at?_append_other {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : i = tr.length)
    (he : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none) :
    ((tr.append e).at? i :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
  subst hi; rw [Symbolic.Swarm.CREF.at?_append_length, he]

private theorem aliceStart_aliceDone_step {tr : ExecTrace}
    {a b : Participant} {idH regB : Nat} {bh : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat}
    (hanc : (Move.aliceStart a b idH regB bh shown).LogsSessionCompletion tr)
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hi : tr.length ≤ i)
    (hev : ((Move.aliceStart a b idH regB bh shown).next tr).getEventAt
      DY.Libsignal.PQXDH.PQXDHEvent i = some ev)
    (had : DY.Libsignal.Composed.Refinement.isAliceDone ev = true) :
    i = tr.length + 5 ∧
      ⟨.rng, [randTerm (tr.length + 1) 32], .kyberCoin 0, none⟩ ∈
        (Move.aliceStart a b idH regB bh shown).vis tr := by
  let m := Move.aliceStart a b idH regB bh shown
  let Inv : ExecTrace → Prop := fun tr' =>
    NoAliceDoneFrom tr.length tr' ∨
      ∃ (hs : DY.Libsignal.PQXDH.AliceHandshakeOut) (dhsA : DY.Bytes) (stA : TRState),
        tr' = ((((((((tr.append (Symbolic.Swarm.COMPOSED.CompInv.RndE 32)).append
          (Symbolic.Swarm.COMPOSED.CompInv.RndE 32)).append
          (Symbolic.Swarm.COMPOSED.CompInv.RndE 32)).append
          (Symbolic.Swarm.COMPOSED.CompInv.NetE hs.ek)).append
          (Symbolic.Swarm.COMPOSED.CompInv.NetE hs.ct)).append
          (Symbolic.Swarm.COMPOSED.CompInv.EvE
            (.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))).append
          (Symbolic.Swarm.COMPOSED.CompInv.TREvE (.InitSession a b (DY.DiffieHellman.dhPk dhsA) hs.spk))).append
          (Symbolic.Swarm.COMPOSED.CompInv.CEvE (.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append
          (Symbolic.Swarm.COMPOSED.CompInv.TRStE a stA)
  have hshape : Inv (m.next tr) := by
    change Inv (((DY.Libsignal.Composed.aliceStart a b idH regB bh >>= fun _ => Pure.pure ()).run tr).2.val)
    rw [xrun_bind_unit]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine Symbolic.Swarm.COMPOSED.CompPresPQXDH.bind_aliceHandshake_at a b idH regB bh tr
      (Or.inl (by simpa only [DY.Traceful.run_pure] using noAliceDone_of_quiet (xquiet_of_fix (xfix_pure ())) tr))
      (Or.inl (by
        simpa only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1,
          DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk,
          Symbolic.DYBridge.DY.Trace.append_eq_1] using noAliceDone_of_quiet (xquiet_genRand 32) tr))
      fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ => by
        dsimp only [Inv]
        right
        simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
          Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
          Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1,
          DY.Libsignal.TripleRatchet.traceLength,
          DY.Traceful.run_bind, DY.Traceful.run_pure, DY.Traceful.run_mk,
          Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2,
          Nat.add_assoc]
        let hs := Symbolic.Swarm.COMPOSED.CompPresPQXDH.aliceOut tr ikA ikBPk spkPk pqPk opk
        let dhsA : DY.Bytes := ({ timestamp := Trace.length tr + (1 + 1), size := 32 } : DY.Random.Random DY.Bytes).pack
        let cc := createChain hs.keys.rk hs.spk dhsA
        let stA : TRState := {
          peer := b
          myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA
          peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB
          rk := cc.1
          dhs := dhsA
          cks := cc.2
          ns := 0
          pn := 0
          sid := DY.Concat.concat (DY.DiffieHellman.dhPk dhsA) hs.keys.rk
          initiator := true
          rIdx := 1
          recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }]
          spqr := Spqr.spqrInit hs.keys.pqr spqrA2B
        }
        exact ⟨hs, dhsA, stA, rfl⟩
  rcases hshape with hno | ⟨hs, dhsA, stA, htr'⟩
  · rw [hno.elim hi hev] at had; cases had
  · have hlen35 : 35 ≤ (m.vis tr).length := by
      by_contra hlt35
      have hneff := noSessionEffect_aliceStart_short' hanc (Nat.lt_of_not_le hlt35)
      have hmem : i ∈ newIndices tr (m.next tr) := xpl_mem_newIndices hi (xlt_of_getEventAt hev)
      have hn := (hneff i hmem).2.1
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
      rcases hat : (((Move.aliceStart a b idH regB bh shown).next tr).at? i :
          Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | e
      · rw [hat] at hev; cases hev
      · rw [hat] at hev
        cases hev
        have hf := Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_pred_eq_false hn hat
          (p := DY.Libsignal.Composed.Refinement.isAliceDone)
        rw [had] at hf; cases hf
    have hex : exposures tr (m.next tr) = [] :=
      exposures_nil_of_not_leakKind' rfl (fun h => nomatch h)
    have hvis_eq : m.vis tr = (aliceVis tr (m.next tr) bh).take shown := by
      rw [xpl_vis_eq, hex, List.append_nil]; rfl
    have hshown : 35 ≤ shown := by
      rw [hvis_eq, List.length_take] at hlen35; omega
    have hnr : newRandoms tr (m.next tr) =
        [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32),
         (randTerm (tr.length + 2) 32, 32)] := by
      rw [htr']
      have h0 : tr.length ≤ tr.length := Nat.le_refl _
      rw [Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_of_proj (by simp only [Symbolic.Swarm.CREF.length_append']; omega) _ rfl,
          Symbolic.Swarm.CREF.newRandoms_append_rnd (by simp only [Symbolic.Swarm.CREF.length_append']; omega),
          Symbolic.Swarm.CREF.newRandoms_append_rnd (by simp only [Symbolic.Swarm.CREF.length_append']; omega),
          Symbolic.Swarm.CREF.newRandoms_append_rnd h0,
          Symbolic.Swarm.CREF.newRandoms_self]
      simp only [Symbolic.Swarm.CREF.length_append', List.nil_append, List.cons_append, Nat.add_assoc]
    have hi_eq : i = tr.length + 5 := by
      by_contra hne
      have hnone : ((m.next tr).at? i :
          Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
        rw [htr']
        rcases Nat.lt_or_ge i (tr.length + 9) with hlt9 | hge9
        · have : i = tr.length ∨ i = tr.length + 1 ∨ i = tr.length + 2 ∨
              i = tr.length + 3 ∨ i = tr.length + 4 ∨ i = tr.length + 6 ∨
              i = tr.length + 7 ∨ i = tr.length + 8 := by omega
          rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            · repeat (rw [Symbolic.Swarm.COMPOSED.CompPresPQXDH.at?_append_of_lt _ _
                (by simp only [Symbolic.Swarm.CREF.length_append']; omega)])
              exact pqEv_at?_append_other _ _
                (by simp only [Symbolic.Swarm.CREF.length_append']; try omega) rfl
        · exact (xnone_of_ge (by simp only [Symbolic.Swarm.CREF.length_append']; omega)).2.1
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev; rw [hnone] at hev; cases hev
    refine ⟨hi_eq, ?_⟩
    rw [hvis_eq]
    unfold aliceVis
    rw [hnr]
    dsimp only [List.map, aliceDraws, List.take]
    rw [List.take_of_length_le (by simp [kyberCoinEntries]; omega)]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
    unfold kyberCoinEntries
    exact List.mem_map.mpr ⟨0, by simp, rfl⟩

private theorem movesAnchored_snoc_at {ms : List Move} {m : Move} {tr : ExecTrace}
    (h : MovesAnchored (ms ++ [m]) tr) :
    MovesAnchored ms tr ∧ m.LogsSessionCompletion (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact ⟨trivial, h.1⟩
  | cons m₀ ms ih =>
    obtain ⟨h₀, hrest⟩ := h
    obtain ⟨hms, hm⟩ := ih hrest
    exact ⟨⟨h₀, hms⟩, hm⟩

private theorem aliceDone_kyberCoin0_mem_runMoves
    (tr₀ : ExecTrace) (hno₀ : NoAliceDoneFrom 0 tr₀)
    (ms : List Move) (hanc : MovesAnchored ms tr₀)
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hev : (runMoves ms tr₀).1.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev)
    (had : DY.Libsignal.Composed.Refinement.isAliceDone ev = true) :
    ∃ t, i = t + 5 ∧
      ⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ ∈ (runMoves ms tr₀).2 := by
  induction ms using List.reverseRecOn generalizing i ev with
  | nil =>
    dsimp only [runMoves] at hev
    rw [hno₀.elim (Nat.zero_le _) hev] at had; cases had
  | append_singleton ms₀ m ih =>
    obtain ⟨hanc₀, hm_anc⟩ := movesAnchored_snoc_at hanc
    have hfst : (runMoves (ms₀ ++ [m]) tr₀).1 = m.next (runMoves ms₀ tr₀).1 := by
      rw [Symbolic.Swarm.CREF.b5_runMoves_append_fst]; rfl
    have hsnd : (runMoves (ms₀ ++ [m]) tr₀).2 =
        (runMoves ms₀ tr₀).2 ++ m.vis (runMoves ms₀ tr₀).1 := by
      rw [Symbolic.Swarm.CREF.b5_runMoves_append_snd]
      dsimp only [runMoves]
      rw [List.append_nil]
    rw [hfst] at hev
    by_cases hlt : i < (runMoves ms₀ tr₀).1.length
    · have hev₀ : (runMoves ms₀ tr₀).1.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev := by
        simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev ⊢
        rwa [← xat?_le_eq (xrun_le m.act (runMoves ms₀ tr₀).1) hlt]
      obtain ⟨t, rfl, hmem⟩ := ih hanc₀ hev₀ had
      exact ⟨t, rfl, hsnd ▸ List.mem_append_left _ hmem⟩
    · have hge : (runMoves ms₀ tr₀).1.length ≤ i := Nat.le_of_not_lt hlt
      by_cases hmA : ∃ a b idH regB bh shown, m = .aliceStart a b idH regB bh shown
      · obtain ⟨a, b, idH, regB, bh, shown, rfl⟩ := hmA
        obtain ⟨hi_eq, hmem⟩ := aliceStart_aliceDone_step hm_anc hge hev had
        exact ⟨(runMoves ms₀ tr₀).1.length, hi_eq, hsnd ▸ List.mem_append_right _ hmem⟩
      · have hno := noAliceDone_nonAlice
          (fun a b idH regB bh shown heq => hmA ⟨a, b, idH, regB, bh, shown, heq⟩)
          (runMoves ms₀ tr₀).1
        rw [hno.elim hge hev] at had; cases had

private theorem noAliceDoneFrom_next {m : Move} (hm : NoAliceDone m.act) (tr : ExecTrace) :
    NoAliceDoneFrom tr.length (m.next tr) :=
  hm tr

private theorem noAliceDoneFrom_setupTrace (r₀ : ProtocolSetup) :
    NoAliceDoneFrom 0 (setupTrace r₀) := by
  rw [← setupMove_next_nil, ← Symbolic.DYBridge.DY.Trace.length_eq_1 (α := ExecTrace.Entry)]
  exact noAliceDoneFrom_next (noAliceDone_setup r₀.alice r₀.bob r₀.withOpk) DY.Trace.nil

private theorem aliceDone_kyberCoin0_mem_runVis
    (r₀ : ProtocolSetup) (ms : List Move)
    (hanc : MovesAnchored ms (setupTrace r₀))
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hev : (runTraceMoves r₀ ms).getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev)
    (had : DY.Libsignal.Composed.Refinement.isAliceDone ev = true) :
    ∃ t, i = t + 5 ∧
      ⟨.rng, [randTerm (t + 1) 32], .kyberCoin 0, none⟩ ∈ runVis r₀ ms := by
  rw [Symbolic.Swarm.CREF.b5_runTrace_eq] at hev
  obtain ⟨t, ht, hmem⟩ :=
    aliceDone_kyberCoin0_mem_runMoves (setupTrace r₀) (noAliceDoneFrom_setupTrace r₀) ms hanc hev had
  rw [Symbolic.Swarm.CREF.b5_runVis_eq]
  exact ⟨t, ht, List.mem_append_right _ hmem⟩

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hxy hrest ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.Mem.head _, hxy⟩
    · obtain ⟨x, hx, hr⟩ := ih hy'
      exact ⟨x, List.Mem.tail _ hx, hr⟩

theorem aliceSlot_sigma_len32_of_explains
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    {who : List Participant} {ok : Nat → Bool}
    (g : Ghost) (ms : List Move) {τ₁ : List MachineEvent}
    (hEx : ExplainsMoves interpretation r₀ S who ok g ms τ₁) :
    ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot (runTraceMoves r₀ ms) t →
      (g.σ (t + 1) 32).length = 32 := by
  intro t hSlot
  obtain ⟨_, _, _, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, _, _, hevA⟩ := hSlot
  have hev : (runTraceMoves r₀ ms).getEventAt DY.Libsignal.PQXDH.PQXDHEvent (t + 5) =
      some (.AliceDone a b ikA ikB spk pqpk opk ek ct keys) := by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hevA
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hevA]
  obtain ⟨t', ht_eq, hmem⟩ :=
    aliceDone_kyberCoin0_mem_runVis r₀ ms hEx.1.2.1.2.2.1.2.1 hev rfl
  have ht : t' = t := by omega
  subst ht
  obtain ⟨e, _, hmatch⟩ := forall₂_mem_right hEx.1.2.2.2.2.2 hmem
  obtain ⟨_, _, t₀, ht₀_eq, hlen32, _⟩ := hmatch
  injection ht₀_eq with ht₀_hd
  subst ht₀_hd
  rwa [gamma_randTerm32_at] at hlen32

end AliceCoinsLen32

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
