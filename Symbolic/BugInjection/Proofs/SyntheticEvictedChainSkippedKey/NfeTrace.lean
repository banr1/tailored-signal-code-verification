/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Trace and Bob-State Step Invariants

Defines the `ExecTrace` invariants `NoBobState` (Calls `0..2`) and `BobActiveInv` (Calls `3..24`)
for `EvictedChainSkippedKeyCli`, together with `MatchesEventsAt` `.run`-event peeling and
single-draw `DrawsMatch` coin pinning. Proves preservation across `.network` prefixes and `"alice"`
steps, unique current-snapshot lookup (`bobActiveInv_pin_state`), and single-snapshot state updates
(`bobActiveInv_of_unique_new`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace

open scoped DY.Libsignal.Composed
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.TripleRatchet (TRState RecvChain isCurrentSnapshot setRecvChain)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma ecKey clamp randTerm rngEntry bobDoneBaseKeys setupTrace runSteps
   StepsWF RunMatches RunRejected DrawsMatch BytesMatchEntry GhostWF
   nextBundleIds MatchesEventsAt stepIn)
open Symbolic.Swarm.COMPOSED.CompTrace
  (Preserves TRStEntry RndE NetE TRStE PQStE CEvE TREvE at?_le_some)
open Symbolic.Swarm.CREF
  (bks_stored_of_getLocalState bks_lt_length_of_at? bks_getEventAt_of_le
   bks_lt_length_of_getEventAt isCurrentSnapshot_false_of_later)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Swarm.CREF.TR.RecvHistStep2 (traceStatesP_setupTrace traceStatesP_at?_st)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (gamma_randTerm_eq stepIn_next run_bind_pure_snd attackerSend_next_eq_network)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx evictedSecretIdx)

theorem r_names_of_fit {r : ProtocolSetup}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r) :
    r.alice = "alice" ∧ r.bob = "bob" :=
  hfit.1.2.2.2.1

theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

theorem runSteps_append (xs ys : List Step) (tr : ExecTrace) :
    runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr) := by
  induction xs generalizing tr with
  | nil => rfl
  | cons s xs ih => exact ih (s.next tr)

theorem stepsWF_append_right :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      StepsWF (pre ++ ss) tr → StepsWF ss (runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_append_right pre hwf

theorem preCond_of_stepIn (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : reachability.PreCond (stepIn c x) tr) :
    c.PreCond x tr :=
  (inst.pf_pre x tr).mpr h

theorem preCond_messageEncrypt {me : Participant} {stateIdx cl pq : Nat} {tr : ExecTrace}
    (h : (Step.messageEncrypt me stateIdx cl pq).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    (me, stateIdx, cl, pq) tr h

theorem preCond_messageEncryptAbort {me : Participant} {stateIdx : Nat} {tr : ExecTrace}
    (h : (Step.messageEncryptAbort me stateIdx).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability
    (me, stateIdx) tr h

theorem preCond_messageDecrypt {me : Participant} {stateIdx mIdx pq : Nat} {spqr : UInt32}
    {tr : ExecTrace} (h : (Step.messageDecrypt me stateIdx mIdx pq spqr).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageDecrypt.reachability
    (me, stateIdx, mIdx, pq, spqr) tr h

theorem preCond_messageDecryptSkipped {me : Participant} {stateIdx mIdx sk pq : Nat}
    {spqr : UInt32} {tr : ExecTrace}
    (h : (Step.messageDecryptSkipped me stateIdx mIdx sk pq spqr).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
    (me, stateIdx, mIdx, sk, pq, spqr) tr h

theorem step_invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

theorem step_ok_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.bobStart b a kh regA mh pqIdx spqr).ok tr =
      ((DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqr).run tr).1.isSome :=
  stepIn_ok DY.Libsignal.Composed.bobStart.reachability (b, a, kh, regA, mh, pqIdx, spqr) tr

theorem step_next_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.bobStart b a kh regA mh pqIdx spqr).next tr =
      (DY.Libsignal.Composed.Refinement.Move.bobStart b a kh regA mh pqIdx spqr 0).next tr := by
  dsimp only [DY.Libsignal.Composed.Refinement.Move.next,
    DY.Libsignal.Composed.Refinement.Move.act, Step.next, Step.toInput]
  erw [stepIn_next]
  exact (run_bind_pure_snd _ tr).symm

theorem step_ok_encrypt (me : Participant) (stateIdx cl pq : Nat) (tr : ExecTrace) :
    (Step.messageEncrypt me stateIdx cl pq).ok tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq).run tr).1.isSome :=
  stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stateIdx, cl, pq) tr

theorem step_next_encrypt (me : Participant) (stateIdx cl pq : Nat) (tr : ExecTrace) :
    (Step.messageEncrypt me stateIdx cl pq).next tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq).run tr).2.val :=
  stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stateIdx, cl, pq) tr

theorem step_ok_encryptAbort_false (me : Participant) (stateIdx : Nat) (tr : ExecTrace) :
    (Step.messageEncryptAbort me stateIdx).ok tr = false := by
  unfold Step.ok Step.toInput
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me, stateIdx) tr]
  dsimp only [DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability,
    DY.Libsignal.TripleRatchet.messageEncryptAbort]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst]
  rcases ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with
    _ | st
  · rfl
  · dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, (Runs.genRand _ 32).1]
    dsimp only
    rw [DY.Traceful.run_failure]
    rfl

theorem step_ok_decrypt (me : Participant) (stateIdx mIdx pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecrypt me stateIdx mIdx pq spqr).ok tr =
      ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx mIdx pq spqr).run tr).1.isSome :=
  stepIn_ok DY.Libsignal.TripleRatchet.messageDecrypt.reachability
    (me, stateIdx, mIdx, pq, spqr) tr

theorem step_next_decrypt (me : Participant) (stateIdx mIdx pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecrypt me stateIdx mIdx pq spqr).next tr =
      (DY.Libsignal.Composed.Refinement.Move.decrypt me stateIdx mIdx pq spqr false).next tr := by
  dsimp only [DY.Libsignal.Composed.Refinement.Move.next,
    DY.Libsignal.Composed.Refinement.Move.act, Step.next, Step.toInput]
  erw [stepIn_next]
  exact (run_bind_pure_snd _ tr).symm

theorem step_ok_decryptSkipped (me : Participant) (stateIdx mIdx sk pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecryptSkipped me stateIdx mIdx sk pq spqr).ok tr =
      ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx mIdx sk pq spqr).run
        tr).1.isSome :=
  stepIn_ok DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
    (me, stateIdx, mIdx, sk, pq, spqr) tr

theorem matchesEventsAt_run_peel {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis visAll : List VisEntry}
    (hnotRej : ¬ RunRejected ev)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt evictedI0 r S g initIds tr ss (.run ev :: evs) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll) :
    ∃ pre s ss' v vs,
      (∀ x ∈ pre, ∃ msg, x = .network msg) ∧
      s.PreCond (runSteps pre tr) ∧
      StepsWF ss' (s.next (runSteps pre tr)) ∧
      RunMatches evictedI0 r S g (runSteps pre tr) s ev v initIds ∧
      (∀ w ∈ v, w ∈ visAll) ∧
      (∀ w ∈ vs, w ∈ visAll) ∧
      MatchesEventsAt evictedI0 r S g (nextBundleIds initIds ev)
        (s.next (runSteps pre tr)) ss' evs vs := by
  cases hm with
  | run0 _ hrej _ => exact False.elim (hnotRej hrej)
  | run1 hinv hrm hrest =>
    have hwf' := stepsWF_append_right _ hwf
    obtain ⟨hpre, _, hwf_tail⟩ := hwf'
    refine ⟨_, _, _, _, _, fun x hx => step_invisible_eq_network (hinv x hx),
      hpre, hwf_tail, hrm,
      fun w hw => hsub w (List.mem_append_left _ hw),
      fun w hw => hsub w (List.mem_append_right _ hw), hrest⟩

theorem drawsMatch_single_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll rest : List VisEntry} {ts : Nat} {coins : HwBytes}
    (hgwf : GhostWF g visAll)
    (hmem : rngEntry (randTerm ts 32) ∈ visAll)
    (hdr : DrawsMatch evictedI0 r S g (rngEntry (randTerm ts 32) :: rest) coins) :
    gamma evictedI0 S g (randTerm ts 32) = coins.take 32 := by
  obtain ⟨pieces, _hne, hpref, hfa⟩ := hdr
  obtain ⟨p, ps, hbm, _, rfl⟩ := List.forall₂_cons_right_iff.mp hfa
  unfold BytesMatchEntry rngEntry at hbm
  dsimp only [List.map] at hbm
  have hp_eq : gamma evictedI0 S g (randTerm ts 32) = p := List.singleton_inj.mp hbm.2
  have hlen_sig : (g.σ ts 32).length = 32 :=
    hgwf.1 _ hmem rfl ts 32 (by decide) (by simp [rngEntry])
  have hp_len : p.length = 32 := by
    rw [← hp_eq, gamma_randTerm_eq _ _ _ _ _ (by decide)]
    exact hlen_sig
  obtain ⟨tail, hcoins⟩ := hpref
  change p ++ ps.flatten ++ tail = coins at hcoins
  rw [hp_eq, ← hcoins, List.append_assoc, ← hp_len, List.take_left]

def NoBobState (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) ≠ some ⟨⟨"bob", st⟩⟩

theorem noBobState_setupTrace (r : ProtocolSetup) : NoBobState (setupTrace r) := by
  intro i st hat
  exact traceStatesP_at?_st (traceStatesP_setupTrace (P := fun _ => False) r) hat

def NoNewBobState (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ j st, tr₀.length ≤ j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨"bob", st⟩⟩

theorem noNewBobState_refl (tr : ExecTrace) : NoNewBobState tr tr := by
  refine ⟨DY.Trace.le_refl tr, fun j st hj hat => ?_⟩
  exact absurd (bks_lt_length_of_at? hat) (by omega)

private theorem at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

theorem noNewBobState_trans {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : NoNewBobState tr₀ tr₁) (h12 : NoNewBobState tr₁ tr₂) :
    NoNewBobState tr₀ tr₂ := by
  refine ⟨DY.Trace.le_trans _ _ _ h01.1 h12.1, fun j st hj hat => ?_⟩
  by_cases hlt : j < tr₁.length
  · rw [at?_of_le_lt h12.1 hlt] at hat
    exact h01.2 j st hj hat
  · exact h12.2 j st (Nat.le_of_not_lt hlt) hat

theorem noNewBobState_append_other {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    (h : NoNewBobState tr₀ tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none) :
    NoNewBobState tr₀ (tr.append e) := by
  refine noNewBobState_trans h ⟨DY.Trace.append_le tr e, fun j st hj hat => ?_⟩
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · rw [hnone] at hproj; cases hproj

theorem noNewBobState_append_trSt_ne {tr₀ tr : ExecTrace} (h : NoNewBobState tr₀ tr)
    (p : Participant) (hp : p ≠ "bob") (st₀ : TRState) :
    NoNewBobState tr₀ (tr.append (TRStE p st₀)) := by
  refine noNewBobState_trans h ⟨DY.Trace.append_le tr _, fun j st hj hat => ?_⟩
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨hlt, _⟩ | ⟨rfl, hproj⟩
  · omega
  · simp only [TRStE, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1
    injection h1 with hp_eq _
    exact hp hp_eq

private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem preserves_genRand {tr₀ : ExecTrace} (n : Nat) :
    Preserves (NoNewBobState tr₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (Runs.genRand tr n).2.symm ▸ noNewBobState_append_other hInv (RndE n) rfl

private theorem preserves_sendMessage {tr₀ : ExecTrace} (m : DY.Bytes) :
    Preserves (NoNewBobState tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Runs.sendMessage tr m).2.symm ▸ noNewBobState_append_other hInv (NetE m) rfl

private theorem preserves_storeLocalState_tr {tr₀ : ExecTrace} (p : Participant) (hp : p ≠ "bob")
    (st : TRState) :
    Preserves (NoNewBobState tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by
    rw [storeLocalState_tr_snd_eq]
    exact noNewBobState_append_trSt_ne hInv p hp st

private theorem preserves_storeLocalState_pq {tr₀ : ExecTrace}
    (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves (NoNewBobState tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (Runs.storeLocalState tr p st).2.symm ▸
    noNewBobState_append_other hInv (PQStE p st) rfl

private theorem preserves_logEventPQ {tr₀ : ExecTrace} (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Preserves (NoNewBobState tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (Runs.logEvent tr ev).2.symm ▸
    noNewBobState_append_other hInv (Symbolic.Swarm.COMPOSED.CompTrace.PQEvE ev) rfl

private theorem preserves_logEventC {tr₀ : ExecTrace} (ev : ComposedEvent) :
    Preserves (NoNewBobState tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewBobState_append_other hInv (CEvE ev) rfl

private theorem preserves_logEventTR {tr₀ : ExecTrace}
    (ev : DY.Libsignal.TripleRatchet.TREvent) :
    Preserves (NoNewBobState tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewBobState_append_other hInv (TREvE ev) rfl

private theorem preserves_getKey {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_lookupIdentity {tr₀ : ExecTrace} (p : Participant) (h : Nat) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logMessageKeyAndStore {tr₀ : ExecTrace}
    (me : Participant) (hme : me ≠ "bob") (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_logEventTR _) fun _ => preserves_storeLocalState_tr me hme st

private theorem preserves_dhRatchetStep {tr₀ : ExecTrace} (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ => Preserves.pure _

private theorem preserves_ensureReceiverChain {tr₀ : ExecTrace} (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logSkippedKeys {tr₀ : ExecTrace}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_logEventTR _) fun _ => ih _ _

local macro "noBobSt_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_genRand
  | with_reducible apply preserves_storeLocalState_tr _ (by decide)
  | with_reducible apply preserves_storeLocalState_pq | with_reducible apply preserves_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_getKey | with_reducible apply preserves_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep
  | with_reducible apply preserves_ensureReceiverChain
  | with_reducible apply preserves_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_logMessageKeyAndStore _ (by decide)
  | with_reducible apply preserves_logEventPQ | with_reducible apply preserves_logEventC
  | with_reducible apply preserves_logEventTR | split | with_reducible intro))

private theorem preserves_aliceHandshake_noNewBobSt {tr₀ : ExecTrace} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; noBobSt_tac

private theorem preserves_bobHandshake_noNewBobSt {tr₀ : ExecTrace} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; noBobSt_tac

theorem noNewBobState_step_network (m : DY.Bytes) (tr : ExecTrace) :
    NoNewBobState tr ((Step.network m).next tr) := by
  rw [next_network]
  exact noNewBobState_append_other (noNewBobState_refl tr) (NetE m) rfl

theorem noNewBobState_runSteps_network :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      NoNewBobState tr (runSteps pre tr)
  | [], tr, _ => noNewBobState_refl tr
  | s :: pre, tr, hnet => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    exact noNewBobState_trans (noNewBobState_step_network m tr)
      (noNewBobState_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)))

theorem noNewBobState_step_alice {s : Step} (tr : ExecTrace)
    (hcls : s.cls = .party) (hp : s.party? = some "alice") :
    NoNewBobState tr (s.next tr) := by
  cases s with
  | aliceStart a b idStateIdx regIdxB bh =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.Composed.aliceStart "alice" b idStateIdx regIdxB bh) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
      exact Preserves.bind
        (preserves_aliceHandshake_noNewBobSt "alice" b idStateIdx regIdxB bh)
        fun _ => by noBobSt_tac
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | bobStart b a kh regIdxA mh pqIdx spqr =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.Composed.bobStart "alice" a kh regIdxA mh pqIdx spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
      exact Preserves.bind
        (preserves_bobHandshake_noNewBobSt "alice" a kh regIdxA mh.ek mh.ct)
        fun _ => by noBobSt_tac
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageEncrypt me stateIdx cl pq =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.TripleRatchet.messageEncrypt "alice" stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageEncryptAbort me stateIdx =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort "alice" stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageDecrypt me stateIdx mIdx pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.TripleRatchet.messageDecrypt "alice" stateIdx mIdx pq spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped "alice" stateIdx mIdx sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | _ => simp [Step.cls] at hcls

theorem noBobState_of_noNew {tr tr' : ExecTrace}
    (hnew : NoNewBobState tr tr') (h0 : NoBobState tr) : NoBobState tr' := by
  intro i st hat
  by_cases hlt : i < tr.length
  · rw [at?_of_le_lt hnew.1 hlt] at hat
    exact h0 i st hat
  · exact hnew.2 i st (Nat.le_of_not_lt hlt) hat

/-- Active Bob session invariant on `tr`: every stored Bob `TRState` has `initiator = false`, the
latest Bob snapshot maps `recv` ratchet keys to `recvIdxs` and `dhs` to `skIdx`, and
`bobDoneBaseKeys tr` records base key `3`. -/
def BobActiveInv (S : OpaqueSymbolSemantics) (g : Ghost)
    (recvIdxs : List (Fin 16)) (skIdx : Fin 16) (tr : ExecTrace) : Prop :=
  (∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"bob", st⟩⟩ → st.initiator = false) ∧
  (∃ idxB stB,
    (tr.at? idxB : Option TRStEntry) = some ⟨⟨"bob", stB⟩⟩ ∧
    (∀ j st, idxB < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨"bob", st⟩⟩) ∧
    stB.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) = recvIdxs.map evictedPubOfIdx ∧
    evictedSecretIdx (clamp (gamma evictedI0 S g stB.dhs)) = some skIdx) ∧
  (∃ ek ∈ bobDoneBaseKeys tr,
    ecKey (gamma evictedI0 S g ek) = ecKey (evictedPubOfIdx ⟨3, by decide⟩))

theorem bobDoneBaseKeys_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') :
    bobDoneBaseKeys tr ⊆ bobDoneBaseKeys tr' := by
  intro ek hek
  unfold bobDoneBaseKeys at hek ⊢
  obtain ⟨i, hi_mem, hfind⟩ := List.mem_filterMap.mp hek
  have hi : i < tr.length := List.mem_range.mp hi_mem
  refine List.mem_filterMap.mpr
    ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)), ?_⟩
  rw [bks_getEventAt_of_le DY.Libsignal.PQXDH.PQXDHEvent hle hi]
  exact hfind

theorem noNewBobState_preserves_active {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16} {tr tr' : ExecTrace}
    (hnew : NoNewBobState tr tr')
    (hinv : BobActiveInv S g recvIdxs skIdx tr) :
    BobActiveInv S g recvIdxs skIdx tr' := by
  obtain ⟨hrole, ⟨idxB, stB, hatB, hmaxB, hrecv, hdhs⟩, ⟨ek, hek, hek_eq⟩⟩ := hinv
  refine ⟨?_, ⟨idxB, stB, at?_le_some hnew.1 hatB, ?_, hrecv, hdhs⟩,
    ⟨ek, bobDoneBaseKeys_mono hnew.1 hek, hek_eq⟩⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat
      exact hrole i st hat
    · exact False.elim (hnew.2 i st (Nat.le_of_not_lt hlt) hat)
  · intro j st hj hat
    by_cases hlt : j < tr.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat
      exact hmaxB j st hj hat
    · exact hnew.2 j st (Nat.le_of_not_lt hlt) hat

theorem bobActiveInv_pin_state {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16} {tr : ExecTrace}
    {stateIdx : Nat} {st : TRState}
    (hinv : BobActiveInv S g recvIdxs skIdx tr)
    (hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    st.initiator = false ∧
    st.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) = recvIdxs.map evictedPubOfIdx ∧
    evictedSecretIdx (clamp (gamma evictedI0 S g st.dhs)) = some skIdx := by
  have hat := bks_stored_of_getLocalState hst
  obtain ⟨hrole, ⟨idxB, stB, hatB, hmaxB, hrecv, hdhs⟩, _⟩ := hinv
  have hle : stateIdx ≤ idxB := by
    by_contra hgt
    exact hmaxB stateIdx st (by omega) hat
  by_cases hlt : stateIdx < idxB
  · exfalso
    have hfalse := isCurrentSnapshot_false_of_later hat hatB hlt
      (by rw [hrole _ _ hatB, hrole _ _ hat])
    rw [hfalse] at hcur
    cases hcur
  · have hidx : stateIdx = idxB := by omega
    subst hidx
    rw [hatB] at hat
    cases hat
    exact ⟨hrole _ _ hatB, hrecv, hdhs⟩

theorem bobActiveInv_of_unique_new {S : OpaqueSymbolSemantics} {g : Ghost}
    {recvIdxs recvIdxs' : List (Fin 16)} {skIdx skIdx' : Fin 16} {tr tr' : ExecTrace}
    (hinv : BobActiveInv S g recvIdxs skIdx tr)
    (hle : tr ≤ tr')
    {idxB' : Nat} {stB' : TRState}
    (hge : tr.length ≤ idxB')
    (hat' : (tr'.at? idxB' : Option TRStEntry) = some ⟨⟨"bob", stB'⟩⟩)
    (huniq : ∀ j st, tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨"bob", st⟩⟩ → j = idxB' ∧ st = stB')
    (hinit' : stB'.initiator = false)
    (hrecv' : stB'.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) =
      recvIdxs'.map evictedPubOfIdx)
    (hdhs' : evictedSecretIdx (clamp (gamma evictedI0 S g stB'.dhs)) = some skIdx') :
    BobActiveInv S g recvIdxs' skIdx' tr' := by
  obtain ⟨hrole, _, ⟨ek, hek, hek_eq⟩⟩ := hinv
  refine ⟨?_, ⟨idxB', stB', hat', ?_, hrecv', hdhs'⟩,
    ⟨ek, bobDoneBaseKeys_mono hle hek, hek_eq⟩⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hle hlt] at hat
      exact hrole i st hat
    · obtain ⟨_, rfl⟩ := huniq i st (Nat.le_of_not_lt hlt) hat
      exact hinit'
  · intro j st hj hat
    obtain ⟨hj_eq, _⟩ := huniq j st (by omega) hat
    omega

theorem setRecvChain_map_ratchetKey (recv : List RecvChain) (c' : RecvChain) :
    (setRecvChain recv c').map (·.ratchetKey) = recv.map (·.ratchetKey) := by
  unfold setRecvChain
  induction recv with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.map]
    rw [ih]
    split
    · next h => rw [beq_iff_eq.mp h]
    · rfl

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
