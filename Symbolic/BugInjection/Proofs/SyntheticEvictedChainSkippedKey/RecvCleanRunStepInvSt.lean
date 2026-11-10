/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
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
# Party-State Trace Invariants

Defines `NoPartyState`, `NoNewPartyState`, and `ActivePartySt` parameterized by `party : Participant`
and `initRole : Bool`, together with preservation lemmas across network and other-party steps and
snapshot-pinning combinators for `isCurrentSnapshot`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt

open scoped DY.Libsignal.Composed
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step gamma clamp setupTrace runSteps stepIn)
open Symbolic.Swarm.COMPOSED.CompTrace
  (Preserves TRStEntry RndE NetE TRStE PQStE PQEvE CEvE TREvE at?_append_cases
   proj_inj_eq at?_le_some)
open Symbolic.Swarm.CREF
  (bks_stored_of_getLocalState bks_lt_length_of_at? isCurrentSnapshot_false_of_later)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Swarm.CREF.TR.RecvHistStep2 (traceStatesP_setupTrace traceStatesP_at?_st)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
  (StateBytesAgree)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
  (at?_of_le_lt)

def NoPartyState (party : Participant) (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩

theorem noPartyState_setupTrace (party : Participant) (r : ProtocolSetup) :
    NoPartyState party (setupTrace r) := by
  intro i st hat
  exact traceStatesP_at?_st (traceStatesP_setupTrace (P := fun _ => False) r) hat

def NoNewPartyState (party : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ j st, tr₀.length ≤ j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩

theorem noNewPartyState_refl (party : Participant) (tr : ExecTrace) :
    NoNewPartyState party tr tr := by
  refine ⟨DY.Trace.le_refl tr, fun j st hj hat => ?_⟩
  exact absurd (bks_lt_length_of_at? hat) (by omega)

theorem noNewPartyState_trans {party : Participant} {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : NoNewPartyState party tr₀ tr₁) (h12 : NoNewPartyState party tr₁ tr₂) :
    NoNewPartyState party tr₀ tr₂ := by
  refine ⟨DY.Trace.le_trans _ _ _ h01.1 h12.1, fun j st hj hat => ?_⟩
  by_cases hlt : j < tr₁.length
  · rw [at?_of_le_lt h12.1 hlt] at hat
    exact h01.2 j st hj hat
  · exact h12.2 j st (Nat.le_of_not_lt hlt) hat

theorem noPartyState_of_noNew {party : Participant} {tr tr' : ExecTrace}
    (hnew : NoNewPartyState party tr tr') (h0 : NoPartyState party tr) :
    NoPartyState party tr' := by
  intro i st hat
  by_cases hlt : i < tr.length
  · rw [at?_of_le_lt hnew.1 hlt] at hat
    exact h0 i st hat
  · exact hnew.2 i st (Nat.le_of_not_lt hlt) hat

theorem noNewPartyState_append_other {E : Type} [ExecTraceTypes.Has E]
    {party : Participant} {tr₀ tr : ExecTrace}
    (h : NoNewPartyState party tr₀ tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none) :
    NoNewPartyState party tr₀ (tr.append e) := by
  refine noNewPartyState_trans h ⟨DY.Trace.append_le tr e, fun j st hj hat => ?_⟩
  rcases at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · rw [hnone] at hproj; cases hproj

theorem noNewPartyState_append_trSt_ne {party : Participant} {tr₀ tr : ExecTrace}
    (h : NoNewPartyState party tr₀ tr) (p : Participant) (hp : p ≠ party) (st₀ : TRState) :
    NoNewPartyState party tr₀ (tr.append (TRStE p st₀)) := by
  refine noNewPartyState_trans h ⟨DY.Trace.append_le tr _, fun j st hj hat => ?_⟩
  rcases at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · simp only [TRStE, proj_inj_eq, Option.some.injEq] at hproj
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

private theorem preserves_genRand {party : Participant} {tr₀ : ExecTrace} (n : Nat) :
    Preserves (NoNewPartyState party tr₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (Runs.genRand tr n).2.symm ▸ noNewPartyState_append_other hInv (RndE n) rfl

private theorem preserves_sendMessage {party : Participant} {tr₀ : ExecTrace} (m : DY.Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Runs.sendMessage tr m).2.symm ▸ noNewPartyState_append_other hInv (NetE m) rfl

private theorem preserves_storeLocalState_tr {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (hp : p ≠ party) (st : TRState) :
    Preserves (NoNewPartyState party tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by
    rw [storeLocalState_tr_snd_eq]
    exact noNewPartyState_append_trSt_ne hInv p hp st

private theorem preserves_storeLocalState_pq {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves (NoNewPartyState party tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (Runs.storeLocalState tr p st).2.symm ▸
    noNewPartyState_append_other hInv (PQStE p st) rfl

private theorem preserves_logEventPQ {party : Participant} {tr₀ : ExecTrace}
    (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (Runs.logEvent tr ev).2.symm ▸
    noNewPartyState_append_other hInv (PQEvE ev) rfl

private theorem preserves_logEventC {party : Participant} {tr₀ : ExecTrace} (ev : ComposedEvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPartyState_append_other hInv (CEvE ev) rfl

private theorem preserves_logEventTR {party : Participant} {tr₀ : ExecTrace}
    (ev : DY.Libsignal.TripleRatchet.TREvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPartyState_append_other hInv (TREvE ev) rfl

private theorem preserves_getKey {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_lookupIdentity {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logMessageKeyAndStore {party : Participant} {tr₀ : ExecTrace}
    (me : Participant) (hme : me ≠ party) (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_logEventTR _) fun _ => preserves_storeLocalState_tr me hme st

private theorem preserves_dhRatchetStep {party : Participant} {tr₀ : ExecTrace}
    (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ => Preserves.pure _

private theorem preserves_ensureReceiverChain {party : Participant} {tr₀ : ExecTrace}
    (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logSkippedKeys {party : Participant} {tr₀ : ExecTrace}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_logEventTR _) fun _ => ih _ _

local macro "noPartySt_tac" hne:ident : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_genRand
  | with_reducible apply preserves_storeLocalState_tr _ $hne
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
  | with_reducible apply preserves_logMessageKeyAndStore _ $hne
  | with_reducible apply preserves_logEventPQ | with_reducible apply preserves_logEventC
  | with_reducible apply preserves_logEventTR | split | with_reducible intro))

theorem noNewPartyState_step_network {party : Participant} (m : DY.Bytes) (tr : ExecTrace) :
    NoNewPartyState party tr ((Step.network m).next tr) := by
  rw [next_network]
  exact noNewPartyState_append_other (noNewPartyState_refl party tr) (NetE m) rfl

theorem noNewPartyState_runSteps_network {party : Participant} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      NoNewPartyState party tr (runSteps pre tr)
  | [], tr, _ => noNewPartyState_refl party tr
  | s :: pre, tr, hnet => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    exact noNewPartyState_trans (noNewPartyState_step_network m tr)
      (noNewPartyState_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)))

theorem noNewPartyState_step_other {party : Participant} {s : Step} (tr : ExecTrace)
    (hcls : s.cls = .party) (hne : s.party? ≠ some party) :
    NoNewPartyState party tr (s.next tr) := by
  cases s with
  | aliceStart a b idStateIdx regIdxB bh =>
    have hne' : a ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]; unfold DY.Libsignal.PQXDH.aliceHandshake
      noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | bobStart b a kh regIdxA mh pqIdx spqr =>
    have hne' : b ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]; unfold DY.Libsignal.PQXDH.bobHandshake
      noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageEncrypt me stateIdx cl pq =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageEncryptAbort me stateIdx =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx mIdx pq spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | _ => simp [Step.cls] at hcls

/-- `party` has a unique latest stored `TRState` snapshot `stP` on `tr` with role `initRole`,
byte-level state agreement with `stClean`, receiver-chain public keys `recvIdxs`, and current DH
ratchet secret index `skIdx`. -/
def ActivePartySt (party : Participant) (initRole : Bool)
    (S : OpaqueSymbolSemantics) (g g' : Ghost)
    (recvIdxs : List (Fin 16)) (skIdx : Fin 16)
    (stClean : TRState) (tr : ExecTrace) : Prop :=
  (∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨party, st⟩⟩ → st.initiator = initRole) ∧
  ∃ idxP stP,
    (tr.at? idxP : Option TRStEntry) = some ⟨⟨party, stP⟩⟩ ∧
    (∀ j st, idxP < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩) ∧
    StateBytesAgree S g g' stP stClean ∧
    stP.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) = recvIdxs.map evictedPubOfIdx ∧
    evictedSecretIdx (clamp (gamma evictedI0 S g stP.dhs)) = some skIdx

theorem noNewPartyState_preserves_active {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16} {stClean : TRState}
    {tr tr' : ExecTrace}
    (hnew : NoNewPartyState party tr tr')
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr) :
    ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr' := by
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, hrecv, hdhs⟩ := hinv
  refine ⟨?_, idxP, stP, at?_le_some hnew.1 hatP, ?_, hagree, hrecv, hdhs⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat
      exact hrole i st hat
    · exact False.elim (hnew.2 i st (Nat.le_of_not_lt hlt) hat)
  · intro j st hj hat
    by_cases hlt : j < tr.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat
      exact hmaxP j st hj hat
    · exact hnew.2 j st (Nat.le_of_not_lt hlt) hat

/-- Any current `TRState` snapshot loaded by `party` (`isCurrentSnapshot tr stateIdx = true`) must
coincide with the unique latest snapshot tracked by `ActivePartySt`. -/
theorem activePartySt_pin_state {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16} {stClean : TRState}
    {tr : ExecTrace} {stateIdx : Nat} {st : TRState}
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr)
    (hst : ((DY.PersistentLocalState.getLocalState party stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    st.initiator = initRole ∧
    StateBytesAgree S g g' st stClean ∧
    st.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) = recvIdxs.map evictedPubOfIdx ∧
    evictedSecretIdx (clamp (gamma evictedI0 S g st.dhs)) = some skIdx := by
  have hat := bks_stored_of_getLocalState hst
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, hrecv, hdhs⟩ := hinv
  have hle : stateIdx ≤ idxP := by
    by_contra hgt
    exact hmaxP stateIdx st (by omega) hat
  by_cases hlt : stateIdx < idxP
  · exfalso
    have hfalse := isCurrentSnapshot_false_of_later hat hatP hlt
      (by rw [hrole _ _ hatP, hrole _ _ hat])
    rw [hfalse] at hcur
    cases hcur
  · have hidx : stateIdx = idxP := by omega
    subst hidx
    rw [hatP] at hat
    cases hat
    exact ⟨hrole _ _ hatP, hagree, hrecv, hdhs⟩

theorem activePartySt_init {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 16)} {skIdx : Fin 16} {stClean : TRState}
    {tr tr' : ExecTrace}
    (hnone : NoPartyState party tr)
    (hle : tr ≤ tr')
    {idxP' : Nat} {stP' : TRState}
    (hat' : (tr'.at? idxP' : Option TRStEntry) = some ⟨⟨party, stP'⟩⟩)
    (huniq : ∀ j st, tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨party, st⟩⟩ → j = idxP' ∧ st = stP')
    (hinit' : stP'.initiator = initRole)
    (hagree' : StateBytesAgree S g g' stP' stClean)
    (hrecv' : stP'.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) =
      recvIdxs.map evictedPubOfIdx)
    (hdhs' : evictedSecretIdx (clamp (gamma evictedI0 S g stP'.dhs)) = some skIdx) :
    ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr' := by
  have hge : tr.length ≤ idxP' := by
    by_contra hlt
    have hat0 : (tr.at? idxP' : Option TRStEntry) = some ⟨⟨party, stP'⟩⟩ := by
      rw [← at?_of_le_lt hle (by omega)]; exact hat'
    exact hnone idxP' stP' hat0
  refine ⟨?_, idxP', stP', hat', ?_, hagree', hrecv', hdhs'⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hle hlt] at hat
      exact False.elim (hnone i st hat)
    · obtain ⟨_, rfl⟩ := huniq i st (Nat.le_of_not_lt hlt) hat
      exact hinit'
  · intro j st hj hat
    obtain ⟨hj_eq, _⟩ := huniq j st (by omega) hat
    omega

theorem activePartySt_of_unique_new {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs recvIdxs' : List (Fin 16)} {skIdx skIdx' : Fin 16}
    {stClean stClean' : TRState} {tr tr' : ExecTrace}
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr)
    (hle : tr ≤ tr')
    {idxP' : Nat} {stP' : TRState}
    (hge : tr.length ≤ idxP')
    (hat' : (tr'.at? idxP' : Option TRStEntry) = some ⟨⟨party, stP'⟩⟩)
    (huniq : ∀ j st, tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨party, st⟩⟩ → j = idxP' ∧ st = stP')
    (hinit' : stP'.initiator = initRole)
    (hagree' : StateBytesAgree S g g' stP' stClean')
    (hrecv' : stP'.recv.map (fun c => gamma evictedI0 S g c.ratchetKey) =
      recvIdxs'.map evictedPubOfIdx)
    (hdhs' : evictedSecretIdx (clamp (gamma evictedI0 S g stP'.dhs)) = some skIdx') :
    ActivePartySt party initRole S g g' recvIdxs' skIdx' stClean' tr' := by
  obtain ⟨hrole, _⟩ := hinv
  refine ⟨?_, idxP', stP', hat', ?_, hagree', hrecv', hdhs'⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hle hlt] at hat
      exact hrole i st hat
    · obtain ⟨_, rfl⟩ := huniq i st (Nat.le_of_not_lt hlt) hat
      exact hinit'
  · intro j st hj hat
    obtain ⟨hj_eq, _⟩ := huniq j st (by omega) hat
    omega

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
