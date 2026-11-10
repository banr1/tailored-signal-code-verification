/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInv
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeStepInvB
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
import Symbolic.Proofs.Tests.Shared.Composed.Runs
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
public import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Prefix Call Peeling and PKI/Handshake Trace Invariants

Peels `MatchesEventsAt` on `trace0.take k` from the front into `PeeledValid` call records
(`peel_evsRange`) to extract a `ValidCoinLens` schedule (`clsOfCalls`), and proves preservation of
`PkiUnchanged` and `OnlyAliceDone` across network and party steps after `t4`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA

open scoped DY.Libsignal.Composed
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState KeyKind AliceHandshakeOut)
open DY.Libsignal.TripleRatchet (TRState)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   runSteps StepsWF RunMatches MatchesEventsAt
   nextBundleIds pendingPreKey stepIn)
open Symbolic.Swarm.COMPOSED.CompTrace
  (Preserves TRStEntry RndE NetE TRStE CEvE TREvE PQEvE at?_append_cases
   proj_inj_eq)
open Symbolic.Swarm.CREF
  (bks_getEventAt_of_le iniAliceStartTr getEventAt_pq_iniAliceStartTr)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (StP EvP registerIdentityTr genSignedPrekeyTr genPQPrekeyTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t1 t2 t3 t4 t1_length t2_length t3_length t4_length
   ikA ikB spkB pqskB)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (t1_eq_pure t2_eq_pure t3_eq_pure t4_eq_pure)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
  (trace0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev ev_not_rejected)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
  (stepsWF_append_right)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (trace0_take_succ sendCallOf)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

/-- A party step `s` paired with its preceding `.network` steps `pre` and visible entries `v`. -/
structure PeeledCall where
  pre : List Step
  s : Step
  v : List VisEntry

/-- Slice `[.run (ev j), ..., .run (ev (k - 1))]` defined by front recursion for `peel_evsRange`. -/
def evsRange (j k : Nat) : List CliEvent :=
  if _ : j < k then .run (ev j) :: evsRange (j + 1) k else []
termination_by k - j

theorem evsRange_self (k : Nat) : evsRange k k = [] := by
  unfold evsRange; simp

theorem evsRange_lt {j k : Nat} (h : j < k) :
    evsRange j k = .run (ev j) :: evsRange (j + 1) k := by
  conv => lhs; unfold evsRange
  simp [h]

theorem evsRange_snoc {j k : Nat} (h : j ≤ k) :
    evsRange j (k + 1) = evsRange j k ++ [.run (ev k)] := by
  by_cases hlt : j < k
  · rw [evsRange_lt (by omega), evsRange_lt hlt, List.cons_append, evsRange_snoc hlt]
  · have heq : j = k := by omega
    subst heq
    rw [evsRange_self, List.nil_append, evsRange_lt (by omega), evsRange_self]
termination_by k - j

theorem trace0_take_eq_evsRange : ∀ {k : Nat}, k ≤ 25 → trace0.take k = evsRange 0 k
  | 0, _ => by simp [evsRange_self]
  | k + 1, hk => by
    rw [trace0_take_succ (by omega), trace0_take_eq_evsRange (by omega),
        evsRange_snoc (Nat.zero_le k)]

def traceAfterCalls : List PeeledCall → ExecTrace → ExecTrace
  | [], tr => tr
  | c :: cs, tr => traceAfterCalls cs (c.s.next (runSteps c.pre tr))

def bundleIdsAfter : Nat → Nat → Option BundlePreKeyIds → Option BundlePreKeyIds
  | _, 0, cur => cur
  | j, n + 1, cur => bundleIdsAfter (j + 1) n (nextBundleIds cur (ev j))

/-- Inductive validity of a peeled call sequence `cs` for `evsRange j (j + cs.length)`. -/
inductive PeeledValid (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (visAll : List VisEntry) :
    Nat → Option BundlePreKeyIds → ExecTrace → List PeeledCall → List Step → Prop where
  | nil {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {tail : List Step} :
      (∀ x ∈ tail, ∃ msg, x = .network msg) →
      PeeledValid r S g visAll j initIds tr [] tail
  | cons {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {c : PeeledCall} {cs : List PeeledCall} {rest : List Step} :
      (∀ x ∈ c.pre, ∃ msg, x = .network msg) →
      c.s.PreCond (runSteps c.pre tr) →
      c.s.LocalOk (runSteps c.pre tr) →
      RunMatches evictedI0 r S g (runSteps c.pre tr) c.s (ev j) c.v initIds →
      (∀ w ∈ c.v, w ∈ visAll) →
      PeeledValid r S g visAll (j + 1) (nextBundleIds initIds (ev j))
        (c.s.next (runSteps c.pre tr)) cs rest →
      PeeledValid r S g visAll j initIds tr (c :: cs) (c.pre ++ c.s :: rest)

theorem peel_evsRange {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ (n j : Nat) {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {ss : List Step} {vis : List VisEntry},
      j + n ≤ 25 →
      StepsWF ss tr →
      MatchesEventsAt evictedI0 r S g initIds tr ss (evsRange j (j + n)) vis →
      (∀ w ∈ vis, w ∈ visAll) →
      ∃ cs : List PeeledCall, cs.length = n ∧ PeeledValid r S g visAll j initIds tr cs ss
  | 0, j, initIds, tr, ss, vis, _, _, hm, _ => by
    rw [Nat.add_zero, evsRange_self] at hm
    cases hm with
    | nil hinv =>
      exact ⟨[], rfl, .nil (fun x hx => NfeTrace.step_invisible_eq_network (hinv x hx))⟩
  | n + 1, j, initIds, tr, ss, vis, hjn, hwf, hm, hsub => by
    have hlt : j < j + (n + 1) := by omega
    rw [evsRange_lt hlt] at hm
    have hj25 : j < 25 := by omega
    have hm_copy := hm
    cases hm with
    | run0 _ hrej _ => exact False.elim (ev_not_rejected j hj25 hrej)
    | @run1 _ _ pre s ss' _ _ v vs hinv hrm hrest =>
      have hwf' := stepsWF_append_right pre hwf
      obtain ⟨hpre, hlok, hwf_tail⟩ := hwf'
      have hnet : ∀ x ∈ pre, ∃ msg, x = .network msg :=
        fun x hx => NfeTrace.step_invisible_eq_network (hinv x hx)
      have hv_sub : ∀ w ∈ v, w ∈ visAll := fun w hw => hsub w (List.mem_append_left _ hw)
      have hvs_sub : ∀ w ∈ vs, w ∈ visAll := fun w hw => hsub w (List.mem_append_right _ hw)
      rw [show j + (n + 1) = (j + 1) + n by omega] at hrest
      obtain ⟨cs, hlen, hpv⟩ := peel_evsRange n (j + 1) (by omega) hwf_tail hrest hvs_sub
      exact ⟨⟨pre, s, v⟩ :: cs, by simp [hlen],
        .cons hnet hpre hlok hrm hv_sub hpv⟩

/-- Extracts the SPQR coin draw length of a `.messageEncrypt` step (defaulting to `0`). -/
def stepCoinLen : Step → Nat
  | .messageEncrypt _ _ cl _ => cl
  | _ => 0

/-- Maps each send index `s` to the SPQR coin length of call `sendCallOf s` in `cs`. -/
def clsOfCalls (cs : List PeeledCall) (s : Nat) : Nat :=
  match cs[sendCallOf s]? with
  | some c => stepCoinLen c.s
  | none => 0

theorem peeledValid_localOk_at {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {cs : List PeeledCall} {ss : List Step},
      PeeledValid r S g visAll j initIds tr cs ss →
      ∀ (i : Nat) (c : PeeledCall), cs[i]? = some c →
        ∃ tr_i, c.s.LocalOk tr_i
  | _, _, _, _, _, .nil _, i, _, hget => by simp at hget
  | _, _, tr, _, _, .cons _ _ hlok _ _ hpv, 0, c, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget
    exact ⟨_, hlok⟩
  | _, _, _, _, _, .cons _ _ _ _ _ hpv, i + 1, c, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact peeledValid_localOk_at hpv i c hget

theorem validCoinLens_clsOfCalls {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {cs : List PeeledCall} {ss : List Step}
    (hpv : PeeledValid r S g visAll j initIds tr cs ss) :
    ValidCoinLens (clsOfCalls cs) := by
  intro s _
  unfold clsOfCalls
  rcases hget : cs[sendCallOf s]? with _ | c
  · exact Or.inl rfl
  · dsimp only
    obtain ⟨tr_i, hlok⟩ := peeledValid_localOk_at hpv (sendCallOf s) c hget
    cases hs : c.s with
    | messageEncrypt me idx cl pq =>
      rw [hs] at hlok
      dsimp only [stepCoinLen]
      exact hlok.1
    | _ => dsimp only [stepCoinLen]; exact Or.inl rfl

abbrev PQStEntry :=
  DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState PQXDHState)
abbrev PQEvEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent

/-- After `setupTrace r = t4`, no step adds any `PQXDHState` or `IdentityRegistered` entry. -/
def PkiUnchanged (tr : ExecTrace) : Prop :=
  t4 ≤ tr ∧
  (∀ i p kst, 22 ≤ i → (tr.at? i : Option PQStEntry) ≠ some ⟨⟨p, kst⟩⟩) ∧
  (∀ i p pk vk c, 22 ≤ i → (tr.at? i : Option PQEvEntry) ≠ some ⟨.IdentityRegistered p pk vk c⟩)

theorem pkiUnchanged_t4 : PkiUnchanged t4 := by
  refine ⟨DY.Trace.le_refl t4, ?_, ?_⟩
  · intro i p kst hi hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQStEntry) t4 i
    rw [hat, t4_length] at hlt; simp at hlt; omega
  · intro i p pk vk c hi hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry) t4 i
    rw [hat, t4_length] at hlt; simp at hlt; omega

private theorem pkiUnchanged_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : PkiUnchanged tr) (e : E)
    (hnoneSt : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQStEntry) = none)
    (hnoneEv : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQEvEntry) = none) :
    PkiUnchanged (tr.append e) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr e), ?_, ?_⟩
  · intro i p kst hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.1 i p kst hi hat0
    · rw [hnoneSt] at hproj; cases hproj
  · intro i p pk vk c hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.2 i p pk vk c hi hat0
    · rw [hnoneEv] at hproj; cases hproj

private theorem pkiUnchanged_append_pqEv {tr : ExecTrace} (h : PkiUnchanged tr)
    (ev : PQXDHEvent)
    (hnreg : ∀ p pk vk c, ev ≠ .IdentityRegistered p pk vk c) :
    PkiUnchanged (tr.append (PQEvE ev)) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr _), ?_, ?_⟩
  · intro i p kst hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.1 i p kst hi hat0
    · cases hproj
  · intro i p pk vk c hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.2 i p pk vk c hi hat0
    · simp only [PQEvE, proj_inj_eq, Option.some.injEq] at hproj
      injection hproj with hev
      exact hnreg p pk vk c hev

private theorem preserves_pki_genRand (n : Nat) :
    Preserves PkiUnchanged (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr h => (Runs.genRand tr n).2.symm ▸ pkiUnchanged_append_non h (RndE n) rfl rfl

private theorem preserves_pki_sendMessage (m : DY.Bytes) :
    Preserves PkiUnchanged (DY.Network.sendMessage m) :=
  fun tr h => (Runs.sendMessage tr m).2.symm ▸ pkiUnchanged_append_non h (NetE m) rfl rfl

private theorem preserves_pki_storeTR (p : Participant) (st : TRState) :
    Preserves PkiUnchanged (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr h => by rw [storeLocalState_tr_snd_eq]; exact pkiUnchanged_append_non h (TRStE p st) rfl rfl

private theorem preserves_pki_logC (ev : ComposedEvent) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd_eq]; exact pkiUnchanged_append_non h (CEvE ev) rfl rfl

private theorem preserves_pki_logTR (ev : DY.Libsignal.TripleRatchet.TREvent) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd_eq]; exact pkiUnchanged_append_non h (TREvE ev) rfl rfl

private theorem preserves_pki_logPQ (ev : PQXDHEvent)
    (hnreg : ∀ p pk vk c, ev ≠ .IdentityRegistered p pk vk c) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => (Runs.logEvent tr ev).2.symm ▸ pkiUnchanged_append_pqEv h ev hnreg

private theorem preserves_pki_getKey (p : Participant) (h : Nat) (kind : KeyKind) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_pki_lookupIdentity (p : Participant) (h : Nat) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_pki_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (pk : DY.Bytes) (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves PkiUnchanged
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_pki_logTR _) fun _ => ih _ _

private theorem preserves_pki_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    Preserves PkiUnchanged (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact Preserves.pure _
  · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
    exact Preserves.bind
      (Preserves.bind (Preserves.guardP _) fun _ =>
        Preserves.bind (preserves_pki_genRand 32) fun _ => Preserves.pure _)
      fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_pki_logMKAndStore (me : Participant)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (r par : Nat) (st : TRState) :
    Preserves PkiUnchanged
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_pki_logTR _) fun _ => preserves_pki_storeTR me st

private theorem preserves_pki_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem preserves_pki_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

local macro "pki_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_pki_prodCasesOn
  | with_reducible apply preserves_pki_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_pki_genRand
  | with_reducible apply preserves_pki_storeTR | with_reducible apply preserves_pki_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_pki_getKey | with_reducible apply preserves_pki_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt
  | with_reducible apply preserves_pki_ensureReceiverChain
  | with_reducible apply preserves_pki_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_pki_logMKAndStore
  | (apply preserves_pki_logPQ; intros; rintro ⟨⟩)
  | with_reducible apply preserves_pki_logC
  | with_reducible apply preserves_pki_logTR | split | with_reducible intro))

theorem pkiUnchanged_runSteps_network :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) → PkiUnchanged tr → PkiUnchanged (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : PkiUnchanged ((Step.network m).next tr) := by
      rw [next_network]; exact pkiUnchanged_append_non h (NetE m) rfl rfl
    exact pkiUnchanged_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem pkiUnchanged_step_party {s : Step} {tr : ExecTrace}
    (hcls : s.cls = .party) (hpki : PkiUnchanged tr) : PkiUnchanged (s.next tr) := by
  cases s with
  | aliceStart a b idIdx regB bh =>
    have hact : Preserves PkiUnchanged (DY.Libsignal.Composed.aliceStart a b idIdx regB bh) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]; unfold DY.Libsignal.PQXDH.aliceHandshake; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | bobStart b a kh regA mh pqIdx spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]; unfold DY.Libsignal.PQXDH.bobHandshake; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageEncrypt me stateIdx cl pq =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageEncryptAbort me stateIdx =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx mIdx pq spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | _ => simp [Step.cls] at hcls

private theorem t1_eq : t1 = registerIdentityTr DY.Trace.nil "alice" := t1_eq_pure
private theorem t2_eq : t2 = registerIdentityTr t1 "bob" := by
  rw [t2_eq_pure]; unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.t2Pure; rw [← t1_eq_pure]
private theorem t3_eq : t3 = genSignedPrekeyTr t2 "bob" ikB := by
  rw [t3_eq_pure]; unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.t3Pure; rw [← t2_eq_pure]
private theorem t4_eq : t4 = genPQPrekeyTr t3 "bob" ikB := by
  rw [t4_eq_pure]; unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.t4Pure; rw [← t3_eq_pure]

private theorem t4_pqSt_cases {i : Nat} {p : Participant} {kst : PQXDHState}
    (hat : (t4.at? i : Option PQStEntry) = some ⟨⟨p, kst⟩⟩) :
    (p = "alice" ∧ kst = { kind := .identity, sk := ikA }) ∨
    (p = "bob" ∧ kst = { kind := .identity, sk := ikB }) ∨
    (p = "bob" ∧ kst = { kind := .signedPrekey, sk := spkB }) ∨
    (p = "bob" ∧ kst = { kind := .pqPrekey, sk := pqskB }) := by
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQStEntry) = none →
      ((tr0.append e).at? j : Option PQStEntry) = some ⟨⟨p, kst⟩⟩ →
      (tr0.at? j : Option PQStEntry) = some ⟨⟨p, kst⟩⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  rw [t4_eq] at hat; dsimp only [genPQPrekeyTr] at hat
  replace hat := peel_non rfl (peel_non rfl hat)
  rcases at?_append_cases hat with ⟨_, hat3⟩ | ⟨_, hproj4⟩
  · replace hat3 := peel_non rfl (peel_non rfl (peel_non rfl hat3))
    rw [t3_eq] at hat3; dsimp only [genSignedPrekeyTr] at hat3
    replace hat3 := peel_non rfl (peel_non rfl hat3)
    rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hproj3⟩
    · replace hat2 := peel_non rfl (peel_non rfl (peel_non rfl hat2))
      rw [t2_eq] at hat2; dsimp only [registerIdentityTr] at hat2
      rcases at?_append_cases hat2 with ⟨_, hat2'⟩ | ⟨_, hproj2⟩
      · iterate 4 replace hat2' := peel_non rfl hat2'
        rw [t1_eq] at hat2'; dsimp only [registerIdentityTr] at hat2'
        rcases at?_append_cases hat2' with ⟨_, hat1'⟩ | ⟨_, hproj1⟩
        · iterate 4 replace hat1' := peel_non rfl hat1'
          have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQStEntry)
            (DY.Trace.nil : ExecTrace) i
          rw [hat1', Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt
        · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hproj1
          cases hproj1
          exact Or.inl ⟨rfl, rfl⟩
      · rw [t1_length] at hproj2
        cases hproj2
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rw [t2_length] at hproj3
      cases hproj3
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rw [t3_length] at hproj4
    cases hproj4
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

private theorem t4_pqEv_cases {i : Nat} {ev : PQXDHEvent}
    (hat : (t4.at? i : Option PQEvEntry) = some ⟨ev⟩) :
    ev = .IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true ∨
    ev = .IdentityRegistered "bob" (dhPk ikB) (DY.Signature.vk ikB) true ∨
    (∃ p k, ev = .SignedPrekeyPublished p k) ∨
    (∃ p k, ev = .PQPrekeyPublished p k) := by
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntry) = none →
      ((tr0.append e).at? j : Option PQEvEntry) = some ⟨ev⟩ →
      (tr0.at? j : Option PQEvEntry) = some ⟨ev⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  rw [t4_eq] at hat; dsimp only [genPQPrekeyTr] at hat
  replace hat := peel_non rfl (peel_non rfl (peel_non rfl hat))
  rcases at?_append_cases hat with ⟨_, hat3⟩ | ⟨_, hproj4⟩
  · replace hat3 := peel_non rfl (peel_non rfl hat3)
    rw [t3_eq] at hat3; dsimp only [genSignedPrekeyTr] at hat3
    replace hat3 := peel_non rfl (peel_non rfl (peel_non rfl hat3))
    rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hproj3⟩
    · replace hat2 := peel_non rfl (peel_non rfl hat2)
      rw [t2_eq] at hat2; dsimp only [registerIdentityTr] at hat2
      replace hat2 := peel_non rfl (peel_non rfl (peel_non rfl hat2))
      rcases at?_append_cases hat2 with ⟨_, hat1⟩ | ⟨_, hproj2⟩
      · replace hat1 := peel_non rfl hat1
        rw [t1_eq] at hat1; dsimp only [registerIdentityTr] at hat1
        replace hat1 := peel_non rfl (peel_non rfl (peel_non rfl hat1))
        rcases at?_append_cases hat1 with ⟨_, hat0⟩ | ⟨_, hproj1⟩
        · replace hat0 := peel_non rfl hat0
          have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry)
            (DY.Trace.nil : ExecTrace) i
          rw [hat0, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt
        · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hproj1
          cases hproj1
          exact Or.inl rfl
      · rw [t1_length] at hproj2
        cases hproj2
        exact Or.inr (Or.inl rfl)
    · cases hproj3
      exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · cases hproj4
    exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))

private theorem t4_pqReg_cases {i : Nat} {p : Participant} {pk vk : DY.Bytes} {c : Bool}
    (hat : (t4.at? i : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩) :
    (p = "alice" ∧ pk = dhPk ikA ∧ vk = DY.Signature.vk ikA) ∨
    (p = "bob" ∧ pk = dhPk ikB ∧ vk = DY.Signature.vk ikB) := by
  rcases t4_pqEv_cases hat with h1 | h2 | ⟨_, _, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
  · cases h1; exact Or.inl ⟨rfl, rfl, rfl⟩
  · cases h2; exact Or.inr ⟨rfl, rfl, rfl⟩

theorem at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

theorem pki_pin_st {tr : ExecTrace} (hpki : PkiUnchanged tr)
    {i : Nat} {p : Participant} {kst : PQXDHState}
    (hat : (tr.at? i : Option PQStEntry) = some ⟨⟨p, kst⟩⟩) :
    (p = "alice" ∧ kst = { kind := .identity, sk := ikA }) ∨
    (p = "bob" ∧ kst = { kind := .identity, sk := ikB }) ∨
    (p = "bob" ∧ kst = { kind := .signedPrekey, sk := spkB }) ∨
    (p = "bob" ∧ kst = { kind := .pqPrekey, sk := pqskB }) := by
  by_cases hlt : i < 22
  · rw [at?_of_le_lt hpki.1 (by rwa [t4_length])] at hat
    exact t4_pqSt_cases hat
  · exact False.elim (hpki.2.1 i p kst (by omega) hat)

theorem pki_pin_reg {tr : ExecTrace} (hpki : PkiUnchanged tr)
    {i : Nat} {p : Participant} {pk vk : DY.Bytes} {c : Bool}
    (hat : (tr.at? i : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩) :
    (p = "alice" ∧ pk = dhPk ikA ∧ vk = DY.Signature.vk ikA) ∨
    (p = "bob" ∧ pk = dhPk ikB ∧ vk = DY.Signature.vk ikB) := by
  by_cases hlt : i < 22
  · rw [at?_of_le_lt hpki.1 (by rwa [t4_length])] at hat
    exact t4_pqReg_cases hat
  · exact False.elim (hpki.2.2 i p pk vk c (by omega) hat)

/-- Every `AliceDone` event logged on `tr` carries `(ek0, ct0)`. -/
def OnlyAliceDone (ek0 ct0 : DY.Bytes) (tr : ExecTrace) : Prop :=
  ∀ d a b ik1 ik2 spk pq opk ek ct keys,
    tr.getEventAt PQXDHEvent d = some (.AliceDone a b ik1 ik2 spk pq opk ek ct keys) →
    ek = ek0 ∧ ct = ct0

theorem onlyAliceDone_t4 (ek0 ct0 : DY.Bytes) : OnlyAliceDone ek0 ct0 t4 := by
  intro d a b ik1 ik2 spk pq opk ek ct keys hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : (t4.at? d : Option PQEvEntry) with _ | ⟨ev0⟩
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; dsimp only at hget
    injection hget with hget'
    rcases ev0 with ⟨ev0⟩
    dsimp only at hget'
    subst hget'
    rcases t4_pqEv_cases hat with h1 | h2 | ⟨_, _, h3⟩ | ⟨_, _, h4⟩
    · cases h1
    · cases h2
    · cases h3
    · cases h4

theorem onlyAliceDone_append_non {E : Type} [ExecTraceTypes.Has E]
    {ek0 ct0 : DY.Bytes} {tr : ExecTrace} (h : OnlyAliceDone ek0 ct0 tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQEvEntry) = none) :
    OnlyAliceDone ek0 ct0 (tr.append e) := by
  intro d a b ik1 ik2 spk pq opk ek ct keys hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : ((tr.append e).at? d : Option PQEvEntry) with _ | ⟨ev0⟩
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; dsimp only at hget
    injection hget with hget'
    rcases ev0 with ⟨ev0⟩
    dsimp only at hget'
    subst hget'
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h d a b ik1 ik2 spk pq opk ek ct keys
        (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0])
    · rw [hnone] at hproj; cases hproj

theorem onlyAliceDone_runSteps_network {ek0 ct0 : DY.Bytes} :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      OnlyAliceDone ek0 ct0 tr → OnlyAliceDone ek0 ct0 (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : OnlyAliceDone ek0 ct0 ((Step.network m).next tr) := by
      rw [next_network]; exact onlyAliceDone_append_non h (NetE m) rfl
    exact onlyAliceDone_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem onlyAliceDone_iniAliceStartTr {tr : ExecTrace} {a b : Participant}
    {o : AliceHandshakeOut} (h0 : OnlyAliceDone o.ek o.ct tr) :
    OnlyAliceDone o.ek o.ct (iniAliceStartTr tr a b o) := by
  have hle : tr ≤ iniAliceStartTr tr a b o := by
    unfold iniAliceStartTr; dsimp only
    iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.append_le _ _
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := getEventAt_pq_iniAliceStartTr tr a b o
  intro d a' b' ik1 ik2 spk pq opk ek ct keys hget
  by_cases hlt : d < tr.length
  · rw [bks_getEventAt_of_le PQXDHEvent hle hlt] at hget
    exact h0 d a' b' ik1 ik2 spk pq opk ek ct keys hget
  · by_cases hgt : tr.length + 9 ≤ d
    · have hlen : (iniAliceStartTr tr a b o).length = tr.length + 9 :=
        Symbolic.Swarm.CREF.length_iniAliceStartTr tr a b o
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
      rcases hat : ((iniAliceStartTr tr a b o).at? d : Option PQEvEntry) with _ | _
      · rw [hat] at hget; cases hget
      · have := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry)
          (iniAliceStartTr tr a b o) d
        rw [hat, hlen] at this; simp at this; omega
    · have hd : d = tr.length + 0 ∨ d = tr.length + 1 ∨ d = tr.length + 2 ∨
          d = tr.length + 3 ∨ d = tr.length + 4 ∨ d = tr.length + 5 ∨
          d = tr.length + 6 ∨ d = tr.length + 7 ∨ d = tr.length + 8 := by omega
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [Nat.add_zero, hp0] at hget; cases hget
      · rw [hp1] at hget; cases hget
      · rw [hp2] at hget; cases hget
      · rw [hp3] at hget; cases hget
      · rw [hp4] at hget; cases hget
      · rw [hp5] at hget
        injection hget with h1
        injection h1 with _ _ _ _ _ _ _ hek hct _
        exact ⟨hek.symm, hct.symm⟩
      · rw [hp6] at hget; cases hget
      · rw [hp7] at hget; cases hget
      · rw [hp8] at hget; cases hget

theorem onlyAliceDone_messageEncrypt {ek0 ct0 : DY.Bytes} {tr : ExecTrace}
    {me : Participant} {stateIdx cl pq : Nat}
    (h0 : OnlyAliceDone ek0 ct0 tr) :
    OnlyAliceDone ek0 ct0 ((Step.messageEncrypt me stateIdx cl pq).next tr) := by
  have hact : Preserves (OnlyAliceDone ek0 ct0)
      (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
    have hlogTR : ∀ ev : DY.Libsignal.TripleRatchet.TREvent,
        Preserves (OnlyAliceDone ek0 ct0) (DY.ProtocolEvent.logEvent ev) :=
      fun ev t h => by rw [logEvent_snd_eq]; exact onlyAliceDone_append_non h (TREvE ev) rfl
    have hstoreTR : ∀ p (st : TRState),
        Preserves (OnlyAliceDone ek0 ct0) (DY.PersistentLocalState.storeLocalState p st) :=
      fun p st t h => by rw [storeLocalState_tr_snd_eq]; exact onlyAliceDone_append_non h (TRStE p st) rfl
    have hgen : ∀ n, Preserves (OnlyAliceDone ek0 ct0) (DY.Random.genRand n : Traceful DY.Bytes) :=
      fun n t h => (Runs.genRand t n).2.symm ▸ onlyAliceDone_append_non h (RndE n) rfl
    have hsend : ∀ m, Preserves (OnlyAliceDone ek0 ct0) (DY.Network.sendMessage m) :=
      fun m t h => (Runs.sendMessage t m).2.symm ▸ onlyAliceDone_append_non h (NetE m) rfl
    have hlmk : ∀ s dir seed pqSalt n r par st,
        Preserves (OnlyAliceDone ek0 ct0)
          (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
      fun _ _ _ _ _ _ _ st =>
        Preserves.bind (hlogTR _) fun _ => hstoreTR me st
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    dsimp only at *
    repeat (first
      | with_reducible apply Preserves.bind | with_reducible apply preserves_pki_prodCasesOn
      | with_reducible apply preserves_pki_optionCasesOn | with_reducible apply Preserves.pure
      | with_reducible apply Preserves.failure | with_reducible apply hgen
      | with_reducible apply hsend | with_reducible apply hlogTR
      | with_reducible apply Preserves.getLocalState_tr
      | with_reducible apply Preserves.receiveMessage
      | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.guardP
      | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
      | with_reducible apply Preserves.requireTracePredicate | with_reducible apply Preserves.traceLength
      | with_reducible apply hlmk | split | with_reducible intro)
  dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0

theorem pendingPreKey_eq_of_onlyAliceDone {ek0 ct0 : DY.Bytes} {tr : ExecTrace} {stateIdx : Nat}
    {ek ct : DY.Bytes}
    (honly : OnlyAliceDone ek0 ct0 tr)
    (hpend : pendingPreKey tr stateIdx = some (ek, ct)) :
    ek = ek0 ∧ ct = ct0 := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt at hpend
  rcases hat : (tr.at? stateIdx : Option TRStEntry) with _ | e
  · simp [hat] at hpend
  · rw [hat] at hpend; dsimp only [Option.map, Option.bind] at hpend
    split at hpend
    · cases hpend
    · obtain ⟨_, ev0, _, heq_evs, hmatch, _⟩ := List.findSome?_eq_some_iff.mp hpend
      have hev_mem : ev0 ∈ DY.Libsignal.Composed.Refinement.sessionHandshakeEvents tr
          (e.st.state.sessionInfo e.st.participant) := by
        rw [heq_evs]; simp
      unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hev_mem
      obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hev_mem
      rcases hce : tr.getEventAt ComposedEvent i with _ | ⟨s, d⟩
      · rw [hce] at hi; cases hi
      · rw [hce] at hi; dsimp only at hi
        split at hi
        · cases ev0 <;> simp at hmatch
          obtain ⟨rfl, rfl⟩ := hmatch
          exact honly d _ _ _ _ _ _ _ _ _ _ hi
        · cases hi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
