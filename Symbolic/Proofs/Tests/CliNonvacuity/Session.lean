/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Specifications.Model.PQXDH
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Repr
import Init.Data.String.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv4
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv6
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv8Mac
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv8Memo
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart3
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart4
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

/-!
# CLI-Level Reachability of `honestSessionTrace` and `exposedSessionTrace`

Discharges `¬ CollisionAfterExplainedPrefix` across every event of `evsHonest` and `evsExposed`
using `PtNoCollision`, `RecvNoCollision`, and the prefix explanations in `SessionSteps`, and proves
`cliReachable_honestSessionTrace` and `cliReachable_exposedSessionTrace`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Session

set_option maxRecDepth 200000

open DY (Bytes ExecTrace)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   setupTrace runSteps runTrace honestSaltsOf parsePreKeyWire
   RunMatches EnvMatches MatchesEventsAt MatchesEvents Explains)
open DY.Libsignal.Composed.Refinement.Cli
  (ReadCollisionCli ModelAcceptsTermAfterAttackerSends
   NextEventCollides CollisionAfterExplainedPrefix)
open Symbolic.Tests.Nonvacuity (honestSessionTrace exposedSessionTrace)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (CliTraceReachableProof not_readCollisionCli_of_append)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp myHooks myInterp_total myInterp_contracts myHooks_agree mkRecords_wf)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision (not_nextEventCollides_pt)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (NoCollisionFrom
   noRecvCollisionBool not_recvCollisionOn_check
   not_collisionAfterExplainedPrefix_of_from not_collision_nil
   not_collision_step_run not_collision_step_irrelevant not_collision_steps_irrelevant
   not_nextEventCollides_accepted_whisper_check
   not_nextEventCollides_accepted_prekey_no_recv
   not_nextEventCollides_accepted_prekey_subsequent)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 S0 myGhost
   move4_dec1 move6_decReply0 move10_dec2
   msHonest msLeaks msTail msExposed
   runTrace_msHonest runTrace_msExposed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04
  (pkMsg0 pkMsg1 wire0_eq wire1_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel58
  (wireReply0_eq wire2_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces
  (runEv0 runEv1 runEv2 runEv3 runEv4 runEv5 runEv6 runEv7 runEv8
   leakEvCkr leakEvCks evLeaks evsHonest evsExposed
   cliTraces_honest cliTraces_exposed
   evsHonest_all_exit0 evsExposed_all_exit0
   invertsGuarded_honest invertsGuarded_exposed
   coinsFresh_honest coinsFresh_exposed)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
  (msPre3 msPre4 msPre5 msPre6 msPre8
   evsPre3 evsPre4 evsPre5 evsPre6 evsPre8
   trAt visAt runTrace_take_eq honestSalts_take_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (matchesEvents_take
   explains_pre3 explains_pre4 explains_pre5 explains_pre6
   explains_honest explains_pre8 explains_exposed
   msg1Term msgReply0Term msg2Term parse_msg2Term x3Rep x4Rep
   x3Rep_mem_pre3 x4Rep_mem_pre4 msg1Term_mem_pre4
   msgReply0Term_mem_pre6 msg2Term_mem_pre8)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart3
  (not_bobStartCollides_call3)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsStart4
  (noBobStartCollision_call4 noReselectCollision_call4 bobDoneBaseKey_call4
   noReselectCollision_call6 noReselectCollision_call8)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv4
  (noRecvCollision_call4)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv6
  (noRecvCollision_call6)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv8Memo
  (noRecvMemo_call8)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsRecv8Mac
  (noRecvMac_call8)

/-! ## Determinism of `MatchesEvents` Without Invisible Steps or Rejected Runs -/

private theorem pre_eq_nil_of_no_invisible {pre tail : List Step}
    (hpre : ∀ x ∈ pre, x.cls = .invisible)
    (hnoInv : ∀ x ∈ pre ++ tail, x.cls ≠ .invisible) : pre = [] := by
  cases pre with
  | nil => rfl
  | cons x _ =>
    exact absurd (hpre x List.mem_cons_self)
      (hnoInv x (List.mem_append_left _ List.mem_cons_self))

private theorem matchesEvents_len_eq {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hnoInv : ∀ x ∈ ss, x.cls ≠ .invisible)
    (hexit : ∀ ev : RunEvent, .run ev ∈ evs → ∃ out, ev.exit = some (0, out)) :
    ss.length = evs.length := by
  induction hm with
  | nil hinv =>
    have hnil : _ = [] := pre_eq_nil_of_no_invisible (tail := []) hinv (by simpa using hnoInv)
    simp [hnil]
  | run1 hpre _ _ ih =>
    have hnil := pre_eq_nil_of_no_invisible hpre hnoInv
    subst hnil
    simp only [List.nil_append, List.length_cons] at hnoInv ⊢
    exact congrArg (· + 1) (ih (fun x hx => hnoInv x (List.mem_cons_of_mem _ hx))
      (fun ev hev => hexit ev (List.mem_cons_of_mem _ hev)))
  | run0 _ hrej =>
    obtain ⟨out, hout⟩ := hexit _ List.mem_cons_self
    exact absurd hout (hrej out)
  | env hpre _ _ ih =>
    have hnil := pre_eq_nil_of_no_invisible hpre hnoInv
    subst hnil
    simp only [List.nil_append, List.length_cons] at hnoInv ⊢
    exact congrArg (· + 1) (ih (fun x hx => hnoInv x (List.mem_cons_of_mem _ hx))
      (fun ev hev => hexit ev (List.mem_cons_of_mem _ hev)))

private theorem runMatches_vis_unique {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step} {ev : RunEvent}
    {v₁ v₂ : List VisEntry} {initIds : Option BundlePreKeyIds}
    (h₁ : RunMatches interp r S g tr s ev v₁ initIds)
    (h₂ : RunMatches interp r S g tr s ev v₂ initIds) : v₁ = v₂ :=
  h₁.2.2.2.2.2.2.1.trans h₂.2.2.2.2.2.2.1.symm

private theorem envMatches_vis_unique {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step} {ev : EnvEvent}
    {v₁ v₂ : List VisEntry}
    (h₁ : EnvMatches interp r S g tr s ev v₁)
    (h₂ : EnvMatches interp r S g tr s ev v₂) : v₁ = v₂ := by
  cases ev with
  | leak _ _ => exact h₁.2.2.2.1.trans h₂.2.2.2.1.symm
  | breakDH => exact h₁.2.trans h₂.2.symm
  | breakKEM => exact h₁.2.trans h₂.2.symm
  | invertDH _ _ =>
    obtain ⟨_, _, _, _, hv₁, _⟩ := h₁
    obtain ⟨_, _, _, _, hv₂, _⟩ := h₂
    exact hv₁.trans hv₂.symm
  | invertKEM _ _ =>
    obtain ⟨_, _, _, _, hv₁, _⟩ := h₁
    obtain ⟨_, _, _, _, hv₂, _⟩ := h₂
    exact hv₁.trans hv₂.symm
  | registerCorrupt _ _ => exact False.elim h₁

private theorem matchesEvents_vis_unique {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis₁ vis₂ : List VisEntry}
    (hm₁ : MatchesEventsAt interp r S g initIds tr ss evs vis₁)
    (hm₂ : MatchesEventsAt interp r S g initIds tr ss evs vis₂)
    (hnoInv : ∀ x ∈ ss, x.cls ≠ .invisible)
    (hexit : ∀ ev : RunEvent, .run ev ∈ evs → ∃ out, ev.exit = some (0, out)) :
    vis₁ = vis₂ := by
  induction evs generalizing initIds tr ss vis₁ vis₂ with
  | nil =>
    cases hm₁
    cases hm₂
    rfl
  | cons e evs' ih =>
    cases e with
    | run ev =>
      cases hm₁ with
      | run0 _ hrej =>
        obtain ⟨out, hout⟩ := hexit _ List.mem_cons_self
        exact absurd hout (hrej out)
      | run1 hpre₁ hrm₁ hrest₁ =>
        have hnil₁ := pre_eq_nil_of_no_invisible hpre₁ hnoInv
        subst hnil₁
        generalize hss : ([] ++ _ :: _) = ss₀ at hm₂
        cases hm₂ with
        | run0 _ hrej =>
          obtain ⟨out, hout⟩ := hexit _ List.mem_cons_self
          exact absurd hout (hrej out)
        | run1 hpre₂ hrm₂ hrest₂ =>
          have hnil₂ := pre_eq_nil_of_no_invisible hpre₂ (hss ▸ hnoInv)
          subst hnil₂
          simp only [List.nil_append, List.cons.injEq] at hss hnoInv
          rcases hss with ⟨rfl, rfl⟩
          dsimp only [runSteps] at hrm₁ hrm₂ hrest₁ hrest₂
          rw [runMatches_vis_unique hrm₁ hrm₂,
            ih hrest₁ hrest₂ (fun x hx => hnoInv x (List.mem_cons_of_mem _ hx))
              (fun rEv hEv => hexit rEv (List.mem_cons_of_mem _ hEv))]
    | env ev =>
      cases hm₁ with
      | env hpre₁ hem₁ hrest₁ =>
        have hnil₁ := pre_eq_nil_of_no_invisible hpre₁ hnoInv
        subst hnil₁
        generalize hss : ([] ++ _ :: _) = ss₀ at hm₂
        cases hm₂ with
        | env hpre₂ hem₂ hrest₂ =>
          have hnil₂ := pre_eq_nil_of_no_invisible hpre₂ (hss ▸ hnoInv)
          subst hnil₂
          simp only [List.nil_append, List.cons.injEq] at hss hnoInv
          rcases hss with ⟨rfl, rfl⟩
          dsimp only [runSteps] at hem₁ hem₂ hrest₁ hrest₂
          rw [envMatches_vis_unique hem₁ hem₂,
            ih hrest₁ hrest₂ (fun x hx => hnoInv x (List.mem_cons_of_mem _ hx))
              (fun rEv hEv => hexit rEv (List.mem_cons_of_mem _ hEv))]

private theorem msExposed_no_invisible {x : Step} (hx : x ∈ msExposed) : x.cls ≠ .invisible := by
  simp only [msExposed, msHonest, msLeaks, msTail, List.append_assoc, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> nofun

/-! ## Prefix `¬ ReadCollisionCli` and `ModelAcceptsTermAfterAttackerSends` Witnesses -/

section ReadCollisionExposed

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

private theorem noRecvCollision_call8 :
    noRecvCollisionBool myInterp r0 S0 myGhost
      (runTrace r0 msPre8) (visAt 10) (honestSaltsOf r0 msPre8) msg2Term = true := by
  unfold noRecvCollisionBool
  rw [show msPre8 = msExposed.take 10 from rfl,
      runTrace_take_eq 10, honestSalts_take_eq 10, parse_msg2Term]
  simp only [Bool.and_eq_true]
  exact ⟨noRecvMemo_call8, noRecvMac_call8⟩

private theorem not_readCollisionCli_exposed :
    ¬ ReadCollisionCli myInterp r0 S0 myGhost msExposed evsExposed := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, _, _, _, hme, hdec, hget, hcol⟩
  have hnoInv₁ : ∀ x ∈ ss₁, x.cls ≠ .invisible := fun x hx =>
    msExposed_no_invisible (by rw [hss]; exact List.mem_append_left _ hx)
  have hexit₁ : ∀ rEv : RunEvent, .run rEv ∈ evs₁ → ∃ o, rEv.exit = some (0, o) := fun rEv hrEv =>
    evsExposed_all_exit0 rEv (by rw [hevs]; exact List.mem_append_left _ hrEv)
  have hlen_eq : ss₁.length = evs₁.length := matchesEvents_len_eq hme hnoInv₁ hexit₁
  have hk_lt : ss₁.length < 11 := by
    have hms_len : msExposed.length = 11 := rfl
    have hss_len := congrArg List.length hss
    simp only [List.length_append, List.length_cons] at hss_len
    omega
  have hss₁ : ss₁ = msExposed.take ss₁.length := by
    conv_lhs => rw [← List.take_left (l₁ := ss₁) (l₂ := m :: ss₂)]
    rw [← hss]
  have hevs₁ : evs₁ = evsExposed.take ss₁.length := by
    rw [hlen_eq]
    conv_lhs => rw [← List.take_left (l₁ := evs₁) (l₂ := .run ev :: evs₂)]
    rw [← hevs]
  have hm_at : msExposed[ss₁.length]? = some m := by
    rw [hss, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  generalize hk : ss₁.length = k at hk_lt hss₁ hevs₁ hm_at
  have hvis₁ : vis₁ = visAt k := by
    rw [hss₁] at hme hnoInv₁
    rw [hevs₁] at hme hexit₁
    exact matchesEvents_vis_unique hme (matchesEvents_take k (Nat.le_of_lt hk_lt)) hnoInv₁ hexit₁
  rw [hss₁] at hget hcol
  rw [hvis₁] at hcol
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm
    injection hdec with hidx; subst hidx
    have h44 : (runTrace r0 (msExposed.take 4)).getMessageSentAt 44 = some msg1Term := by
      rw [runTrace_take_eq 4]
      change Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t8.getMessageSentAt 44 =
        some msg1Term
      have hpeel : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (T : ExecTrace) (e : E),
          44 < T.length →
          ((T.append e).at? 44 : Option DY.Network.ExecEntryT) =
            (T.at? 44 : Option DY.Network.ExecEntryT) := by
        intro E _ T e hlt
        have hlt' : 44 < (T.snoc (DY.TraceEntryHas.inj e)).length := by
          rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
        have hne : ¬ (44 = T.length) := by omega
        simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, hlt, hlt', ↓reduceDIte,
          Symbolic.DYBridge.DY.Trace.at_eq_2, hne]
      have hsent : ∀ (T : ExecTrace) (b : Bytes) (n : Nat), T.length = n →
          (T.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt n =
            some b := by
        intro T b n hn; subst hn
        rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
      have ⟨b7, ht7⟩ : ∃ b7,
          Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7.getMessageSentAt 44 = some b7 :=
        ⟨_, by
          dsimp only [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7,
            Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr]
          apply hsent
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t6_length]⟩
      have hm1 : msg1Term = b7 := by unfold msg1Term; rw [ht7]; rfl
      rw [hm1]
      unfold Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t8
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      repeat (rw [hpeel _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7_length]; omega)])
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at ht7
      exact ht7
    rw [h44] at hget; injection hget with ht; subst ht
    exact not_recvCollisionOn_check noRecvCollision_call4 hcol
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm
    injection hdec with hidx; subst hidx
    have h64 : (runTrace r0 (msExposed.take 6)).getMessageSentAt 64 = some msgReply0Term := by
      rw [runTrace_take_eq 6]
      change Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10.getMessageSentAt 64 =
        some msgReply0Term
      have hsent : ∀ (T : ExecTrace) (b : Bytes) (n : Nat), T.length = n →
          (T.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt n =
            some b := by
        intro T b n hn; subst hn
        rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
      have ⟨b10, ht10⟩ : ∃ b10,
          Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10.getMessageSentAt 64 = some b10 :=
        ⟨_, by
          dsimp only [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10,
            Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr]
          apply hsent
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t9_length]⟩
      unfold msgReply0Term
      rw [ht10]; rfl
    rw [h64] at hget; injection hget with ht; subst ht
    exact not_recvCollisionOn_check noRecvCollision_call6 hcol
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm; cases hdec
  · injection hm_at with hm; subst hm
    injection hdec with hidx; subst hidx
    have h82 : (runTrace r0 (msExposed.take 10)).getMessageSentAt 82 = some msg2Term := by
      rw [runTrace_take_eq 10]
      change Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14.getMessageSentAt 82 =
        some msg2Term
      have hsent : ∀ (T : ExecTrace) (b : Bytes) (n : Nat), T.length = n →
          (T.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt n =
            some b := by
        intro T b n hn; subst hn
        rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
      have ⟨b14, ht14⟩ : ∃ b14,
          Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14.getMessageSentAt 82 = some b14 :=
        ⟨_, by
          dsimp only [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14,
            Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr]
          apply hsent
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13_length]⟩
      unfold msg2Term
      rw [ht14]; rfl
    rw [h82] at hget; injection hget with ht; subst ht
    exact not_recvCollisionOn_check noRecvCollision_call8 hcol

end ReadCollisionExposed

private theorem not_readCollisionCli_take (k : Nat) :
    ¬ ReadCollisionCli myInterp r0 S0 myGhost (msExposed.take k) (evsExposed.take k) :=
  not_readCollisionCli_of_append
    (ss₂ := msExposed.drop k) (more := evsExposed.drop k)
    (by rw [List.take_append_drop, List.take_append_drop]; exact not_readCollisionCli_exposed)

private theorem modelAccepts_direct {ss ss' : List Step} {evs₁ evs' : List CliEvent}
    {ev : RunEvent} {m : Step} {msgIdx : Nat} {t : Bytes} {vis₁ : List VisEntry}
    (hdec : m.decryptMsgIdx? = some msgIdx)
    (hget : (runTrace r0 ss).getMessageSentAt msgIdx = some t)
    (hss : ss ++ [m] = ss')
    (hevs : evs₁ ++ [.run ev] = evs')
    (hexp : Explains myInterp r0 S0 myGhost ss' vis₁ evs') :
    ModelAcceptsTermAfterAttackerSends myInterp r0 S0 myGhost ss evs₁ ev t := by
  refine ⟨[], m, msgIdx, myGhost, vis₁, by simp, hdec, rfl, fun _ _ => rfl, ?_, ?_⟩
  · simpa using hget
  · simpa [hss, hevs] using hexp

private theorem modelAccepts_call4 :
    ModelAcceptsTermAfterAttackerSends myInterp r0 S0 myGhost msPre4 evsPre4 runEv4 msg1Term :=
  modelAccepts_direct (m := move4_dec1) rfl
    (by
      rw [show msPre4 = msExposed.take 4 from rfl, runTrace_take_eq 4]
      change Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t8.getMessageSentAt 44 =
        some msg1Term
      have hpeel : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (T : ExecTrace) (e : E),
          44 < T.length →
          ((T.append e).at? 44 : Option DY.Network.ExecEntryT) =
            (T.at? 44 : Option DY.Network.ExecEntryT) := by
        intro E _ T e hlt
        have hlt' : 44 < (T.snoc (DY.TraceEntryHas.inj e)).length := by
          rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
        have hne : ¬ (44 = T.length) := by omega
        simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, hlt, hlt', ↓reduceDIte,
          Symbolic.DYBridge.DY.Trace.at_eq_2, hne]
      have hsent : ∀ (T : ExecTrace) (b : Bytes) (n : Nat), T.length = n →
          (T.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt n =
            some b := by
        intro T b n hn; subst hn
        rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
      have ⟨b7, ht7⟩ : ∃ b7,
          Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7.getMessageSentAt 44 = some b7 :=
        ⟨_, by
          dsimp only [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7,
            Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr]
          apply hsent
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t6_length]⟩
      have hm1 : msg1Term = b7 := by unfold msg1Term; rw [ht7]; rfl
      rw [hm1]
      unfold Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t8
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      repeat (rw [hpeel _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t7_length]; omega)])
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at ht7
      exact ht7)
    rfl rfl explains_pre5

private theorem modelAccepts_call6 :
    ModelAcceptsTermAfterAttackerSends myInterp r0 S0 myGhost msPre6 evsPre6 runEv6
      msgReply0Term :=
  modelAccepts_direct (m := move6_decReply0) rfl
    (by
      rw [show msPre6 = msExposed.take 6 from rfl, runTrace_take_eq 6]
      change Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10.getMessageSentAt 64 =
        some msgReply0Term
      have hsent : ∀ (T : ExecTrace) (b : Bytes) (n : Nat), T.length = n →
          (T.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt n =
            some b := by
        intro T b n hn; subst hn
        rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
      have ⟨b10, ht10⟩ : ∃ b10,
          Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10.getMessageSentAt 64 = some b10 :=
        ⟨_, by
          dsimp only [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t10,
            Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr]
          apply hsent
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t9_length]⟩
      unfold msgReply0Term
      rw [ht10]; rfl)
    rfl rfl explains_honest

private theorem modelAccepts_call8 :
    ModelAcceptsTermAfterAttackerSends myInterp r0 S0 myGhost msPre8 evsPre8 runEv8 msg2Term :=
  modelAccepts_direct (m := move10_dec2) rfl
    (by
      rw [show msPre8 = msExposed.take 10 from rfl, runTrace_take_eq 10]
      change Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14.getMessageSentAt 82 =
        some msg2Term
      have hsent : ∀ (T : ExecTrace) (b : Bytes) (n : Nat), T.length = n →
          (T.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt n =
            some b := by
        intro T b n hn; subst hn
        rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?_append]
      have ⟨b14, ht14⟩ : ∃ b14,
          Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14.getMessageSentAt 82 = some b14 :=
        ⟨_, by
          dsimp only [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t14,
            Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr]
          apply hsent
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2,
            Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t13_length]⟩
      unfold msg2Term
      rw [ht14]; rfl)
    (by simp [msPre8, msExposed, msTail, List.append_assoc])
    (by simp [evsPre8, evsExposed, List.append_assoc])
    explains_exposed

/-! ## Stepping `NoCollisionFrom` Across Calls 0..8 -/

private theorem noCollision_prefix06 {rest : List CliEvent}
    (hTail : NoCollisionFrom myInterp r0 S0 evsHonest rest) :
    NoCollisionFrom myInterp r0 S0 [] (evsHonest ++ rest) := by
  have hp3_is : (parsePreKeyWire (wirePrekeyTag :: pkMsg0.bytes)).isSome = true := by
    decide +kernel
  obtain ⟨p3, hp3⟩ := Option.isSome_iff_exists.mp hp3_is
  have hp4_is : (parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes)).isSome = true := by
    decide +kernel
  obtain ⟨p4, hp4⟩ := Option.isSome_iff_exists.mp hp4_is
  dsimp only [evsHonest, List.cons_append, List.nil_append]
  refine not_collision_step_irrelevant (by rfl) ?_
  refine not_collision_step_run (fun _ _ _ hExp => ?_) ?_
  · dsimp only [List.nil_append] at hExp ⊢
    exact not_nextEventCollides_pt rfl (by decide) (by decide) (by decide +kernel) hExp
  refine not_collision_step_run (fun _ _ _ hExp => ?_) ?_
  · dsimp only [List.nil_append, List.cons_append] at hExp ⊢
    exact not_nextEventCollides_pt rfl (by decide) (by decide) (by decide +kernel) hExp
  refine not_collision_step_run (fun g ss vis hOuter => ?_) ?_
  · change Explains myInterp r0 S0 g ss vis evsPre3 at hOuter
    change ¬ NextEventCollides myInterp r0 S0 g ss vis evsPre3 runEv3
    exact not_nextEventCollides_accepted_prekey_no_recv rfl wire0_eq hOuter (by rfl) hp3
      explains_pre3 (not_readCollisionCli_take 3) x3Rep_mem_pre3 (not_bobStartCollides_call3 hp3)
  refine not_collision_step_run (fun g ss vis _ => ?_) ?_
  · change ¬ NextEventCollides myInterp r0 S0 g ss vis evsPre4 runEv4
    exact not_nextEventCollides_accepted_prekey_subsequent rfl wire1_eq hp4
      explains_pre4 (not_readCollisionCli_take 4) (msg1Term_mem_pre4 hp4) modelAccepts_call4
      noRecvCollision_call4 noReselectCollision_call4 x4Rep_mem_pre4 bobDoneBaseKey_call4
      (noBobStartCollision_call4 hp4)
  refine not_collision_step_run (fun g ss vis hExp => ?_) ?_
  · change Explains myInterp r0 S0 g ss vis evsPre5 at hExp
    change ¬ NextEventCollides myInterp r0 S0 g ss vis evsPre5 runEv5
    exact not_nextEventCollides_pt rfl (by decide) (by decide) (by decide +kernel) hExp
  refine not_collision_step_run (fun g ss vis _ => ?_) ?_
  · change ¬ NextEventCollides myInterp r0 S0 g ss vis evsPre6 runEv6
    exact not_nextEventCollides_accepted_whisper_check rfl wireReply0_eq
      explains_pre6 (not_readCollisionCli_take 6) msgReply0Term_mem_pre6 modelAccepts_call6
      noRecvCollision_call6 noReselectCollision_call6
  exact hTail

theorem not_collision_honest :
    ¬ CollisionAfterExplainedPrefix myInterp r0 S0 evsHonest := by
  apply not_collisionAfterExplainedPrefix_of_from
  simpa using noCollision_prefix06 not_collision_nil

theorem not_collision_exposed :
    ¬ CollisionAfterExplainedPrefix myInterp r0 S0 evsExposed := by
  apply not_collisionAfterExplainedPrefix_of_from
  unfold evsExposed
  refine noCollision_prefix06 ?_
  refine not_collision_steps_irrelevant (blk := evLeaks) (by rfl) ?_
  refine not_collision_step_run (fun _ _ _ hExp => ?_) ?_
  · exact not_nextEventCollides_pt rfl (by decide) (by decide) (by decide +kernel) hExp
  refine not_collision_step_run (fun _ _ _ _ => ?_) ?_
  · have heq8 : (evsHonest ++ evLeaks) ++ [.run runEv7] = evsPre8 := by
      simp [evsPre8, evLeaks, List.append_assoc]
    rw [heq8]
    exact not_nextEventCollides_accepted_whisper_check rfl wire2_eq
      explains_pre8 (not_readCollisionCli_take 10) msg2Term_mem_pre8 modelAccepts_call8
      noRecvCollision_call8 noReselectCollision_call8
  exact not_collision_nil

/-! ## CLI-Level Reachability Theorems -/

theorem cliReachable_honestSessionTrace :
    CliTraceReachableProof honestSessionTrace :=
  ⟨myInterp, myHooks, r0, S0, evsHonest, myGhost, msHonest, visAt 7,
   cliTraces_honest, evsHonest_all_exit0, explains_honest, runTrace_msHonest,
   myInterp_total, myInterp_contracts, myHooks_agree, mkRecords_wf false,
   invertsGuarded_honest, coinsFresh_honest, not_collision_honest⟩

theorem cliReachable_exposedSessionTrace :
    CliTraceReachableProof exposedSessionTrace :=
  ⟨myInterp, myHooks, r0, S0, evsExposed, myGhost, msExposed, visAt 11,
   cliTraces_exposed, evsExposed_all_exit0, explains_exposed, runTrace_msExposed,
   myInterp_total, myInterp_contracts, myHooks_agree, mkRecords_wf false,
   invertsGuarded_exposed, coinsFresh_exposed, not_collision_exposed⟩

end Symbolic.Proofs.Tests.CliNonvacuity.Session
