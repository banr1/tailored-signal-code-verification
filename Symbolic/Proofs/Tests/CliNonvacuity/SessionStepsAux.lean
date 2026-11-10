/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces
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
import Init.Data.Repr
import Init.Data.String.Defs
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.SendRetBridge
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
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
# Auxiliary Cuts, Concrete Trace Tables, and `ModelRunWF`/`GhostWF`

Defines prefix step and `CliEvent` sequences (`msPre3`..`msPre8`, `evsPre3`..`evsPre8`),
pre-computed trace, visible-entry, and honest-salt tables (`trAt`, `visAt`, `saltsAt`) linked to
`runTrace` and `honestSaltsOf`, and `ModelRunWF`/`GhostWF` proofs across all session prefixes.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux

set_option maxRecDepth 200000

open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed (reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup Ghost Step VisEntry stepIn randTerm
   aliceVis bobVis bobOpkPk encDraws lastSent decVis exposures newRandoms
   setupTrace setupRandoms runSteps runTrace honestKeysOf honestSaltsOf
   StepsWF StepsStateFaithful ModelRunWF GhostWF)
open DY.Libsignal.Composed.Refinement.Cli (aliceUuid bobUuid serializeAddresses)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (modelRunWF_of_append ghostWF_of_append)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myParams freshBytes)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs aliceTr aliceTrOpt encTr exposeCkrTr exposeCksTr StT RndE NetE rnd
   encMsg encSig parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
   t4_length t5_length t6_length t7_length t8_length t9_length
   t10_length t11_length t12_length t13_length t14_length t15_length
   stA0 stA1 stA2 stA4 stB2 stB3 key0 key1 key2 key3 coins0 coins1 coins2 m0 m1
   t5_runs t6_runs t7_runs t8_runs t9_runs t10_runs t11_runs
   t12_runs t13_runs t14_runs t15_runs
   t4_reach t5_reach t6_reach t7_reach t8_reach t9_reach t10_reach t11_reach
   t12_reach t13_reach t14_reach t15_reach)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
  (r0 myGhost myGhostAddr msg0WireTerm msg1WireTerm
   move0_init move1_enc0 move2_enc1 move3_bobStart move4_dec1 move5_encReply0
   move6_decReply0 move7_leakCkr move8_leakCks move9_enc2 move10_dec2
   msHonest msLeaks msExposed
   setupTrace_r0_eq move0_next move1_next move2_next move3_next move4_next
   move5_next move6_next move7_next move8_next move9_next move10_next)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionTraces
  (runEv0 runEv1 runEv2 runEv3 runEv4 runEv5 runEv7
   leakEvCkr leakEvCks evsHonest)

unseal DY.Bytes

/-! ## Prefix `Step` and `CliEvent` Sequences -/

def initPieces : List HwBytes :=
  [freshBytes 22 32] ++ List.replicate 32 (List.replicate 4 24#8) ++ [freshBytes 24 32]

def msPre3 : List Step := [move0_init, move1_enc0, move2_enc1]
def msPre4 : List Step := [move0_init, move1_enc0, move2_enc1, move3_bobStart]
def msPre5 : List Step := [move0_init, move1_enc0, move2_enc1, move3_bobStart, move4_dec1]
def msPre6 : List Step :=
  [move0_init, move1_enc0, move2_enc1, move3_bobStart, move4_dec1, move5_encReply0]
def msPre8 : List Step := msHonest ++ msLeaks ++ [move9_enc2]

def evsPre3 : List CliEvent := [.run runEv0, .run runEv1, .run runEv2]
def evsPre4 : List CliEvent := [.run runEv0, .run runEv1, .run runEv2, .run runEv3]
def evsPre5 : List CliEvent := [.run runEv0, .run runEv1, .run runEv2, .run runEv3, .run runEv4]
def evsPre6 : List CliEvent :=
  [.run runEv0, .run runEv1, .run runEv2, .run runEv3, .run runEv4, .run runEv5]
def evsPre8 : List CliEvent := evsHonest ++ [.env leakEvCkr, .env leakEvCks, .run runEv7]

/-! ## Concrete Trace, Vis, and Salt Tables -/

def trAt : Nat → ExecTrace
  | 0 => t4 | 1 => t5 | 2 => t6 | 3 => t7 | 4 => t8 | 5 => t9
  | 6 => t10 | 7 => t11 | 8 => t12 | 9 => t13 | 10 => t14 | _ => t15

def encSendBetween (tr tr' : ExecTrace) (wrap : Option (Nat × Nat)) : List VisEntry :=
  match lastSent tr tr' with
  | some w =>
    match wrap with
    | some (ekIdx, ctIdx) =>
      match tr.getMessageSentAt ekIdx, tr.getMessageSentAt ctIdx with
      | some ek, some ct => [⟨.send, [ek, ct, w], .preKeySend, none⟩]
      | _, _ => []
    | none => [⟨.send, [w], .whisper, none⟩]
  | none => []

def visBetween (s : Step) (tr tr' : ExecTrace) (wrap : Option (Nat × Nat)) (wrappedDec : Bool) :
    List VisEntry :=
  (match s with
    | .aliceStart _ _ _ _ h => aliceVis tr tr' h
    | .bobStart b _ kh _ mh _ _ => bobVis tr tr' mh (bobOpkPk b kh tr)
    | .messageEncrypt .. => encDraws (newRandoms tr tr') ++ encSendBetween tr tr' wrap
    | .messageDecrypt _ stateIdx msgIdx .. => decVis tr tr' stateIdx msgIdx wrappedDec
    | .messageDecryptSkipped _ stateIdx msgIdx .. => decVis tr tr' stateIdx msgIdx wrappedDec
    | _ => []) ++
  exposures tr tr'

def visSteps : List (List VisEntry) :=
  [visBetween move0_init t4 t5 none false,
   visBetween move1_enc0 t5 t6 (some (25, 26)) false,
   visBetween move2_enc1 t6 t7 (some (25, 26)) false,
   visBetween move3_bobStart t7 t8 none false,
   visBetween move4_dec1 t8 t9 none true,
   visBetween move5_encReply0 t9 t10 none false,
   visBetween move6_decReply0 t10 t11 none false,
   visBetween move7_leakCkr t11 t12 none false,
   visBetween move8_leakCks t12 t13 none false,
   visBetween move9_enc2 t13 t14 none false,
   visBetween move10_dec2 t14 t15 none false]

def visAt (k : Nat) : List VisEntry := (visSteps.take k).flatten

def saltStep (s : Step) (tr tr' : ExecTrace) : List DY.Bytes :=
  match s with
  | .messageEncrypt _ _ _ pqIdx =>
    if pqIdx = tr.length + 3 then [] else (tr'.getMessageSentAt (tr.length + 2)).toList
  | _ => []

def saltSteps : List (List DY.Bytes) :=
  [saltStep move0_init t4 t5, saltStep move1_enc0 t5 t6, saltStep move2_enc1 t6 t7,
   saltStep move3_bobStart t7 t8, saltStep move4_dec1 t8 t9, saltStep move5_encReply0 t9 t10,
   saltStep move6_decReply0 t10 t11, saltStep move7_leakCkr t11 t12,
   saltStep move8_leakCks t12 t13, saltStep move9_enc2 t13 t14, saltStep move10_dec2 t14 t15]

def saltsAt (k : Nat) : List DY.Bytes := DY.Spqr.zeroKey :: (saltSteps.take k).flatten

private theorem runSteps_cons_eq {s : Step} {ss : List Step} {tr tr' trOut : ExecTrace}
    (hnext : s.next tr = tr') (hrest : runSteps ss tr' = trOut) :
    runSteps (s :: ss) tr = trOut := by
  unfold runSteps
  rw [hnext, hrest]

theorem runSteps_take_eq (k : Nat) : runSteps (msExposed.take k) t4 = trAt k := by
  match k with
  | 0 => rfl
  | 1 => exact runSteps_cons_eq move0_next rfl
  | 2 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next rfl)
  | 3 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next rfl))
  | 4 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next rfl)))
  | 5 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next rfl))))
  | 6 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next
      (runSteps_cons_eq move5_next rfl)))))
  | 7 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next
      (runSteps_cons_eq move5_next (runSteps_cons_eq move6_next rfl))))))
  | 8 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next
      (runSteps_cons_eq move5_next (runSteps_cons_eq move6_next (runSteps_cons_eq move7_next rfl)))))))
  | 9 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next
      (runSteps_cons_eq move5_next (runSteps_cons_eq move6_next (runSteps_cons_eq move7_next
      (runSteps_cons_eq move8_next rfl))))))))
  | 10 => exact runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
      (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next
      (runSteps_cons_eq move5_next (runSteps_cons_eq move6_next (runSteps_cons_eq move7_next
      (runSteps_cons_eq move8_next (runSteps_cons_eq move9_next rfl)))))))))
  | n + 11 =>
    have h11 : runSteps msExposed t4 = t15 :=
      runSteps_cons_eq move0_next (runSteps_cons_eq move1_next
        (runSteps_cons_eq move2_next (runSteps_cons_eq move3_next (runSteps_cons_eq move4_next
        (runSteps_cons_eq move5_next (runSteps_cons_eq move6_next (runSteps_cons_eq move7_next
        (runSteps_cons_eq move8_next (runSteps_cons_eq move9_next
        (runSteps_cons_eq move10_next rfl))))))))))
    have htake : msExposed.take (n + 11) = msExposed := by
      have hlen : msExposed.length = 11 := rfl
      exact List.take_of_length_le (by omega)
    rw [htake]
    exact h11

theorem runTrace_take_eq (k : Nat) : runTrace r0 (msExposed.take k) = trAt k := by
  unfold runTrace
  rw [setupTrace_r0_eq, runSteps_take_eq k]

theorem runTrace_msExposed_eq_t15 : runTrace r0 msExposed = t15 :=
  runTrace_take_eq 11

theorem runTrace_take_msExposed_reach (k : Nat) :
    (runTrace r0 (msExposed.take k)).Reachable reachability := by
  rw [runTrace_take_eq]
  match k with
  | 0 => exact t4_reach | 1 => exact t5_reach | 2 => exact t6_reach | 3 => exact t7_reach
  | 4 => exact t8_reach | 5 => exact t9_reach | 6 => exact t10_reach | 7 => exact t11_reach
  | 8 => exact t12_reach | 9 => exact t13_reach | 10 => exact t14_reach | _ + 11 => exact t15_reach

private theorem honestKeysFrom_cons {s : Step} {ss : List Step} {tr tr' : ExecTrace}
    {ks : List DY.Bytes} (hnext : s.next tr = tr') (hrest : honestKeysOf tr' ss = ks) :
    honestKeysOf tr (s :: ss) = saltStep s tr tr' ++ ks := by
  unfold honestKeysOf DY.Libsignal.Composed.Refinement.Step.publishedSpqrKey?
    DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx
    DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx saltStep
  rw [hnext, hrest]
  cases s with
  | messageEncrypt _ _ _ pqIdx => dsimp only; split_ifs <;> rfl
  | _ => rfl

theorem honestSalts_take_eq (k : Nat) : honestSaltsOf r0 (msExposed.take k) = saltsAt k := by
  unfold honestSaltsOf saltsAt
  rw [setupTrace_r0_eq]
  congr 1
  match k with
  | 0 => rfl
  | 1 => exact honestKeysFrom_cons move0_next rfl
  | 2 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next rfl)
  | 3 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next rfl))
  | 4 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next rfl)))
  | 5 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
      (honestKeysFrom_cons move4_next rfl))))
  | 6 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
      (honestKeysFrom_cons move4_next (honestKeysFrom_cons move5_next rfl)))))
  | 7 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
      (honestKeysFrom_cons move4_next (honestKeysFrom_cons move5_next
      (honestKeysFrom_cons move6_next rfl))))))
  | 8 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
      (honestKeysFrom_cons move4_next (honestKeysFrom_cons move5_next
      (honestKeysFrom_cons move6_next (honestKeysFrom_cons move7_next rfl)))))))
  | 9 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
      (honestKeysFrom_cons move4_next (honestKeysFrom_cons move5_next
      (honestKeysFrom_cons move6_next (honestKeysFrom_cons move7_next
      (honestKeysFrom_cons move8_next rfl))))))))
  | 10 => exact honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
      (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
      (honestKeysFrom_cons move4_next (honestKeysFrom_cons move5_next
      (honestKeysFrom_cons move6_next (honestKeysFrom_cons move7_next
      (honestKeysFrom_cons move8_next (honestKeysFrom_cons move9_next rfl)))))))))
  | n + 11 =>
    have h11 : honestKeysOf t4 msExposed = saltSteps.flatten :=
      honestKeysFrom_cons move0_next (honestKeysFrom_cons move1_next
        (honestKeysFrom_cons move2_next (honestKeysFrom_cons move3_next
        (honestKeysFrom_cons move4_next (honestKeysFrom_cons move5_next
        (honestKeysFrom_cons move6_next (honestKeysFrom_cons move7_next
        (honestKeysFrom_cons move8_next (honestKeysFrom_cons move9_next
        (honestKeysFrom_cons move10_next rfl))))))))))
    have htake1 : msExposed.take (n + 11) = msExposed := by
      have hlen : msExposed.length = 11 := rfl
      exact List.take_of_length_le (by omega)
    have htake2 : saltSteps.take (n + 11) = saltSteps := by
      have hlen : saltSteps.length = 11 := rfl
      exact List.take_of_length_le (by omega)
    rw [htake1, htake2]
    exact h11

theorem move_next_trAt : ∀ (j : Nat) {s : Step}, msExposed[j]? = some s →
    s.next (trAt j) = trAt (j + 1)
  | 0, _, h => by injection h with h; subst h; exact move0_next
  | 1, _, h => by injection h with h; subst h; exact move1_next
  | 2, _, h => by injection h with h; subst h; exact move2_next
  | 3, _, h => by injection h with h; subst h; exact move3_next
  | 4, _, h => by injection h with h; subst h; exact move4_next
  | 5, _, h => by injection h with h; subst h; exact move5_next
  | 6, _, h => by injection h with h; subst h; exact move6_next
  | 7, _, h => by injection h with h; subst h; exact move7_next
  | 8, _, h => by injection h with h; subst h; exact move8_next
  | 9, _, h => by injection h with h; subst h; exact move9_next
  | 10, _, h => by injection h with h; subst h; exact move10_next
  | _ + 11, _, h => by
    have hlen : msExposed.length = 11 := rfl
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    omega

/-! ## `ModelRunWF` and `GhostWF` Across All Prefixes -/

private theorem stepsWF_cons {s : Step} {ss : List Step} {tr tr' : ExecTrace}
    (hp : s.PreCond tr) (hl : s.LocalOk tr) (hnext : s.next tr = tr')
    (hrest : StepsWF ss tr') : StepsWF (s :: ss) tr :=
  ⟨hp, hl, hnext ▸ hrest⟩

open scoped DY.Libsignal.Composed in
theorem stepsWF_msExposed : StepsWF msExposed (setupTrace r0) := by
  have hlen : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E),
      (tr.append e).length = tr.length + 1 := fun tr e => by
    rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hat_keep : ∀ {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
      {tr : ExecTrace} {k : Nat} {x : E1} (e : E2),
      tr.at? k = some x → (tr.append e).at? k = some x :=
    fun e h => Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (Trace.append_le _ e) h
  have hat_app : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {k : Nat},
      tr.length = k → (tr.append e).at? k = some e := by
    intro E _ tr e k hk; subst hk; exact Trace.at?_append tr e
  have hcur_self : ∀ (tr : ExecTrace) (me : Participant)
      (st : DY.Libsignal.TripleRatchet.TRState) {k : Nat},
      tr.length = k →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot (tr.append (StT me st)) k = true := by
    intro tr me st k hk; subst hk
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
    rw [Trace.at?_append tr (StT me st), hlen, Nat.sub_self]; rfl
  have hcur_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {k : Nat} (e : E),
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (PersistentGlobalState.State.ExecEntryT
          (PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))) = none →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot tr k = true →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot (tr.append e) k = true := by
    intro E _ tr k e hnone hcur
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
    cases hst : (tr.at? k :
        Option (PersistentGlobalState.State.ExecEntryT
          (PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))) with
    | none => rw [hst] at hcur; cases hcur
    | some es =>
      rw [hst] at hcur
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (Trace.append_le tr e) hst]
      dsimp only at hcur ⊢
      have hk : k < tr.length := by
        have := Trace.at?_eq_some_implies_length_le
          (EntryT := PersistentGlobalState.State.ExecEntryT
            (PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) tr k
        rwa [hst] at this
      have hsub : (tr.append e).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
        rw [hlen]; omega
      rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
        List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true] at hcur ⊢
        intro j hj
        rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr e
          (by rw [List.mem_range'_1] at hj; omega)]
        exact hcur j hj
      · simp only [Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2, show tr.length < tr.length + 1 by omega,
          ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hnone]
  have hcur_ne : ∀ {tr : ExecTrace} {me me' : Participant}
      {st st' : DY.Libsignal.TripleRatchet.TRState} {k : Nat},
      tr.at? k = some (StT me st) → (me' != me) = true →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot tr k = true →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot (tr.append (StT me' st')) k = true := by
    intro tr me me' st st' k hst hne hcur
    have hk : k < tr.length := by
      have := Trace.at?_eq_some_implies_length_le
        (EntryT := PersistentGlobalState.State.ExecEntryT
          (PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) tr k
      rwa [hst] at this
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
    rw [hst] at hcur
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (Trace.append_le tr (StT me' st')) hst]
    dsimp only at hcur ⊢
    have hsub : (tr.append (StT me' st')).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
      rw [hlen]; omega
    rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at hcur ⊢
      intro j hj
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr (StT me' st')
        (by rw [List.mem_range'_1] at hj; omega)]
      exact hcur j hj
    · rw [Trace.at?_append]; simp [hne]
  have hcur_enc_self : ∀ (tr : ExecTrace) (me : Participant) (stH : Nat)
      (st : DY.Libsignal.TripleRatchet.TRState) (pq : DY.Bytes) {n5 : Nat},
      tr.length + 5 = n5 →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot (encTr tr me stH st pq) n5 = true := by
    intro tr me stH st pq n5 h5; subst h5; dsimp only [encTr]
    refine hcur_non _ rfl (hcur_self _ _ _ ?_)
    simp only [hlen]
  have hcur_enc_ne : ∀ {tr : ExecTrace} {me me' : Participant}
      {st st' : DY.Libsignal.TripleRatchet.TRState} {stH k : Nat} {pq : DY.Bytes},
      tr.at? k = some (StT me st) → (me' != me) = true →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot tr k = true →
      DY.Libsignal.TripleRatchet.isCurrentSnapshot (encTr tr me' stH st' pq) k = true := by
    intro tr me me' st st' stH k pq hst hne hcur
    dsimp only [encTr]
    refine hcur_non _ rfl (hcur_ne (by
      iterate 5 refine hat_keep _ ?_
      exact hst) hne ?_)
    iterate 5 refine hcur_non _ rfl ?_
    exact hcur
  have hcur5_30 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t5 30 = true := by
    dsimp only [t5, aliceTr, aliceTrOpt]
    exact hcur_self _ _ _ (by simp only [hlen, t4_length])
  have hcur6_36 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t6 36 = true :=
    hcur_enc_self t5 "alice" 30 stA0 key0 (by rw [t5_length])
  have hcur7_43 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t7 43 = true :=
    hcur_enc_self t6 "alice" 36 stA1 key1 (by rw [t6_length])
  have hst7 : t7.at? 43 = some (StT "alice" stA2) := by
    dsimp only [t7, encTr, stA2]
    have hc : rnd (t6.length + 1) 32 = coins1 := by rw [t6_length]
    rw [hc]
    exact hat_keep _ (hat_app _ _ (by simp only [hlen, t6_length]))
  have hcur8_53 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t8 53 = true := by
    dsimp only [t8]; exact hcur_self _ _ _ (by simp only [hlen, t7_length])
  have hcur8_43 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t8 43 = true := by
    dsimp only [t8]
    refine hcur_ne (by
      iterate 8 refine hat_keep _ ?_
      exact hst7) rfl ?_
    iterate 8 refine hcur_non _ rfl ?_
    exact hcur7_43
  have hst8 : t8.at? 43 = some (StT "alice" stA2) := by
    dsimp only [t8]
    iterate 9 refine hat_keep _ ?_
    exact hst7
  have hcur9_57 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t9 57 = true := by
    dsimp only [t9]; exact hcur_self _ _ _ (by simp only [hlen, t8_length])
  have hcur9_43 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t9 43 = true := by
    dsimp only [t9]
    refine hcur_ne (by
      iterate 3 refine hat_keep _ ?_
      exact hst8) rfl ?_
    iterate 3 refine hcur_non _ rfl ?_
    exact hcur8_43
  have hst9 : t9.at? 43 = some (StT "alice" stA2) := by
    dsimp only [t9]
    iterate 4 refine hat_keep _ ?_
    exact hst8
  have hcur10_43 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t10 43 = true :=
    hcur_enc_ne hst9 rfl hcur9_43
  have hcur10_63 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t10 63 = true :=
    hcur_enc_self t9 "bob" 57 stB2 key2 (by rw [t9_length])
  have hst10 : t10.at? 63 = some (StT "bob" stB3) := by
    dsimp only [t10, encTr, stB3]
    have hc : rnd (t9.length + 1) 32 = coins2 := by rw [t9_length]
    rw [hc]
    exact hat_keep _ (hat_app _ _ (by simp only [hlen, t9_length]))
  have hcur11_71 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t11 71 = true := by
    dsimp only [t11]; exact hcur_self _ _ _ (by simp only [hlen, t10_length])
  have hcur11_63 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t11 63 = true := by
    dsimp only [t11]
    refine hcur_ne (by
      iterate 6 refine hat_keep _ ?_
      exact hst10) rfl ?_
    iterate 6 refine hcur_non _ rfl ?_
    exact hcur10_63
  have hst11 : t11.at? 63 = some (StT "bob" stB3) := by
    dsimp only [t11]
    iterate 7 refine hat_keep _ ?_
    exact hst10
  have hcur12_71 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t12 71 = true := by
    dsimp only [t12, exposeCkrTr]
    iterate 2 refine hcur_non _ rfl ?_
    exact hcur11_71
  have hcur13_71 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t13 71 = true := by
    dsimp only [t13, exposeCksTr]
    iterate 2 refine hcur_non _ rfl ?_
    exact hcur12_71
  have hcur13_63 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t13 63 = true := by
    dsimp only [t13, exposeCksTr, t12, exposeCkrTr]
    iterate 4 refine hcur_non _ rfl ?_
    exact hcur11_63
  have hst13 : t13.at? 63 = some (StT "bob" stB3) := by
    dsimp only [t13, exposeCksTr, t12, exposeCkrTr]
    iterate 4 refine hat_keep _ ?_
    exact hst11
  have hcur14_63 : DY.Libsignal.TripleRatchet.isCurrentSnapshot t14 63 = true :=
    hcur_enc_ne hst13 rfl hcur13_63
  rw [setupTrace_r0_eq]
  dsimp only [msExposed, msHonest, msLeaks, SessionDefs.msTail, List.cons_append, List.nil_append]
  exact stepsWF_cons trivial trivial move0_next
    (stepsWF_cons hcur5_30 ⟨Or.inr (Or.inl rfl), Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t5_length])⟩ move1_next
    (stepsWF_cons hcur6_36 ⟨Or.inr (Or.inl rfl), Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t6_length])⟩ move2_next
    (stepsWF_cons trivial trivial move3_next
    (stepsWF_cons hcur8_53 trivial move4_next
    (stepsWF_cons hcur9_57 ⟨Or.inr (Or.inl rfl), Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t9_length])⟩ move5_next
    (stepsWF_cons hcur10_43 trivial move6_next
    (stepsWF_cons trivial hcur11_71 move7_next
    (stepsWF_cons trivial hcur12_71 move8_next
    (stepsWF_cons hcur13_71 ⟨Or.inr (Or.inl rfl), Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t13_length])⟩ move9_next
    (stepsWF_cons hcur14_63 trivial move10_next trivial))))))))))

def stateFaithfulNoDupBool (ss : List Step) : Bool :=
  (List.range ss.length).all fun i =>
    (List.range ss.length).all fun j =>
      !(decide (i < j)) ||
        match ss[i]?, ss[j]? with
        | some si, some sj =>
          match si.stateLoad?, sj.stateLoad? with
          | some (p1, k1, true), some (p2, k2, _) => !(p1 == p2 && k1 == k2)
          | _, _ => true
        | _, _ => true

theorem stateFaithful_of_bool {r : ProtocolSetup} {ss : List Step}
    (h : stateFaithfulNoDupBool ss = true) : StepsStateFaithful r ss := by
  intro i j si sj p k b hij hsi hsj hli _ hlj
  have hjlt : j < ss.length := (List.getElem?_eq_some_iff.mp hsj).1
  have hilt : i < ss.length := Nat.lt_trans hij hjlt
  have hi := List.all_eq_true.mp h i (List.mem_range.mpr hilt)
  have hj := List.all_eq_true.mp hi j (List.mem_range.mpr hjlt)
  rw [hsi, hsj] at hj
  dsimp only at hj
  rw [hli, hlj] at hj
  simp [hij] at hj

theorem modelRunWF_msExposed : ModelRunWF r0 msExposed :=
  ⟨Symbolic.Swarm.CREF.TR.setupRandoms_length r0 (by decide),
   setupTrace_r0_eq ▸ t4_reach,
   stepsWF_msExposed,
   stateFaithful_of_bool rfl⟩

theorem modelRunWF_take (k : Nat) : ModelRunWF r0 (msExposed.take k) := by
  have heq : msExposed = msExposed.take k ++ msExposed.drop k :=
    (List.take_append_drop k msExposed).symm
  exact modelRunWF_of_append (heq ▸ modelRunWF_msExposed)

def ghostWFBool (g : Ghost) (vis : List VisEntry) : Bool :=
  vis.all fun v =>
    if v.kind == .rng then
      v.terms.all fun t =>
        match t.view? DY.Random.Random with
        | some r => r.size == 0 || (g.σ r.timestamp r.size).length == r.size
        | none => true
    else true

theorem ghostWF_of_bool {g : Ghost} {vis : List VisEntry}
    (h : ghostWFBool g vis = true)
    (haddr : ∀ t, g.addr t = [] ∨ g.addr t = serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩)
    (hsend : ∀ v ∈ vis, v.kind = .send →
      (v.layout = .preKeySend →
        ∀ ek ct msg pm, v.terms = [ek, ct, msg] →
          DY.Libsignal.TripleRatchet.parseTrSignalMsg msg = some pm →
          g.addr pm.wire = serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩) ∧
      (v.layout = .whisper →
        ∀ msg pm, v.terms = [msg] →
          DY.Libsignal.TripleRatchet.parseTrSignalMsg msg = some pm →
          g.addr pm.wire = [])) : GhostWF g vis := by
  refine ⟨?_, haddr, hsend⟩
  intro v hv hk ts n hn ht
  have hv' := List.all_eq_true.mp h v hv
  simp only [hk, beq_self_eq_true, ↓reduceIte] at hv'
  have ht' := List.all_eq_true.mp hv' (randTerm ts n) ht
  have hview : (randTerm ts n).view? DY.Random.Random = some { timestamp := ts, size := n } := by
    unfold randTerm
    exact DY.BytesView.view_pack _
  rw [hview] at ht'
  simp only [Bool.or_eq_true, beq_iff_eq] at ht'
  rcases ht' with h0 | hlen
  · exact absurd h0 hn
  · exact hlen

private theorem ghostWF_visAt_11_rng :
    ∀ v ∈ visAt 11, v.kind = .rng →
      ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms → (myGhost.σ ts n).length = n := by
  intro v hv hk ts n _ ht
  have hsigma_len : ts ≠ 31 → ts ≠ 38 → ts ≠ 58 → ts ≠ 76 → (myGhost.σ ts n).length = n := by
    intro h31 h38 h58 h76
    dsimp only [myGhost, SessionDefs.myGhostSigma]
    by_cases hn32 : (n == 32) = true
    · have hn' : n = 32 := beq_iff_eq.mp hn32
      subst hn'
      simp only [beq_self_eq_true, ↓reduceIte, beq_eq_false_iff_ne.mpr h31,
        beq_eq_false_iff_ne.mpr h38, beq_eq_false_iff_ne.mpr h58,
        beq_eq_false_iff_ne.mpr h76, Bool.false_eq_true]
      by_cases h32 : (ts == 32) = true
      · simp only [h32, ↓reduceIte]; decide
      · by_cases h39 : (ts == 39) = true
        · simp only [h32, h39, Bool.false_eq_true, ↓reduceIte]; decide
        · by_cases h59 : (ts == 59) = true
          · simp only [h32, h39, h59, Bool.false_eq_true, ↓reduceIte]; decide
          · by_cases h77 : (ts == 77) = true
            · simp only [h32, h39, h59, h77, Bool.false_eq_true, ↓reduceIte]; decide
            · simp only [h32, h39, h59, h77, Bool.false_eq_true, ↓reduceIte, freshBytes,
                List.length_replicate]
    · simp only [hn32, Bool.false_eq_true, ↓reduceIte, freshBytes, List.length_replicate]
  have hexp_not_rng : ∀ {tr tr' : ExecTrace}, v ∈ exposures tr tr' → False := by
    intro tr tr' hmem_e
    simp only [exposures, List.mem_append, List.mem_filterMap,
      DY.Libsignal.Composed.Refinement.pqExposureAt,
      DY.Libsignal.Composed.Refinement.trExposureAt] at hmem_e
    rcases hmem_e with ⟨j, _, hj⟩ | ⟨j, _, hj⟩
    · split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> cases hk
    · split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> cases hk
  have hnr_bounds : ∀ {tr tr' : ExecTrace} {t : DY.Bytes},
      t ∈ (newRandoms tr tr').map (·.1) → randTerm ts n = t →
      tr.length ≤ ts ∧ ts < tr'.length := by
    intro tr tr' t hmem_t heq_t
    simp only [newRandoms, DY.Libsignal.Composed.Refinement.newIndices, List.mem_map,
      List.mem_filterMap] at hmem_t
    obtain ⟨⟨t', l'⟩, ⟨i, hi, hmap⟩, rfl⟩ := hmem_t
    obtain ⟨e, _, heq'⟩ := Option.map_eq_some_iff.mp hmap
    injection heq' with ht' _
    obtain ⟨rfl, _⟩ := open scoped DY.Libsignal.Composed in
      Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj (heq_t.trans ht'.symm)
    have ⟨hlo, hhi⟩ := List.mem_range'_1.mp hi
    exact ⟨hlo, by omega⟩
  have had_mem : ∀ {done : Option Nat} {xs : List DY.Bytes},
      v ∈ DY.Libsignal.Composed.Refinement.aliceDraws done xs → randTerm ts n ∈ xs := by
    intro done xs had
    match xs with
    | [] => cases had
    | [ek] =>
      simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_singleton] at had
      subst had
      simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at ht ⊢
      exact ht
    | ek :: entropy :: rest =>
      simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_cons, List.mem_append,
        DY.Libsignal.Composed.Refinement.kyberCoinEntries, List.mem_map] at had
      rcases had with (rfl | ⟨_, _, rfl⟩) | ⟨d, hd, rfl⟩
      · simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at ht
        exact List.mem_cons.mpr (Or.inl ht)
      · simp only [List.mem_singleton] at ht
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ht)))
      · simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at ht
        rcases rest with _ | ⟨dhs, _⟩
        · cases hd
        · simp only [List.take, List.mem_singleton] at hd
          subst hd
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ht)))))
  have halice_bounds : ∀ {tr tr' : ExecTrace} {bh : DY.Libsignal.PQXDH.BundleHandles},
      v ∈ aliceVis tr tr' bh ++ exposures tr tr' → tr.length ≤ ts ∧ ts < tr'.length := by
    intro tr tr' bh hva
    rw [List.mem_append] at hva
    rcases hva with hva | hve
    · simp only [aliceVis, List.mem_cons] at hva
      rcases hva with rfl | had
      · cases hk
      · exact hnr_bounds (had_mem had) rfl
    · exact (hexp_not_rng hve).elim
  have hbob_bounds : ∀ {tr tr' : ExecTrace} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles}
      {opk : Option DY.Bytes},
      v ∈ bobVis tr tr' mh opk ++ exposures tr tr' → tr.length ≤ ts ∧ ts < tr'.length := by
    intro tr tr' mh opk hvb
    rw [List.mem_append] at hvb
    rcases hvb with hvb | hve
    · simp only [bobVis, List.mem_cons, List.mem_append, List.mem_map] at hvb
      rcases hvb with (rfl | ⟨⟨t', l'⟩, hr, rfl⟩) | hb_a
      · cases hk
      · simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at ht
        exact hnr_bounds (List.mem_map_of_mem (f := (·.1)) hr) ht
      · rw [Option.mem_toList] at hb_a
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hb_a
        cases hk
    · exact (hexp_not_rng hve).elim
  have hdec_bounds : ∀ {tr tr' : ExecTrace} {stIdx msgIdx : Nat} {w : Bool},
      v ∈ decVis tr tr' stIdx msgIdx w ++ exposures tr tr' → tr.length ≤ ts ∧ ts < tr'.length := by
    intro tr tr' stIdx msgIdx w hvd
    rw [List.mem_append] at hvd
    rcases hvd with hvd | hve
    · simp only [decVis, List.mem_append, List.mem_map] at hvd
      rcases hvd with (hd_r | ⟨⟨t', l'⟩, hr, rfl⟩) | hd_a
      · rw [Option.mem_toList] at hd_r
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hd_r
        cases hk
      · simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at ht
        exact hnr_bounds (List.mem_map_of_mem (f := (·.1)) hr) ht
      · rw [Option.mem_toList] at hd_a
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hd_a
        cases hk
    · exact (hexp_not_rng hve).elim
  have henc_bounds : ∀ {tr : ExecTrace} {me : Participant} {stH : Nat}
      {st : DY.Libsignal.TripleRatchet.TRState} {pq : DY.Bytes}
      {wrap : Option (Nat × Nat)},
      v ∈ (encDraws (newRandoms tr (encTr tr me stH st pq)) ++
        encSendBetween tr (encTr tr me stH st pq) wrap) ++
        exposures tr (encTr tr me stH st pq) →
      tr.length + 1 ≤ ts ∧ ts < tr.length + 7 := by
    intro tr me stH st pq wrap hve
    rw [List.mem_append, List.mem_append] at hve
    rcases hve with (hve_d | hsb) | hve_x
    · have hat0 : ((encTr tr me stH st pq).at? tr.length : Option DY.Random.ExecEntryT) =
          some (RndE 32) := by
        unfold encTr; dsimp only
        iterate 6 refine (open scoped DY.Libsignal.Composed in
          Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (Trace.append_le _ _) ?_)
        exact Trace.at?_append tr (RndE 32)
      have hlen_enc : (encTr tr me stH st pq).length = tr.length + 7 := by
        unfold encTr
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hnr_eq : newRandoms tr (encTr tr me stH st pq) = (randTerm tr.length 32, 32) ::
          (List.range' (tr.length + 1) 6).filterMap (fun i =>
            ((encTr tr me stH st pq).at? i : Option DY.Random.ExecEntryT).map
              fun e => (randTerm i e.length, e.length)) := by
        unfold newRandoms DY.Libsignal.Composed.Refinement.newIndices
        rw [hlen_enc, show tr.length + 7 - tr.length = 7 by omega]
        show ((tr.length :: List.range' (tr.length + 1) 6).filterMap _) = _
        simp only [List.filterMap_cons, hat0, Option.map_some]
      rw [hnr_eq] at hve_d
      simp only [encDraws, List.mem_cons, List.mem_map, List.mem_filter,
        List.mem_filterMap] at hve_d
      rcases hve_d with rfl | ⟨⟨t', l'⟩, ⟨⟨i, hi, hmap⟩, _⟩, rfl⟩
      · cases hk
      · obtain ⟨e, _, heq'⟩ := Option.map_eq_some_iff.mp hmap
        injection heq' with ht' _
        simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at ht
        obtain ⟨rfl, _⟩ := open scoped DY.Libsignal.Composed in
          Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj (ht.trans ht'.symm)
        have ⟨hlo, hhi⟩ := List.mem_range'_1.mp hi
        exact ⟨hlo, by omega⟩
    · rcases hls : lastSent tr (encTr tr me stH st pq) with _ | w <;>
        simp only [encSendBetween, hls] at hsb
      · cases hsb
      · rcases wrap with _ | ⟨ekIdx, ctIdx⟩ <;> simp only at hsb
        · simp only [List.mem_singleton] at hsb; subst hsb; cases hk
        · rcases h1 : tr.getMessageSentAt ekIdx with _ | ek <;>
            rcases h2 : tr.getMessageSentAt ctIdx with _ | ct <;>
            simp only [h1, h2, List.not_mem_nil, List.mem_singleton] at hsb
          subst hsb; cases hk
    · exact (hexp_not_rng hve_x).elim
  rw [show visAt 11 = visSteps.flatten from rfl, List.mem_flatten] at hv
  obtain ⟨l, hl, hv_l⟩ := hv
  simp only [visSteps, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only [visBetween, move0_init] at hv_l
    have ⟨hlo, hhi⟩ := halice_bounds hv_l
    rw [t4_length] at hlo; rw [t5_length] at hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move1_enc0, t6] at hv_l
    have ⟨hlo, hhi⟩ := henc_bounds hv_l
    rw [t5_length] at hlo hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move2_enc1, t7] at hv_l
    have ⟨hlo, hhi⟩ := henc_bounds hv_l
    rw [t6_length] at hlo hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move3_bobStart] at hv_l
    have ⟨hlo, hhi⟩ := hbob_bounds hv_l
    rw [t7_length] at hlo; rw [t8_length] at hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move4_dec1] at hv_l
    have ⟨hlo, hhi⟩ := hdec_bounds hv_l
    rw [t8_length] at hlo; rw [t9_length] at hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move5_encReply0, t10] at hv_l
    have ⟨hlo, hhi⟩ := henc_bounds hv_l
    rw [t9_length] at hlo hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move6_decReply0] at hv_l
    have ⟨hlo, hhi⟩ := hdec_bounds hv_l
    rw [t10_length] at hlo; rw [t11_length] at hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move7_leakCkr, List.nil_append] at hv_l
    exact (hexp_not_rng hv_l).elim
  · dsimp only [visBetween, move8_leakCks, List.nil_append] at hv_l
    exact (hexp_not_rng hv_l).elim
  · dsimp only [visBetween, move9_enc2, t14] at hv_l
    have ⟨hlo, hhi⟩ := henc_bounds hv_l
    rw [t13_length] at hlo hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)
  · dsimp only [visBetween, move10_dec2] at hv_l
    have ⟨hlo, hhi⟩ := hdec_bounds hv_l
    rw [t14_length] at hlo; rw [t15_length] at hhi
    exact hsigma_len (by omega) (by omega) (by omega) (by omega)

private theorem at?_append_of_length_eq {E : Type} [ExecTraceTypes.Has E]
    {tr₆ : ExecTrace} {e : E} {k : Nat} (hk : tr₆.length = k) :
    (tr₆.append e).at? k = some e := by
  subst hk; exact Trace.at?_append tr₆ e

private theorem lastSent_encTr (tr : ExecTrace) (me : Participant) (stH : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (pq : DY.Bytes) :
    lastSent tr (encTr tr me stH st pq) =
      some (encMsg st (rnd (tr.length + 1) 32) pq (rnd tr.length 32)) := by
  have hlen : (encTr tr me stH st pq).length = tr.length + 7 := by
    unfold encTr
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlt : tr.length < (encTr tr me stH st pq).length := by omega
  unfold lastSent
  simp only [hlt, ↓reduceIte]
  rw [hlen, show tr.length + 7 - 1 = tr.length + 6 by omega]
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  unfold encTr
  dsimp only
  rw [at?_append_of_length_eq (by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])]

private theorem encSig_wire_dhs_eq {st₁ st₂ : DY.Libsignal.TripleRatchet.TRState}
    {c₁ pq₁ m₁ c₂ pq₂ m₂ : DY.Bytes}
    (h : (encSig st₁ c₁ pq₁ m₁).wire = (encSig st₂ c₂ pq₂ m₂).wire) :
    st₁.dhs = st₂.dhs := by
  have hf := congrArg DY.TrWire.trWireMsgFields? h
  unfold encSig DY.Libsignal.TripleRatchet.trHonestWireMsg at hf
  dsimp only at hf
  rw [DY.TrWire.trWireMsgFields?_trWireMsg, DY.TrWire.trWireMsgFields?_trWireMsg] at hf
  injection hf with hf'
  exact Symbolic.Proofs.Tests.Shared.Composed.Runs.dhPk_inj
    (congrArg DY.TrWire.TrWireMsg.SubF.senderRatchetKey hf')

theorem ghostWF_visAt_11 : GhostWF myGhost (visAt 11) := by
  have haddr_eq :
      ((CryptoVerification.E2E.pqxdhSessionParams myParams).sendAddrs .A).getD [] =
        serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ :=
    Symbolic.Swarm.CREF.Cli.Slots.sendAddrs_A_getD_eq_serializeAddresses myParams
  refine ⟨ghostWF_visAt_11_rng, ?_, ?_⟩
  · intro t
    dsimp only [myGhost, myGhostAddr]
    split
    · exact Or.inr haddr_eq
    · split
      · exact Or.inr haddr_eq
      · exact Or.inl rfl
  · intro v hv hk
    have hexp : ∀ {tr tr' : ExecTrace}, v ∈ exposures tr tr' → False := by
      intro tr tr' hmem_e
      simp only [exposures, List.mem_append, List.mem_filterMap,
        DY.Libsignal.Composed.Refinement.pqExposureAt,
        DY.Libsignal.Composed.Refinement.trExposureAt] at hmem_e
      rcases hmem_e with ⟨_, _, hj⟩ | ⟨_, _, hj⟩
      · split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> cases hk
      · split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> cases hk
    have had : ∀ {tr tr' : ExecTrace} {bh : DY.Libsignal.PQXDH.BundleHandles},
        v ∈ aliceVis tr tr' bh ++ exposures tr tr' → False := by
      intro tr tr' bh hva
      rcases List.mem_append.mp hva with hva | hve
      · simp only [aliceVis, List.mem_cons] at hva
        rcases hva with rfl | had'
        · cases hk
        · rcases xs_eq : (newRandoms tr tr').map (·.1) with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rw [xs_eq] at had'
          · cases had'
          · simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_singleton] at had'
            subst had'; cases hk
          · simp only [DY.Libsignal.Composed.Refinement.aliceDraws, List.mem_cons, List.mem_append,
              DY.Libsignal.Composed.Refinement.kyberCoinEntries, List.mem_map] at had'
            rcases had' with (rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> cases hk
      · exact hexp hve
    have hbob : ∀ {tr tr' : ExecTrace} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles}
        {opk : Option DY.Bytes}, v ∈ bobVis tr tr' mh opk ++ exposures tr tr' → False := by
      intro tr tr' mh opk hvb
      rcases List.mem_append.mp hvb with hvb | hve
      · simp only [bobVis, List.mem_cons, List.mem_append, List.mem_map, Option.mem_toList,
          Option.map_eq_some_iff] at hvb
        rcases hvb with ((rfl | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> cases hk
      · exact hexp hve
    have hdec : ∀ {tr tr' : ExecTrace} {stIdx msgIdx : Nat} {w : Bool},
        v ∈ decVis tr tr' stIdx msgIdx w ++ exposures tr tr' → False := by
      intro tr tr' stIdx msgIdx w hvd
      rcases List.mem_append.mp hvd with hvd | hve
      · simp only [decVis, List.mem_append, List.mem_map, Option.mem_toList,
          Option.map_eq_some_iff] at hvd
        rcases hvd with ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> cases hk
      · exact hexp hve
    have hed : ∀ {xs : List (DY.Bytes × Nat)}, v ∈ encDraws xs → False := by
      intro xs hw
      rcases xs with _ | ⟨_, _⟩
      · cases hw
      · simp only [encDraws, List.mem_cons, List.mem_map] at hw
        rcases hw with rfl | ⟨_, _, rfl⟩ <;> cases hk
    rw [show visAt 11 = visSteps.flatten from rfl, List.mem_flatten] at hv
    obtain ⟨l, hl, hv_l⟩ := hv
    simp only [visSteps, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (had hv_l).elim
    · dsimp only [visBetween, move1_enc0, t6] at hv_l
      rcases List.mem_append.mp hv_l with hv_de | hv_x
      · rcases List.mem_append.mp hv_de with hv_d | hv_s
        · exact (hed hv_d).elim
        · simp only [encSendBetween, lastSent_encTr, t5_length] at hv_s
          rcases h1 : t5.getMessageSentAt 25 with _ | ek <;>
            rcases h2 : t5.getMessageSentAt 26 with _ | ct <;>
            simp only [h1, h2, List.not_mem_nil, List.mem_singleton] at hv_s
          subst hv_s
          refine ⟨fun _ _ _ msg pm hterms hpm => ?_, fun hwh => nomatch hwh⟩
          injection hterms with _ htl; injection htl with _ htl'; injection htl' with hmsg _
          rw [← hmsg, parse_encMsg] at hpm
          injection hpm with hpm_eq
          rw [← hpm_eq]
          have hw0 : (encSig stA0 (rnd (31 + 1) 32) key0 (rnd 31 32)).wire = msg0WireTerm := rfl
          rw [hw0]
          simp [myGhost, myGhostAddr, haddr_eq]
      · exact (hexp hv_x).elim
    · dsimp only [visBetween, move2_enc1, t7] at hv_l
      rcases List.mem_append.mp hv_l with hv_de | hv_x
      · rcases List.mem_append.mp hv_de with hv_d | hv_s
        · exact (hed hv_d).elim
        · simp only [encSendBetween, lastSent_encTr, t6_length] at hv_s
          rcases h1 : t6.getMessageSentAt 25 with _ | ek <;>
            rcases h2 : t6.getMessageSentAt 26 with _ | ct <;>
            simp only [h1, h2, List.not_mem_nil, List.mem_singleton] at hv_s
          subst hv_s
          refine ⟨fun _ _ _ msg pm hterms hpm => ?_, fun hwh => nomatch hwh⟩
          injection hterms with _ htl; injection htl with _ htl'; injection htl' with hmsg _
          rw [← hmsg, parse_encMsg] at hpm
          injection hpm with hpm_eq
          rw [← hpm_eq]
          have hw1 : (encSig stA1 (rnd (38 + 1) 32) key1 (rnd 38 32)).wire = msg1WireTerm := rfl
          rw [hw1]
          by_cases h01 : (msg1WireTerm == msg0WireTerm) = true <;>
            simp [myGhost, myGhostAddr, h01, haddr_eq]
      · exact (hexp hv_x).elim
    · exact (hbob hv_l).elim
    · exact (hdec hv_l).elim
    · dsimp only [visBetween, move5_encReply0, t10] at hv_l
      rcases List.mem_append.mp hv_l with hv_de | hv_x
      · rcases List.mem_append.mp hv_de with hv_d | hv_s
        · exact (hed hv_d).elim
        · simp only [encSendBetween, lastSent_encTr, List.mem_singleton] at hv_s
          subst hv_s
          refine ⟨(fun hpk => nomatch hpk), fun _ msg pm hterms hpm => ?_⟩
          injection hterms with hmsg _
          rw [← hmsg, parse_encMsg] at hpm
          injection hpm with hpm_eq
          rw [← hpm_eq]
          have hne0 : (encSig stB2 (rnd (t9.length + 1) 32) key2 (rnd t9.length 32)).wire ≠
              msg0WireTerm := by
            intro heq
            have hdhs := encSig_wire_dhs_eq heq
            obtain ⟨hts, _⟩ := open scoped DY.Libsignal.Composed in
              Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hdhs
            omega
          have hne1 : (encSig stB2 (rnd (t9.length + 1) 32) key2 (rnd t9.length 32)).wire ≠
              msg1WireTerm := by
            intro heq
            have hdhs := encSig_wire_dhs_eq heq
            obtain ⟨hts, _⟩ := open scoped DY.Libsignal.Composed in
              Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hdhs
            omega
          simp [myGhost, myGhostAddr, beq_eq_false_iff_ne.mpr hne0, beq_eq_false_iff_ne.mpr hne1]
      · exact (hexp hv_x).elim
    · exact (hdec hv_l).elim
    · dsimp only [visBetween, move7_leakCkr, List.nil_append] at hv_l
      exact (hexp hv_l).elim
    · dsimp only [visBetween, move8_leakCks, List.nil_append] at hv_l
      exact (hexp hv_l).elim
    · dsimp only [visBetween, move9_enc2, t14] at hv_l
      rcases List.mem_append.mp hv_l with hv_de | hv_x
      · rcases List.mem_append.mp hv_de with hv_d | hv_s
        · exact (hed hv_d).elim
        · simp only [encSendBetween, lastSent_encTr, List.mem_singleton] at hv_s
          subst hv_s
          refine ⟨(fun hpk => nomatch hpk), fun _ msg pm hterms hpm => ?_⟩
          injection hterms with hmsg _
          rw [← hmsg, parse_encMsg] at hpm
          injection hpm with hpm_eq
          rw [← hpm_eq]
          have hne0 : (encSig stA4 (rnd (t13.length + 1) 32) key3 (rnd t13.length 32)).wire ≠
              msg0WireTerm := by
            intro heq
            have hdhs := encSig_wire_dhs_eq heq
            obtain ⟨hts, _⟩ := open scoped DY.Libsignal.Composed in
              Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hdhs
            omega
          have hne1 : (encSig stA4 (rnd (t13.length + 1) 32) key3 (rnd t13.length 32)).wire ≠
              msg1WireTerm := by
            intro heq
            have hdhs := encSig_wire_dhs_eq heq
            obtain ⟨hts, _⟩ := open scoped DY.Libsignal.Composed in
              Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hdhs
            omega
          simp [myGhost, myGhostAddr, beq_eq_false_iff_ne.mpr hne0, beq_eq_false_iff_ne.mpr hne1]
      · exact (hexp hv_x).elim
    · exact (hdec hv_l).elim

theorem ghostWF_visAt (k : Nat) : GhostWF myGhost (visAt k) := by
  have h11 : visAt 11 = visSteps.flatten := rfl
  have hsplit : visSteps.flatten = visAt k ++ (visSteps.drop k).flatten := by
    unfold visAt
    rw [← List.flatten_append, List.take_append_drop]
  have hg : GhostWF myGhost (visAt k ++ (visSteps.drop k).flatten) := by
    rw [← hsplit, ← h11]
    exact ghostWF_visAt_11
  exact ghostWF_of_append hg

def sentOnTraceBool (tr : ExecTrace) (t : DY.Bytes) : Bool :=
  (List.range tr.length).any fun idx => tr.getMessageSentAt idx == some t

theorem attackerKnows_of_sentOnTraceBool {tr : ExecTrace} {t : DY.Bytes}
    (h : sentOnTraceBool tr t = true) : t.AttackerKnows tr := by
  obtain ⟨idx, _, hget⟩ := List.any_eq_true.mp h
  exact Trace.MessageSentAt_implies_AttackerKnows tr t idx
    ((Trace.MessageSentAt_eq_getMessageSentAt t idx tr).mpr (beq_iff_eq.mp hget))

end Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux
