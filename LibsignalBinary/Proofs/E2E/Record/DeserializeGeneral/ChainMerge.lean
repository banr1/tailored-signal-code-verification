/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainLeaves

/-!
# General `message::merge<Chain>` Composition

Composes the entry, per-field loop (`chainLoopG_run`), and exit leaves from `ChainLeaves.lean` by
induction on the remaining fields to prove `chainMergeGen_ok`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed

/-- By induction on the remaining fields `m`, execution from `ChainLoopG` after `k` fields
satisfies `chainMergeGenSpec.post` (or panics with `chainMergeGenSpec.onPanic`). -/
theorem chainLoopG_run {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      ChainLoopG C ctl x R s0 k s →
      reaches_outcome (recordProg C ctl abs) chainMergeGenSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (chainExitG_ok C ctl (abs := abs) x R s0 s hs) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', ChainLoopG C ctl x R s0 (k + 1) s' →
        reaches_outcome (recordProg C ctl abs) chainMergeGenSpec x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (chainSenderRatchetKeyG_ok C ctl hC x R s0 k s hlt h12 hs) next
    · exact segStepG_then (chainKeyFieldG_ok C ctl hC x R s0 k s hlt h3 hs) next
    · exact segStepG_then (chainMessageKeysG_ok C ctl hC x R s0 k s hlt h4 hs) next

/-- `prost::encoding::message::merge::<Chain>` (`0x3974`) satisfies `chainMergeGenSpec` on
`tripleRatchetProgAt`. -/
theorem chainMergeGen_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) : ChainMergeGenOk C ctl abs := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  exact segStepG_then (chainEntryG_ok C ctl hC x R s0 hpc hrun hpre hal)
    (fun s hs => chainLoopG_run hC _ 0 s (Nat.zero_add _) hs)

end CryptoVerification.E2E.Record.DeserializeGeneral
