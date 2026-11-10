/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix
public import Symbolic.Proofs.Swarm.CREF.OpkRelOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# One-Time Pre-Key Relation over Clean Explanations

Specializes `COpkRelOn` to `Clean` explanations (`COpkRelC`), proving prefix closure of `Clean`
and providing transfer lemmas across non-accepting and non-OPK-consuming blocks.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open DY
open DY.Libsignal
open DY.Libsignal.PQXDH
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents
open CryptoProofLib.Refinement (ExternInterpretation)

section PrefixClosedClean
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}

theorem xplPrefixClosed_clean {who : List Participant} {ok : Nat → Bool} :
    XplPrefixClosed interpretation r S who (Clean interpretation r S who ok) :=
  ⟨fun _ _ _ h => h.1.1, fun _ _ _ _ _ h hm => clean_prefix (matchedPrefix_length_eq hm) h⟩

end PrefixClosedClean

/-- One-time pre-key relation over `Clean` explanations. -/
abbrev COpkRelC (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (used : Bool) (acc : List MachineEvent) : Prop :=
  COpkRelOn r (Clean interpretation r S who ok) used acc

section Clean
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
  {who : List Participant} {ok : Nat → Bool} {used used' : Bool}
  {acc blk : List MachineEvent}

theorem cOpkRelC_nil : COpkRelC interpretation r S who ok used [] :=
  cOpkRelOn_nil fun _ _ h => h.1.1

theorem COpkRelC.apply (h : COpkRelC interpretation r S who ok used acc)
    (hw : r.withOpk = true) (hu : used = false) {g : Ghost} {ms : List Move}
    (hc : Clean interpretation r S who ok g ms acc) :
    DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms) r.bob (setupPublic r 8) = false :=
  h hw hu g ms hc

theorem cOpkRelC_of_no_accept'
    (hopk : COpkRelC interpretation r S who ok used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hnoacc : ∀ e ∈ blk, eventKind e ≠ .accept) :
    COpkRelC interpretation r S who ok used' (acc ++ blk) :=
  cOpkRelOn_of_no_accept' xplPrefixClosed_clean hopk hused hhead hnoacc

theorem cOpkRelC_of_no_accept
    (hopk : COpkRelC interpretation r S who ok used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hreach : ∀ g ms, MatchedPrefix interpretation r S who g ms (acc ++ blk) →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable Composed.reachability)
    (hnoacc : ∀ e ∈ blk, eventKind e ≠ .accept) :
    COpkRelC interpretation r S who ok used' (acc ++ blk) :=
  cOpkRelOn_of_no_accept xplPrefixClosed_clean hopk hused hhead hreach hnoacc

theorem cOpkRelC_of_no_opkNamed_recv
    (hopk : COpkRelC interpretation r S who ok used acc)
    (hused : used' = false → used = false)
    (hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hreach : ∀ g ms, MatchedPrefix interpretation r S who g ms (acc ++ blk) →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable Composed.reachability)
    (hnoopk : ∀ b, MachineEvent.recv b ∈ blk → ¬ OpkNamed r b true) :
    COpkRelC interpretation r S who ok used' (acc ++ blk) :=
  cOpkRelOn_of_no_opkNamed_recv xplPrefixClosed_clean hopk hused hhead hreach hnoopk

theorem cOpkRelC_of_exists {b d pt : HwBytes}
    (hopk : COpkRelC interpretation r S who ok used acc)
    (hused : used' = false → used = false)
    (hreach : ∀ g ms,
      MatchedPrefix interpretation r S who g ms (acc ++ [.recv b, .rng d, .accept pt]) →
      ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable Composed.reachability)
    (hex : ¬ OpkNamed r b true ∨
      ∃ g₀ ms₀ b' a kh regIdxA mh pqIdx spqrMsgIdx n,
        kh.opk = none ∧
        List.Forall₂ (EventMatchesEntry interpretation r S g₀)
          [.recv b, .rng d, .accept pt]
          ((Move.bobStart b' a kh regIdxA mh pqIdx spqrMsgIdx (n + 1)).vis (runTraceMoves r ms₀))) :
    COpkRelC interpretation r S who ok used' (acc ++ [.recv b, .rng d, .accept pt]) :=
  cOpkRelOn_of_exists xplPrefixClosed_clean hopk hused hreach hex

end Clean

end Symbolic.Swarm.CREF
