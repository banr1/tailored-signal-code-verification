/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.EquationalTheory.Literal
import DY.EquationalTheory.DiffieHellman
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# One-Time Prekey Choice for `session_initiate`

Defines `PureExternContracts` and proves `ini_opkChoice`, selecting either Bob's setup one-time
prekey handle, an `attackerSend` of its canonical X25519 variation, or an `attackerSend` literal to
match an accepted bundle's OPK slice.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.IniPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open DY DY.Comparse DY.Libsignal
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (X25519TorsionShiftsRejected)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet (x25519LowOrder)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-- External primitive laws required by `session_initiate` (`ExternContractsHoldCli`). -/
abbrev PureExternContracts (interp : ExternInterpretation) : Prop :=
  ExternCryptoLawsHold interp ∧ X25519PubCanonical interp ∧ X25519TorsionShiftsRejected interp

theorem ini_opkChoice (interpretation : ExternInterpretation) (hext : PureExternContracts interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} (who : List Participant) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (bundle : HwBytes) (ds : List HwBytes)
    (hm : MatchedPrefix interpretation r S who g ms acc)
    (hhon : HonestBundle interpretation r bundle) (hok : IniOkBin bundle ds) :
    ∃ (ms_opk : List Move) (oi : Option Nat) (opk : Option DY.Bytes),
      (ms_opk = [] ∨ ∃ t, ms_opk = [.attackerSend t] ∧ t.AttackerKnows (runTraceMoves r ms)) ∧
      MatchedPrefix interpretation r S who g (ms ++ ms_opk) acc ∧
      NetOpt (runTraceMoves r (ms ++ ms_opk)) oi opk ∧
      (opk.all fun o => !x25519LowOrder o) = true ∧
      ∀ g' : Ghost, g'.addr = g.addr →
        (∀ i j, i < (runTraceMoves r (ms ++ ms_opk)).length → g'.σ i j = g.σ i j) →
        PreKeyBundleLayoutMatches interpretation S g' bundle
          (received (runTraceMoves r (ms ++ ms_opk)) ([14, 15, 20, 21] ++ oi.toList)) := by
  have hNe : r.alice ≠ r.bob := hwf.1
  have hEq : ExternCryptoLawsHold interpretation := hext.1
  have hPubCanon : X25519PubCanonical interpretation := hext.2.1
  have hreach_ms : (runTraceMoves r ms).Reachable reachability := hm.2.1.2.2.1.1
  rcases hok.opk with h0 | ⟨h1, hb9, hlowLit⟩
  · refine ⟨[], none, none, Or.inl rfl, by simpa using hm, trivial, rfl, ?_⟩
    intro g' haddr hσ
    have hC' := compat_of_sigma_eq_lt hNe (ms ++ []) hm.1 haddr hσ
    rw [List.append_nil, Option.toList, List.append_nil, received_setupHandles r ms hNe]
    exact ⟨bundleCore_of_honestBundle interpretation r hNe _ g' hC' bundle hhon hok.bundle_len, h0⟩
  · obtain ⟨hslice, hlen32⟩ := slice_9_33_eq_ecKey hok.bundle_len hb9
    let opkBytes := slice bundle 10 32
    by_cases hHonU : r.withOpk = true ∧ x25519UCoord opkBytes = x25519UCoord (pubBytes interpretation (secretBytes r 6))
    · rcases hHonU with ⟨hWith, huOf⟩
      by_cases hBytes : opkBytes = pubBytes interpretation (secretBytes r 6)
      · refine ⟨[], some 25, some (setupPublic r 8), Or.inl rfl, by simpa using hm, ?_, ?_, ?_⟩
        · simp only [NetOpt, List.append_nil]
          exact at?_of_setupTrace (setupTrace_at?_25 r hNe hWith)
        · simp only [Option.all, setupPublic_8 r hNe hWith]
          have hv1 : (DY.DiffieHellman.dhPk (randTerm 22 32)).view? DY.X25519.Variant.SubF = none :=
            Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
          have hv2 : (DY.DiffieHellman.dhPk (randTerm 22 32)).view? DY.Literal.Literal.SubF = none :=
            Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
          simp only [x25519LowOrder, DY.X25519.normalizeX25519Key, hv1,
            DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv2]
          rfl
        · intro g' haddr hσ
          have hC' := compat_of_sigma_eq_lt hNe (ms ++ []) hm.1 haddr hσ
          rw [received_setupHandles_some r (ms ++ []) hNe
            (runTrace_getMessageSentAt_25 r (ms ++ []) hNe hWith)]
          refine ⟨bundleCore_of_honestBundle interpretation r hNe _ g' hC' bundle hhon hok.bundle_len,
            h1, ?_⟩
          rw [gamma_setupPublic_8 interpretation r hNe hWith _ g' hC', ← hBytes]
          exact hslice
      · let opkTerm := DY.X25519.x25519Variant (setupPublic r 8) (keyVariation opkBytes)
        let ms_opk : List Move := [.attackerSend opkTerm]
        have hknows : opkTerm.AttackerKnows (runTraceMoves r ms) :=
          attackerKnows_x25519Variant_opkPub r ms hNe hWith (keyVariation opkBytes)
        have hreach' : (runTraceMoves r (ms ++ ms_opk)).Reachable reachability := by
          rw [Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc]
          exact attackerSend_reachable hreach_ms hknows
        have hsent : (runTraceMoves r (ms ++ ms_opk)).getMessageSentAt (runTraceMoves r ms).length =
            some opkTerm := by
          rw [Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc]
          exact getMessageSentAt_attackerSend _ _
        refine ⟨ms_opk, some (runTraceMoves r ms).length, some opkTerm,
          Or.inr ⟨opkTerm, rfl, hknows⟩,
          Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_attackerSend hm hreach', ?_, ?_, ?_⟩
        · simp only [ms_opk, NetOpt, Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc,
            Symbolic.Swarm.Leaves.IC12Stage1MP.attackerSend_next]
          exact at?_append_self _ _
        · simp [Option.all, opkTerm, x25519LowOrder_x25519Variant_opkPub r hNe hWith]
        · intro g' haddr hσ
          have hC' := compat_of_sigma_eq_lt hNe (ms ++ ms_opk) hm.1 haddr hσ
          rw [received_setupHandles_some r (ms ++ ms_opk) hNe hsent]
          refine ⟨bundleCore_of_honestBundle interpretation r hNe _ g' hC' bundle hhon hok.bundle_len,
            h1, ?_⟩
          dsimp only [opkTerm]
          rw [gamma_x25519Variant_opkPub hEq hPubCanon hwf hWith _ g' hC' hlen32 huOf]
          exact hslice
    · let opkTerm := compHwLit opkBytes
      let ms_opk : List Move := [.attackerSend opkTerm]
      have hknows : opkTerm.AttackerKnows (runTraceMoves r ms) :=
        attackerKnows_compHwLit opkBytes (runTraceMoves r ms)
      have hreach' : (runTraceMoves r (ms ++ ms_opk)).Reachable reachability := by
        rw [Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc]
        exact attackerSend_reachable hreach_ms hknows
      have hsent : (runTraceMoves r (ms ++ ms_opk)).getMessageSentAt (runTraceMoves r ms).length =
          some opkTerm := by
        rw [Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc]
        exact getMessageSentAt_attackerSend _ _
      refine ⟨ms_opk, some (runTraceMoves r ms).length, some opkTerm,
        Or.inr ⟨opkTerm, rfl, hknows⟩,
        Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_attackerSend hm hreach', ?_, ?_, ?_⟩
      · simp only [ms_opk, NetOpt, Symbolic.Swarm.Leaves.IC12Stage1MP.runTrace_snoc,
          Symbolic.Swarm.Leaves.IC12Stage1MP.attackerSend_next]
        exact at?_append_self _ _
      · dsimp only [Option.all, opkTerm, compHwLit]
        rw [hlowLit]; rfl
      · intro g' haddr hσ
        have hC' := compat_of_sigma_eq_lt hNe (ms ++ ms_opk) hm.1 haddr hσ
        rw [received_setupHandles_some r (ms ++ ms_opk) hNe hsent]
        refine ⟨bundleCore_of_honestBundle interpretation r hNe _ g' hC' bundle hhon hok.bundle_len,
          h1, ?_⟩
        dsimp only [opkTerm]
        rw [gamma_compHwLit]
        exact hslice

end Symbolic.Swarm.CREF.CliPure.IniPure
