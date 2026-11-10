/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecryptNoop
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg) open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
def Split40DecompSwapRepOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (wsIdx1Trace.take 40) → parsePreKeyWire wire3Idx1Bytes = some p → ∃ (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), ExplainsMoves compI0 r S who ok g ms' (wsIdx1Trace.take 40) ∧ WsIdx1DecryptNoop.DecryptNoop r ms' ∧ WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧ Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ ∧ x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂ ∈ preKeyRepresentations compI0 r S g ms' wire3Idx1Bytes
def Split40MemoCensusOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (runTraceMoves r ms') (runVis r ms') (WsIdx1Split40Census.split40NewTerms r ms' p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂)) []
theorem noBscAt40_of_own (hDecomp : Split40DecompSwapRepOwn) (_hpk : WsIdx1Split40Census.Split40PkPin) (hM : Split40MemoCensusOwn) (hO : WsIdx1Split40Census.Split40OwnSaltMac) : NoBscAt40 := by
  intro r S g ms p hfits hex hp; obtain ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex', hdf, hinv, hown, hx⟩ := hDecomp r S g ms p hfits hex hp
  refine ⟨g, ms', hex', WsIdx1DecryptNoop.not_readCollision_of_decryptNoop hdf, _, hx, ?_⟩
  have hM' := hM r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; intro h; unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects at h; dsimp only at h
  rcases hP : parseTrSignalMsg (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg with _ | msg <;>
    simp only [WsIdx1Split40Census.split40NewTerms, hP] at h hM'
  · exact hM' h
  · exact h.elim (fun hm => hM' (Symbolic.BugInjection.Proofs.Common443.CompExcuse.memoCollisionOn_bobTrials_to_bobTerms hP hm)) (hO r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ msg hfits hp hinv hP)
def Split81DecompSwapRepOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (wsIdx1Trace.take 81) → CompSetupSecrecy.NoBrk r ms → parsePreKeyWire wire6Idx1Bytes = some p → ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), ExplainsMoves compI0 r S who ok g ms' (wsIdx1Trace.take 81) ∧ WsIdx1DecryptNoop.DecryptNoop r ms' ∧ WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' wire6Idx1Bytes
def Split81MemoCensusOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (runTraceMoves r ms') (runVis r ms') (WsIdx1Split81Census.split81NewTerms r ms' p (x81Idx1 r tr₁ tr₂ tr₄ cl₁)) []
theorem noBscAt81_of_own (hDecomp : Split81DecompSwapRepOwn) (hpin : WsIdx1Split81Census.Split81PinObl) (hM : Split81MemoCensusOwn) : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (wsIdx1Trace.take 81) → parsePreKeyWire (recvAt 81) = some p → ∃ g' ms', ExplainsMoves compI0 r S who ok g' ms' (wsIdx1Trace.take 81) ∧ ¬ ReadCollision compI0 r S g' ms' (wsIdx1Trace.take 81) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' (recvAt 81), ¬ BobStartCollision compI0 r S g' ms' p x := by
  have hO := WsIdx1Split81Census.split81OwnSaltMac_of_pin hpin; intro r S g ms p hfits hnb hex hp; obtain ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', hdf, hinv, hown, hx⟩ := hDecomp r S g ms p hfits hex hnb hp
  refine ⟨g, ms', hex', WsIdx1DecryptNoop.not_readCollision_of_decryptNoop hdf, _, hx, ?_⟩
  have hM' := hM r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; intro h; unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects at h; dsimp only at h
  rcases hP : parseTrSignalMsg (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg with _ | msg <;>
    simp only [WsIdx1Split81Census.split81NewTerms, hP] at h hM'
  · exact hM' h
  · exact h.elim (fun hm => hM' (Symbolic.BugInjection.Proofs.Common443.CompExcuse.memoCollisionOn_bobTrials_to_bobTerms hP hm)) (hO r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ msg hfits hp hinv hP)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn
