/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public import Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreSalt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKIR
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoClose
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (QRest)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff ZVal)
open Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38 (PreNXOK)
def Split40PreNXOKOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), PreNXOK S g u
def Split40PreUntaggedOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ preMemo40 r S g ms', assumedInjective x.1 = true → x.2.2.take 4 ≠ compTag4
theorem split40PreUntaggedOwn_of_preNXOK (h : Split40PreNXOKOwn) : Split40PreUntaggedOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx hai; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  by_cases hX : x.2.2 ∈ CompRI0TermInj.x25519Vals
  · exact CompRI0TermInj.x25519Vals_untagged _ hX
  · exact h r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu x hxu hai hX
def Split40NonInjOffZOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ preMemo40 r S g ms' ++ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂, Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x → assumedInjective x.1 = false → ∀ z ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂, x.2.2 ≠ gamma compI0 S g z
theorem zVal_of_mem_saltedNodes40 {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {u : DY.Bytes} (hu : u ∈ saltedNodes40 salt tr stA cl) : ZVal (gamma compI0 S g u) := by
  unfold saltedNodes40 at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact CompRNonInj38Census.zVal_kdfExtract _ _ | exact CompRNonInj38Census.zVal_trunc8_kdfExtract _ _
theorem zVal_of_mem_z40Terms {S : Sem} {g : Ghost} {r : Records} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} (hu : u ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) : ZVal (gamma compI0 S g u) := (List.mem_append.mp hu).elim zVal_of_mem_saltedNodes40 zVal_of_mem_saltedNodes40
theorem split40NonInjOffZOwn_of_census (hN : WsIdx1Split40MemoPreRest.Split40NonInjCensusOwn) : Split40NonInjOffZOwn := by intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx hc hai z hz hxz; exact CompRNonInj38Census.not_zVal_of_nonInjOff (hN r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx hc hai).1 (hxz ▸ zVal_of_mem_z40Terms hz)
theorem split40PairsOwn_qZ40_of (hU : Split40PreUntaggedOwn) (hX : Split40NonInjOffZOwn) : Split40PairsOwn QZ40 := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; dsimp only; intro x₁ hx₁ x₂ hx₂ hc₁ hc₂ hz ⟨hsh, _, _, _, hval⟩; have hU' := hU r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hX' := hX r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; obtain ⟨htag, hzinj⟩ := WsIdx1Split40MemoCk1Pin.split40ZTagInj r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv; have hx₁' : x₁ ∈ preMemo40 r S g ms' ++ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_right _ hx₁
  have hs₁ := WsIdx1Split40MemoTagged.sound_of_mem_pre_new hx₁'; have hs₂ := WsIdx1Split40MemoTagged.sound_of_mem_pre_new hx₂
  rcases hz with hz₁ | hz₂
  · exact WsIdx1Split40MemoTagged.core_false hs₁ hs₂ htag hzinj (hU' x₂)
      (hX' x₂ hx₂ hc₂) hc₂ hz₁ hsh hval
  · exact WsIdx1Split40MemoTagged.core_false hs₂ hs₁ htag hzinj (hU' x₁)
      (hX' x₁ hx₁' hc₁) hc₁ hz₂ hsh.symm hval.symm
theorem split40PairsOwn_qRest40_of' (hU : Split40PreUntaggedOwn) (hK : Split40PairsOwn QKdf40) (hR : Split40PairsOwn fun S g known pts _ _ x₁ x₂ => QRest S g known pts x₁ x₂) : Split40PairsOwn QRest40 := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown pre new Z x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨u₁, _, hxu₁⟩ := List.mem_flatMap.mp hx₁
  obtain ⟨u₂, hxu₂⟩ : ∃ u₂, x₂ ∈ (gamma' compI0 S g u₂).memo := by
    rcases List.mem_append.mp hx₂ with hm | hm <;>
    · obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hm; exact ⟨u, hum⟩
  exact qRest40_of S g _ _ _ _ x₁ x₂ u₁ u₂ hxu₁ hxu₂ hc₁ hc₂ (hU r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown) (hK r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hR r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂)
def Split40NewSubOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂, Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x
theorem split40MemoCensusOwn_of_parts (hN : Split40NewSubOwn) (hZ : Split40PairsOwn QZ40) (hR : Split40PairsOwn QRest40) : WsIdx1CensusOwn.Split40MemoCensusOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown ⟨x₁, hx₁, x₂, hx₂, hb⟩; have hN' := hN r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hc₁ := hN' x₁ hx₁; have hc₂ : Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x₂ := (List.mem_append.mp hx₂).elim Or.inl (hN' x₂)
  by_cases hz : x₁.1 ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ ∨ x₂.1 ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
  · exact hZ r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂ hz hb
  · exact hR r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂
      (hz ∘ Or.inl) (hz ∘ Or.inr) hb
theorem kirDraws_of_drawPins {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (h : WsIdx1Split40MemoPreRest.Split40DrawPins r S g tr₁ tr₂ tr₃ cl₁ cl₂) : WsIdx1Split40MemoPreKIR.Split40KirDraws S g tr₁ tr₂ tr₃ cl₁ cl₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨WsIdx1Split40MemoPreKIR.kirVal_of_nonInjOff h1.1,
    WsIdx1Split40MemoPreKIR.kirVal_of_nonInjOff h2.1, by rw [h3]; decide +kernel,
    WsIdx1Split40MemoPreKIR.kirVal_of_nonInjOff h4.1, by rw [h5]; decide +kernel,
    WsIdx1Split40MemoPreKIR.kirVal_of_nonInjOff h6.1⟩
def Split40DrawPinsOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → WsIdx1Split40MemoPreRest.Split40DrawPins r S g tr₁ tr₂ tr₃ cl₁ cl₂
theorem split40MemoCensusOwn_of_enum (hE : Split40PrefixEnum) (hSub : Split40NewSubOwn) (hNew : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ u ∈ split40NewTerms r ms' p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂), CompC2Census38.Census compI0 S g u) (hD : Split40DrawPinsOwn) (hKK : WsIdx1Split40MemoPreKdf.Split40PreKKOwn) (hNX : Split40PreNXOKOwn) (hF : WsIdx1Split40MemoPreRest.Split40RestFnOwn) : WsIdx1CensusOwn.Split40MemoCensusOwn := by
  have hNC := WsIdx1Split40MemoPreRest.split40NonInjCensusOwn_of_enum hE hNew
  have hK := WsIdx1Split40MemoPreKdf.split40PairsOwn_qKdf40_of (WsIdx1Split40MemoPreSalt.split40PreSalt32Own_of_enum hE) hKK (WsIdx1Split40MemoPreKIR.split40PreKIROwn_of_enum hE
      fun r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown =>
        kirDraws_of_drawPins (hD r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown))
    fun r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx hc hai =>
      (hNC r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx hc hai).1
  have hQR := WsIdx1Split40MemoPreRest.split40PairsOwn_qRest_of_entry_fn hNC (WsIdx1Split40MemoPreRest.split40RestEntryOwn_of_enum hE hD) hF; have hU := split40PreUntaggedOwn_of_preNXOK hNX; exact split40MemoCensusOwn_of_parts hSub (split40PairsOwn_qZ40_of hU (split40NonInjOffZOwn_of_census hNC)) (split40PairsOwn_qRest40_of' hU hK hQR)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoClose
