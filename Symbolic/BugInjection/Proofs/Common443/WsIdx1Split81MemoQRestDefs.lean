/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
public import Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compKyberE2 compKyberCt2)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.CompC2Rest38 Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore (PairQ PairSide QKdf)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (QRest)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus (KdfSalt32)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff ZVal QKdfKK QKdfInjRest)
open Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ (NonInjOffXZ)
open Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38 (PreNXOK)
def Split81ExtPairsOwn (Q : PairQ40) : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let pre := preMemo81 r S g ms'
    let new := newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∀ x₁ ∈ new, ∀ x₂ ∈ pre ++ new, Cls40 base Z x₁ → Cls40 base Z x₂ →
      Q S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (ptAtoms (runVis r ms') ++ []) base Z x₁ x₂
def Split81PreNXOKOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), PreNXOK S g u
def Split81PreUntaggedOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ x ∈ preMemo81 r S g ms', assumedInjective x.1 = true → x.2.2.take 4 ≠ compTag4
def Split81ExtBaseUntaggedOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ x ∈ extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁, assumedInjective x.1 = true → x.2.2.take 4 ≠ compTag4
theorem split81PreUntaggedOwn_of_preNXOK (h : Split81PreNXOKOwn) : Split81PreUntaggedOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hx hai; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  by_cases hX : x.2.2 ∈ CompRI0TermInj.x25519Vals
  · exact CompRI0TermInj.x25519Vals_untagged _ hX
  · exact h r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown u hu x hxu hai hX
theorem split81ExtBaseUntaggedOwn_of_pre (h : Split81PreUntaggedOwn) : Split81ExtBaseUntaggedOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hx hai
  rcases List.mem_append.mp hx with hpre | hext
  · exact h r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hpre hai
  · exact extChainRows81_untagged hfits hp hinv x hext
theorem split81ExtBaseUntaggedOwn_of_preNXOK (h : Split81PreNXOKOwn) : Split81ExtBaseUntaggedOwn := split81ExtBaseUntaggedOwn_of_pre (split81PreUntaggedOwn_of_preNXOK h)
def Split81NonInjCensusOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let pre := preMemo81 r S g ms'
    let new := newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∀ x ∈ pre ++ new, Cls40 base Z x → assumedInjective x.1 = false → NonInjOffXZ x.2.2
def Split81NonInjOffZOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let pre := preMemo81 r S g ms'
    let new := newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∀ x ∈ pre ++ new, Cls40 base Z x → assumedInjective x.1 = false → ∀ z ∈ Z, x.2.2 ≠ gamma compI0 S g z
theorem zVal_of_mem_saltedNodes81 {r : Records} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} {u : DY.Bytes} (hu : u ∈ saltedNodes81 r salt tr₁ tr₂ tr₄ cl₁) : ZVal (gamma compI0 S g u) := by
  unfold saltedNodes81 at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact CompRNonInj38Census.zVal_kdfExtract _ _
  · exact CompRNonInj38Census.zVal_kdfExtract _ _
  · exact CompRNonInj38Census.zVal_kdfExtract _ _
  · exact CompRNonInj38Census.zVal_kdfExtract _ _
  · exact CompRNonInj38Census.zVal_kdfExtract _ _
  · exact CompRNonInj38Census.zVal_trunc8_kdfExtract _ _
theorem zVal_of_mem_z81Terms {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr₄ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} (hu : u ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂) : ZVal (gamma compI0 S g u) := by
  rcases List.mem_append.mp hu with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2 <;> exact zVal_of_mem_saltedNodes81 ‹_›
    · exact zVal_of_mem_saltedNodes81 h3
  · exact zVal_of_mem_saltedNodes81 h4
theorem split81NonInjOffZOwn_of_census (hN : Split81NonInjCensusOwn) : Split81NonInjOffZOwn := by intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown _ _ _ _ x hx hc hai z hz hxz; exact CompRNonInj38Census.not_zVal_of_nonInjOff (hN r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hx hc hai).1 (hxz ▸ zVal_of_mem_z81Terms hz)
theorem split81ExtPairsOwn_qZ40_of (hU : Split81ExtBaseUntaggedOwn) (hX : Split81NonInjOffZOwn) (hT : Split81ZTagInj) : Split81ExtPairsOwn QZ40 := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown _ _ _ _ x₁ hx₁ x₂ hx₂ hc₁ hc₂ hz ⟨hsh, _, _, _, hval⟩; have hU' := hU r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; have hX' := hX r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; obtain ⟨htag, hzinj⟩ := hT r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv; have hx₁' : x₁ ∈ preMemo81 r S g ms' ++ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁ := List.mem_append_right _ hx₁
  have hs₁ := sound_of_mem_pre_new81 hx₁'; have hs₂ := sound_of_mem_pre_new81 hx₂
  rcases hz with hz₁ | hz₂
  · exact core_false hs₁ hs₂ htag hzinj (fun h => hU' x₂ h) (hX' x₂ hx₂ hc₂) hc₂ hz₁ hsh hval
  · exact core_false hs₂ hs₁ htag hzinj (fun h => hU' x₁ h) (hX' x₁ hx₁' hc₁) hc₁ hz₂ (Ne.symm hsh) hval.symm
def Split81PreSalt32Own : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ x ∈ preMemo81 r S g ms', KdfSalt32 S g x
def Split81ExtKKOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∀ x₁ ∈ base, ∀ x₂ ∈ base, x₁.1 ∉ Z → x₂.1 ∉ Z →
      QKdfKK S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (ptAtoms (runVis r ms') ++ []) x₁ x₂
def Split81PreKIROwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let pre := preMemo81 r S g ms'
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∀ x₁ ∈ base, ∀ x₂ ∈ pre, x₁.1 ∉ Z → x₂.1 ∉ Z →
      QKdfInjRest S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (ptAtoms (runVis r ms') ++ []) x₁ x₂
theorem kdfSalt32_of_extChainRows81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) {x : Row} (hx : x ∈ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁) : KdfSalt32 S g x := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx; unfold extChainTerms81 at hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact kdfSalt32_of_not_kdf fun ⟨k, m, h⟩ =>
      CompRPreMemo38KdfCensus.ne_kdfExtract_of_notKdf (CompRPreMemo38KdfCensus.nk_dhPk _) k m h
  rcases List.mem_cons.mp hu with rfl | hbob
  · exact kdfSalt32_of_not_kdf fun ⟨k, m, h⟩ =>
      CompRPreMemo38KdfCensus.ne_kdfExtract_of_notKdf (CompRPreMemo38KdfCensus.nk_kemEncap_fst _ _) k m h
  · exact (bobChainRow_props r S g tr₁ tr₂ tr₄ cl₁ hbob).1
theorem qKdfInjRest_of_extChainRows81 (r : Records) (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) (hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2) (x₁ : Row) {x₂ : Row} (hx₂ : x₂ ∈ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁) : QKdfInjRest S g known pts x₁ x₂ := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx₂; unfold extChainTerms81 at hu
  rcases List.mem_cons.mp hu with rfl | hu
  · intro _ _ _ _ hX; exact absurd (Or.inl ⟨_, rfl⟩) hX
  rcases List.mem_cons.mp hu with rfl | hbob
  · intro _ _ _ _ _ _ _ _ _ _; right
    change (gamma compI0 S g (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₄.length + 1) 32)).1).length ≠ 32; rw [gamma_kemEncap_fst_of_e2 hent₂, kyberCtVals_lengths.2.2.1]; decide
  · exact (bobChainRow_props r S g tr₁ tr₂ tr₄ cl₁ hbob).2.2.1 known pts x₁
theorem split81ExtPairsOwn_qKdf40_of (hS : Split81PreSalt32Own) (hKK : Split81ExtKKOwn)
    (hR : Split81PreKIROwn)
    (hN : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
      let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
      let pre := preMemo81 r S g ms'
      let new := newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁
      let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
      ∀ x ∈ pre ++ new, Cls40 base Z x → assumedInjective x.1 = false → NonInjOff x.2.2) :
    Split81ExtPairsOwn QKdf40 := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown _ _ _ _ x₁ _ x₂ hx₂ hc₁ hc₂ hz₁ hz₂
  obtain ⟨u₂, hxu₂⟩ : ∃ u₂, x₂ ∈ (gamma' compI0 S g u₂).memo := by
    rcases List.mem_append.mp hx₂ with hm | hm <;> { obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hm; exact ⟨u, hum⟩ }
  have hS' := hS r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown
  let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
  let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
  have hsalt : ∀ x : Row, Cls40 base Z x → x.1 ∉ Z → KdfSalt32 S g x := fun x hc hz k m hk => by
    rcases List.mem_append.mp (cls40_pre_of_kdf hc hz hk) with hpre | hext
    · exact hS' x hpre k m hk
    · exact kdfSalt32_of_extChainRows81 r S g tr₁ tr₂ tr₄ cl₁ hext k m hk
  refine qKdf_of_parts S g _ _ x₁ x₂ u₂ hxu₂ (hsalt x₁ hc₁ hz₁) (hsalt x₂ hc₂ hz₂)
    (fun k₁ m₁ k₂ m₂ hk₁ hk₂ => hKK r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown
      x₁ (cls40_pre_of_kdf hc₁ hz₁ hk₁) x₂ (cls40_pre_of_kdf hc₂ hz₂ hk₂) hz₁ hz₂ k₁ m₁ k₂ m₂ hk₁ hk₂) ?_
    (hN r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₂ hx₂ hc₂)
  intro k m hk hK hX hT hai
  rcases List.mem_append.mp (cls40_pre_of_inj hc₂ hz₂ hai) with hpre₂ | hext₂
  · exact hR r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown
      x₁ (cls40_pre_of_kdf hc₁ hz₁ hk) x₂ hpre₂ hz₁ hz₂ k m hk hK hX hT hai
  · exact qKdfInjRest_of_extChainRows81 r S g _ _ tr₁ tr₂ tr₄ cl₁ hinv.hent₂ x₁ hext₂ k m hk hK hX hT hai
theorem split81ExtPairsOwn_qKdf40_of_census (hS : Split81PreSalt32Own) (hKK : Split81ExtKKOwn) (hR : Split81PreKIROwn) (hNC : Split81NonInjCensusOwn) : Split81ExtPairsOwn QKdf40 := split81ExtPairsOwn_qKdf40_of hS hKK hR (fun r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hx hc hai => (hNC r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x hx hc hai).1)
def Split81RestEntryOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let pre := preMemo81 r S g ms'
    let new := newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∀ x ∈ pre ++ new, Cls40 base Z x → RestEntry S g x
def Split81RestFnOwn : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ →
    let base := extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁
    let pre := preMemo81 r S g ms'
    let new := newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁
    let Z := z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
    ∃ (fn : HwBytes → DY.Bytes) (Rv : HwBytes → Prop), ∀ x ∈ pre ++ new, Cls40 base Z x → RestFnEntry fn Rv S g x
theorem exists_memo_of_mem81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {p : PreKeyFields} {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} {x : Row} (hx : x ∈ preMemo81 r S g ms' ++ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁) : x.2.2 = gamma compI0 S g x.1 := (sound_of_mem_pre_new81 hx).2
theorem split81ExtPairsOwn_qRest_of_entry_fn (hN : Split81NonInjCensusOwn) (hE : Split81RestEntryOwn) (hF : Split81RestFnOwn) : Split81ExtPairsOwn (liftPairQ40 QRest) := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown _ _ _ _ x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨fn, Rv, hfn⟩ := hF r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; have hx₁_mem : x₁ ∈ preMemo81 r S g ms' ++ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁ := List.mem_append_right _ hx₁; have hv₁ := exists_memo_of_mem81 hx₁_mem; have hv₂ := exists_memo_of_mem81 hx₂; have hf₁ := hfn x₁ hx₁_mem hc₁; have hf₂ := hfn x₂ hx₂ hc₂
  exact qRest_of_entries S g _ _ x₁ x₂ hv₁ hv₂ (hN r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₁ hx₁_mem hc₁) (hN r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₂ hx₂ hc₂) (hE r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₁ hx₁_mem hc₁) (hE r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₂ hx₂ hc₂) (qRestNR_of_fn hv₁ hv₂ hf₁ hf₂) (qRestRR_of_fn hv₁ hv₂ hf₁ hf₂) (qRestXX_of_fn hv₁ hv₂ hf₁ hf₂) (qRestTT_of_fn hv₁ hv₂ hf₁ hf₂)
theorem split81ExtPairsOwn_qRest40_of (hU : Split81ExtBaseUntaggedOwn) (hK : Split81ExtPairsOwn QKdf40) (hR : Split81ExtPairsOwn (liftPairQ40 QRest)) : Split81ExtPairsOwn QRest40 := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown base pre new Z x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨u₁, _, hxu₁⟩ := List.mem_flatMap.mp hx₁
  obtain ⟨u₂, hxu₂⟩ : ∃ u₂, x₂ ∈ (gamma' compI0 S g u₂).memo := by
    rcases List.mem_append.mp hx₂ with hm | hm <;> { obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hm; exact ⟨u, hum⟩ }
  exact qRest40_of S g _ _ _ _ x₁ x₂ u₁ u₂ hxu₁ hxu₂ hc₁ hc₂ (hU r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown) (hK r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hR r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂)
theorem split81ExtPairsOwn_qRest40_of_pre (hU : Split81PreUntaggedOwn) (hK : Split81ExtPairsOwn QKdf40) (hR : Split81ExtPairsOwn (liftPairQ40 QRest)) : Split81ExtPairsOwn QRest40 := split81ExtPairsOwn_qRest40_of (split81ExtBaseUntaggedOwn_of_pre hU) hK hR
theorem split81MemoCensusOwn_of_ext_parts (hZ : Split81ExtPairsOwn QZ40) (hR : Split81ExtPairsOwn QRest40) : Split81MemoCensusOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown ⟨x₁, hx₁, x₂, hx₂, hbody⟩; have hN' := split81ExtNewSub r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv; have hc₁ := hN' x₁ hx₁
  have hc₂ : Cls40 (extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁) (z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂) x₂ := by
    rcases List.mem_append.mp hx₂ with h | h
    · exact Or.inl (List.mem_append_left _ h)
    · exact hN' x₂ h
  by_cases hz : x₁.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ ∨ x₂.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂
  · exact hZ r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂ hz hbody
  · exact hR r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown x₁ hx₁ x₂ hx₂ hc₁ hc₂
      (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h)) hbody
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
