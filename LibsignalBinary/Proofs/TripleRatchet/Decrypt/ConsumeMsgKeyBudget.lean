/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey

/-!
# Budget-Threaded `consume_message_key` Callee Contract & Call Combinators

Defines the budget-threaded relocatable `[LibsignalPlacement]` `cmkRawSpecPlaced` contract
(parameterized by an allocator event envelope `cmkEnv`, with `onOom = ⌜False⌝` and `allocFailedIn`
dropped from `onPanic`), along with `Steps` call-continuation combinators preserving
`LibsignalCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSession (ConsumeMessageKeyGhost)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)

/-- Budget-threaded relocatable `[LibsignalPlacement]` `consume_message_key` raw specification,
    reusing `KeyDerive.cmkRawSpecPlaced` via `A.atState`, eliminating `onOom` (`⌜False⌝`), and
    dropping `allocFailedIn` from `onPanic` so only `(x.model F).1 = .error .panic` remains. -/
def cmkRawSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cmkEnv : ConsumeMessageKeyGhost → List AllocEvent → Prop) :
    Spec (ConsumeMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (cmkEnv x)⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced
        F (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜cmkEnv x evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced
        F (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜(x.model F).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Call continuation combinator on `Steps` preserving `LibsignalCodeRoLoaded lsmpl`. -/
theorem steps_call_out_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {Out : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → Out sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ Out s')
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ Out s' := by
  obtain ⟨s', hsteps, hout | hout⟩ :=
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.steps_call_placed
      x hcall hpc hrun hsp hlr hcl hL hpre hpanic
      (fun sf h1 h2 h3 h4 h5 h6 h7 h8 =>
        let ⟨s', hs, ho⟩ := hnext sf h1 h2 h3 h4 h5 h6 h7 h8
        ⟨s', hs, Or.inl ho⟩) hexit hoom
  · exact ⟨s', hsteps, hout⟩
  · exact ⟨s', hsteps, hout⟩

/-- Call continuation combinator on `Steps` for `withLsCodeRoLoaded lsmpl spec` callees. -/
theorem steps_call_out_placed_cro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {Out : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → Out sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ Out s')
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ Out s' := by
  have hpre' : sm.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact steps_call_out_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget
