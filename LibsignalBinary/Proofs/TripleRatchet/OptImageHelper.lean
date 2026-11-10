/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.InImageLift
public import ProofLib.SepLogic.WP

/-!
# Optional-Image Specification and `SepWP` / `SepWPp` Sequencing Helpers

Combinators parameterized by `oimg : Option Obj.Image` that specialize uniformly to plain
`Spec α` (`oimg = none`) and `spec.inImage img` (`oimg = some img`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib SepProp CryptoVerification.InImageLift

/-- Prepends `⌜OptCallInv oimg s⌝` to `spec.pre`.
At `oimg = some img`, `specWithOptInv (some img) spec` is definitionally `spec.inImage img`. -/
abbrev specWithOptInv {α : Type} (oimg : Option Obj.Image) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜OptCallInv oimg s⌝ ∗ spec.pre x s }

theorem specWithOptInv_some_eq {α : Type} (img : Obj.Image) (spec : Spec α) :
    specWithOptInv (some img) spec = spec.inImage img :=
  rfl

theorem subroutine_ok_to_optNone {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (specWithOptInv none spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ R := by
    simpa only [specWithOptInv, OptCallInv, pure_true, emp_sepConj] using hpre
  exact (h.to_outcome x R s0 hpc hrun hpre' hal).mono_outcome fun _ hout => hout

theorem subroutine_ok_of_optNone {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr (specWithOptInv none spec)) :
    subroutine_ok P addr spec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (specWithOptInv none spec).pre x s0 ∗ R := by
    simpa only [specWithOptInv, OptCallInv, pure_true, emp_sepConj] using hpre
  exact (h.to_outcome x R s0 hpc hrun hpre' hal).mono_outcome fun _ hout => hout

theorem subroutine_ok_optImage_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (oimg : Option Obj.Image) (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (specWithOptInv oimg spec) := by
  cases oimg with
  | none => exact subroutine_ok_to_optNone h
  | some img => exact subroutine_ok_inImage_of_subroutine_ok img h

/-- Thread `OptCallInv oimg` across a `SepWP` segment to `mid`. -/
theorem SepWP.seq_optImage {prog : Program} {oimg : Option Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : OptCallInv oimg s)
    (h : SepWP prog mid s P (fun sm Pm => OptCallInv oimg sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  cases oimg with
  | none =>
    exact ProofLib.SepWP.seq h fun _ _ _ _ hnext => hnext trivial
  | some img =>
    exact ProofLib.SepWP.of_sepWP_frozen hinv.1 hinv.2
      (ProofLib.SepWP.mono h fun _ _ _ _ hnext hfl hsym => hnext ⟨hfl, hsym⟩)

/-- Thread `OptCallInv oimg` across a `SepWP` segment to `mid`, continuing in `SepWPp` to `ret`. -/
theorem SepWPp.of_sepWP_optImage {prog : Program} {oimg : Option Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : OptCallInv oimg s)
    (h : SepWP prog mid s P (fun sm Pm => OptCallInv oimg sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  cases oimg with
  | none =>
    exact ProofLib.SepWPp.of_sepWP
      (ProofLib.SepWP.mono h fun _ _ _ _ hnext => hnext trivial)
  | some img =>
    exact ProofLib.SepWPp.of_sepWP_frozen hinv.1 hinv.2
      (ProofLib.SepWP.mono h fun _ _ _ _ hnext hfl hsym => hnext ⟨hfl, hsym⟩)

end CryptoVerification.LibsignalTripleRatchet
