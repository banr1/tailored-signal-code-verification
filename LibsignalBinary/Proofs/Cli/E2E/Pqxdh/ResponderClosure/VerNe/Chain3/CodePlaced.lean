/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DefsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `message::merge<Chain> [local#4]` Code and Stack Helpers

`[LibsignalPlacement]` Block-`516` instruction-fetch helpers and stack-frame splits corresponding to
`VerNe.Chain3.Code`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

theorem libsignalCodeLoaded_preserve_c3 {mpl : Obj.MultiPlacement} {prog : Program} {s sm : State}
    (hcl : LibsignalCodeLoaded mpl s.mem) (hsteps : Steps prog s sm) :
    LibsignalCodeLoaded mpl sm.mem :=
  fun i hi hmut X O svc => hsteps.codeLoaded (hcl i hi hmut X O svc)

theorem SepWPp.of_sepWP_lscl_c3 [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (libsignalCodeLoaded_preserve_c3 hcl hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

theorem SepWPp.call_lscl_c3 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → LibsignalCodeLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm (libsignalCodeLoaded_preserve_c3 hcl hsteps)
        hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
