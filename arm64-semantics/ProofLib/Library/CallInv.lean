/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.Invariant
public import ProofLib.Library
import Arm64.Trusted.Spec.SepLogic

/-!
# Image Call Invariant and `Spec.inImage` Call Rules

Defines `Obj.Image.CallInv` (`img.FrozenLoaded s ∧ s.symtab = img.symtab`), proves its
preservation across `Memory.KeepsFrozen` updates and `Steps`, and threads it through `reaches_pc`
sequences and `Spec.inImage` subroutine calls.
-/

@[expose] public section

namespace Arm64

open ProofLib

/-- The part of `Spec.inImage img`'s precondition about the state. -/
def Obj.Image.CallInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

/-- A state update that keeps `symtab` and frozen bytes keeps `CallInv` (e.g. stores to
    writable memory, `Memory.keepsFrozen_write64`). -/
theorem Obj.Image.CallInv.of_keepsFrozen {img : Obj.Image} {s s' : State}
    (h : img.CallInv s) (hsym : s'.symtab = s.symtab) (hk : s.mem.KeepsFrozen s'.mem) :
    img.CallInv s' :=
  ⟨h.1.of_keepsFrozen hk, hsym.trans h.2⟩

theorem Obj.Image.CallInv.of_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : img.CallInv s) (hs : Steps prog s s') : img.CallInv s' :=
  h.of_keepsFrozen hs.symtab_eq hs.keepsFrozen

theorem reaches_pc_callInv {prog : Program} {img : Obj.Image} {t : BitVec 64} {s : State}
    {Q oom : State → Prop} (hinv : img.CallInv s) (h : reaches_pc prog t s Q oom) :
    reaches_pc prog t s (fun sf => Q sf ∧ img.CallInv sf) oom := by
  intro hL
  rcases h hL with ⟨sf, hst, ⟨hpc, hrun, hq⟩ | hoom⟩
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, hq, hinv.of_steps hst⟩⟩
  · exact ⟨sf, hst, Or.inr hoom⟩

theorem reaches_pc_seq_callInv {prog : Program} {img : Obj.Image} {mid t : BitVec 64}
    {s : State} {Q post oom : State → Prop} (hinv : img.CallInv s)
    (h1 : reaches_pc prog mid s Q oom)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm → img.CallInv sm →
      reaches_pc prog t sm post oom) :
    reaches_pc prog t s post oom :=
  reaches_pc_seq (reaches_pc_callInv hinv h1) fun sm hpc hrun hq => h2 sm hpc hrun hq.1 hq.2

theorem Spec.inImage_pre {α : Type} {spec : Spec α} {img : Obj.Image} {x : α} {s : State}
    {R : SepProp} (hinv : img.CallInv s) (h : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hinv, h⟩

/-- Call a subroutine satisfying `spec.inImage img`, threading `img.CallInv` across the call
    when `onPanic` and `onExit` are unsatisfiable. -/
theorem reaches_pc_call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {callee ret_pc exit_pc : BitVec 64} {spec : Spec α}
    (h_callee : subroutine_ok prog callee (spec.inImage img)) (x : α) (R : SepProp)
    {s_call : State} {post oom : State → Prop}
    (h_pc : s_call.pc = callee) (h_run : s_call.status = .Running)
    (h_lr : s_call.readReg64 Reg.lr = ret_pc)
    (h_inv : img.CallInv s_call)
    (h_pre : s_call.mem ⊨ spec.pre x s_call ∗ R)
    (h_cont : ∀ s_ret : State,
      s_ret.pc = ret_pc → s_ret.status = .Running → s_ret.sp = s_call.sp →
      CalleeSavedPreserved s_call s_ret → img.CallInv s_ret →
      (s_ret.mem ⊨ spec.post x s_call s_ret ∗ R) →
      reaches_pc prog exit_pc s_ret post oom)
    (h_sp_align : s_call.spAligned = true)
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s_call sf ∗ R) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code s_call sf ∗ R) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s_call sf ∗ R) → oom sf := by
      intro _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    reaches_pc prog exit_pc s_call post oom := by
  have h_reach := subroutine_ok_apply_full h_callee x R h_pc h_run (Spec.inImage_pre h_inv h_pre)
    h_sp_align h_no_panic h_no_exit h_oom
  rw [h_lr] at h_reach
  refine reaches_pc_seq (reaches_pc_callInv h_inv h_reach) fun s_ret h_ret_pc h_ret_run hq => ?_
  obtain ⟨⟨h_post, h_sp, h_cs⟩, hinv⟩ := hq
  exact h_cont s_ret h_ret_pc h_ret_run h_sp h_cs hinv h_post

end Arm64
