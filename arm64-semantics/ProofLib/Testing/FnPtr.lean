/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.FnPtr
public import ProofLib.SepLogic.WP

/-!
# Function-Pointer Hoare Logic Tests

Unit and regression tests for `FnPtrSpec`, `SafeFnPtrSpec`, `wp_blr_of_fnPtrSpec`,
`wp_br_of_fnPtrSpec`, and `rodataPtr_eq_fnAddr_of_loads`.
-/

@[expose] public section

namespace ProofLib.Tests.FnPtr

open Arm64 ProofLib ProofLib.ProgramReflection

def syntheticLinkedImage : Obj.LinkedImage :=
  { code := List.replicate 8 0#8
    dataOff := 0x1000
    data := List.replicate 16 0#8
    bss := 0
    roData := [(0x1000, 16)]
    gotOff := 0x1010
    relocs := [{ off := 8, width := 8, target := 4 }]
    symbols := [("alpha", 0), ("widget", 4), ("table", 0x1000)]
    stubs := [] }

theorem synthetic_rodata_ptr_ok {img : Obj.Image}
    (himg : Obj.Loads syntheticLinkedImage img) :
    rodataPtr img (0x1000 + 8) = img.fnAddr "widget" :=
  rodataPtr_eq_fnAddr_of_loads himg (by rfl_kernel)

/-- info: 'ProofLib.Tests.FnPtr.synthetic_rodata_ptr_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms synthetic_rodata_ptr_ok

/--
error: (kernel) application type mismatch
  rodataPtr_eq_fnAddr_of_loads himg (Eq.refl (checkRodataReloc syntheticLinkedImage (4096 + 8) "alpha"))
argument has type
  checkRodataReloc syntheticLinkedImage (4096 + 8) "alpha" = checkRodataReloc syntheticLinkedImage (4096 + 8) "alpha"
but function has type
  checkRodataReloc syntheticLinkedImage (4096 + 8) "alpha" = true → rodataPtr img (4096 + 8) = img.fnAddr "alpha"
-/
#guard_msgs in
theorem synthetic_rodata_ptr_wrong_target {img : Obj.Image}
    (himg : Obj.Loads syntheticLinkedImage img) :
    rodataPtr img (0x1000 + 8) = img.fnAddr "alpha" :=
  rodataPtr_eq_fnAddr_of_loads himg (by rfl_kernel)

theorem wp_blr_and_br_smoke {prog : Program} {s : State} {spec : Spec Unit} {P : SepProp}
    {post : State → SepProp → Prop}
    (hfn : FnPtrSpec prog (s.readReg64 .x8) spec)
    (hpc : s.pc = 0x2000#64) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hfetch : prog.fetch 0x2000#64 = some (.blr .x8))
    (hpre : ∀ R, s.mem ⊨ P ∗ R →
      s.mem ⊨ spec.pre () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) ∗ (emp ∗ R))
    (hnopan : ∀ R' sf, sf.status = .Panicked →
      ¬(sf.mem ⊨ spec.onPanic () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ R'))
    (hnoex : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit () code ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ R'))
    (hnooom : ∀ R' sf, sf.status = .OutOfMemory →
      ¬(sf.mem ⊨ spec.onOom () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ R'))
    (hcont : ∀ sf, sf.pc = 0x2004#64 → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog 0x2008#64 sf (spec.post () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ emp) post) :
    SepWP prog 0x2008#64 s P post :=
  wp_blr_of_fnPtrSpec hfn hpc hrun halign hfetch hpre hnopan hnoex hcont
    (fun R sf hst ho => False.elim (hnooom (emp ∗ R) sf hst ho))

end ProofLib.Tests.FnPtr
