/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib

/-!
# Frozen-Image and Symbol-Table Invariant Threading for `SepWP` and `SepWPp`

Threads `img.FrozenLoaded s ∧ s.symtab = img.symtab` across `SepWP` and `SepWPp` segments
(`SepWPp.of_sepWP_frozen`, `SepWPp.of_sepWP_inv`, `SepWP.of_sepWP_inv`) and shows that
`Obj.Image.FrozenLoaded` depends only on `State.mem` (`frozenLoaded_of_mem_eq`).
-/

@[expose] public section

namespace CryptoVerification

open Arm64 ProofLib

/-- `SepWP` to a midpoint whose postcondition needs the frozen-image invariant, followed by
    `SepWPp`. The invariant at the start carries over to the midpoint. -/
theorem SepWPp.of_sepWP_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.of_sepWP_frozen hF hsym h

/-- Same statement as `SepWPp.of_sepWP_frozen`, under the name used by some call sites. -/
theorem SepWPp.of_sepWP_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.of_sepWP_frozen hfl hsym h

/-- `SepWP` composition carrying the frozen-image invariant to the midpoint. -/
theorem SepWP.of_sepWP_inv {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  ProofLib.SepWP.of_sepWP_frozen hfl hsym h

/-- `FrozenLoaded` depends only on memory. -/
theorem frozenLoaded_of_mem_eq {img : Obj.Image} {s0 s : State}
    (hmem : s0.mem = s.mem) (hfrozen : img.FrozenLoaded s) :
    img.FrozenLoaded s0 := by
  rw [Obj.Image.frozenLoaded_iff] at hfrozen ⊢
  rwa [hmem]

end CryptoVerification
