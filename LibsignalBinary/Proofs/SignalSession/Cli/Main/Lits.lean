/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
public import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import all Init.Data.String.Defs

@[expose] public section

set_option autoImplicit false

/-!
# Read-Only `.rodata` Literals of `signal-session` `main`

**Checked by Lean.**

Proves that the 8 read-only string literals in `mainLits img` (`"coins"` and the 7 nonempty `Dir`
paths of `Stores::open()`) hold automatically whenever `img.FrozenLoaded s` holds
(`mainLits_of_frozenLoaded`), eliminating `mainLits img` from `main` hop preconditions
(`sepWPp_mainFrame_mainLits`).
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

def mainLitList : List (Nat × List (BitVec 8)) :=
  (coinsLitOff.toNat, utf8 "coins") :: dirLits.map fun l => (l.1.toNat, utf8 l.2)

theorem foldr_lits_eq_roLits (base : BitVec 64) (ls : List (BitVec 64 × String)) :
    ls.foldr (fun l P => ((base + l.1) ↦ᵣ utf8 l.2) ∗ P) emp =
      roLits base (ls.map fun l => (l.1.toNat, utf8 l.2)) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => rw [List.foldr_cons, ih, List.map_cons, roLits_cons, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]

theorem mainLits_eq_roLits (img : Obj.Image) : mainLits img = roLits img.base mainLitList := by
  rw [mainLits, foldr_lits_eq_roLits, mainLitList, roLits_cons, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

open ProofLib.ProgramReflection in
/-- Kernel check that all 8 entries of `mainLitList` are relocation-free `.rodata` literals of `libsignalSessionImage`. -/
theorem mainLitList_roLitAt :
    mainLitList.all (fun l => libsignalSessionImage.RoLitAt l.1 l.2) = true := by
  rfl_kernel

/-- Extracts `mainLits img` from `img.FrozenLoaded s` without consuming separation-logic frame `P`. -/
theorem mainLits_of_frozenLoaded {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ mainLits img ∗ P := by
  rw [mainLits_eq_roLits]
  exact hF.sat_roLits himg mainLitList_roLitAt hP

@[simp] theorem mainLits_dup (img : Obj.Image) : (mainLits img ∗ mainLits img) = mainLits img := by
  rw [mainLits_eq_roLits, roLits_dup]

/-- Eliminates `mainLits img` from `mainFrame`'s statics hypothesis whenever `img.FrozenLoaded s` holds. -/
theorem sepWPp_mainFrame_mainLits {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {A : RustAlloc} {stk : Nat} {Statics : SepProp} {i : Inputs}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hwp : SepWPp prog ret s (mainFrame A stk (Statics ∗ mainLits img) i s) Q Qp oom) :
    SepWPp prog ret s (mainFrame A stk Statics i s) Q Qp oom := by
  intro R hm
  apply hwp R
  have h := mainLits_of_frozenLoaded himg hF hm
  refine Satisfies.of_eq h ?_
  simp only [mainFrame]
  ac_rfl

end CryptoVerification.SignalSession.Cli.MainHops
