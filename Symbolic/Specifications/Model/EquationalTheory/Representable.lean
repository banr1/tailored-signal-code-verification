/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Misc.Instances
public import DY.Bytes.Basic
import Std.Data.DTreeMap.Internal.Operations

/-!
# Single-Constructor `SubBytesFunctor` Builders

Arity-indexed builders for single-constructor `ALaCarte` term functors (`SubF`) and their
`FunctorSizeOf`, `Representable`, `RepresentableDecidableEq`, and `RepresentableOrd` instances.
-/

namespace DY

public abbrev ALaCarte.FunctorSizeOf.unary {F : Type → Type}
    (f0 : {a : Type} → F a → a) : ALaCarte.FunctorSizeOf F where
  sizeOf x := SizeOf.sizeOf (f0 x)

public abbrev ALaCarte.FunctorSizeOf.binary {F : Type → Type}
    (f0 f1 : {a : Type} → F a → a) : ALaCarte.FunctorSizeOf F where
  sizeOf x := SizeOf.sizeOf (f0 x) + SizeOf.sizeOf (f1 x)

public abbrev ALaCarte.FunctorSizeOf.ternary {F : Type → Type}
    (f0 f1 f2 : {a : Type} → F a → a) : ALaCarte.FunctorSizeOf F where
  sizeOf x := SizeOf.sizeOf (f0 x) + SizeOf.sizeOf (f1 x) + SizeOf.sizeOf (f2 x)

/-- Builds a `SubBytesFunctor` for a single-constructor functor `F` with non-recursive metadata `D`
and `n` recursive children. -/
@[expose, instance_reducible] public def SubBytesFunctor.ofDataExplicit {F : Type → Type}
    [sz : ALaCarte.FunctorSizeOf F]
    (D : Type) (deqD : DecidableEq D) (ordD : Ord D)
    (lawfulD : @Std.LawfulEqOrd D ordD) (transD : @Std.TransOrd D ordD)
    (n : Nat)
    (toData : {a : Type} → F a → D)
    (toChildren : {a : Type} → F a → Vector a n)
    (ofDataChildren : {a : Type} → D → Vector a n → F a)
    (from_to : {a : Type} → (x : F a) → ofDataChildren (toData x) (toChildren x) = x)
    (toData_of : {a : Type} → (d : D) → (as : Vector a n) → toData (ofDataChildren d as) = d)
    (toChildren_of : {a : Type} → (d : D) → (as : Vector a n) →
      toChildren (ofDataChildren d as) = as)
    (sizeOf_eq : {a : Type} → [SizeOf a] → (x : F a) →
      ALaCarte.FunctorSizeOf.sizeOf x = ((toChildren x).map SizeOf.sizeOf).sum) :
    SubBytesFunctor F :=
  letI repr : ALaCarte.Representable F := {
    CtorId := Unit
    ctors := fun () => { Data := D, nRec := n }
    toRepr := fun x => { id := (), data := toData x, as := toChildren x }
    fromRepr := fun r => ofDataChildren r.data r.as
    from_to := from_to
    to_from := fun ⟨(), d, as⟩ => by
      simp only [ALaCarte.FunctorRepr.mk.injEq, heq_eq_eq, true_and]
      exact ⟨toData_of d as, toChildren_of d as⟩
    sizeOf_eq := sizeOf_eq
  }
  letI deq : ALaCarte.RepresentableDecidableEq F := {
    ctorid_deq := (inferInstance : DecidableEq Unit)
    ctor_data_deq := fun () => deqD
  }
  letI ord : ALaCarte.RepresentableOrd F := {
    ctoridOrd := (inferInstance : Ord Unit)
    ctoridOrd_lawfulEq := (inferInstance : Std.LawfulEqOrd Unit)
    ctoridOrd_trans := (inferInstance : Std.TransOrd Unit)
    ctorDataOrd := fun () => ordD
    ctorDataOrd_lawfulEq := fun () => lawfulD
    ctorDataOrd_trans := fun () => transD
  }
  {}

@[expose, instance_reducible] public def SubBytesFunctor.unary {F : Type → Type}
    [sz : ALaCarte.FunctorSizeOf F]
    (f0 : {a : Type} → F a → a) (mk : {a : Type} → a → F a)
    (eta : {a : Type} → (x : F a) → mk (f0 x) = x := by intros; rfl)
    (f0_mk : {a : Type} → (x0 : a) → f0 (mk x0) = x0 := by intros; rfl)
    (hsz : {a : Type} → [SizeOf a] → (x : F a) →
      ALaCarte.FunctorSizeOf.sizeOf x = SizeOf.sizeOf (f0 x) := by intros; rfl) :
    SubBytesFunctor F :=
  SubBytesFunctor.ofDataExplicit Unit inferInstance inferInstance inferInstance inferInstance 1
    (fun _ => ())
    (fun x => #v[f0 x])
    (fun () as => mk as[0])
    (fun x => eta x)
    (fun () _ => rfl)
    (fun () as => by
      obtain ⟨⟨l⟩, hl⟩ := as
      match l, hl with
      | [x0], _ => simp [f0_mk])
    (fun x => by rw [hsz]; simp +arith)

@[expose, instance_reducible] public def SubBytesFunctor.binary {F : Type → Type}
    [sz : ALaCarte.FunctorSizeOf F]
    (f0 f1 : {a : Type} → F a → a) (mk : {a : Type} → a → a → F a)
    (eta : {a : Type} → (x : F a) → mk (f0 x) (f1 x) = x := by intros; rfl)
    (f0_mk : {a : Type} → (x0 x1 : a) → f0 (mk x0 x1) = x0 := by intros; rfl)
    (f1_mk : {a : Type} → (x0 x1 : a) → f1 (mk x0 x1) = x1 := by intros; rfl)
    (hsz : {a : Type} → [SizeOf a] → (x : F a) →
      ALaCarte.FunctorSizeOf.sizeOf x = SizeOf.sizeOf (f0 x) + SizeOf.sizeOf (f1 x) := by
        intros; rfl) :
    SubBytesFunctor F :=
  SubBytesFunctor.ofDataExplicit Unit inferInstance inferInstance inferInstance inferInstance 2
    (fun _ => ())
    (fun x => #v[f0 x, f1 x])
    (fun () as => mk as[0] as[1])
    (fun x => eta x)
    (fun () _ => rfl)
    (fun () as => by
      obtain ⟨⟨l⟩, hl⟩ := as
      match l, hl with
      | [x0, x1], _ => simp [f0_mk, f1_mk])
    (fun x => by rw [hsz]; simp +arith)

@[expose, instance_reducible] public def SubBytesFunctor.ternary {F : Type → Type}
    [sz : ALaCarte.FunctorSizeOf F]
    (f0 f1 f2 : {a : Type} → F a → a) (mk : {a : Type} → a → a → a → F a)
    (eta : {a : Type} → (x : F a) → mk (f0 x) (f1 x) (f2 x) = x := by intros; rfl)
    (f0_mk : {a : Type} → (x0 x1 x2 : a) → f0 (mk x0 x1 x2) = x0 := by intros; rfl)
    (f1_mk : {a : Type} → (x0 x1 x2 : a) → f1 (mk x0 x1 x2) = x1 := by intros; rfl)
    (f2_mk : {a : Type} → (x0 x1 x2 : a) → f2 (mk x0 x1 x2) = x2 := by intros; rfl)
    (hsz : {a : Type} → [SizeOf a] → (x : F a) →
      ALaCarte.FunctorSizeOf.sizeOf x =
        SizeOf.sizeOf (f0 x) + SizeOf.sizeOf (f1 x) + SizeOf.sizeOf (f2 x) := by intros; rfl) :
    SubBytesFunctor F :=
  SubBytesFunctor.ofDataExplicit Unit inferInstance inferInstance inferInstance inferInstance 3
    (fun _ => ())
    (fun x => #v[f0 x, f1 x, f2 x])
    (fun () as => mk as[0] as[1] as[2])
    (fun x => eta x)
    (fun () _ => rfl)
    (fun () as => by
      obtain ⟨⟨l⟩, hl⟩ := as
      match l, hl with
      | [x0, x1, x2], _ => simp [f0_mk, f1_mk, f2_mk])
    (fun x => by rw [hsz]; simp +arith)

/-- Builds a `SubBytesFunctor` for a 1-child functor `F` carrying non-recursive metadata `D`. -/
@[expose, instance_reducible] public def SubBytesFunctor.unaryData {F : Type → Type}
    [sz : ALaCarte.FunctorSizeOf F]
    (D : Type) [DecidableEq D] [Ord D] [Std.LawfulEqOrd D] [Std.TransOrd D]
    (toData : {a : Type} → F a → D) (f0 : {a : Type} → F a → a) (mk : {a : Type} → D → a → F a)
    (eta : {a : Type} → (x : F a) → mk (toData x) (f0 x) = x)
    (toData_mk : {a : Type} → (d : D) → (x0 : a) → toData (mk d x0) = d)
    (f0_mk : {a : Type} → (d : D) → (x0 : a) → f0 (mk d x0) = x0 := by intros; rfl)
    (hsz : {a : Type} → [SizeOf a] → (x : F a) →
      ALaCarte.FunctorSizeOf.sizeOf x = SizeOf.sizeOf (f0 x) := by intros; rfl) :
    SubBytesFunctor F :=
  SubBytesFunctor.ofDataExplicit D inferInstance inferInstance inferInstance inferInstance 1
    toData
    (fun x => #v[f0 x])
    (fun d as => mk d as[0])
    eta
    (fun d as => toData_mk d as[0])
    (fun d as => by
      obtain ⟨⟨l⟩, hl⟩ := as
      match l, hl with
      | [x0], _ => simp [f0_mk])
    (fun x => by rw [hsz]; simp +arith)

/-- Builds a `SubBytesFunctor` for a 3-child functor `F` whose non-recursive metadata `D` inherits
its `Ord` laws along an injective encoding `code : D → C`. -/
@[expose, instance_reducible] public def SubBytesFunctor.ternaryByCode {F : Type → Type}
    [sz : ALaCarte.FunctorSizeOf F]
    {D C : Type} [DecidableEq D] [Ord C] [Std.LawfulEqOrd C] [Std.TransOrd C]
    (code : D → C) (code_inj : ∀ {x y : D}, code x = code y → x = y)
    (toData : {a : Type} → F a → D) (f0 f1 f2 : {a : Type} → F a → a)
    (mk : {a : Type} → D → a → a → a → F a)
    (eta : {a : Type} → (x : F a) → mk (toData x) (f0 x) (f1 x) (f2 x) = x := by intros; rfl)
    (toData_mk : {a : Type} → (d : D) → (x0 x1 x2 : a) → toData (mk d x0 x1 x2) = d := by
      intros; rfl)
    (f0_mk : {a : Type} → (d : D) → (x0 x1 x2 : a) → f0 (mk d x0 x1 x2) = x0 := by intros; rfl)
    (f1_mk : {a : Type} → (d : D) → (x0 x1 x2 : a) → f1 (mk d x0 x1 x2) = x1 := by intros; rfl)
    (f2_mk : {a : Type} → (d : D) → (x0 x1 x2 : a) → f2 (mk d x0 x1 x2) = x2 := by intros; rfl)
    (hsz : {a : Type} → [SizeOf a] → (x : F a) →
      ALaCarte.FunctorSizeOf.sizeOf x =
        SizeOf.sizeOf (f0 x) + SizeOf.sizeOf (f1 x) + SizeOf.sizeOf (f2 x) := by intros; rfl) :
    SubBytesFunctor F :=
  letI ordD : Ord D := { compare x y := Ord.compare (code x) (code y) }
  letI reflD : Std.ReflOrd D := {
    compare_self := fun {x} => Std.ReflOrd.compare_self (a := code x)
  }
  letI lawfulD : Std.LawfulEqOrd D := {
    eq_of_compare := fun h => code_inj (Std.LawfulEqOrd.eq_of_compare h)
  }
  letI orientD : Std.OrientedOrd D := {
    eq_swap := fun {x y} => Std.OrientedOrd.eq_swap (a := code x) (b := code y)
  }
  letI transD : Std.TransOrd D := {
    isLE_trans := fun h1 h2 =>
      Std.TransOrd.isLE_trans (a := code _) (b := code _) (c := code _) h1 h2
  }
  SubBytesFunctor.ofDataExplicit D inferInstance ordD lawfulD transD 3
    toData
    (fun x => #v[f0 x, f1 x, f2 x])
    (fun d as => mk d as[0] as[1] as[2])
    eta
    (fun d as => toData_mk d as[0] as[1] as[2])
    (fun d as => by
      obtain ⟨⟨l⟩, hl⟩ := as
      match l, hl with
      | [x0, x1, x2], _ => simp [f0_mk, f1_mk, f2_mk])
    (fun x => by rw [hsz]; simp +arith)

end DY
