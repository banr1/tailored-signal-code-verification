/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.ALaCarte.Basic
import all DY.ALaCarte.Basic

public section

namespace Symbolic.DYBridge

theorem DY.ALaCarte.Container.PartialFun.combine_eq_1 :
    ∀ {t : Type} [DecidableEq t] {functors : t → Type → Type}
      [(id : t) → DY.ALaCarte.FunctorSizeOf (functors id)] {g : Type → Type} [DY.ALaCarte.FunctorSizeOf g]
      [DY.ALaCarte.Representable g] {a : Type}
      (funs : (id : t) → DY.ALaCarte.Container.PartialFun (functors id) g a) (id : t)
      (val : functors id (DY.ALaCarte.ContainerFor g))
      (rec_2 : (y : DY.ALaCarte.ContainerFor g) → sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf ({ id := id, val := val } : DY.ALaCarte.FunctorUnion functors (DY.ALaCarte.ContainerFor g)) → a),
      DY.ALaCarte.Container.PartialFun.combine funs ({ id := id, val := val } : DY.ALaCarte.FunctorUnion functors (DY.ALaCarte.ContainerFor g)) rec_2 = funs id val rec_2 :=
  @_root_.DY.ALaCarte.Container.PartialFun.combine.eq_1

theorem DY.ALaCarte.Container.view_pack_cross
    (f h : Type → Type) {g : Type → Type}
    [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf h] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.SubFunctorTC h g]
    [DY.ALaCarte.Representable g]
    (x : f (DY.ALaCarte.ContainerFor g)) :
    DY.ALaCarte.Container.view h (DY.ALaCarte.Container.pack f x) =
      DY.ALaCarte.SubFunctorTC.proj (f := h) (DY.ALaCarte.SubFunctorTC.inj (g := g) x) := by
  unfold _root_.DY.ALaCarte.Container.view _root_.DY.ALaCarte.Container.pack
  rw [_root_.DY.ALaCarte.Container.intoFunctor_fromFunctor, _root_.DY.ALaCarte.Representable.from_to]

theorem DY.ALaCarte.Container.PartialFun.combine_apply
    {t : Type} [DecidableEq t]
    {functors : t → Type → Type} [∀ id, DY.ALaCarte.FunctorSizeOf (functors id)]
    {g : Type → Type} [DY.ALaCarte.FunctorSizeOf g] [DY.ALaCarte.Representable g]
    {a : Type}
    (funs : (id : t) → DY.ALaCarte.Container.PartialFun (functors id) g a)
    (x : DY.ALaCarte.FunctorUnion functors (DY.ALaCarte.ContainerFor g))
    (rec : ∀ y : DY.ALaCarte.ContainerFor g, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → a) :
    DY.ALaCarte.Container.PartialFun.combine funs x rec = funs x.id x.val rec := by
  unfold _root_.DY.ALaCarte.Container.PartialFun.combine
  rfl

end Symbolic.DYBridge

end
