/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Bytes.Basic
public import Symbolic.DYBridge.DY.ALaCarte.Basic
import all DY.Bytes.Basic

public section

namespace Symbolic.DYBridge

theorem DY.Bytes.length_eq_1 :
    ∀ [DY.BytesFunctor] [DY.BytesLength] (b : DY.Bytes),
      b.length = DY.Bytes.rec DY.BytesLength.funs b :=
  @_root_.DY.Bytes.length.eq_1

unseal DY.Bytes in
theorem DY.Bytes.view?_pack_cross
    [DY.BytesFunctor]
    {F1 : Type → Type} (F2 : Type → Type)
    [DY.SubBytesFunctor F1] [DY.SubBytesFunctor F2]
    [DY.BytesFunctor.Has F1] [DY.BytesFunctor.Has F2]
    (b : DY.BytesView F1) :
    (DY.BytesView.pack (SubF := F1) b).view? F2 =
      DY.ALaCarte.SubFunctorTC.proj (f := F2)
        (DY.ALaCarte.SubFunctorTC.inj (f := F1) (g := DY.BytesF) b) := by
  unfold _root_.DY.Bytes.view? _root_.DY.BytesView.pack
  exact Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross F1 F2 b

theorem DY.BytesView.view?_pack_eq_none
    [DY.BytesFunctor]
    {F1 : Type → Type} (F2 : Type → Type)
    [DY.SubBytesFunctor F1] [DY.SubBytesFunctor F2]
    [DY.BytesFunctor.Has F1] [DY.BytesFunctor.Has F2]
    (x : DY.BytesView F1)
    (h : DY.ALaCarte.SubFunctorTC.proj (f := F2)
      (DY.ALaCarte.SubFunctorTC.inj (f := F1) (g := DY.BytesF) x) = none := by rfl) :
    (DY.BytesView.pack (SubF := F1) x).view? F2 = none :=
  (Symbolic.DYBridge.DY.Bytes.view?_pack_cross F2 x).trans h

theorem DY.BytesView.pack_ne_pack_of_proj_none
    [DY.BytesFunctor]
    {F1 F2 : Type → Type}
    [DY.SubBytesFunctor F1] [DY.SubBytesFunctor F2]
    [DY.BytesFunctor.Has F1] [DY.BytesFunctor.Has F2]
    {x : DY.BytesView F1} {y : DY.BytesView F2}
    (heq : DY.BytesView.pack (SubF := F1) x = DY.BytesView.pack (SubF := F2) y)
    (h : DY.ALaCarte.SubFunctorTC.proj (f := F2)
      (DY.ALaCarte.SubFunctorTC.inj (f := F1) (g := DY.BytesF) x) = none := by rfl) :
    False := by
  have hv := congrArg (fun b : _root_.DY.Bytes => b.view? F2) heq
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none F2 x h, _root_.DY.BytesView.view_pack] at hv
  cases hv

theorem DY.BytesView.pack_inj
    [DY.BytesFunctor]
    {SubF : Type → Type} [DY.SubBytesFunctor SubF] [DY.BytesFunctor.Has SubF]
    {x y : DY.BytesView SubF} :
    DY.BytesView.pack x = DY.BytesView.pack y ↔ x = y := by
  constructor
  · intro h
    have hv := congrArg (fun b : _root_.DY.Bytes => b.view? SubF) h
    rw [_root_.DY.BytesView.view_pack, _root_.DY.BytesView.view_pack, Option.some.injEq] at hv
    exact hv
  · exact congrArg _root_.DY.BytesView.pack

unseal DY.Bytes in
theorem DY.Bytes.PartialFunction.combine_eq
    [DY.BytesFunctor]
    {t : Type} [DecidableEq t] [Ord t] [Std.LawfulEqOrd t] [Std.TransOrd t]
    {SubFs : t → Type → Type} [∀ id, DY.SubBytesFunctor (SubFs id)]
    {a : Type}
    (funs : (id : t) → DY.Bytes.PartialFunction (SubFs id) a) :
    DY.Bytes.PartialFunction.combine funs = fun x rec => funs x.id x.val rec := by
  funext x rec
  unfold _root_.DY.Bytes.PartialFunction.combine
  exact Symbolic.DYBridge.DY.ALaCarte.Container.PartialFun.combine_apply _ x @rec

unseal DY.Bytes in
theorem DY.BytesView.pack_eq_container_pack
    [DY.BytesFunctor] {SubF : Type → Type} [DY.SubBytesFunctor SubF] [DY.BytesFunctor.Has SubF]
    (x : DY.BytesView SubF) :
    DY.BytesView.pack (SubF := SubF) x = DY.ALaCarte.Container.pack SubF x := by
  unfold _root_.DY.BytesView.pack
  rfl

end Symbolic.DYBridge

end
