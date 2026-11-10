/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Misc.Fixpoint
import all DY.Misc.Fixpoint

public section

namespace Symbolic.DYBridge

theorem DY.Fixpoint.mkLeastFixpoint_eq_1 :
    ∀ {α : Type _} (f : DY.Fixpoint.Set α → DY.Fixpoint.Set α) (x : α),
      DY.Fixpoint.mkLeastFixpoint f x =
        (∀ (s : DY.Fixpoint.Set α), (∀ (y : α), f s y → s y) → s x) :=
  @_root_.DY.Fixpoint.mkLeastFixpoint.eq_1

end Symbolic.DYBridge

end
