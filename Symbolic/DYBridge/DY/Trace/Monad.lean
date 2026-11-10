/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Trace.Monad
import all DY.Trace.Monad

public section

namespace Symbolic.DYBridge

theorem DY.Traceful.run_eq_1 :
    ∀ {a : Type} [DY.ExecTraceTypes] (x : DY.Traceful a) (tr : DY.ExecTrace),
      x.run tr = x tr :=
  @_root_.DY.Traceful.run.eq_1

theorem DY.Traceful.mk_eq_1 :
    ∀ [DY.ExecTraceTypes] {α : Type}
      (f : (tr : DY.ExecTrace) → Option α × { trOut // tr ≤ trOut }),
      DY.Traceful.mk f = f :=
  @_root_.DY.Traceful.mk.eq_1

end Symbolic.DYBridge

end
