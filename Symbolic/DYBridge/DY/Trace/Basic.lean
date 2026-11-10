/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Trace.Basic
import all DY.Trace.Basic

public section

namespace Symbolic.DYBridge

theorem DY.Trace.length_eq_1 :
    ∀ {α : Type},
      (DY.Trace.nil : DY.Trace α).length = 0 :=
  @_root_.DY.Trace.length.eq_1

theorem DY.Trace.length_eq_2 :
    ∀ {α : Type} (trBefore : DY.Trace α) (a : α),
      (trBefore.snoc a).length = trBefore.length + 1 :=
  @_root_.DY.Trace.length.eq_2

theorem DY.Trace.append_eq_1 :
    ∀ {EntryT α : Type} [DY.TraceEntryHas EntryT α] (tr : DY.Trace α) (entry : EntryT),
      tr.append entry = tr.snoc (DY.TraceEntryHas.inj entry) :=
  @_root_.DY.Trace.append.eq_1

theorem DY.Trace.prefix_eq_1 :
    ∀ {α : Type} (i : Nat),
      (DY.Trace.nil : DY.Trace α).prefix i = if (DY.Trace.nil : DY.Trace α).length ≤ i then (DY.Trace.nil : DY.Trace α) else (DY.Trace.nil : DY.Trace α) :=
  @_root_.DY.Trace.prefix.eq_1

theorem DY.Trace.prefix_eq_2 :
    ∀ {α : Type} (i : Nat) (trBefore : DY.Trace α) (a : α),
      (trBefore.snoc a).prefix i = if (trBefore.snoc a).length ≤ i then trBefore.snoc a else trBefore.prefix i :=
  @_root_.DY.Trace.prefix.eq_2

theorem DY.Trace.at_snoc_lt_aux {α : Type} {trBefore : DY.Trace α} {entry : α} {i : Nat}
    (h : i < (trBefore.snoc entry).length) (hne : ¬ i = trBefore.length) :
    i < trBefore.length := by
  rw [_root_.DY.Trace.length.eq_2] at h
  omega

theorem DY.Trace.at_eq_2 {α : Type} (i : Nat) (trBefore : DY.Trace α) (entry : α)
    (h_i : i < (trBefore.snoc entry).length) :
    (trBefore.snoc entry).at i h_i =
      if h : i = trBefore.length then entry
      else trBefore.at i (DY.Trace.at_snoc_lt_aux h_i h) :=
  @_root_.DY.Trace.at.eq_2 α i trBefore entry h_i

theorem DY.Trace.nil_length_not_lt {α : Type} (i : Nat) :
    ¬ i < (DY.Trace.nil : DY.Trace α).length := by
  rw [_root_.DY.Trace.length.eq_1]
  omega

end Symbolic.DYBridge

end
