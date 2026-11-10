/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# State-Indexed Frame Transport Tests

Tests automatic post-call frame transport in `wp_call` / `wpp_call`, standalone
`wp_frame_transport` on write spines and non-trailing state arguments, and `wp_rel_close` on
chained preservation relations.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpCallTransport

open Arm64 _root_.ProofLib

/-- State fields a `WidgetPool` footprint may depend on. -/
abbrev WidgetKeep (s s' : State) : Prop := s'.brk = s.brk ∧ s'.tpidrEl0 = s.tpidrEl0

/-- A state-indexed allocator handle: its footprint depends only on `WidgetKeep` fields. -/
structure WidgetPool where
  pool : State → SepProp
  pool_transport : ∀ s s' : State, WidgetKeep s s' → pool s' = pool s

attribute [frame_transport] WidgetPool.pool_transport

/-- A callee at `entry + 0x100` that owns `p`, keeps the `WidgetKeep` fields. -/
abbrev keepSpec (p : BitVec 64) :=
  Spec.split (fun (_ : Unit) _ => True) (fun _ => p ↦₆₄ 0#64)
    (fun _ s0 sf => WidgetKeep s0 sf) (fun _ => p ↦₆₄ 1#64)

/-- A callee that only keeps `brk` (too weak for `WidgetPool.pool_transport`). -/
abbrev brkOnlySpec (p : BitVec 64) :=
  Spec.split (fun (_ : Unit) _ => True) (fun _ => p ↦₆₄ 0#64)
    (fun _ s0 sf => sf.brk = s0.brk) (fun _ => p ↦₆₄ 1#64)

/-! ## Basic Frame Transport -/

set_option maxHeartbeats 100000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State) (W : WidgetPool) (p : BitVec 64)
    (h_pc : s.pc = entry + 0x100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + 0x100#64) (keepSpec p)) :
    SepWP prog ret_pc s (W.pool s ∗ (p ↦₆₄ 0#64))
      (fun sf Q => Q = ((p ↦₆₄ 1#64) ∗ W.pool sf)) := by
  wp_call h_callee ()
  fail_if_success wp_frame_transport
  exact SepWP.done (by assumption) (by assumption) rfl

set_option maxHeartbeats 100000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State) (W : WidgetPool) (p : BitVec 64)
    (h_pc : s.pc = entry + 0x100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + 0x100#64) (keepSpec p)) :
    SepWPp prog ret_pc s (W.pool s ∗ (p ↦₆₄ 0#64))
      (fun sf Q => Q = ((p ↦₆₄ 1#64) ∗ W.pool sf)) (fun _ _ => False) := by
  wpp_call h_callee ()
  fail_if_success wp_frame_transport
  exact SepWPp.done (by assumption) (by assumption) rfl

example (prog : Program) (ret_pc v : BitVec 64) (s sf : State) (W : WidgetPool) (p : BitVec 64)
    (h_brk : sf.brk = s.brk) (h_tp : s.tpidrEl0 = sf.tpidrEl0)
    (h : SepWP prog ret_pc (sf.writeReg64 .x0 v)
      ((p ↦₆₄ 1#64) ∗ W.pool (sf.writeReg64 .x0 v)) (fun _ _ => True)) :
    SepWP prog ret_pc (sf.writeReg64 .x0 v) ((p ↦₆₄ 1#64) ∗ W.pool s) (fun _ _ => True) := by
  wp_frame_transport
  exact h

example (prog : Program) (ret_pc v : BitVec 64) (sf1 sf2 : State) (W : WidgetPool)
    (p : BitVec 64) (h : WidgetKeep ((sf1.writeReg64 .x0 v).setPC ret_pc) sf2)
    (hk : SepWP prog ret_pc sf2 ((p ↦₆₄ 1#64) ∗ W.pool sf2) (fun _ _ => True)) :
    SepWP prog ret_pc sf2 ((p ↦₆₄ 1#64) ∗ W.pool sf1) (fun _ _ => True) := by
  wp_frame_transport
  exact hk

set_option maxHeartbeats 100000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State) (W : WidgetPool) (p : BitVec 64)
    (h_pc : s.pc = entry + 0x100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + 0x100#64) (keepSpec p)) :
    SepWP prog ret_pc s (W.pool s ∗ (p ↦₆₄ 0#64))
      (fun sf Q => Q = ((p ↦₆₄ 1#64) ∗ W.pool sf)) := by
  set_option proofLib.wpCallFrameTransport false in
  wp_call h_callee ()
  fail_if_success exact SepWP.done (by assumption) (by assumption) rfl
  wp_frame_transport
  exact SepWP.done (by assumption) (by assumption) rfl

/--
error: wp_frame_transport: no state-indexed atom could be moved to the current state (no matching `@[frame_transport]` lemma, or `wp_frame_transport_discharge` failed on its side condition)
-/
#guard_msgs in
example (prog : Program) (ret_pc : BitVec 64) (s sf : State) (W : WidgetPool) (p : BitVec 64) :
    SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ W.pool s) (fun _ _ => True) := by
  wp_frame_transport

/--
error: wp_frame_transport: no state-indexed atom could be moved to the current state (no matching `@[frame_transport]` lemma, or `wp_frame_transport_discharge` failed on its side condition)
-/
#guard_msgs in
set_option maxHeartbeats 100000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State) (W : WidgetPool) (p : BitVec 64)
    (h_pc : s.pc = entry + 0x100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + 0x100#64) (brkOnlySpec p)) :
    SepWP prog ret_pc s (W.pool s ∗ (p ↦₆₄ 0#64))
      (fun sf Q => Q = ((p ↦₆₄ 1#64) ∗ W.pool sf)) := by
  wp_call h_callee ()
  wp_frame_transport

/-! ## Non-Trailing State Arguments -/

/-- A user frame predicate with the state in the middle of its arguments. -/
def widgetFrame (W : WidgetPool) (s : State) (q : BitVec 64) : SepProp :=
  W.pool s ∗ (q ↦₆₄ 7#64)

theorem widgetFrame_transport (W : WidgetPool) (q : BitVec 64) (s s' : State)
    (h : WidgetKeep s s') : widgetFrame W s' q = widgetFrame W s q := by
  simp only [widgetFrame, W.pool_transport s s' h]

attribute [frame_transport] widgetFrame_transport

example (prog : Program) (ret_pc : BitVec 64) (s sf : State) (W : WidgetPool) (p q : BitVec 64)
    (h_keep : WidgetKeep s sf)
    (h : SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ widgetFrame W sf q) (fun _ _ => True)) :
    SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ widgetFrame W s q) (fun _ _ => True) := by
  wp_frame_transport
  exact h

set_option maxHeartbeats 100000 in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State) (W : WidgetPool) (p q : BitVec 64)
    (h_pc : s.pc = entry + 0x100#64) (h_run : s.status = .Running)
    (h_sp : s.spAligned = true) (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog (entry + 0x100#64) (keepSpec p)) :
    SepWP prog ret_pc s (widgetFrame W s q ∗ (p ↦₆₄ 0#64))
      (fun sf Q => Q = ((p ↦₆₄ 1#64) ∗ widgetFrame W sf q)) := by
  wp_call h_callee ()
  fail_if_success wp_frame_transport
  exact SepWP.done (by assumption) (by assumption) rfl

def widgetTwo (W : WidgetPool) (s t : State) : SepProp := W.pool s ∗ W.pool t

theorem widgetTwo_transport (W : WidgetPool) (s s' t t' : State)
    (h : WidgetKeep s s') (h' : WidgetKeep t t') : widgetTwo W s' t' = widgetTwo W s t := by
  simp only [widgetTwo, W.pool_transport s s' h, W.pool_transport t t' h']

attribute [frame_transport] widgetTwo_transport

/--
error: wp_frame_transport: no state-indexed atom could be moved to the current state (no matching `@[frame_transport]` lemma, or `wp_frame_transport_discharge` failed on its side condition)
-/
#guard_msgs in
example (prog : Program) (ret_pc : BitVec 64) (s sf : State) (W : WidgetPool) (p : BitVec 64)
    (h_keep : WidgetKeep s sf) :
    SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ widgetTwo W s s) (fun _ _ => True) := by
  wp_frame_transport

/--
error: wp_frame_transport: no state-indexed atom could be moved to the current state (no matching `@[frame_transport]` lemma, or `wp_frame_transport_discharge` failed on its side condition)
-/
#guard_msgs in
example (prog : Program) (ret_pc : BitVec 64) (s sf : State) (W : WidgetPool) (p q : BitVec 64)
    (h_brk : sf.brk = s.brk) :
    SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ widgetFrame W s q) (fun _ _ => True) := by
  wp_frame_transport

/-! ## Chained Relations -/

example (s0 s1 s2 sf : State) (v : BitVec 64)
    (h1 : WidgetKeep s0 s1) (h2 : WidgetKeep ((s1.writeReg64 .x0 v).setPC 4#64) s2)
    (h3 : WidgetKeep (s2.writeReg64 .x1 v) sf) :
    WidgetKeep s0 sf := by
  wp_rel_close

example (prog : Program) (ret_pc v : BitVec 64) (s0 s1 sf : State) (W : WidgetPool) (p : BitVec 64)
    (h1 : WidgetKeep s0 s1) (h2 : WidgetKeep (s1.writeReg64 .x0 v) sf)
    (h : SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ W.pool sf) (fun _ _ => True)) :
    SepWP prog ret_pc sf ((p ↦₆₄ 1#64) ∗ W.pool s0) (fun _ _ => True) := by
  wp_frame_transport
  exact h

/--
error: wp_rel_close: could not close the goal from the hypotheses of the same relation
-/
#guard_msgs in
example (s0 s1 s2 sf : State) (h1 : WidgetKeep s0 s1) (h3 : WidgetKeep s2 sf) :
    WidgetKeep s0 sf := by
  wp_rel_close

end Examples.Testing.ProofLib.WpCallTransport
