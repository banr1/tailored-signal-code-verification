/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public meta import ProofLib.Testing.Perf.Budget

/-!
# Performance Regression Tests for `wp_frame_split`

Tests `wp_frame_split` under `#perf_budget` on a 24-cell 64-bit frame for target offsets written
both as `BitVec.ofNat` literals (`sp + 96#64`) and as `OfNat` numerals (`sp + 96`). Covers
succeeding splits and failing splits (`frame_split: no match`); failing `OfNat`-offset splits carry
a wider heartbeat budget pending pre-match offset normalization.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.Perf.FrameSplit

open Arm64 _root_.ProofLib

/-! ## Successful splits -/

-- Last cell, `BitVec.ofNat` offset. Measured: ~0.5k heartbeats.
#perf_budget 2000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 184#64) ↦₆₄ v23) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

-- Last cell, `OfNat` offset. Measured: ~1.5k heartbeats.
#perf_budget 4000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 184) ↦₆₄ v23) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

-- Middle cell, `OfNat` offset. Measured: ~1.3k heartbeats.
#perf_budget 4000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 96) ↦₆₄ v12) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

/-! ## Failing splits: must fail fast with `frame_split: no match` -/

-- Address not in the frame, `BitVec.ofNat` offset. Measured: ~0.9k heartbeats.
/--
error: frame_split: no match for (sp + 100#64) ↦₆₄
-/
#guard_msgs (error, drop info, substring := true) in
#perf_budget 3000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 w : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 100#64) ↦₆₄ w) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

-- Right address, wrong value (near-miss), `BitVec.ofNat` offset. Measured: ~11k heartbeats.
/--
error: frame_split: no match for (sp + 184#64) ↦₆₄ w in precondition
-/
#guard_msgs (error, drop info, substring := true) in
#perf_budget 30000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 w : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 184#64) ↦₆₄ w) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

-- Address not in the frame, `OfNat` offset (known slow path). Measured: ~77k heartbeats.
/--
error: frame_split: no match for (sp + 100) ↦₆₄
-/
#guard_msgs (error, drop info, substring := true) in
#perf_budget 200000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 w : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 100) ↦₆₄ w) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

-- Right address, wrong value (near-miss), `OfNat` offset (known slow path). Measured: ~84k heartbeats.
/--
error: frame_split: no match for (sp + 96) ↦₆₄ w in precondition
-/
#guard_msgs (error, drop info, substring := true) in
#perf_budget 200000 in
example (m : Memory) (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 w : BitVec 64)
    (hpre : m ⊨
      (sp + 0#64) ↦₆₄ v0 ∗
      (sp + 8#64) ↦₆₄ v1 ∗
      (sp + 16#64) ↦₆₄ v2 ∗
      (sp + 24#64) ↦₆₄ v3 ∗
      (sp + 32#64) ↦₆₄ v4 ∗
      (sp + 40#64) ↦₆₄ v5 ∗
      (sp + 48#64) ↦₆₄ v6 ∗
      (sp + 56#64) ↦₆₄ v7 ∗
      (sp + 64#64) ↦₆₄ v8 ∗
      (sp + 72#64) ↦₆₄ v9 ∗
      (sp + 80#64) ↦₆₄ v10 ∗
      (sp + 88#64) ↦₆₄ v11 ∗
      (sp + 96#64) ↦₆₄ v12 ∗
      (sp + 104#64) ↦₆₄ v13 ∗
      (sp + 112#64) ↦₆₄ v14 ∗
      (sp + 120#64) ↦₆₄ v15 ∗
      (sp + 128#64) ↦₆₄ v16 ∗
      (sp + 136#64) ↦₆₄ v17 ∗
      (sp + 144#64) ↦₆₄ v18 ∗
      (sp + 152#64) ↦₆₄ v19 ∗
      (sp + 160#64) ↦₆₄ v20 ∗
      (sp + 168#64) ↦₆₄ v21 ∗
      (sp + 176#64) ↦₆₄ v22 ∗
      (sp + 184#64) ↦₆₄ v23) :
    ∃ F, m ⊨ ((sp + 96) ↦₆₄ w) ∗ F := by
  exact ⟨_, by wp_frame_split⟩

end Examples.Testing.ProofLib.Perf.FrameSplit
