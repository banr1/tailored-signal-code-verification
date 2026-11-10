/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# `sep_frame` Synthetic Benchmarks

Synthetic scaling benchmarks comparing manual frame witnesses (`*_hand`) against automatic
frame inference (`*_auto` via `sep_frame`, `sep_frame_apply`, and
`SepWP.call_subroutine_frame_auto`) across three families:
- `callN_*`: framed subroutine calls carving a callee stack frame from a larger caller stack;
- `stepN_*`: framed straight-line `SepWP` segments inside `SepWP.seq`;
- `ghostN_*`: chained ghost-cell entailments (`p ↦₆₄ v ∗ v ↦₆₄ w`) with decoy cells.
-/

@[expose] public section

namespace Testing.SepFrameBench

open Arm64 ProofLib

/-- Synthetic drop contract: consumes `dropPre box` and 32 bytes of stack, returns the box region. -/
def dropSpec (size : Nat) (dropPre : BitVec 64 → SepProp) : Spec (BitVec 64) where
  pre := fun box s => ⌜s.readReg64 .x0 = box⌝ ∗ dropPre box ∗ stackAt s.sp 32
  post := fun box s0 _ => memRegion box size ∗ stackAt s0.sp 32

/-- The 1008-byte caller stack seen as its unused bottom and the callee's 32 bytes. -/
theorem stackAt_1008_split32 (sp : BitVec 64) :
    stackAt sp 1008 = memRegion (sp - 1008#64) 976 ∗ stackAt sp 32 :=
  stackAt_split_bottom sp 32 976 (by decide)

/-! ## Framed call, 4 frame atoms -/

theorem call4_hand
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ dropPre box ∗ stackAt sp 1008)
      post := by
  rw [stackAt_1008_split32 sp]
  refine SepWP.call_subroutine_frame hcall (x := box)
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗ memRegion (sp - 1008#64) 976)
    hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [dropSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hm
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

theorem call4_auto
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ dropPre box ∗ stackAt sp 1008)
      post := by
  refine SepWP.call_subroutine_frame_auto hcall (x := box) hpc hrun halign hlr ?_ ?_ ?_
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

/-! ## Framed call, 8 frame atoms -/

theorem call8_hand
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ dropPre box ∗ stackAt sp 1008)
      post := by
  rw [stackAt_1008_split32 sp]
  refine SepWP.call_subroutine_frame hcall (x := box)
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
          ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
          ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp - 1008#64) 976)
    hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [dropSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hm
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

theorem call8_auto
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ dropPre box ∗ stackAt sp 1008)
      post := by
  refine SepWP.call_subroutine_frame_auto hcall (x := box) hpc hrun halign hlr ?_ ?_ ?_
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

/-! ## Framed call, 16 frame atoms -/

theorem call16_hand
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗ dropPre box ∗ stackAt sp 1008)
      post := by
  rw [stackAt_1008_split32 sp]
  refine SepWP.call_subroutine_frame hcall (x := box)
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
          ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
          ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
          ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
          ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗ memRegion (sp - 1008#64) 976)
    hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [dropSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hm
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

theorem call16_auto
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗ dropPre box ∗ stackAt sp 1008)
      post := by
  refine SepWP.call_subroutine_frame_auto hcall (x := box) hpc hrun halign hlr ?_ ?_ ?_
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

/-! ## Framed call, 32 frame atoms -/

theorem call32_hand
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
       ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2400#64) 40 ∗
       ((sp + 864#64) ↦₆₄ 18#64) ∗ ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2592#64) 40 ∗ ((sp + 888#64) ↦₆₄ 21#64) ∗
       ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2784#64) 40 ∗
       ((sp + 912#64) ↦₆₄ 24#64) ∗ ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2976#64) 40 ∗ ((sp + 936#64) ↦₆₄ 27#64) ∗
       ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 3168#64) 40 ∗
       ((sp + 960#64) ↦₆₄ 30#64) ∗ ((futVt + 248#64) ↦₆₄ᵣ boxSize) ∗ dropPre box ∗
       stackAt sp 1008)
      post := by
  rw [stackAt_1008_split32 sp]
  refine SepWP.call_subroutine_frame hcall (x := box)
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
          ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
          ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
          ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
          ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
          ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2400#64) 40 ∗
          ((sp + 864#64) ↦₆₄ 18#64) ∗ ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2592#64) 40 ∗ ((sp + 888#64) ↦₆₄ 21#64) ∗
          ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2784#64) 40 ∗
          ((sp + 912#64) ↦₆₄ 24#64) ∗ ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2976#64) 40 ∗ ((sp + 936#64) ↦₆₄ 27#64) ∗
          ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 3168#64) 40 ∗
          ((sp + 960#64) ↦₆₄ 30#64) ∗ ((futVt + 248#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp - 1008#64) 976)
    hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [dropSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    exact Satisfies.congr_prop (by ac_rfl) hm
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

theorem call32_auto
    {prog : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    {size : Nat} {dropPre : BitVec 64 → SepProp}
    (hcall : subroutine_ok prog entry (dropSpec size dropPre))
    (s : State) (sp box futVt boxSize : BitVec 64)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hsp : s.sp = sp) (hx0 : s.readReg64 .x0 = box)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      ∀ F, SepWP prog target sf ((dropSpec size dropPre).post box s sf ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
       ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2400#64) 40 ∗
       ((sp + 864#64) ↦₆₄ 18#64) ∗ ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2592#64) 40 ∗ ((sp + 888#64) ↦₆₄ 21#64) ∗
       ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2784#64) 40 ∗
       ((sp + 912#64) ↦₆₄ 24#64) ∗ ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2976#64) 40 ∗ ((sp + 936#64) ↦₆₄ 27#64) ∗
       ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 3168#64) 40 ∗
       ((sp + 960#64) ↦₆₄ 30#64) ∗ ((futVt + 248#64) ↦₆₄ᵣ boxSize) ∗ dropPre box ∗
       stackAt sp 1008)
      post := by
  refine SepWP.call_subroutine_frame_auto hcall (x := box) hpc hrun halign hlr ?_ ?_ ?_
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4
    exact hk sf h1 h2 h3 h4 _

/-! ## Framed segment inside `SepWP.seq`, 4 frame atoms -/

theorem step4_hand
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
       ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  have hrearr :
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
         ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) =
      ((((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) ∗
        (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64))) := by
    ac_rfl
  rw [hrearr]
  refine SepWP.seq (SepWP.frame_post_entails
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64)) h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

theorem step4_auto
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
       ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  refine SepWP.seq (by sep_frame_apply SepWP.frame_post_entails h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

/-! ## Framed segment inside `SepWP.seq`, 8 frame atoms -/

theorem step8_hand
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗
       ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗ ((sp + 768#64) ↦₆₄ 6#64) ∗
       ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  have hrearr :
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
         ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1632#64) 40 ∗ ((sp + 768#64) ↦₆₄ 6#64) ∗
         ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) =
      ((((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) ∗
        (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
         ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
         ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize))) := by
    ac_rfl
  rw [hrearr]
  refine SepWP.seq (SepWP.frame_post_entails
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
          ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
          ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize)) h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

theorem step8_auto
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗
       ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗ ((sp + 768#64) ↦₆₄ 6#64) ∗
       ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  refine SepWP.seq (by sep_frame_apply SepWP.frame_post_entails h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

/-! ## Framed segment inside `SepWP.seq`, 16 frame atoms -/

theorem step16_hand
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
       ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
       ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  have hrearr :
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
         ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
         ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
         ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
         ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2016#64) 40 ∗ ((sp + 816#64) ↦₆₄ 12#64) ∗
         ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2208#64) 40 ∗
         ((sp + 840#64) ↦₆₄ 15#64) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) =
      ((((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) ∗
        (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
         ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
         ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
         ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
         ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64))) := by
    ac_rfl
  rw [hrearr]
  refine SepWP.seq (SepWP.frame_post_entails
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
          ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
          ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
          ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
          ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64)) h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

theorem step16_auto
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
       ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
       ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  refine SepWP.seq (by sep_frame_apply SepWP.frame_post_entails h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

/-! ## Framed segment inside `SepWP.seq`, 32 frame atoms -/

theorem step32_hand
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
       ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2400#64) 40 ∗ ((sp + 864#64) ↦₆₄ 18#64) ∗
       ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2592#64) 40 ∗
       ((sp + 888#64) ↦₆₄ 21#64) ∗ ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2784#64) 40 ∗ ((sp + 912#64) ↦₆₄ 24#64) ∗
       ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2976#64) 40 ∗
       ((sp + 936#64) ↦₆₄ 27#64) ∗ ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 3168#64) 40 ∗ ((sp + 960#64) ↦₆₄ 30#64) ∗
       ((futVt + 248#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  have hrearr :
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
         ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
         ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
         ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
         ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
         ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2400#64) 40 ∗ ((sp + 864#64) ↦₆₄ 18#64) ∗
         ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2592#64) 40 ∗
         ((sp + 888#64) ↦₆₄ 21#64) ∗ ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2784#64) 40 ∗ ((sp + 912#64) ↦₆₄ 24#64) ∗
         ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2976#64) 40 ∗
         ((sp + 936#64) ↦₆₄ 27#64) ∗ ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 3168#64) 40 ∗ ((sp + 960#64) ↦₆₄ 30#64) ∗
         ((futVt + 248#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) =
      ((((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign)) ∗
        (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
         ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
         ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
         ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
         ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
         ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2400#64) 40 ∗
         ((sp + 864#64) ↦₆₄ 18#64) ∗ ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2592#64) 40 ∗ ((sp + 888#64) ↦₆₄ 21#64) ∗
         ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2784#64) 40 ∗
         ((sp + 912#64) ↦₆₄ 24#64) ∗ ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗
         memRegion (sp + 2976#64) 40 ∗ ((sp + 936#64) ↦₆₄ 27#64) ∗
         ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 3168#64) 40 ∗
         ((sp + 960#64) ↦₆₄ 30#64) ∗ ((futVt + 248#64) ↦₆₄ᵣ boxSize))) := by
    ac_rfl
  rw [hrearr]
  refine SepWP.seq (SepWP.frame_post_entails
    (F := ((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1440#64) 40 ∗ ((sp + 744#64) ↦₆₄ 3#64) ∗
          ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
          ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 1824#64) 40 ∗ ((sp + 792#64) ↦₆₄ 9#64) ∗
          ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
          ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
          ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2400#64) 40 ∗
          ((sp + 864#64) ↦₆₄ 18#64) ∗ ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2592#64) 40 ∗ ((sp + 888#64) ↦₆₄ 21#64) ∗
          ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2784#64) 40 ∗
          ((sp + 912#64) ↦₆₄ 24#64) ∗ ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗
          memRegion (sp + 2976#64) 40 ∗ ((sp + 936#64) ↦₆₄ 27#64) ∗
          ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 3168#64) 40 ∗
          ((sp + 960#64) ↦₆₄ 30#64) ∗ ((futVt + 248#64) ↦₆₄ᵣ boxSize)) h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

theorem step32_auto
    {prog : Program} {mid target : BitVec 64} {post : State → SepProp → Prop}
    {Q : State → Prop} {P' : SepProp} (s : State) (sp futVt boxSize boxAlign : BitVec 64)
    (h : SepWP prog mid s (((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      (fun sf Pf => (Pf ⊢ P') ∧ Q sf))
    (hk : ∀ s1, s1.pc = mid → s1.status = .Running → Q s1 → ∀ F,
      SepWP prog target s1 (P' ∗ F) post) :
    SepWP prog target s
      (((sp + 720#64) ↦₆₄ 0#64) ∗ ((futVt + 8#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1440#64) 40 ∗
       ((sp + 744#64) ↦₆₄ 3#64) ∗ ((futVt + 32#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1632#64) 40 ∗
       ((sp + 768#64) ↦₆₄ 6#64) ∗ ((futVt + 56#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 1824#64) 40 ∗
       ((sp + 792#64) ↦₆₄ 9#64) ∗ ((futVt + 80#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2016#64) 40 ∗
       ((sp + 816#64) ↦₆₄ 12#64) ∗ ((futVt + 104#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2208#64) 40 ∗ ((sp + 840#64) ↦₆₄ 15#64) ∗
       ((futVt + 4096#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 128#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2400#64) 40 ∗ ((sp + 864#64) ↦₆₄ 18#64) ∗
       ((futVt + 152#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2592#64) 40 ∗
       ((sp + 888#64) ↦₆₄ 21#64) ∗ ((futVt + 176#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 2784#64) 40 ∗ ((sp + 912#64) ↦₆₄ 24#64) ∗
       ((futVt + 200#64) ↦₆₄ᵣ boxSize) ∗ memRegion (sp + 2976#64) 40 ∗
       ((sp + 936#64) ↦₆₄ 27#64) ∗ ((futVt + 224#64) ↦₆₄ᵣ boxSize) ∗
       memRegion (sp + 3168#64) 40 ∗ ((sp + 960#64) ↦₆₄ 30#64) ∗
       ((futVt + 248#64) ↦₆₄ᵣ boxSize) ∗ ((futVt + 4104#64) ↦₆₄ᵣ boxAlign))
      post := by
  refine SepWP.seq (by sep_frame_apply SepWP.frame_post_entails h) ?_
  intro s1 P1 h1 h2 ⟨hent, hq⟩
  exact SepWP.weaken_pre hent (hk s1 h1 h2 hq _)

/-! ## Chained ghost cells, 4 decoys -/

theorem ghost4_hand
    (m : Memory) (a0 a1 a2 a3 a4 w : BitVec 64)
    (h : m ⊨ (a0 ↦₆₄ a1) ∗ (a1 ↦₆₄ a2) ∗ (a2 ↦₆₄ a3) ∗ (a3 ↦₆₄ a4) ∗ (a4 ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F := by
  exact ⟨a3, a4, _, by sep_entail⟩

theorem ghost4_auto
    (m : Memory) (a0 a1 a2 a3 a4 w : BitVec 64)
    (h : m ⊨ (a0 ↦₆₄ a1) ∗ (a1 ↦₆₄ a2) ∗ (a2 ↦₆₄ a3) ∗ (a3 ↦₆₄ a4) ∗ (a4 ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F := by
  exact ⟨_, _, _, by sep_frame⟩

/-! ## Chained ghost cells, 8 decoys -/

theorem ghost8_hand
    (m : Memory) (a0 a1 a2 a3 a4 a5 a6 a7 a8 w : BitVec 64)
    (h : m ⊨ (a0 ↦₆₄ a1) ∗ (a1 ↦₆₄ a2) ∗ (a2 ↦₆₄ a3) ∗ (a3 ↦₆₄ a4) ∗ (a4 ↦₆₄ a5) ∗ (a5 ↦₆₄ a6) ∗
      (a6 ↦₆₄ a7) ∗ (a7 ↦₆₄ a8) ∗ (a8 ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F := by
  exact ⟨a7, a8, _, by sep_entail⟩

theorem ghost8_auto
    (m : Memory) (a0 a1 a2 a3 a4 a5 a6 a7 a8 w : BitVec 64)
    (h : m ⊨ (a0 ↦₆₄ a1) ∗ (a1 ↦₆₄ a2) ∗ (a2 ↦₆₄ a3) ∗ (a3 ↦₆₄ a4) ∗ (a4 ↦₆₄ a5) ∗ (a5 ↦₆₄ a6) ∗
      (a6 ↦₆₄ a7) ∗ (a7 ↦₆₄ a8) ∗ (a8 ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F := by
  exact ⟨_, _, _, by sep_frame⟩

/-! ## Chained ghost cells, 16 decoys -/

theorem ghost16_hand
    (m : Memory) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 w : BitVec 64)
    (h : m ⊨ (a0 ↦₆₄ a1) ∗ (a1 ↦₆₄ a2) ∗ (a2 ↦₆₄ a3) ∗ (a3 ↦₆₄ a4) ∗ (a4 ↦₆₄ a5) ∗ (a5 ↦₆₄ a6) ∗
      (a6 ↦₆₄ a7) ∗ (a7 ↦₆₄ a8) ∗ (a8 ↦₆₄ a9) ∗ (a9 ↦₆₄ a10) ∗ (a10 ↦₆₄ a11) ∗ (a11 ↦₆₄ a12) ∗
      (a12 ↦₆₄ a13) ∗ (a13 ↦₆₄ a14) ∗ (a14 ↦₆₄ a15) ∗ (a15 ↦₆₄ a16) ∗ (a16 ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F := by
  exact ⟨a15, a16, _, by sep_entail⟩

theorem ghost16_auto
    (m : Memory) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 w : BitVec 64)
    (h : m ⊨ (a0 ↦₆₄ a1) ∗ (a1 ↦₆₄ a2) ∗ (a2 ↦₆₄ a3) ∗ (a3 ↦₆₄ a4) ∗ (a4 ↦₆₄ a5) ∗ (a5 ↦₆₄ a6) ∗
      (a6 ↦₆₄ a7) ∗ (a7 ↦₆₄ a8) ∗ (a8 ↦₆₄ a9) ∗ (a9 ↦₆₄ a10) ∗ (a10 ↦₆₄ a11) ∗ (a11 ↦₆₄ a12) ∗
      (a12 ↦₆₄ a13) ∗ (a13 ↦₆₄ a14) ∗ (a14 ↦₆₄ a15) ∗ (a15 ↦₆₄ a16) ∗ (a16 ↦₆₄ w)) :
    ∃ p v F, m ⊨ (p ↦₆₄ v) ∗ (v ↦₆₄ w) ∗ F := by
  exact ⟨_, _, _, by sep_frame⟩

end Testing.SepFrameBench

#print axioms Testing.SepFrameBench.call4_hand
#print axioms Testing.SepFrameBench.call4_auto
#print axioms Testing.SepFrameBench.step4_hand
#print axioms Testing.SepFrameBench.step4_auto
#print axioms Testing.SepFrameBench.call8_hand
#print axioms Testing.SepFrameBench.call8_auto
#print axioms Testing.SepFrameBench.step8_hand
#print axioms Testing.SepFrameBench.step8_auto
#print axioms Testing.SepFrameBench.call16_hand
#print axioms Testing.SepFrameBench.call16_auto
#print axioms Testing.SepFrameBench.step16_hand
#print axioms Testing.SepFrameBench.step16_auto
#print axioms Testing.SepFrameBench.call32_hand
#print axioms Testing.SepFrameBench.call32_auto
#print axioms Testing.SepFrameBench.step32_hand
#print axioms Testing.SepFrameBench.step32_auto
#print axioms Testing.SepFrameBench.ghost4_hand
#print axioms Testing.SepFrameBench.ghost4_auto
#print axioms Testing.SepFrameBench.ghost8_hand
#print axioms Testing.SepFrameBench.ghost8_auto
#print axioms Testing.SepFrameBench.ghost16_hand
#print axioms Testing.SepFrameBench.ghost16_auto
