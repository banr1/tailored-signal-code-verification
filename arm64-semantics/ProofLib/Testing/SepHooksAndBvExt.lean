/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib

/-!
# Separation-Logic Hooks, Region Splits, and Bitvector Extension Tests

Regression tests and negative `#guard_msgs` checks for `SepWP.reaches_of_sepWP`,
memory region and cell splitting/disjointness lemmas, `fieldHook`/`fieldHook64` and stack-frame
combinators, sign/zero-extension and bit-0 arithmetic lemmas, and `Obj.hasWords_patchCalls_slice`.
-/

@[expose] public section

namespace Examples.Testing.SepHooksAndBvExtTest

open Arm64 Arm64.CType ProofLib

/-! ## `SepWP.reaches_of_sepWP` -/

example {prog : Program} {t : BitVec 64} {s : State} {P R : SepProp}
    {post : State → Prop}
    (h : SepWP prog t s P (fun sf _ => post sf))
    (hm : s.mem ⊨ P ∗ R) :
    reaches_pc prog t s post :=
  SepWP.reaches_of_sepWP h hm

/-- error: Application type mismatch: The argument
  h
has type
  SepWP prog t s P (fun sf x => post sf) fun x => emp
but is expected to have type
  SepWP prog t s P fun sf x => post sf
in the application
  SepWP.reaches_of_sepWP h

Note: The following definitions were not unfolded because their definition is not exposed:
  SepProp.pure ↦ 2
  emp ↦ 1 -/
#guard_msgs in
example {prog : Program} {t : BitVec 64} {s : State} {P R : SepProp}
    {post : State → Prop}
    (h : SepWP prog t s P (fun sf _ => post sf) (fun _ => emp))
    (hm : s.mem ⊨ P ∗ R) :
    reaches_pc prog t s post :=
  SepWP.reaches_of_sepWP h hm

/-! ## Region and Cell Splitting -/

example (b : BitVec 64) :
    memRegion (b + BitVec.ofNat 64 16) 8 ∗ (memRegion b 16 ∗ memRegion (b + BitVec.ofNat 64 24) 8) =
      memRegion b 32 :=
  memRegion_merge3 b 32 16 8 (by decide) (by decide)

example (a : BitVec 64) :
    memRegion a 32 =
      memRegion a 8 ∗ memRegion (a + BitVec.ofNat 64 8) 16 ∗ memRegion (a + BitVec.ofNat 64 24) 8 :=
  memRegion_split3_ord a 32 8 16 (by decide) (by decide)

example (a : BitVec 64) (v : BitVec 8) :
    ((a ↦₈ v) ∗ memRegion (a + 1#64) 7) ⊢ memRegion a 8 :=
  memRegion_byte_merge a v 7 (by decide)

example (a lo hi : BitVec 64) :
    ((a ↦₆₄ lo) ∗ ((a + 8#64) ↦₆₄ hi)) = (a ↦₁₂₈ (hi ++ lo)) :=
  pointsTo64_pair a lo hi

example (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) = ((a ↦₆₄ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ v.extractLsb' 64 64)) :=
  pointsTo128_split64 a v

example {a v p : BitVec 64} {bs : List (BitVec 8)}
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hn : 0 < bs.length) :
    ((a ↦₆₄ v) ∗ (p ↦ₛ bs)) ⊢
      ⌜a.toNat + 8 ≤ p.toNat ∨ p.toNat + bs.length ≤ a.toNat⌝ ∗ ((a ↦₆₄ v) ∗ (p ↦ₛ bs)) :=
  pointsTo64_outside_pointsToBytes ha hn

example {C P Q : SepProp} {χ : Prop} (h : χ → (C ∗ P ⊢ Q)) :
    (C ∗ (P ∗ ⌜χ⌝)) ⊢ Q :=
  entails_pure_in_frame h

example {prog : Program} {t : BitVec 64} {s : State} {b : BitVec 64} {v : BitVec 8}
    {post : State → SepProp → Prop}
    (h : SepWP prog t s (memRegion (b + 64#64) 1 ∗ memRegion b 32) post) :
    SepWP prog t s (memRegion b 32 ∗ ((b + 64#64) ↦₈ v)) post := by
  apply SepWP.region_split3 b 32 8 16 (by decide) (by decide)
  apply SepWP.region_merge3 b 32 8 16 (by decide) (by decide)
  apply SepWP.byte_merge (b + 64#64) v
  exact SepWP.weaken_left (Entails.refl _) h

/-- error: unsolved goals
a v p : BitVec 64
ha : a.toNat + 8 ≤ 2 ^ 64
⊢ 0 < [].length -/
#guard_msgs in
example {a v p : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64) :
    ((a ↦₆₄ v) ∗ (p ↦ₛ ([] : List (BitVec 8)))) ⊢
      ⌜a.toNat + 8 ≤ p.toNat ∨ p.toNat + ([] : List (BitVec 8)).length ≤ a.toNat⌝ ∗
        ((a ↦₆₄ v) ∗ (p ↦ₛ ([] : List (BitVec 8)))) :=
  pointsTo64_outside_pointsToBytes ha (by skip)

/-! ## Field and Stack Hook Combinators -/

structure WidgetModel where
  flags : BitVec 32
  cookie : BitVec 64

def widgetRep (p : BitVec 64) (m : WidgetModel) : SepProp :=
  ((p + 4#64) ↦₃₂ m.flags) ∗ ((p + 8#64) ↦₆₄ m.cookie)

@[reducible] def WidgetHandle : SemType WidgetModel where
  tyName := "struct widget *"
  interp := widgetRep

c_type_spec widgetFlagsSpec (w : ptr) (ghost m : WidgetModel) : u32 where
  c_arg w : ShrRef WidgetHandle m
  returns (m.flags >>> 1) &&& 1#32

c_type_spec widgetCookieSpec (w : ptr) (ghost m : WidgetModel) : u64 where
  c_arg w : ShrRef WidgetHandle m
  returns m.cookie

c_type_spec widgetQuery32Spec (ctx f : WidgetModel → BitVec 32)
    (w : ptr) (ghost m : WidgetModel) : u32 where
  c_arg w : ShrRef WidgetHandle m
  returns f m

example : HookOk (fieldHook 4#64 fun v => (v >>> 1) &&& 1#32) widgetFlagsSpec := by
  refine fieldHook_ok (rep := widgetRep) 4#64 _ (fun m => (m.flags >>> 1) &&& 1#32)
    fun {mem p m R} h => ?_
  unfold widgetRep at h
  rw [sepConj_assoc] at h
  rw [(IsBlock.pointsTo32 (p + 4#64) m.flags).read h]

example : HookOk (fieldHook 4#64 id) (widgetQuery32Spec WidgetModel.flags) := by
  refine fieldHook_ok (rep := widgetRep) 4#64 id WidgetModel.flags fun {mem p m R} h => ?_
  unfold widgetRep at h
  rw [sepConj_assoc] at h
  exact (IsBlock.pointsTo32 (p + 4#64) m.flags).read h

example : HookOk (fieldHook64 8#64 id) widgetCookieSpec := by
  refine fieldHook64_ok (rep := widgetRep) 8#64 id WidgetModel.cookie fun {mem p m R} h => ?_
  unfold widgetRep at h
  rw [sepConj_comm ((p + 4#64) ↦₃₂ m.flags), sepConj_assoc] at h
  exact (IsBlock.pointsTo64 (p + 8#64) m.cookie).read h

example (sp : BitVec 64) :
    stackAt sp (64 + 4096) =
      memRegion (sp - BitVec.ofNat 64 (64 + 4096)) 64 ∗ stackAt sp 4096 :=
  stackAt_split_hook sp 64

example (sp : BitVec 64) :
    (memRegion (sp - 112#64) 48 ∗ stackAt sp 64) ⊢ stackAt sp 112 :=
  stackAt_refold_bottom sp (sp - 112#64) 64 48 112

/--
error: could not synthesize default value for parameter 'hn' using tactics
---
error: Tactic `decide` proved that the proposition
  64 + 32 = 112
is false
-/
#guard_msgs in
example (sp : BitVec 64) :
    (memRegion (sp - 112#64) 32 ∗ stackAt sp 64) ⊢ stackAt sp 112 :=
  stackAt_refold_bottom sp (sp - 112#64) 64 32 112

/-! ## Bitvector Sign/Zero-Extension and Bit-0 Lemmas -/

example (v : BitVec 32) (h : v.getLsbD 31 = false) :
    BitVec.signExtend 64 v = BitVec.zeroExtend 64 v :=
  sext_eq_zext v h

example (v : BitVec 64) : (v.truncate 32).msb = v.getLsbD 31 :=
  msb_trunc32 v

example (v : BitVec 64) : (v.truncate 16).msb = v.getLsbD 15 :=
  msb_truncate v

example (v : BitVec 8) (h : v.toNat < 128) :
    BitVec.signExtend 64 v = BitVec.ofNat 64 v.toNat :=
  signExtend64_byte_of_lt v h

example (v : BitVec 8) (h : 128 ≤ v.toNat) :
    BitVec.signExtend 64 v = BitVec.ofNat 64 v.toNat - 256#64 :=
  signExtend64_byte_of_ge v h

example (v : BitVec 8) :
    (BitVec.signExtend 64 v).getLsbD 63 = decide (128 ≤ v.toNat) :=
  getLsbD_63_signExtend64_byte v

example (x : BitVec 32) (hx : x.toNat + 16 < 2 ^ 32) :
    (x + BitVec.ofNat 32 16).toNat = x.toNat + 16 :=
  BitVec.toNat_addOfNat rfl hx

example (x : BitVec 32) (hx : x.getLsbD 0 = false) :
    x ||| 1#32 = x + 1#32 :=
  or_one_eq_add_one_of_lsb_false hx

/-- Counterexample showing `x.getLsbD 0 = false` is essential in `or_one_eq_add_one_of_lsb_false`. -/
example : (3#8 ||| 1#8) ≠ (3#8 + 1#8) := by decide

/-- Counterexample showing `v.getLsbD 31 = false` is essential in `sext_eq_zext`. -/
example : BitVec.signExtend 64 (0x80000000#32) ≠ BitVec.zeroExtend 64 (0x80000000#32) := by decide

/-! ## `Obj.hasWords_patchCalls_slice` -/

private def sampleWords : List (BitVec 32) :=
  [0xd2800000#32, 0x94000000#32, 0xd65f03c0#32]

private def sampleCalls : List (Nat × String) :=
  [(4, "ext_fn")]

example {prog : Program} {a : BitVec 64} {resolve : String → BitVec 64}
    (h : prog.hasWords a (Obj.patchCalls sampleCalls sampleWords a resolve)) :
    prog.hasWords (a + BitVec.ofNat 64 (4 * 2)) ((sampleWords.drop 2).take 1) :=
  Obj.hasWords_patchCalls_slice 2 1 h (by decide) (by decide) (by decide)

/-- error: Tactic `decide` proved that the proposition
  ∀ (j : Nat), j < 2 → List.find? (fun x => x.fst == 4 * (0 + j)) sampleCalls = none
is false -/
#guard_msgs in
example {prog : Program} {a : BitVec 64} {resolve : String → BitVec 64}
    (h : prog.hasWords a (Obj.patchCalls sampleCalls sampleWords a resolve)) :
    prog.hasWords (a + BitVec.ofNat 64 (4 * 0)) ((sampleWords.drop 0).take 2) :=
  Obj.hasWords_patchCalls_slice 0 2 h (by decide) (by decide) (by decide)

end Examples.Testing.SepHooksAndBvExtTest
