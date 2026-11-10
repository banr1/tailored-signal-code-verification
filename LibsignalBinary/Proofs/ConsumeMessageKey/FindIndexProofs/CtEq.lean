/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Specifications.LibsignalSession
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Keys.KeysCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.FindReceiverChainIndex

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSession
open CryptoGames.LibsignalSession

/-- Contract for `subtle::black_box::<u8>` (`0x47fa8`): preserves memory and trace while masking
`x0` to its low byte. -/
def blackBoxSpec : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜sf.readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧ sf.trace = s0.trace⌝

theorem blackBoxHook_sat {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook) :
    HookSat H "subtle::black_box::<u8>" blackBoxSpec := by
  refine ⟨blackBoxHook, h_bb, ?_⟩
  unfold blackBoxHook
  refine retHook_ok fun v R s0 hrun hpre _ => ?_
  dsimp [blackBoxSpec] at hpre ⊢
  rw [satisfies_pure_sepConj] at hpre ⊢
  obtain ⟨hx0, hm⟩ := hpre
  refine ⟨Memory.KeepsFrozen.refl _, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨⟨?_, rfl⟩, hm⟩⟩
  simp [hx0]

theorem black_box_ok (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook) :
    let prog := libsignalSessionCode.rebase b H
    let entry := prog.fnAddr "<[u8] as subtle::ConstantTimeEq>::ct_eq"
    subroutine_ok prog (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) blackBoxSpec := by
  intro prog entry
  exact hook_ok_at_raw (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
    (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) (stub := num% (ls_off% "subtle::black_box::<u8>")) (by decide) (by decide)
    (ls_hook% "subtle::black_box::<u8>") (blackBoxHook_sat h_bb)

/-- Unfolded 32-byte slice as 32 `↦₈` atoms. -/
def pointsToBytes32 (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₈ bs.getD 0 0#8) ∗ ((a + 1#64) ↦₈ bs.getD 1 0#8) ∗
  ((a + 2#64) ↦₈ bs.getD 2 0#8) ∗ ((a + 3#64) ↦₈ bs.getD 3 0#8) ∗
  ((a + 4#64) ↦₈ bs.getD 4 0#8) ∗ ((a + 5#64) ↦₈ bs.getD 5 0#8) ∗
  ((a + 6#64) ↦₈ bs.getD 6 0#8) ∗ ((a + 7#64) ↦₈ bs.getD 7 0#8) ∗
  ((a + 8#64) ↦₈ bs.getD 8 0#8) ∗ ((a + 9#64) ↦₈ bs.getD 9 0#8) ∗
  ((a + 10#64) ↦₈ bs.getD 10 0#8) ∗ ((a + 11#64) ↦₈ bs.getD 11 0#8) ∗
  ((a + 12#64) ↦₈ bs.getD 12 0#8) ∗ ((a + 13#64) ↦₈ bs.getD 13 0#8) ∗
  ((a + 14#64) ↦₈ bs.getD 14 0#8) ∗ ((a + 15#64) ↦₈ bs.getD 15 0#8) ∗
  ((a + 16#64) ↦₈ bs.getD 16 0#8) ∗ ((a + 17#64) ↦₈ bs.getD 17 0#8) ∗
  ((a + 18#64) ↦₈ bs.getD 18 0#8) ∗ ((a + 19#64) ↦₈ bs.getD 19 0#8) ∗
  ((a + 20#64) ↦₈ bs.getD 20 0#8) ∗ ((a + 21#64) ↦₈ bs.getD 21 0#8) ∗
  ((a + 22#64) ↦₈ bs.getD 22 0#8) ∗ ((a + 23#64) ↦₈ bs.getD 23 0#8) ∗
  ((a + 24#64) ↦₈ bs.getD 24 0#8) ∗ ((a + 25#64) ↦₈ bs.getD 25 0#8) ∗
  ((a + 26#64) ↦₈ bs.getD 26 0#8) ∗ ((a + 27#64) ↦₈ bs.getD 27 0#8) ∗
  ((a + 28#64) ↦₈ bs.getD 28 0#8) ∗ ((a + 29#64) ↦₈ bs.getD 29 0#8) ∗
  ((a + 30#64) ↦₈ bs.getD 30 0#8) ∗ ((a + 31#64) ↦₈ bs.getD 31 0#8)

noncomputable def ctEqSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (p1, k1, p2, k2) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    pointsToBytes32 p1 k1 ∗ pointsToBytes32 p2 k2 ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" s.sp
  post := fun (p1, k1, p2, k2) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    pointsToBytes32 p1 k1 ∗ pointsToBytes32 p2 k2 ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" s0.sp

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?

@[local simp, wp_norm, arm64_norm]
theorem byte_bne_zext32 (a b : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 b) = (a != b) := by
  by_cases h : a = b
  · subst h; rw [bne_self_eq_false, bne_self_eq_false]
  · have h32 : BitVec.setWidth 32 a ≠ BitVec.setWidth 32 b := by
      intro heq
      apply h
      apply BitVec.eq_of_toNat_eq
      have hnat := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_setWidth] at hnat
      have ha := a.isLt
      have hb := b.isLt
      omega
    rw [bne_iff_ne.mpr h, bne_iff_ne.mpr h32]

@[local simp, wp_norm, arm64_norm]
theorem ite_bne_byte_0_1 (a b : BitVec 8) :
    (if (a != b) = true then 0#64 else 1#64) = if (a == b) = true then 1#64 else 0#64 := by
  cases h : a == b <;> simp [bne, h]

@[local simp, wp_norm, arm64_norm]
theorem setWidth32_ite_1_0 (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem setWidth8_ite_1_0 (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem setWidth64_ite_1_0_32 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem setWidth64_ite_1_0_8 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem and64_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem and64_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 1#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem and64_mask32_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem and32_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, wp_norm, arm64_norm]
theorem and32_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

theorem externAt?_black_box (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook) :
    let prog := libsignalSessionCode.rebase b H
    let entry := prog.fnAddr "<[u8] as subtle::ConstantTimeEq>::ct_eq"
    prog.externAt? (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) = some blackBoxHook := by
  intro prog entry
  rw [Program.externAt?_fnAddr_add (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
    (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) (stub := num% (ls_off% "subtle::black_box::<u8>")) (by decide) (by decide),
    (ls_hook% "subtle::black_box::<u8>"), h_bb]

theorem reaches_pc_extern {prog : Program} {target_pc : BitVec 64} {s : State}
    {f : State → State} {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_ext : prog.externAt? s.pc = some f)
    (h_keep : s.mem.KeepsFrozen (f s).mem)
    (h_next : reaches_pc prog target_pc (f s) post oom)
    (h_symtab : (f s).symtab = s.symtab := by rfl) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  have hs := Step.extern h_run h_ext h_keep h_symtab
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

theorem step_blackBox {prog : Program} {target_pc entry_bb : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    (hext : prog.externAt? entry_bb = some blackBoxHook)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hs' : (s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  refine reaches_pc_extern hrun (hpc ▸ hext) (Memory.KeepsFrozen.refl _) ?_ rfl
  change reaches_pc prog target_pc
    ((s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr)) _ _
  rw [hs']
  have hmem : s'.mem = s.mem := by rw [← hs']; rfl
  exact hnext R (hmem ▸ hm)

macro "wp_black_box" hext:ident : tactic =>
  `(tactic| (
    apply step_blackBox $hext
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
  ))

theorem pointsToBytes_drop_step (a : BitVec 64) (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length) :
    ((a + BitVec.ofNat 64 i) ↦ₛ bs.drop i) =
      ((a + BitVec.ofNat 64 i) ↦₈ bs.getD i 0#8) ∗
      ((a + BitVec.ofNat 64 (i + 1)) ↦ₛ bs.drop (i + 1)) := by
  have hdrop : bs.drop i = bs.getD i 0#8 :: bs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
    simp [List.getD, List.getElem?_eq_getElem hi]
  have hadd : a + BitVec.ofNat 64 i + 1#64 = a + BitVec.ofNat 64 (i + 1) := by bv_omega
  rw [hdrop, pointsToBytes_cons, hadd]

theorem pointsToBytes_eq_pointsToBytes32 (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    (a ↦ₛ bs) = pointsToBytes32 a bs := by
  have h0 : (a ↦ₛ bs) = ((a + BitVec.ofNat 64 0) ↦ₛ bs.drop 0) := by simp
  rw [h0]
  iterate 32 (rw [pointsToBytes_drop_step a bs _ (by omega)])
  have h32 : bs.drop 32 = [] := by simp [h]
  rw [h32, pointsToBytes_nil, sepConj_emp]
  unfold pointsToBytes32
  simp only [BitVec.add_zero]

theorem list_eq_of_length_32_iff {k1 k2 : List (BitVec 8)} (h1 : k1.length = 32) (h2 : k2.length = 32) :
    ((List.range 32).all (fun i => k1.getD i 0#8 == k2.getD i 0#8) = true) ↔ k1 = k2 := by
  rw [List.all_eq_true]
  constructor
  · intro hall
    apply List.ext_getElem (by omega)
    intro i hi1 hi2
    have hi : i ∈ List.range 32 := List.mem_range.mpr (by omega)
    have heq := beq_iff_eq.mp (hall i hi)
    simpa [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] using heq
  · intro heq i _
    subst heq
    exact beq_self_eq_true _

theorem ct_eq_bool_32 {k1 k2 : List (BitVec 8)} (h1 : k1.length = 32) (h2 : k2.length = 32) :
    (if (k1.getD 0 0#8 == k2.getD 0 0#8 &&
        (k1.getD 1 0#8 == k2.getD 1 0#8 &&
        (k1.getD 2 0#8 == k2.getD 2 0#8 &&
        (k1.getD 3 0#8 == k2.getD 3 0#8 &&
        (k1.getD 4 0#8 == k2.getD 4 0#8 &&
        (k1.getD 5 0#8 == k2.getD 5 0#8 &&
        (k1.getD 6 0#8 == k2.getD 6 0#8 &&
        (k1.getD 7 0#8 == k2.getD 7 0#8 &&
        (k1.getD 8 0#8 == k2.getD 8 0#8 &&
        (k1.getD 9 0#8 == k2.getD 9 0#8 &&
        (k1.getD 10 0#8 == k2.getD 10 0#8 &&
        (k1.getD 11 0#8 == k2.getD 11 0#8 &&
        (k1.getD 12 0#8 == k2.getD 12 0#8 &&
        (k1.getD 13 0#8 == k2.getD 13 0#8 &&
        (k1.getD 14 0#8 == k2.getD 14 0#8 &&
        (k1.getD 15 0#8 == k2.getD 15 0#8 &&
        (k1.getD 16 0#8 == k2.getD 16 0#8 &&
        (k1.getD 17 0#8 == k2.getD 17 0#8 &&
        (k1.getD 18 0#8 == k2.getD 18 0#8 &&
        (k1.getD 19 0#8 == k2.getD 19 0#8 &&
        (k1.getD 20 0#8 == k2.getD 20 0#8 &&
        (k1.getD 21 0#8 == k2.getD 21 0#8 &&
        (k1.getD 22 0#8 == k2.getD 22 0#8 &&
        (k1.getD 23 0#8 == k2.getD 23 0#8 &&
        (k1.getD 24 0#8 == k2.getD 24 0#8 &&
        (k1.getD 25 0#8 == k2.getD 25 0#8 &&
        (k1.getD 26 0#8 == k2.getD 26 0#8 &&
        (k1.getD 27 0#8 == k2.getD 27 0#8 &&
        (k1.getD 28 0#8 == k2.getD 28 0#8 &&
        (k1.getD 29 0#8 == k2.getD 29 0#8 &&
        (k1.getD 30 0#8 == k2.getD 30 0#8 &&
        (k1.getD 31 0#8 == k2.getD 31 0#8)))))))))))))))))))))))))))))))) = true then 1#64 else 0#64) =
      (if k1 = k2 then 1#64 else 0#64) := by
  have hall :
      ((List.range 32).all (fun i => k1.getD i 0#8 == k2.getD i 0#8)) =
      (k1.getD 0 0#8 == k2.getD 0 0#8 &&
        (k1.getD 1 0#8 == k2.getD 1 0#8 &&
        (k1.getD 2 0#8 == k2.getD 2 0#8 &&
        (k1.getD 3 0#8 == k2.getD 3 0#8 &&
        (k1.getD 4 0#8 == k2.getD 4 0#8 &&
        (k1.getD 5 0#8 == k2.getD 5 0#8 &&
        (k1.getD 6 0#8 == k2.getD 6 0#8 &&
        (k1.getD 7 0#8 == k2.getD 7 0#8 &&
        (k1.getD 8 0#8 == k2.getD 8 0#8 &&
        (k1.getD 9 0#8 == k2.getD 9 0#8 &&
        (k1.getD 10 0#8 == k2.getD 10 0#8 &&
        (k1.getD 11 0#8 == k2.getD 11 0#8 &&
        (k1.getD 12 0#8 == k2.getD 12 0#8 &&
        (k1.getD 13 0#8 == k2.getD 13 0#8 &&
        (k1.getD 14 0#8 == k2.getD 14 0#8 &&
        (k1.getD 15 0#8 == k2.getD 15 0#8 &&
        (k1.getD 16 0#8 == k2.getD 16 0#8 &&
        (k1.getD 17 0#8 == k2.getD 17 0#8 &&
        (k1.getD 18 0#8 == k2.getD 18 0#8 &&
        (k1.getD 19 0#8 == k2.getD 19 0#8 &&
        (k1.getD 20 0#8 == k2.getD 20 0#8 &&
        (k1.getD 21 0#8 == k2.getD 21 0#8 &&
        (k1.getD 22 0#8 == k2.getD 22 0#8 &&
        (k1.getD 23 0#8 == k2.getD 23 0#8 &&
        (k1.getD 24 0#8 == k2.getD 24 0#8 &&
        (k1.getD 25 0#8 == k2.getD 25 0#8 &&
        (k1.getD 26 0#8 == k2.getD 26 0#8 &&
        (k1.getD 27 0#8 == k2.getD 27 0#8 &&
        (k1.getD 28 0#8 == k2.getD 28 0#8 &&
        (k1.getD 29 0#8 == k2.getD 29 0#8 &&
        (k1.getD 30 0#8 == k2.getD 30 0#8 &&
        (k1.getD 31 0#8 == k2.getD 31 0#8)))))))))))))))))))))))))))))))) := by
    simp only [List.range, List.range.loop, List.all_cons, List.all_nil, Bool.and_true]
  rw [← hall]
  by_cases heq : k1 = k2
  · have ht : ((List.range 32).all (fun i => k1.getD i 0#8 == k2.getD i 0#8) = true) :=
      (list_eq_of_length_32_iff h1 h2).mpr heq
    rw [ite_eq_left_iff.mpr (fun h => absurd ht h), ite_eq_left_iff.mpr (fun h => absurd heq h)]
  · have hf : ¬((List.range 32).all (fun i => k1.getD i 0#8 == k2.getD i 0#8) = true) := by
      intro ht
      exact heq ((list_eq_of_length_32_iff h1 h2).mp ht)
    rw [ite_eq_right_iff.mpr (fun ht => absurd ht hf), ite_eq_right_iff.mpr (fun h => absurd h heq)]

attribute [local simp, wp_norm, arm64_norm] Bool.and_assoc

noncomputable def ctEqSliceSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp

theorem ct_eq_ok (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<[u8] as subtle::ConstantTimeEq>::ct_eq")
      ctEqSliceSpec := by
  simp only [ctEqSliceSpec]
  have hext := externAt?_black_box b h_bb
  dsimp only at hext
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq") (num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) 840
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32
  simp only [sepConj_assoc]
  iterate 33 (wp_steps; wp_black_box hext)
  rw [ct_eq_bool_32 h_4 h]
  wp_done

/-! ## `<PublicKey as PartialEq>::eq` (`0x3ebf0`) -/

@[local simp, wp_norm, arm64_norm]
theorem publicKey_bytes_toList_length (pk : PublicKey) : pk.bytes.toList.length = 32 :=
  pk.bytes.2

@[local simp, wp_norm, arm64_norm]
theorem and64_mask255_ite_1_0 (p : Prop) [Decidable p] :
    ((if p then 1#64 else 0#64) &&& 4294967551#64) = if p then 1#64 else 0#64 := by
  by_cases hp : p <;> simp [hp]

@[local simp, wp_norm, arm64_norm]
theorem csinc_eq_zero32_ite_1_0 (p : Prop) [Decidable p] :
    (if (BitVec.setWidth 32 (if p then 1#64 else 0#64) == 0#32) = true then 0#64 else 1#64) =
      if p then 1#64 else 0#64 := by
  by_cases hp : p <;> simp [hp]

theorem publicKey_toList_eq_iff (pk1 pk2 : PublicKey) :
    pk1.bytes.toList = pk2.bytes.toList ↔ (pk1 == pk2) = true := by
  rw [beq_iff_eq]
  cases pk1 with | mk b1 =>
  cases pk2 with | mk b2 =>
  cases b1 with | mk l1 h1 =>
  cases b2 with | mk l2 h2 =>
  simp only [List.Vector.toList]
  constructor
  · intro h; subst h; rfl
  · intro h; injection h with h'; injection h'

theorem publicKey_ite_toList_eq (pk1 pk2 : PublicKey) :
    (if pk1.bytes.toList = pk2.bytes.toList then 1#64 else 0#64) =
      if pk1 == pk2 then 1#64 else 0#64 := by
  by_cases h : (pk1 == pk2) = true
  · have hlist := (publicKey_toList_eq_iff pk1 pk2).mpr h
    simp [h, hlist]
  · have hlist : ¬(pk1.bytes.toList = pk2.bytes.toList) := by
      intro hl
      exact h ((publicKey_toList_eq_iff pk1 pk2).mp hl)
    simp [h, hlist]

noncomputable def publicKeyEqSpec : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64)
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64)

theorem publicKey_eq_ok (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
      publicKeyEqSpec := by
  simp only [publicKeyEqSpec]
  have hct := ct_eq_ok b h_bb
  rw [Program.fnAddr_rel (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq") (k := 212) rfl] at hct
  simp only [ctEqSliceSpec] at hct
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")) 28
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h
  wp_steps
  wp_apply
  rw [publicKey_ite_toList_eq] at *
  wp_steps
  wp_done

/-! ## Stacked 32-Bit `subtle::black_box::<u8>` (`extHookStack = 16384`) -/

abbrev extHookStack32 : Nat := 16384

/-- 32-bit stacked `subtle::black_box::<u8>` contract (`SignalSession.CliExt.blackBoxSpec`):
requires `stackAt s.sp 16384` and constrains `(sf.readReg64 .x0).setWidth 32`. -/
def blackBoxSpec32 : Spec (BitVec 64) where
  pre := fun v s =>
    ⌜s.readReg64 .x0 = v⌝ ∗ stackAt s.sp extHookStack32
  post := fun v s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = (v.setWidth 8).zeroExtend 32 ∧
      sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack32

attribute [local irreducible] Program.fnOff

theorem black_box_ok_ext32 (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<[u8] as subtle::ConstantTimeEq>::ct_eq" +
        bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq"))
      blackBoxSpec32 :=
  hook_ok_at_raw (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
    (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq"))
    (stub := num% (ls_off% "subtle::black_box::<u8>")) (by decide) (by decide)
    (ls_hook% "subtle::black_box::<u8>") h_bb

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth8_ite_prop_1_0_ext32 (P : Prop) [Decidable P] :
    BitVec.setWidth 8 (if P then 1#64 else 0#64) = if P then 1#8 else 0#8 := by
  split <;> rfl

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth8_ite_1_0_32_ext32 (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#32 else 0#32) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth8_zext64_32_ext32 (x : BitVec 32) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth8_setWidth32_ext32 (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth8_and64_ext32 (x y : BitVec 64) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth8_and32_ext32 (x y : BitVec 32) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
theorem ite_one_zero_and_8_ext32 (b1 b2 : Bool) :
    ((if b1 = true then 1#8 else 0#8) &&& (if b2 = true then 1#8 else 0#8)) =
      if (b1 && b2) = true then 1#8 else 0#8 := by
  cases b1 <;> cases b2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
theorem setWidth32_and_4294967297_ext32 (x : BitVec 64) :
    BitVec.setWidth 32 (x &&& 4294967297#64) =
      BitVec.zeroExtend 32 (BitVec.setWidth 8 x &&& 1#8) := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem ite_one_zero_and_one_8_ext32 (b : Bool) :
    ((if b = true then 1#8 else 0#8) &&& 1#8) =
      if b = true then 1#8 else 0#8 := by
  cases b <;> rfl

@[local simp, local wp_norm, local arm64_norm]
theorem zeroExtend32_ite_one_zero_8_ext32 (b : Bool) :
    BitVec.zeroExtend 32 (if b = true then 1#8 else 0#8) =
      if b = true then 1#32 else 0#32 := by
  cases b <;> rfl

@[local simp, local wp_norm, local arm64_norm]
theorem zeroExtend32_ite_prop_1_0_8_ext32 (P : Prop) [Decidable P] :
    BitVec.zeroExtend 32 (if P then 1#8 else 0#8) =
      if P then 1#32 else 0#32 := by
  split <;> rfl

theorem ct_eq_bool_32_u8_ext32 {k1 k2 : List (BitVec 8)} (h1 : k1.length = 32) (h2 : k2.length = 32) :
    (if (k1.getD 0 0#8 == k2.getD 0 0#8 &&
        (k1.getD 1 0#8 == k2.getD 1 0#8 &&
        (k1.getD 2 0#8 == k2.getD 2 0#8 &&
        (k1.getD 3 0#8 == k2.getD 3 0#8 &&
        (k1.getD 4 0#8 == k2.getD 4 0#8 &&
        (k1.getD 5 0#8 == k2.getD 5 0#8 &&
        (k1.getD 6 0#8 == k2.getD 6 0#8 &&
        (k1.getD 7 0#8 == k2.getD 7 0#8 &&
        (k1.getD 8 0#8 == k2.getD 8 0#8 &&
        (k1.getD 9 0#8 == k2.getD 9 0#8 &&
        (k1.getD 10 0#8 == k2.getD 10 0#8 &&
        (k1.getD 11 0#8 == k2.getD 11 0#8 &&
        (k1.getD 12 0#8 == k2.getD 12 0#8 &&
        (k1.getD 13 0#8 == k2.getD 13 0#8 &&
        (k1.getD 14 0#8 == k2.getD 14 0#8 &&
        (k1.getD 15 0#8 == k2.getD 15 0#8 &&
        (k1.getD 16 0#8 == k2.getD 16 0#8 &&
        (k1.getD 17 0#8 == k2.getD 17 0#8 &&
        (k1.getD 18 0#8 == k2.getD 18 0#8 &&
        (k1.getD 19 0#8 == k2.getD 19 0#8 &&
        (k1.getD 20 0#8 == k2.getD 20 0#8 &&
        (k1.getD 21 0#8 == k2.getD 21 0#8 &&
        (k1.getD 22 0#8 == k2.getD 22 0#8 &&
        (k1.getD 23 0#8 == k2.getD 23 0#8 &&
        (k1.getD 24 0#8 == k2.getD 24 0#8 &&
        (k1.getD 25 0#8 == k2.getD 25 0#8 &&
        (k1.getD 26 0#8 == k2.getD 26 0#8 &&
        (k1.getD 27 0#8 == k2.getD 27 0#8 &&
        (k1.getD 28 0#8 == k2.getD 28 0#8 &&
        (k1.getD 29 0#8 == k2.getD 29 0#8 &&
        (k1.getD 30 0#8 == k2.getD 30 0#8 &&
        (k1.getD 31 0#8 == k2.getD 31 0#8)))))))))))))))))))))))))))))))) = true then 1#8 else 0#8) =
      (if k1 = k2 then 1#8 else 0#8) := by
  have h64 := ct_eq_bool_32 h1 h2
  have h8 := congrArg (BitVec.setWidth 8) h64
  simpa only [setWidth8_ite_1_0, setWidth8_ite_prop_1_0_ext32] using h8

@[local simp, local wp_norm, local arm64_norm]
theorem fnFrameBytes_ctEqName_ext32 :
    fnFrameBytes libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" = 48 :=
  ls_lemma% frameBytes "<[u8] as subtle::ConstantTimeEq>::ct_eq"

@[local simp, local wp_norm, local arm64_norm]
theorem fnFrameBytes_publicKeyEqName_ext32 :
    fnFrameBytes libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" = 16 :=
  ls_lemma% frameBytes "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"

theorem stackFrameFor_ctEq_eq_cells_ext32 (sp : BitVec 64) :
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp =
      cells (sp - BitVec.ofNat 64 48) 6 := by
  symm
  cells_unfold
  simp only [stackFrameFor, fnFrameBytes_ctEqName_ext32, reduceStackFrameAt]

theorem stackFrameFor_eq_eq_memRegion_ext32 (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor, fnFrameBytes_publicKeyEqName_ext32, reduceStackFrameAt]

theorem stackFrameFor_ctEq_eq_memRegion_ext32 (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor, fnFrameBytes_ctEqName_ext32, reduceStackFrameAt]

theorem ctEqFrame_entails_ext32 (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
     ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) ⊢
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [stackFrameFor_ctEq_eq_cells_ext32]
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  have h1 : (((sp - 8#64) ↦₆₄ v5) ∗ emp) ⊢ cells (sp - BitVec.ofNat 64 8) 1 :=
    cells_sub_succ_entails 8 1 (Entails.refl _)
  rwa [sepConj_emp] at h1

theorem ctEqFrame_sepConj_stackAt_ext32 (sp : BitVec 64) :
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
      stackAt (sp - 48#64) extHookStack32 =
    stackAt sp extHookStack32 ∗ memRegion (sp - 16432#64) 48 := by
  rw [stackFrameFor_ctEq_eq_cells_ext32, sepConj_comm]
  have h1 := (ProofLib.stackAt_split_cells sp extHookStack32 6 (by decide)).symm
  have h2 := ProofLib.stackAt_split_bottom sp extHookStack32 48 (by decide)
  have h3 : BitVec.ofNat 64 (extHookStack32 + 48) = 16432#64 := rfl
  rw [h3] at h2
  rw [h1, h2, sepConj_comm]

theorem ctEq_pre_rearrange_ext32 (S1 S2 C0 C1 C2 C3 C4 C5 Stk : SepProp) :
    S1 ∗ S2 ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ Stk =
      Stk ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ (S1 ∗ S2) := by
  ac_rfl

theorem sp_sub48_aligned_ext32 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_bits

private theorem low8_of_setWidth32_zext_ext32 {w v : BitVec 64}
    (h : w.setWidth 32 = (v.setWidth 8).zeroExtend 32) :
    w.setWidth 8 = v.setWidth 8 := by
  have h8 := congrArg (BitVec.setWidth 8) h
  revert h8; bv_bits

theorem step_blackBox_ext32
    {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s0 s : State} {sp_cur x19_v x20_v : BitVec 64}
    {x0_v x19_8_v x21_8_v x22_8_v : BitVec 8}
    {R_rest : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb blackBoxSpec32)
    (hal_cur : (sp_cur &&& 15#64 == 0#64) = true)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hlr : s.readReg64 (Reg.gpr 30#5) = ret_pc)
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x19_v)
    (hx19_8 : (s.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x20_v)
    (hx21_8 : (s.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v)
    (hx22_8 : (s.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = sp_cur)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp_cur →
      (sf.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v →
      sf.readReg64 (Reg.gpr 19#5) = x19_v →
      (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v →
      sf.readReg64 (Reg.gpr 20#5) = x20_v →
      (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v →
      (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v →
      sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) →
      sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) →
      sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) →
      sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) →
      sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) →
      sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sf.readReg64 (Reg.gpr 29#5) = sp_cur →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.trace = s0.trace →
      SepWP prog target_pc sf (stackAt sp_cur extHookStack32 ∗ R_rest) post) :
    SepWP prog target_pc s (stackAt sp_cur extHookStack32 ∗ R_rest) post := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0) (F := R_rest)
    hpc hrun hal hlr
    (fun R hm => by
      rw [sepConj_assoc] at hm
      simp only [blackBoxSpec32, hsp, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨trivial, hm⟩)
    (fun _ _ _ hpost => not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => not_satisfies_false_sepConj hpost)
    ?_
  intro sf hret_pc hret_run hsp_eq hcs
  have hcc : CallingConventionPreserved s sf := ⟨hsp_eq, hcs⟩
  simp only [blackBoxSpec32, hsp, sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_sf32, htr_sf⟩
  have hx0_sf : (sf.readReg64 .x0).setWidth 8 = (s.readReg64 .x0).setWidth 8 :=
    low8_of_setWidth32_zext_ext32 hx0_sf32
  have hsp_sf : sf.sp = sp_cur := hcc.1.trans hsp
  have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = x19_v := hcc.2.1.trans hx19
  have hx19_8_sf : (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v := by
    change (sf.readReg64 .x19).setWidth 8 = x19_8_v
    rw [hcc.2.1]; exact hx19_8
  have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = x20_v := hcc.2.2.1.trans hx20
  have hx21_8_sf : (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v := by
    change (sf.readReg64 .x21).setWidth 8 = x21_8_v
    rw [hcc.2.2.2.1]; exact hx21_8
  have hx22_8_sf : (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v := by
    change (sf.readReg64 .x22).setWidth 8 = x22_8_v
    rw [hcc.2.2.2.2.1]; exact hx22_8
  have hx23_sf : sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) := hcc.2.2.2.2.2.1.trans hx23
  have hx24_sf : sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) := hcc.2.2.2.2.2.2.1.trans hx24
  have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := hcc.2.2.2.2.2.2.2.1.trans hx25
  have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := hcc.2.2.2.2.2.2.2.2.1.trans hx26
  have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := hcc.2.2.2.2.2.2.2.2.2.1.trans hx27
  have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx28
  have hx29_sf : sf.readReg64 (Reg.gpr 29#5) = sp_cur := hcc.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
  exact hnext sf hret_pc hret_run hsp_sf
    (hx0_sf.trans hx0) hx19_sf hx19_8_sf hx20_sf hx21_8_sf hx22_8_sf
    hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf hvregs_sf
    (htr_sf.trans htr)

theorem step_blackBox_tail_ext32
    {prog : Program} {entry_bb : BitVec 64}
    {s0 s : State} {x0_v x0_target : BitVec 8}
    {v0 v1 v2 v3 v4 v5 : BitVec 64}
    {R_slices S1 S2 R0 : SepProp}
    (hbb : subroutine_ok prog entry_bb blackBoxSpec32)
    (hal_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hlr : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5))
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5))
    (hx21 : s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5))
    (hx22 : s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hx0_eq : x0_v = x0_target)
    (h_slices : R_slices = S1 ∗ S2) :
    SepWP prog (s0.readReg64 .lr) s
      (stackAt (s0.sp - 48#64) extHookStack32 ∗
        ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
        ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
        R_slices)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R0 →
          sf.mem ⊨
            (⌜(sf.readReg64 .x0).setWidth 32 = x0_target.zeroExtend 32 ∧ sf.trace = s0.trace⌝ ∗
              S1 ∗ S2 ∗
              stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" s0.sp ∗
              stackAt (s0.sp - 48#64) extHookStack32) ∗ R0) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0)
    (F := memRegion (s0.sp - 16432#64) 48 ∗ R_slices)
    hpc hrun hal hlr
    (fun R hm => by
      have hm1 : s.mem ⊨
          (stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" s0.sp ∗
            stackAt (s0.sp - 48#64) extHookStack32) ∗ (R_slices ∗ R) := by
        have hrearr :
            (stackAt (s0.sp - 48#64) extHookStack32 ∗
              ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
              ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
              R_slices) ∗ R =
            (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
              ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
            (stackAt (s0.sp - 48#64) extHookStack32 ∗ (R_slices ∗ R)) := by ac_rfl
        rw [hrearr] at hm
        have hm' := Satisfies.mono (sepConj_mono_left (ctEqFrame_entails_ext32 s0.sp v0 v1 v2 v3 v4 v5)) hm
        rwa [← sepConj_assoc] at hm'
      rw [ctEqFrame_sepConj_stackAt_ext32 s0.sp, sepConj_assoc] at hm1
      simp only [blackBoxSpec32, hsp, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨trivial, hm1⟩)
    (fun _ _ _ hpost => not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => not_satisfies_false_sepConj hpost)
    ?_
  intro sf hret_pc hret_run hsp_eq hcs
  have hcc : CallingConventionPreserved s sf := ⟨hsp_eq, hcs⟩
  simp only [blackBoxSpec32, hsp, sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_sf32, htr_sf⟩
  have hsp0 : sf.sp = s0.sp := hcc.1.trans hsp
  have hcs0 : CalleeSavedPreserved s0 sf :=
    ⟨hcc.2.1.trans hx19,
     hcc.2.2.1.trans hx20,
     hcc.2.2.2.1.trans hx21,
     hcc.2.2.2.2.1.trans hx22,
     hcc.2.2.2.2.2.1.trans hx23,
     hcc.2.2.2.2.2.2.1.trans hx24,
     hcc.2.2.2.2.2.2.2.1.trans hx25,
     hcc.2.2.2.2.2.2.2.2.1.trans hx26,
     hcc.2.2.2.2.2.2.2.2.2.1.trans hx27,
     hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx28,
     hcc.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29,
     hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs⟩
  have hx0_32 : (sf.readReg64 .x0).setWidth 32 = x0_target.zeroExtend 32 := by
    rw [hx0_sf32]
    change ((s.readReg64 (Reg.gpr 0#5)).setWidth 8).zeroExtend 32 = x0_target.zeroExtend 32
    rw [hx0, hx0_eq]
  have htr0 : sf.trace = s0.trace := htr_sf.trans htr
  refine SepWP.done hret_pc hret_run ⟨?_, hsp0, hcs0⟩
  intro hm_post
  have hm_sf' : sf.mem ⊨
      (stackAt s0.sp extHookStack32 ∗ memRegion (s0.sp - 16432#64) 48) ∗ (R_slices ∗ R0) := by
    simpa only [sepConj_assoc] using hm_post
  rw [← ctEqFrame_sepConj_stackAt_ext32 s0.sp, sepConj_left_comm, sepConj_assoc, h_slices,
    sepConj_assoc] at hm_sf'
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hx0_32, htr0⟩, by simpa only [sepConj_assoc] using hm_sf'⟩

set_option hygiene false in
macro "wp_black_box_ext32 " hbb:ident hal:ident : tactic =>
  `(tactic| (
    refine step_blackBox_ext32 $hbb $hal
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    try clear hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb s_bb
    intro s_bb hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb
  ))

/-- `ctEqSliceSpec` extended with 16 KiB hook stack under `blackBoxSpec32`. -/
noncomputable def ctEqSliceSpecExt :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
    stackAt (sp - 48#64) extHookStack32
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = (if k1 = k2 then 1#32 else 0#32) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
    stackAt (sp - 48#64) extHookStack32

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem ct_eq_ok_ext32 (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<[u8] as subtle::ConstantTimeEq>::ct_eq")
      ctEqSliceSpecExt := by
  simp only [ctEqSliceSpecExt]
  have hbb := black_box_ok_ext32 b h_bb
  code_fetches libsignalSessionCode libsignalSessionBin b H
    (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
    (num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) 840
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  have hal_sub48 : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    sp_sub48_aligned_ext32 hsp_align
  have h_slices :
      pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) k1 ∗
        pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) k2 =
      ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ k1) ∗ ((s0.readReg64 (Reg.gpr 1#5)) ↦ₛ k2) := by
    rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
        pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  rw [ctEq_pre_rearrange_ext32]
  conv =>
    arg 4
    rw [← h_slices]
    unfold pointsToBytes32
    simp only [sepConj_assoc]
  wp_steps
  iterate 31 (wp_black_box_ext32 hbb hal_sub48; wp_steps)
  wp_black_box_ext32 hbb hal_sub48
  clear hx19_bb
  wp_steps
  conv =>
    arg 5; ext sf P_f
    rw [← zeroExtend32_ite_prop_1_0_8_ext32 (k1 = k2)]
  refine step_blackBox_tail_ext32 hbb hsp_align
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (ct_eq_bool_32_u8_ext32 h_4 h) ?_
  rw [← h_slices]
  unfold pointsToBytes32
  simp only [sepConj_assoc]

/-! ## `<PublicKey as PartialEq>::eq` under `blackBoxSpec32` -/

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_and64_ext32 (x y : BitVec 64) :
    BitVec.setWidth 32 (x &&& y) = BitVec.setWidth 32 x &&& BitVec.setWidth 32 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_zext64_32_ext32 (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.zeroExtend 64 x) = x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_255_ite_1_0_ext32 (P : Prop) [Decidable P] :
    ((if P then 1#32 else 0#32) &&& 255#32) = if P then 1#32 else 0#32 := by
  split <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem csinc_eq_zero32_ite32_1_0_ext32 (P : Prop) [Decidable P] :
    (if ((if P then 1#32 else 0#32) == 0#32) = true then 0#64 else 1#64) =
      if P then 1#64 else 0#64 := by
  by_cases hp : P <;> simp [hp]

theorem publicKey_ite32_toList_eq_ext32 (pk1 pk2 : PublicKey) :
    (if pk1.bytes.toList = pk2.bytes.toList then 1#32 else 0#32) =
      if (pk1 == pk2) = true then 1#32 else 0#32 := by
  by_cases h : (pk1 == pk2) = true
  · have hlist := (publicKey_toList_eq_iff pk1 pk2).mpr h
    simp [h, hlist]
  · have hlist : ¬(pk1.bytes.toList = pk2.bytes.toList) := by
      intro hl
      exact h ((publicKey_toList_eq_iff pk1 pk2).mp hl)
    simp [h, hlist]

/-- `publicKeyEqSpec` extended with 16 KiB hook stack under `blackBoxSpec32`. -/
noncomputable def publicKeyEqSpecExt :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) ∗
    stackAt (sp - 64#64) extHookStack32
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) ∗
    stackAt (sp - 64#64) extHookStack32

theorem publicKey_eq_ok_ext32 (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
      publicKeyEqSpecExt := by
  simp only [publicKeyEqSpecExt, ← stackFrameFor_ctEq_eq_memRegion_ext32,
    stackFrameFor, fnFrameBytes_publicKeyEqName_ext32, reduceStackFrameAt]
  have hct := ct_eq_ok_ext32 b h_bb
  rw [Program.fnAddr_rel
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
    (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq") (k := 212) rfl] at hct
  simp only [ctEqSliceSpecExt, ← stackFrameFor_ctEq_eq_memRegion_ext32] at hct
  code_fetches libsignalSessionCode libsignalSessionBin b H
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
    (num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")) 28
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h
  have hstack_eq : s0.sp - 16#64 - 48#64 = s0.sp - 64#64 := by bv_omega
  rw [← hstack_eq]
  wp_steps
  wp_apply
  rw [publicKey_ite32_toList_eq_ext32, hstack_eq] at *
  wp_steps
  wp_done

theorem stackAt_16448_eq_publicKeyEq_frames_ext32 (sp : BitVec 64) :
    stackAt sp (64 + extHookStack32) =
      stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) ∗
      stackAt (sp - 64#64) extHookStack32 := by
  rw [← stackFrameFor_eq_eq_memRegion_ext32 sp,
      ← stackFrameFor_ctEq_eq_memRegion_ext32 (sp - 16#64)]
  simp only [stackAt, extHookStack32]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  have h16448 : sp - 64#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 (64 + 16384) := by bv_omega
  rw [h64, h16448,
      ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (64 + 16384)) (n := 16384) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  ac_rfl

def publicKeyEqStackSpecExt :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp (64 + extHookStack32)
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp (64 + extHookStack32)

theorem publicKey_eq_stack_ok_ext32 (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
      publicKeyEqStackSpecExt := by
  refine subroutine_ok_map (publicKey_eq_ok_ext32 b h_bb) ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [publicKeyEqSpecExt, publicKeyEqStackSpecExt,
      stackAt_16448_eq_publicKeyEq_frames_ext32 sp, sepConj_assoc] using hpre
  · intro sf hpost
    simpa only [publicKeyEqSpecExt, publicKeyEqStackSpecExt,
      stackAt_16448_eq_publicKeyEq_frames_ext32 sp, sepConj_assoc] using hpost

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Blocks 212 and 213) -/

theorem ct_eq_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceSpec := by
  simp only [ctEqSliceSpec]
  have hext : ((blkPC_213).rebase (blkPl_213).base H).externAt? (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
    (ls_externAt?_of_mem).trans h_bb
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32
  simp only [sepConj_assoc]
  iterate 33 (wp_steps; wp_black_box hext)
  rw [ct_eq_bool_32 h_4 h]
  wp_done

theorem publicKey_eq_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqSpec) := by
  simp only [withLsCodeLoaded, publicKeyEqSpec]
  have hct0 : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213) ctEqSliceSpec :=
    ct_eq_placed_ok h_bb
  have hct := ls_subroutine_ok_of_block (callerProg := (blkPC_212).rebase (blkPl_212).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hct0)
  simp only [withLsCodeLoaded, ctEqSliceSpec] at hct
  wp_init x s0
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  apply sepWP_seq_lscl h (mid := lsmpl.base 213)
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_call
  wp_apply
  rw [publicKey_ite_toList_eq] at *
  wp_steps
  wp_done

/-- Image-free `[u8]::ct_eq` contract with explicit 48-byte stack `memRegion`. -/
def ctEqSliceMemSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    memRegion (sp - 48#64) 48
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    memRegion (sp - 48#64) 48

private theorem memRegion_48_eq_cells_6 (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6 := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]

private theorem memRegion_16_eq_cells_2 (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 = cells (sp - 16#64) 2 := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]

theorem ct_eq_mem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceMemSpec := by
  simp only [ctEqSliceMemSpec, memRegion_48_eq_cells_6]
  cells_unfold
  have hext : ((blkPC_213).rebase (blkPl_213).base H).externAt? (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
    (ls_externAt?_of_mem).trans h_bb
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32
  simp only [sepConj_assoc]
  iterate 33 (wp_steps; wp_black_box hext)
  rw [ct_eq_bool_32 h_4 h]
  wp_done

/-- Image-free placed `<PublicKey as PartialEq>::eq` (Block 212) contract. -/
theorem publicKey_eq_mem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl
        { pre := fun (p1, (pk1 : PublicKey), p2, (pk2 : PublicKey), sp) s =>
            ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
            (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
            memRegion (sp - 16#64) 16 ∗
            memRegion (sp - 16#64 - 48#64) 48
          post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
            ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
            (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
            memRegion (sp - 16#64) 16 ∗
            memRegion (sp - 16#64 - 48#64) 48 }) := by
  simp only [withLsCodeLoaded, memRegion_16_eq_cells_2]
  cells_unfold
  have hct0 : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213) ctEqSliceMemSpec :=
    ct_eq_mem_placed_ok h_bb
  have hct := ls_subroutine_ok_of_block (callerProg := (blkPC_212).rebase (blkPl_212).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hct0)
  simp only [withLsCodeLoaded, ctEqSliceMemSpec] at hct
  wp_init x s0
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  apply sepWP_seq_lscl h (mid := lsmpl.base 213)
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_call
  wp_apply
  rw [publicKey_ite_toList_eq] at *
  wp_steps
  wp_done

end CryptoVerification.LibsignalSession.FindReceiverChainIndex
