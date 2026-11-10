/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Probe
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics
import ProofLib.BV.ReflectROBDD

/-!
# SwissTable Read-Only Lookups

Placement-generic (`HbPlaced`) machine-code proofs for `hashbrown_get` and
`hashbrown_contains_key`, with control-group memory focus and 8-bit `BitMask` population-count
helpers (`bv8Pop`).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 ProofLib

theorem ctrlGroupWord_eq_readLE (bs : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE bs off 8 = ctrlGroupWord bs off :=
  (ByteSlice.pack64_eq_readLE_8 bs off).symm

theorem pointsToBytes_focus_ctrlGroupWord (base : BitVec 64) (ctrl : List (BitVec 8))
    {pos : Nat} (h : pos + 8 ≤ ctrl.length) :
    (base ↦ₛ ctrl) =
      ((base + BitVec.ofNat 64 pos) ↦₆₄ ctrlGroupWord ctrl pos) ∗
      ((base ↦ₛ ctrl.take pos) ∗
        ((base + BitVec.ofNat 64 (pos + 8)) ↦ₛ ctrl.drop (pos + 8))) := by
  have hsplit := pointsToBytes_split3 base ctrl pos 8 h
  rw [pointsToBytes_take8_eq_pointsTo64 _ ctrl pos h] at hsplit
  exact hsplit

private theorem cntTrue_zero_iff (p : Nat → Bool) :
    ∀ n, cntTrue p n = 0 ↔ ∀ i < n, p i = false
  | 0 => by simp [cntTrue]
  | n + 1 => by
    simp only [cntTrue]
    refine ⟨fun h i hi => ?_, fun h => ?_⟩
    · by_cases hin : i = n
      · subst hin; cases hpn : p i <;> simp_all
      · exact (cntTrue_zero_iff p n).1 (by cases hpn : p n <;> simp_all) i (by omega)
    · rw [(cntTrue_zero_iff p n).2 (fun i hi => h i (by omega)), h n (by omega)]; simp

/-- Population count (number of set bits) of an 8-bit `BitMask`. -/
def bv8Pop (b : BitVec 8) : Nat := cntTrue b.getLsbD 8

theorem bv8Pop_eq_zero_iff (b : BitVec 8) : bv8Pop b = 0 ↔ b = 0#8 :=
  (cntTrue_zero_iff b.getLsbD 8).trans (bv8_eq_zero_iff_forall b).symm

theorem bv8Pop_clear_lowest {b : BitVec 8} (hb : b ≠ 0#8) :
    bv8Pop ((b - 1#8) &&& b) + 1 = bv8Pop b := by
  rcases bv8_ctz_spec hb with ⟨hk8, htrue, _⟩
  have hclr : ((b - 1#8) &&& b).getLsbD b.ctz.toNat = false := by
    rw [bv8_getLsbD_clear_lowest b hk8]; simp
  have hset := cntTrue_set ((b - 1#8) &&& b).getLsbD b.ctz.toNat 8 hk8 hclr
  have hcongr : cntTrue (fun y => ((b - 1#8) &&& b).getLsbD y || (b.ctz.toNat == y)) 8 =
      cntTrue b.getLsbD 8 :=
    cntTrue_congr 8 fun y hy => by
      rw [bv8_getLsbD_clear_lowest b hy]
      by_cases hyk : y = b.ctz.toNat
      · subst hyk; simp [htrue]
      · simp [hyk, Ne.symm hyk]
  unfold bv8Pop; omega

theorem bv8Pop_eq_one_unique {b : BitVec 8} (h1 : bv8Pop b = 1) {j : Nat} (hj : j < 8)
    (ht : b.getLsbD j = true) : j = b.ctz.toNat := by
  have hb : b ≠ 0#8 := by rintro rfl; simp at ht
  have h0 : (b - 1#8) &&& b = 0#8 :=
    (bv8Pop_eq_zero_iff _).1 (by have := bv8Pop_clear_lowest hb; omega)
  have hc := bv8_getLsbD_clear_lowest b hj
  rw [h0] at hc
  exact Classical.byContradiction fun hne => by simp [ht, hne] at hc

theorem subroutine_ok_withCodeInv_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    (A : HbAlloc) {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withCodeInv A spec) :=
  subroutine_ok_mono_sp h
    (fun _ _ => by dsimp only [withCodeInv]; exact Entails.pure_left fun _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)

section MachineProofs
arm64_proof_prelude

def dupByte8Vec (tag64 : BitVec 64) : BitVec 128 :=
  mapLanes 8 0#128 (fun _ => tag64.zeroExtend 128 &&& 0xff#128) 8

theorem dup_lsr57_eq (x : BitVec 64) :
    (0#128 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
      (BitVec.setWidth 128 (x >>> 57) &&& 255#128 &&& 255#128) <<< 56) =
    dupByte8Vec (x >>> 57) := by
  simp only [dupByte8Vec, mapLanes, laneMask_8, BitVec.zeroExtend]

private def RoFrame (s0 st : State) : Prop :=
  st.sp = s0.sp ∧ st.readReg64 .lr = s0.readReg64 .lr ∧
  CalleeSavedPreserved s0 st ∧ StdStartup.StdStatePreserved s0 st ∧ st.mem = s0.mem

private theorem RoFrame.rfl (s0 : State) : RoFrame s0 s0 :=
  ⟨Eq.refl _, Eq.refl _, CalleeSavedPreserved.rfl s0, StdStartup.StdStatePreserved.rfl s0, Eq.refl _⟩

private theorem RoFrame.trans {s0 s1 s2 : State} (h01 : RoFrame s0 s1) (h12 : RoFrame s1 s2) :
    RoFrame s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1,
   CalleeSavedPreserved.trans h01.2.2.1 h12.2.2.1,
   StdStartup.StdStatePreserved.trans h01.2.2.2.1 h12.2.2.2.1,
   h12.2.2.2.2.trans h01.2.2.2.2⟩

@[local simp] private theorem roFrame_rfl (s0 : State) : RoFrame s0 s0 := RoFrame.rfl s0
@[local simp] private theorem roFrame_setPC (s0 s : State) (pc : BitVec 64) :
    RoFrame s0 (s.setPC pc) ↔ RoFrame s0 s := by
  simp [RoFrame, StdStartup.StdStatePreserved]
@[local simp] private theorem roFrame_advancePC (s0 s : State) :
    RoFrame s0 s.advancePC ↔ RoFrame s0 s := by
  simp [RoFrame, StdStartup.StdStatePreserved]
@[local simp] private theorem roFrame_setPState (s0 s : State) (ps : PState) :
    RoFrame s0 (s.setPState ps) ↔ RoFrame s0 s := by
  simp [RoFrame, StdStartup.StdStatePreserved]
@[local simp] private theorem roFrame_writeReg64 (s0 s : State) (idx : BitVec 5) (val : BitVec 64)
    (hcs : isCalleeSavedReg (.gpr idx) = false := by decide)
    (hlr : idx ≠ 30#5 := by decide) :
    RoFrame s0 (s.writeReg64 (.gpr idx) val) ↔ RoFrame s0 s := by
  have hne : Reg.lr ≠ Reg.gpr idx := by intro h; cases h; exact hlr rfl
  simp [RoFrame, StdStartup.StdStatePreserved, hcs, hne]
@[local simp] private theorem roFrame_writeReg32 (s0 s : State) (idx : BitVec 5) (val : BitVec 32)
    (hcs : isCalleeSavedReg (.gpr idx) = false := by decide)
    (hlr : idx ≠ 30#5 := by decide) :
    RoFrame s0 (s.writeReg32 (.gpr idx) val) ↔ RoFrame s0 s :=
  roFrame_writeReg64 s0 s idx (val.zeroExtend 64) hcs hlr
@[local simp] private theorem roFrame_writeVReg128 (s0 s : State) (v : BitVec 5) (val : BitVec 128)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RoFrame s0 (s.writeVReg128 v val) ↔ RoFrame s0 s := by
  simp [RoFrame, StdStartup.StdStatePreserved, CalleeSavedPreserved_writeVReg128 s0 s v val hcs]
@[local simp] private theorem roFrame_writeVReg64 (s0 s : State) (v : BitVec 5) (val : BitVec 64)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RoFrame s0 (s.writeVReg64 v val) ↔ RoFrame s0 s :=
  roFrame_writeVReg128 s0 s v (val.zeroExtend 128) hcs
@[local simp] private theorem roFrame_writeVReg32 (s0 s : State) (v : BitVec 5) (val : BitVec 32)
    (hcs : isCalleeSavedVReg v = false := by decide) :
    RoFrame s0 (s.writeVReg32 v val) ↔ RoFrame s0 s :=
  roFrame_writeVReg128 s0 s v (val.zeroExtend 128) hcs

private theorem close_ro_post {P_rep R P_f : SepProp} {s0 sf : State} {φ : Prop}
    (hpre : s0.mem ⊨ P_rep ∗ R) (hφ : φ)
    (hstd : StdStartup.StdStatePreserved s0 sf) (hmem : sf.mem = s0.mem)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (⌜φ ∧ StdStartup.StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗ P_rep) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  refine ⟨fun _ => ?_, hsp, hcs⟩
  rw [hmem, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hφ, hstd, hmem ▸ Memory.KeepsFrozen.refl s0.mem⟩, hpre⟩

private theorem close_ro_frame {P_rep R P_f : SepProp} {s0 sf : State} {φ : Prop}
    (hpre : s0.mem ⊨ P_rep ∗ R) (hro : RoFrame s0 sf) (hφ : φ) :
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (⌜φ ∧ StdStartup.StdStatePreserved s0 sf ∧ s0.mem.KeepsFrozen sf.mem⌝ ∗ P_rep) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf :=
  close_ro_post hpre hφ hro.2.2.2.1 hro.2.2.2.2 hro.1 hro.2.2.1

theorem slotsDownFrom_focus_ldur (ctrlPtr : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) {idx : Nat} (hi : idx < slots.length) :
    slotsDownFrom ctrlPtr slots =
      (((ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ (slots[idx]'hi).1) ∗
      (((ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ (slots[idx]'hi).2) ∗
      (slotsDownFrom ctrlPtr (slots.take idx) ∗
       slotsDownFrom (slotAddr ctrlPtr idx) (slots.drop (idx + 1))) := by
  rw [slotsDownFrom_focus ctrlPtr slots hi, slotPairAt, ← slotAddr_sub_lsl4_sub8 ctrlPtr idx]
  conv => rhs; arg 1; arg 1; rw [slotAddr_sub_lsl4_sub16 ctrlPtr idx]
  rw [sepConj_assoc]

private def ProbeInvAt (s0 : State) (w : HbHeapMapWitness) (bm k : BitVec 64)
    (step : Nat) (st : State) : Prop :=
  RoFrame s0 st ∧
  st.readReg64 (Reg.gpr 1#5) = k ∧
  st.readReg64 (Reg.gpr 8#5) = bm ∧
  st.readReg64 (Reg.gpr 9#5) = w.ctrlPtr ∧
  st.readReg64 (Reg.gpr 10#5) = BitVec.ofNat 64 (8 * step) ∧
  (st.readReg64 (Reg.gpr 11#5) &&& bm) = BitVec.ofNat 64 (probePos bm k step) ∧
  st.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57) ∧
  st.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128 ∧
  (∀ s < step, ∀ j < 8,
    getLane8 (ctrlGroupWord w.ctrl (probePos bm k s)) j = h2Tag k →
    (h : (probePos bm k s + j) % (bm.toNat + 1) < w.slots.length) →
    (w.slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)

private def ProbeInnerInv (s0 : State) (w : HbHeapMapWitness) (bm k : BitVec 64)
    (step : Nat) (b : BitVec 8) (st : State) : Prop :=
  let pos := probePos bm k step
  let g := ctrlGroupWord w.ctrl pos
  b ≠ 0#8 ∧
  RoFrame s0 st ∧
  st.readReg64 (Reg.gpr 1#5) = k ∧
  st.readReg64 (Reg.gpr 8#5) = bm ∧
  st.readReg64 (Reg.gpr 9#5) = w.ctrlPtr ∧
  st.readReg64 (Reg.gpr 10#5) = BitVec.ofNat 64 (8 * step) ∧
  st.readReg64 (Reg.gpr 11#5) = BitVec.ofNat 64 pos ∧
  st.readReg64 (Reg.gpr 12#5) = highBitMaskOfBits b ∧
  st.readVReg128 0#5 = dupByte8Vec ((k * fxSeed) >>> 57) ∧
  st.readVReg128 1#5 = 0xffffffffffffffffffffffffffffffff#128 ∧
  st.readVReg128 2#5 = g.zeroExtend 128 ∧
  (∀ j < 8, b.getLsbD j = true → getLane8 g j = h2Tag k) ∧
  (∀ j < 8, getLane8 g j = h2Tag k → b.getLsbD j = false →
    (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
    (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k)

local macro "ro_simp0" : tactic =>
  `(tactic| simp (config := { decide := true }) only [
      roFrame_setPC, roFrame_advancePC, roFrame_setPState,
      roFrame_writeReg64, roFrame_writeReg32,
      roFrame_writeVReg128, roFrame_writeVReg64, roFrame_writeVReg32, roFrame_rfl])

local macro "ro_simp" h:term : tactic =>
  `(tactic| simp (config := { decide := true }) only [
      roFrame_setPC, roFrame_advancePC, roFrame_setPState,
      roFrame_writeReg64, roFrame_writeReg32,
      roFrame_writeVReg128, roFrame_writeVReg64, roFrame_writeVReg32, roFrame_rfl, $h:term])

private theorem extend_probe_prev {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {bm k : BitVec 64} {step : Nat}
    (hprev : ∀ s < step, ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    ∀ s < step + 1, ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k := by
  intro s hs j hj htag hsl
  by_cases hlt : s < step
  · exact hprev s hlt j hj htag hsl
  · have rfl_s : s = step := by omega
    subst rfl_s; exact hno_h2 j hj htag hsl

private theorem probe_empty_miss_lookup {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {map : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots map) {k : BitVec 64} {step : Nat}
    (hemp_ne : eqBits8 (ctrlGroupWord ctrl (probePos bm k step)) tagEmpty ≠ 0#8)
    (hprev : ∀ s < step, ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm k s)) j = h2Tag k →
      (h : (probePos bm k s + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k s + j) % (bm.toNat + 1)]'h).1 ≠ k)
    (hno_h2 : ∀ j < 8,
      getLane8 (ctrlGroupWord ctrl (probePos bm k step)) j = h2Tag k →
      (h : (probePos bm k step + j) % (bm.toNat + 1) < slots.length) →
      (slots[(probePos bm k step + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    cliMapLookup k map = none := by
  rcases (bv8_ne_zero_iff_exists _).1 hemp_ne with ⟨je, hje, hbit_e⟩
  rw [getLsbD_eqBits8 _ tagEmpty hje, beq_iff_eq] at hbit_e
  have hpos_lt := probePos_lt_buckets hinv.validMask k step
  have hlen := hinv.mirror.1
  have hemp_pos : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step) :=
    (mem_ctrlGroupAt_iff (by omega) tagEmpty).2 ⟨je, hje, hbit_e⟩
  exact hinv.lookup_eq_none_of_probe_empty (step := step) hemp_pos fun s hs j hj htag =>
    extend_probe_prev hprev hno_h2 s (by omega) j hj htag _

private theorem probe_nonempty_lt_end {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {map : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots map) {k : BitVec 64}
    {step step_end : Nat} (hstep_le : step ≤ step_end)
    (hemp_end : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k step_end))
    (hemp_eq : eqBits8 (ctrlGroupWord ctrl (probePos bm k step)) tagEmpty = 0#8) :
    step < step_end := by
  apply Classical.byContradiction; intro hge
  have heq_s : step = step_end := by omega
  subst heq_s
  have hpos_lt := probePos_lt_buckets hinv.validMask k step
  have hlen := hinv.mirror.1
  rcases (mem_ctrlGroupAt_iff (by omega) tagEmpty).1 hemp_end with ⟨je, hje, hlane_e⟩
  have hbit_e := (bv8_eq_zero_iff_forall _).1 hemp_eq je hje
  rw [getLsbD_eqBits8 _ _ hje, beq_eq_false_iff_ne] at hbit_e
  exact hbit_e hlane_e

private theorem clear_lowest_miss {g bm k : BitVec 64} {slots : List (BitVec 64 × BitVec 64)}
    {pos : Nat} {b : BitVec 8}
    {hidx : (pos + b.ctz.toNat) % (bm.toNat + 1) < slots.length}
    (hk_ne : (slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx).1 ≠ k)
    (hmiss_b : ∀ j < 8, getLane8 g j = h2Tag k → b.getLsbD j = false →
      (h : (pos + j) % (bm.toNat + 1) < slots.length) →
      (slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k) :
    ∀ j < 8, getLane8 g j = h2Tag k → ((b - 1#8) &&& b).getLsbD j = false →
      (h : (pos + j) % (bm.toNat + 1) < slots.length) →
      (slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := by
  intro j hj htag hbf' hsl
  rw [bv8_getLsbD_clear_lowest b hj] at hbf'
  by_cases hbj : b.getLsbD j = true
  · rw [hbj, Bool.true_and, decide_eq_false_iff_not, Classical.not_not] at hbf'
    subst hbf'; exact hk_ne
  · exact hmiss_b j hj htag (Bool.eq_false_iff.2 hbj) hsl

theorem hashbrown_get_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg4 P).rebase P.pl4.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_get") (hashbrownGetSpec P.pl A) := by
  dsimp only
  unfold hashbrownGetSpec
  wp_entry
  revert a_1 a a_2 a_3 a_rest_1 hsp_align hpre h_1 h
  intro mapPtr map bm u k _ hpre hx0 hx1
  wp_conv_pre => unfold U64MapRep
  apply SepWP.pure_elim; rintro ⟨hmap_al, hmap_nw, hmap_wf⟩
  by_cases hbm0 : bm = 0#64
  · subst hbm0
    wp_simp_pre [U64MapStruct]
    wp_focus_pure; rintro rfl
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    exact close_ro_frame hpre (by ro_simp0) (by simp [wp_norm, arm64_norm])
  · wp_simp_pre [hbm0]
    apply SepWP.exists_left; intro w
    wp_focus_pure; rintro ⟨hinv, h_u, h_al1, h_al2, h_al3, h_ce⟩
    clear h_u h_al1 h_al2 h_al3 h_ce
    wp_simp_pre [U64MapStruct]
    by_cases hitems0 : w.items = 0#64
    · have hnil : map = [] := hinv.items_eq_zero_iff_nil.1 hitems0
      subst hnil
      wp_simp_pre [hitems0]
      wp_sym_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      exact close_ro_frame hpre (by ro_simp0) (by simp [wp_norm, arm64_norm])
    · have hctrl_len : w.ctrl.length = (bm.toNat + 1) + 8 := hinv.mirror.1
      have hslots_len : w.slots.length = bm.toNat + 1 := hinv.slots_len
      rcases hinv.exists_empty_probe_group k with ⟨step_end, _, hemp_end⟩
      wp_sym_steps 13
      apply SepWP.cfg_fixpoint_wf_cps (Label := Nat) (l0 := 0) (cut_pc := fun _ => _)
        (meas := fun step _ => step_end + 1 - step) (P_inv := fun _ _ => _)
        (Inv := fun step st => step ≤ step_end ∧ ProbeInvAt s0 w bm k step st) (post := fun _ => _)
      · wp_focus_close wp_norm_lhs
      · simp only [wp_norm, arm64_norm, hrun]
      · exact Entails.refl _
      · have hfx : k * 5871781006564002453#64 = k * fxSeed := rfl
        refine ⟨Nat.zero_le _, by ro_simp0, by simp only [wp_norm, arm64_norm, hx1],
          by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
          by simp only [wp_norm, arm64_norm],
          by simpa only [wp_norm, arm64_norm, hfx, fxHash, fxProd, triByteOff_zero, BitVec.add_zero]
               using probePos_bv_eq bm k 0,
          by simpa only [wp_norm, arm64_norm, hfx] using dup_lsr57_eq (k * fxSeed),
          by simp only [wp_norm, arm64_norm], fun _ hs => by omega⟩
      · intro step st hpc_st hrun_st ⟨hstep_le, hro, hx1_st, hx8_st, hx9_st, hx10_st, hx11_st,
          hv0_st, hv1_st, hprev⟩ ih_outer
        let pos := probePos bm k step
        let g := ctrlGroupWord w.ctrl pos
        have hpos_lt : pos < bm.toNat + 1 := probePos_lt_buckets hinv.validMask k step
        wp_sym_steps 1
        wp_conv_pre =>
          rw [pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
        set_option proofLib.wpBranchAutoDecide false in
        wp_sym_steps 5
        wp_conv_pre =>
          rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
        have hm_h2 := simd_cmeq_dup8_highMask g ((k * fxSeed) >>> 57)
        change (zipLanes 8 (g.zeroExtend 128) (dupByte8Vec ((k * fxSeed) >>> 57))
          (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 &&&
          0x8080808080808080#64 = highBitMaskOfBits (eqBits8 g (h2Tag k)) at hm_h2
        conv at hm_h2 => lhs; simp only [wp_norm, arm64_norm]
        rw [hm_h2]
        wp_if hbeq
        · have hb0 : eqBits8 g (h2Tag k) = 0#8 :=
            (highBitMaskOfBits_eq_zero_iff _).1 (by simpa using hbeq)
          have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k →
              (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
              (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag => by
            have hbit := (bv8_eq_zero_iff_forall _).1 hb0 j hj
            rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbit
            exact False.elim (hbit htag)
          wp_sym_steps 1
          have hall := simd_cmeq_allOnes8 g
          conv at hall => lhs; simp only [wp_norm, arm64_norm]
          rw [hall]
          wp_sym_steps 1
          have humax := simdUmaxv8_byteMaskOfBits (eqBits8 g tagEmpty)
          conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
          rw [humax]
          set_option proofLib.wpBranchAutoDecide false in
          wp_sym_steps 2
          wp_if htbnz
          · have hemp_ne : eqBits8 g tagEmpty ≠ 0#8 := fun hz => by rw [hz] at htbnz; simp at htbnz
            have hnone := probe_empty_miss_lookup hinv hemp_ne hprev hno_h2
            wp_sym_steps 2
            apply SepWP.done (by simp [wp_norm, arm64_norm, hro.2.1])
              (by simp [wp_norm, arm64_norm, hrun_st])
            exact close_ro_frame hpre (by ro_simp hro) (by simp [hnone, wp_norm, arm64_norm])
          · have hemp_eq : eqBits8 g tagEmpty = 0#8 :=
              Classical.byContradiction fun hne => htbnz (by simp only [hne, ↓reduceIte]; decide)
            have hlt_end := probe_nonempty_lt_end hinv hstep_le hemp_end hemp_eq
            wp_sym_steps 3
            apply ih_outer (step + 1) _ (by omega)
            · wp_focus_close wp_norm_lhs
            · simp only [wp_norm, arm64_norm, hrun_st]
            · refine ⟨by omega, by ro_simp hro, by simp only [wp_norm, arm64_norm, hx1_st],
                by simp only [wp_norm, arm64_norm, hx8_st],
                by simp only [wp_norm, arm64_norm, hx9_st],
                by simp only [wp_norm, arm64_norm]
                   rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
                by simpa only [wp_norm, arm64_norm, hx10_st] using
                     probePos_step_bv hinv.validMask k step,
                by simp only [wp_norm, arm64_norm, hv0_st],
                by simp only [wp_norm, arm64_norm, hv1_st], extend_probe_prev hprev hno_h2⟩
        · have hb0 : eqBits8 g (h2Tag k) ≠ 0#8 := fun hz => by
            rw [hz, highBitMaskOfBits_zero] at hbeq; simp at hbeq
          apply SepWP.cfg_fixpoint_wf_cps (Label := BitVec 8) (l0 := eqBits8 g (h2Tag k))
            (cut_pc := fun _ => _) (meas := fun b _ => b.toNat) (P_inv := fun _ _ => _)
            (Inv := fun b sti => ProbeInnerInv s0 w bm k step b sti) (post := fun _ => _)
          · wp_focus_close wp_norm_lhs
          · simp only [wp_norm, arm64_norm, hrun_st]
          · exact Entails.refl _
          · refine ⟨hb0, by ro_simp hro, by simp only [wp_norm, arm64_norm, hx1_st],
              by simp only [wp_norm, arm64_norm, hx8_st],
              by simp only [wp_norm, arm64_norm, hx9_st],
              by simp only [wp_norm, arm64_norm, hx10_st],
              by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
              by simp only [wp_norm, arm64_norm, hv0_st],
              by simp only [wp_norm, arm64_norm, hv1_st],
              by simp only [wp_norm, arm64_norm]; rfl,
              fun j hj hbit => by rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_iff_eq] at hbit; exact hbit,
              fun j hj htag hbf => by
                rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbf
                exact False.elim (hbf htag)⟩
          · intro b sti hpc_i hrun_i ⟨hb, hro_i, hx1_i, hx8_i, hx9_i, hx10_i, hx11_i, hx12_i,
              hv0_i, hv1_i, hv2_i, hsub_b, hmiss_b⟩ ih_inner
            rcases bv8_ctz_spec hb with ⟨hj0_lt, hj0_bit, _⟩
            have hidx_lt : (pos + b.ctz.toNat) % (bm.toNat + 1) < w.slots.length := by
              rw [hslots_len]; exact Nat.mod_lt _ (by omega)
            have htag_j0 : getLane8 g b.ctz.toNat = h2Tag k := hsub_b b.ctz.toNat hj0_lt hj0_bit
            wp_sym_steps 5
            rw [ProofLib.reverseBits_eq_reverse, highBitMaskOfBits_lowestLane b,
              hinv.validMask.laneIdx_bv hpos_lt hj0_lt]
            wp_conv_pre => rw [slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
            set_option proofLib.wpBranchAutoDecide false in
            wp_sym_steps 3
            wp_if hkeq
            · have hlook : cliMapLookup k map =
                  some (w.slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx_lt).2 :=
                hinv.lookup_eq_some_of_lane_match hpos_lt hj0_lt htag_j0 hkeq.symm
              wp_sym_steps 3
              apply SepWP.done (by simp [wp_norm, arm64_norm, hro_i.2.1])
                (by simp [wp_norm, arm64_norm, hrun_i])
              exact close_ro_frame hpre (by ro_simp hro_i) (by simp [hlook, wp_norm, arm64_norm])
            · have hk_ne : (w.slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx_lt).1 ≠ k :=
                Ne.symm hkeq
              wp_conv_pre => rw [← slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
              set_option proofLib.wpBranchAutoDecide false in
              wp_sym_steps 3
              rw [highBitMaskOfBits_clear_lowest b]
              wp_if hbne
              · have hb' : (b - 1#8) &&& b ≠ 0#8 := fun hz => by
                  rw [hz, highBitMaskOfBits_zero] at hbne; simp at hbne
                apply ih_inner ((b - 1#8) &&& b) _ (bv8_clear_lowest_lt hb)
                · wp_focus_close wp_norm_lhs
                · simp only [wp_norm, arm64_norm, hrun_i]
                · refine ⟨hb', by ro_simp hro_i, by simp only [wp_norm, arm64_norm, hx1_i],
                    by simp only [wp_norm, arm64_norm, hx8_i],
                    by simp only [wp_norm, arm64_norm, hx9_i],
                    by simp only [wp_norm, arm64_norm, hx10_i],
                    by simp only [wp_norm, arm64_norm, hx11_i],
                    by simp only [wp_norm, arm64_norm],
                    by simp only [wp_norm, arm64_norm, hv0_i],
                    by simp only [wp_norm, arm64_norm, hv1_i],
                    by simp only [wp_norm, arm64_norm, hv2_i],
                    fun j hj hbit' => by
                      rw [bv8_getLsbD_clear_lowest b hj, Bool.and_eq_true] at hbit'
                      exact hsub_b j hj hbit'.1,
                    clear_lowest_miss hk_ne hmiss_b⟩
              · have hb'_zero : (b - 1#8) &&& b = 0#8 :=
                  (highBitMaskOfBits_eq_zero_iff _).1 hbne
                have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k →
                    (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
                    (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag hsl =>
                  clear_lowest_miss hk_ne hmiss_b j hj htag
                    ((bv8_eq_zero_iff_forall _).1 hb'_zero j hj) hsl
                wp_sym_steps 1
                have hall := simd_cmeq_allOnes8 g
                conv at hall => lhs; simp only [wp_norm, arm64_norm]
                rw [hall]
                wp_sym_steps 1
                have humax := simdUmaxv8_byteMaskOfBits (eqBits8 g tagEmpty)
                conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
                rw [humax]
                set_option proofLib.wpBranchAutoDecide false in
                wp_sym_steps 2
                wp_if htbnz
                · have hemp_ne : eqBits8 g tagEmpty ≠ 0#8 := fun hz => by
                    rw [hz] at htbnz; simp at htbnz
                  have hnone := probe_empty_miss_lookup hinv hemp_ne hprev hno_h2
                  wp_sym_steps 2
                  apply SepWP.done (by simp [wp_norm, arm64_norm, hro_i.2.1])
                    (by simp [wp_norm, arm64_norm, hrun_i])
                  exact close_ro_frame hpre (by ro_simp hro_i)
                    (by simp [hnone, wp_norm, arm64_norm])
                · have hemp_eq : eqBits8 g tagEmpty = 0#8 :=
                    Classical.byContradiction fun hne => htbnz (by simp only [hne, ↓reduceIte]; decide)
                  have hlt_end := probe_nonempty_lt_end hinv hstep_le hemp_end hemp_eq
                  wp_sym_steps 3
                  apply ih_outer (step + 1) _ (by omega)
                  · wp_focus_close wp_norm_lhs
                  · simp only [wp_norm, arm64_norm, hrun_i]
                  · refine ⟨by omega, by ro_simp hro_i, by simp only [wp_norm, arm64_norm, hx1_i],
                      by simp only [wp_norm, arm64_norm, hx8_i],
                      by simp only [wp_norm, arm64_norm, hx9_i],
                      by simp only [wp_norm, arm64_norm]
                         rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
                      by simpa only [wp_norm, arm64_norm, hx10_i, hx11_i] using
                           probePos_step_bv hinv.validMask k step,
                      by simp only [wp_norm, arm64_norm, hv0_i],
                      by simp only [wp_norm, arm64_norm, hv1_i],
                      extend_probe_prev hprev hno_h2⟩

theorem hashbrown_get_withCodeInv_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg4 P).rebase P.pl4.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_get") (withCodeInv A (hashbrownGetSpec P.pl A)) :=
  subroutine_ok_withCodeInv_of_plain A (hashbrown_get_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_get_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_get" (fun mpl => hashbrownGetSpec (mplAsPl mpl) A) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_get" 4 (off := 0) (fun P X' => hbProg4_rebase P X')
    (fun mpl => hashbrownGetSpec (mplAsPl mpl) A) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_get_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_get_withCodeInv_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_get"
      (fun mpl => withCodeInv A (hashbrownGetSpec (mplAsPl mpl) A)) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_get" 4 (off := 0) (fun P X' => hbProg4_rebase P X')
    (fun mpl => withCodeInv A (hashbrownGetSpec (mplAsPl mpl) A)) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_get_withCodeInv_ok P A X)

theorem hashbrown_contains_key_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg2 P).rebase P.pl2.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_contains_key")
      (hashbrownContainsKeySpec P.pl A) := by
  dsimp only
  unfold hashbrownContainsKeySpec
  wp_entry
  revert a_1 a a_2 a_3 a_rest_1 hsp_align hpre h_1 h
  intro mapPtr map bm u k _ hpre hx0 hx1
  wp_conv_pre => unfold U64MapRep
  apply SepWP.pure_elim; rintro ⟨hmap_al, hmap_nw, hmap_wf⟩
  by_cases hbm0 : bm = 0#64
  · subst hbm0
    wp_simp_pre [U64MapStruct]
    wp_focus_pure; rintro rfl
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    exact close_ro_frame hpre (by ro_simp0) (by simp [wp_norm, arm64_norm])
  · wp_simp_pre [hbm0]
    apply SepWP.exists_left; intro w
    wp_focus_pure; rintro ⟨hinv, h_u, h_al1, h_al2, h_al3, h_ce⟩
    clear h_u h_al1 h_al2 h_al3 h_ce
    wp_simp_pre [U64MapStruct]
    by_cases hitems0 : w.items = 0#64
    · have hnil : map = [] := hinv.items_eq_zero_iff_nil.1 hitems0
      subst hnil
      wp_simp_pre [hitems0]
      wp_sym_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      exact close_ro_frame hpre (by ro_simp0) (by simp [wp_norm, arm64_norm])
    · have hctrl_len : w.ctrl.length = (bm.toNat + 1) + 8 := hinv.mirror.1
      have hslots_len : w.slots.length = bm.toNat + 1 := hinv.slots_len
      rcases hinv.exists_empty_probe_group k with ⟨step_end, _, hemp_end⟩
      wp_sym_steps 13
      apply SepWP.cfg_fixpoint_wf_cps (Label := Nat) (l0 := 0) (cut_pc := fun _ => _)
        (meas := fun step _ => step_end + 1 - step) (P_inv := fun _ _ => _)
        (Inv := fun step st => step ≤ step_end ∧ ProbeInvAt s0 w bm k step st) (post := fun _ => _)
      · wp_focus_close wp_norm_lhs
      · simp only [wp_norm, arm64_norm, hrun]
      · exact Entails.refl _
      · have hfx : k * 5871781006564002453#64 = k * fxSeed := rfl
        refine ⟨Nat.zero_le _, by ro_simp0, by simp only [wp_norm, arm64_norm, hx1],
          by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
          by simp only [wp_norm, arm64_norm],
          by simpa only [wp_norm, arm64_norm, hfx, fxHash, fxProd, triByteOff_zero, BitVec.add_zero]
               using probePos_bv_eq bm k 0,
          by simpa only [wp_norm, arm64_norm, hfx] using dup_lsr57_eq (k * fxSeed),
          by simp only [wp_norm, arm64_norm], fun _ hs => by omega⟩
      · intro step st hpc_st hrun_st ⟨hstep_le, hro, hx1_st, hx8_st, hx9_st, hx10_st, hx11_st,
          hv0_st, hv1_st, hprev⟩ ih_outer
        let pos := probePos bm k step
        let g := ctrlGroupWord w.ctrl pos
        have hpos_lt : pos < bm.toNat + 1 := probePos_lt_buckets hinv.validMask k step
        wp_sym_steps 1
        wp_conv_pre =>
          rw [pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
        set_option proofLib.wpBranchAutoDecide false in
        wp_sym_steps 5
        wp_conv_pre =>
          rw [← pointsToBytes_focus_ctrlGroupWord w.ctrlPtr w.ctrl (pos := pos) (by omega)]
        have hm_h2 := simd_cmeq_dup8_highMask g ((k * fxSeed) >>> 57)
        change (zipLanes 8 (g.zeroExtend 128) (dupByte8Vec ((k * fxSeed) >>> 57))
          (fun a b => if a == b then 0xff#128 else 0#128) 8).truncate 64 &&&
          0x8080808080808080#64 = highBitMaskOfBits (eqBits8 g (h2Tag k)) at hm_h2
        conv at hm_h2 => lhs; simp only [wp_norm, arm64_norm]
        rw [hm_h2]
        wp_if hbeq
        · have hb0 : eqBits8 g (h2Tag k) = 0#8 :=
            (highBitMaskOfBits_eq_zero_iff _).1 (by simpa using hbeq)
          have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k →
              (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
              (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag => by
            have hbit := (bv8_eq_zero_iff_forall _).1 hb0 j hj
            rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbit
            exact False.elim (hbit htag)
          wp_sym_steps 1
          have hall := simd_cmeq_allOnes8 g
          conv at hall => lhs; simp only [wp_norm, arm64_norm]
          rw [hall]
          wp_sym_steps 1
          have humax := simdUmaxv8_byteMaskOfBits (eqBits8 g tagEmpty)
          conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
          rw [humax]
          set_option proofLib.wpBranchAutoDecide false in
          wp_sym_steps 2
          wp_if htbnz
          · have hemp_ne : eqBits8 g tagEmpty ≠ 0#8 := fun hz => by rw [hz] at htbnz; simp at htbnz
            have hnone := probe_empty_miss_lookup hinv hemp_ne hprev hno_h2
            wp_sym_steps 2
            apply SepWP.done (by simp [wp_norm, arm64_norm, hro.2.1])
              (by simp [wp_norm, arm64_norm, hrun_st])
            exact close_ro_frame hpre (by ro_simp hro) (by simp [hnone, wp_norm, arm64_norm])
          · have hemp_eq : eqBits8 g tagEmpty = 0#8 :=
              Classical.byContradiction fun hne => htbnz (by simp only [hne, ↓reduceIte]; decide)
            have hlt_end := probe_nonempty_lt_end hinv hstep_le hemp_end hemp_eq
            wp_sym_steps 3
            apply ih_outer (step + 1) _ (by omega)
            · wp_focus_close wp_norm_lhs
            · simp only [wp_norm, arm64_norm, hrun_st]
            · refine ⟨by omega, by ro_simp hro, by simp only [wp_norm, arm64_norm, hx1_st],
                by simp only [wp_norm, arm64_norm, hx8_st],
                by simp only [wp_norm, arm64_norm, hx9_st],
                by simp only [wp_norm, arm64_norm]
                   rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
                by simpa only [wp_norm, arm64_norm, hx10_st] using
                     probePos_step_bv hinv.validMask k step,
                by simp only [wp_norm, arm64_norm, hv0_st],
                by simp only [wp_norm, arm64_norm, hv1_st], extend_probe_prev hprev hno_h2⟩
        · have hb0 : eqBits8 g (h2Tag k) ≠ 0#8 := fun hz => by
            rw [hz, highBitMaskOfBits_zero] at hbeq; simp at hbeq
          apply SepWP.cfg_fixpoint_wf_cps (Label := BitVec 8) (l0 := eqBits8 g (h2Tag k))
            (cut_pc := fun _ => _) (meas := fun b _ => b.toNat) (P_inv := fun _ _ => _)
            (Inv := fun b sti => ProbeInnerInv s0 w bm k step b sti) (post := fun _ => _)
          · wp_focus_close wp_norm_lhs
          · simp only [wp_norm, arm64_norm, hrun_st]
          · exact Entails.refl _
          · refine ⟨hb0, by ro_simp hro, by simp only [wp_norm, arm64_norm, hx1_st],
              by simp only [wp_norm, arm64_norm, hx8_st],
              by simp only [wp_norm, arm64_norm, hx9_st],
              by simp only [wp_norm, arm64_norm, hx10_st],
              by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
              by simp only [wp_norm, arm64_norm, hv0_st],
              by simp only [wp_norm, arm64_norm, hv1_st],
              by simp only [wp_norm, arm64_norm]; rfl,
              fun j hj hbit => by rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_iff_eq] at hbit; exact hbit,
              fun j hj htag hbf => by
                rw [getLsbD_eqBits8 g (h2Tag k) hj, beq_eq_false_iff_ne] at hbf
                exact False.elim (hbf htag)⟩
          · intro b sti hpc_i hrun_i ⟨hb, hro_i, hx1_i, hx8_i, hx9_i, hx10_i, hx11_i, hx12_i,
              hv0_i, hv1_i, hv2_i, hsub_b, hmiss_b⟩ ih_inner
            rcases bv8_ctz_spec hb with ⟨hj0_lt, hj0_bit, _⟩
            have hidx_lt : (pos + b.ctz.toNat) % (bm.toNat + 1) < w.slots.length := by
              rw [hslots_len]; exact Nat.mod_lt _ (by omega)
            have htag_j0 : getLane8 g b.ctz.toNat = h2Tag k := hsub_b b.ctz.toNat hj0_lt hj0_bit
            wp_sym_steps 5
            rw [ProofLib.reverseBits_eq_reverse, highBitMaskOfBits_lowestLane b,
              hinv.validMask.laneIdx_bv hpos_lt hj0_lt]
            wp_conv_pre => rw [slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
            set_option proofLib.wpBranchAutoDecide false in
            wp_sym_steps 3
            wp_if hkeq
            · have hlook : cliMapLookup k map =
                  some (w.slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx_lt).2 :=
                hinv.lookup_eq_some_of_lane_match hpos_lt hj0_lt htag_j0 hkeq.symm
              wp_sym_steps 2
              apply SepWP.done (by simp [wp_norm, arm64_norm, hro_i.2.1])
                (by simp [wp_norm, arm64_norm, hrun_i])
              exact close_ro_frame hpre (by ro_simp hro_i) (by simp [hlook, wp_norm, arm64_norm])
            · have hk_ne : (w.slots[(pos + b.ctz.toNat) % (bm.toNat + 1)]'hidx_lt).1 ≠ k :=
                Ne.symm hkeq
              wp_conv_pre => rw [← slotsDownFrom_focus_ldur w.ctrlPtr w.slots hidx_lt]
              set_option proofLib.wpBranchAutoDecide false in
              wp_sym_steps 3
              rw [highBitMaskOfBits_clear_lowest b]
              wp_if hbne
              · have hb' : (b - 1#8) &&& b ≠ 0#8 := fun hz => by
                  rw [hz, highBitMaskOfBits_zero] at hbne; simp at hbne
                apply ih_inner ((b - 1#8) &&& b) _ (bv8_clear_lowest_lt hb)
                · wp_focus_close wp_norm_lhs
                · simp only [wp_norm, arm64_norm, hrun_i]
                · refine ⟨hb', by ro_simp hro_i, by simp only [wp_norm, arm64_norm, hx1_i],
                    by simp only [wp_norm, arm64_norm, hx8_i],
                    by simp only [wp_norm, arm64_norm, hx9_i],
                    by simp only [wp_norm, arm64_norm, hx10_i],
                    by simp only [wp_norm, arm64_norm, hx11_i],
                    by simp only [wp_norm, arm64_norm],
                    by simp only [wp_norm, arm64_norm, hv0_i],
                    by simp only [wp_norm, arm64_norm, hv1_i],
                    by simp only [wp_norm, arm64_norm, hv2_i],
                    fun j hj hbit' => by
                      rw [bv8_getLsbD_clear_lowest b hj, Bool.and_eq_true] at hbit'
                      exact hsub_b j hj hbit'.1,
                    clear_lowest_miss hk_ne hmiss_b⟩
              · have hb'_zero : (b - 1#8) &&& b = 0#8 :=
                  (highBitMaskOfBits_eq_zero_iff _).1 hbne
                have hno_h2 : ∀ j < 8, getLane8 g j = h2Tag k →
                    (h : (pos + j) % (bm.toNat + 1) < w.slots.length) →
                    (w.slots[(pos + j) % (bm.toNat + 1)]'h).1 ≠ k := fun j hj htag hsl =>
                  clear_lowest_miss hk_ne hmiss_b j hj htag
                    ((bv8_eq_zero_iff_forall _).1 hb'_zero j hj) hsl
                wp_sym_steps 1
                have hall := simd_cmeq_allOnes8 g
                conv at hall => lhs; simp only [wp_norm, arm64_norm]
                rw [hall]
                wp_sym_steps 1
                have humax := simdUmaxv8_byteMaskOfBits (eqBits8 g tagEmpty)
                conv at humax => lhs; simp only [simdUmaxv8, wp_norm, arm64_norm]
                rw [humax]
                set_option proofLib.wpBranchAutoDecide false in
                wp_sym_steps 2
                wp_if htbnz
                · have hemp_ne : eqBits8 g tagEmpty ≠ 0#8 := fun hz => by
                    rw [hz] at htbnz; simp at htbnz
                  have hnone := probe_empty_miss_lookup hinv hemp_ne hprev hno_h2
                  wp_sym_steps 2
                  apply SepWP.done (by simp [wp_norm, arm64_norm, hro_i.2.1])
                    (by simp [wp_norm, arm64_norm, hrun_i])
                  exact close_ro_frame hpre (by ro_simp hro_i)
                    (by simp [hnone, wp_norm, arm64_norm])
                · have hemp_eq : eqBits8 g tagEmpty = 0#8 :=
                    Classical.byContradiction fun hne => htbnz (by simp only [hne, ↓reduceIte]; decide)
                  have hlt_end := probe_nonempty_lt_end hinv hstep_le hemp_end hemp_eq
                  wp_sym_steps 3
                  apply ih_outer (step + 1) _ (by omega)
                  · wp_focus_close wp_norm_lhs
                  · simp only [wp_norm, arm64_norm, hrun_i]
                  · refine ⟨by omega, by ro_simp hro_i, by simp only [wp_norm, arm64_norm, hx1_i],
                      by simp only [wp_norm, arm64_norm, hx8_i],
                      by simp only [wp_norm, arm64_norm, hx9_i],
                      by simp only [wp_norm, arm64_norm]
                         rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add],
                      by simpa only [wp_norm, arm64_norm, hx10_i, hx11_i] using
                           probePos_step_bv hinv.validMask k step,
                      by simp only [wp_norm, arm64_norm, hv0_i],
                      by simp only [wp_norm, arm64_norm, hv1_i],
                      extend_probe_prev hprev hno_h2⟩

theorem hashbrown_contains_key_withCodeInv_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg2 P).rebase P.pl2.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_contains_key")
      (withCodeInv A (hashbrownContainsKeySpec P.pl A)) :=
  subroutine_ok_withCodeInv_of_plain A (hashbrown_contains_key_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_contains_key_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_contains_key"
      (fun mpl => hashbrownContainsKeySpec (mplAsPl mpl) A) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_contains_key" 2 (off := 0)
    (fun P X' => hbProg2_rebase P X')
    (fun mpl => hashbrownContainsKeySpec (mplAsPl mpl) A) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_contains_key_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_contains_key_withCodeInv_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_contains_key"
      (fun mpl => withCodeInv A (hashbrownContainsKeySpec (mplAsPl mpl) A)) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_contains_key" 2 (off := 0)
    (fun P X' => hbProg2_rebase P X')
    (fun mpl => withCodeInv A (hashbrownContainsKeySpec (mplAsPl mpl) A)) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_contains_key_withCodeInv_ok P A X)

end MachineProofs

end CaseStudies.Hashbrown.Proofs
