/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.RehashInPlacePrep
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.LoopTactics
import ProofLib.BV.ReflectROBDD

/-!
# In-Place Tombstone Reclamation

Verifies the `rehash_in_place` path of `RawTable<(u64, u64)>::reserve_rehash` (`hbRehashInPlace_wp`),
reclaiming tombstones in place when `m.length + 1 ≤ bucketMaskToCapacity bm / 2`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown

/-! ## Dual-Slot Focus and Probe Helpers -/

private theorem drop_set_gt {α : Type} (xs : List α) {i j : Nat}
    (hij : i < j) (_hj : j < xs.length) (v : α) :
    (xs.set j v).drop (i + 1) = (xs.drop (i + 1)).set (j - (i + 1)) v := by
  apply List.ext_getElem (by simp)
  intro q hq1 _
  simp only [List.length_drop, List.length_set] at hq1
  rw [List.getElem_drop, List.getElem_set, List.getElem_set]
  by_cases hqj : j - (i + 1) = q
  · have hjeq : j = i + 1 + q := by omega
    simp [hjeq]
  · have hjne : j ≠ i + 1 + q := by omega
    simp [hqj, hjne, List.getElem_drop]

private theorem slotsDownFrom_focus2_lt (top : BitVec 64) (slots : List (BitVec 64 × BitVec 64))
    {i j : Nat} (hij : i < j) (hj : j < slots.length) :
    ∃ R : SepProp,
      slotsDownFrom top slots =
        slotPairAt (slotAddr top i) slots[i] ∗ (slotPairAt (slotAddr top j) slots[j] ∗ R) ∧
      ∀ kv_i kv_j : BitVec 64 × BitVec 64,
        slotPairAt (slotAddr top i) kv_i ∗ (slotPairAt (slotAddr top j) kv_j ∗ R) =
          slotsDownFrom top ((slots.set i kv_i).set j kv_j) := by
  let tail := slots.drop (i + 1)
  let d := j - (i + 1)
  have hi : i < slots.length := by omega
  have hd : d < tail.length := by simp [tail, d]; omega
  have haddr_d : slotAddr (slotAddr top i) d = slotAddr top j := by
    unfold slotAddr
    rw [show 16 * (j + 1) = 16 * (i + 1) + 16 * (d + 1) by dsimp only [d]; omega, BitVec.ofNat_add]
    bv_lin
  have hget_d : tail[d]'hd = slots[j]'hj := by
    simp only [tail, List.getElem_drop]; congr 1; dsimp only [d]; omega
  refine ⟨slotsDownFrom top (slots.take i) ∗
    (slotsDownFrom (slotAddr top i) (tail.take d) ∗ slotsDownFrom (slotAddr top j) (tail.drop (d + 1))), ?_, ?_⟩
  · rw [slotsDownFrom_focus top slots hi, slotsDownFrom_focus (slotAddr top i) tail hd, haddr_d, hget_d]
    ac_rfl
  · intro kv_i kv_j
    let s2 := (slots.set i kv_i).set j kv_j
    have hs2_i : i < s2.length := by simp [s2, hi]
    have hs2_get : s2[i]'hs2_i = kv_i := by
      dsimp only [s2]; rw [List.getElem_set_ne (by omega), List.getElem_set_self]
    have hs2_take : s2.take i = slots.take i := by
      dsimp only [s2]; rw [List.take_set_of_le (by omega), List.take_set_of_le (by omega)]
    have hs2_drop : s2.drop (i + 1) = tail.set d kv_j := by
      dsimp only [s2, tail, d]
      rw [drop_set_gt (slots.set i kv_i) hij (by simp [hj]) kv_j, List.drop_set_of_lt (by omega)]
    rw [slotsDownFrom_focus top s2 hs2_i, hs2_get, hs2_take, hs2_drop,
      ← slotsDownFrom_update (slotAddr top i) tail hd kv_j, haddr_d]
    ac_rfl

/-- Focus two distinct buckets `j ≠ i` simultaneously in `slotsDownFrom top slots`, with an
    update equation producing `(slots.set i kv_i).set j kv_j`. -/
theorem slotsDownFrom_focus2 (top : BitVec 64) (slots : List (BitVec 64 × BitVec 64))
    {i j : Nat} (hi : i < slots.length) (hj : j < slots.length) (hji : j ≠ i) :
    ∃ R : SepProp,
      slotsDownFrom top slots =
        slotPairAt (slotAddr top i) slots[i] ∗ (slotPairAt (slotAddr top j) slots[j] ∗ R) ∧
      ∀ kv_i kv_j : BitVec 64 × BitVec 64,
        slotPairAt (slotAddr top i) kv_i ∗ (slotPairAt (slotAddr top j) kv_j ∗ R) =
          slotsDownFrom top ((slots.set i kv_i).set j kv_j) := by
  by_cases hij : i < j
  · exact slotsDownFrom_focus2_lt top slots hij hj
  · rcases slotsDownFrom_focus2_lt top slots (by omega : j < i) hi with ⟨R, hfoc, hupd⟩
    refine ⟨R, hfoc.trans (by ac_rfl), fun kv_i kv_j => ?_⟩
    rw [show slotPairAt (slotAddr top i) kv_i ∗ (slotPairAt (slotAddr top j) kv_j ∗ R) =
          slotPairAt (slotAddr top j) kv_j ∗ (slotPairAt (slotAddr top i) kv_i ∗ R) by ac_rfl,
        hupd kv_j kv_i, List.set_comm kv_j kv_i hji]

private theorem all_lanes_full_of_mask_zero {bm : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    (h : RehashTableInv bm m ctrl slots) (k : BitVec 64) (s : Nat)
    (hz : byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm k s))) = 0#64) :
    ∀ j < 8, isFullTag (ctrl[(probePos bm k s + j) % (bm.toNat + 1)]'(by
      have := h.mirror.1
      have := @Nat.mod_lt (probePos bm k s + j) (bm.toNat + 1) (by omega)
      omega)) = true := by
  intro j hj
  have hb0 : specialBits8 (ctrlGroupWord ctrl (probePos bm k s)) = 0#8 :=
    (byteMaskOfBits_eq_zero_iff _).mp hz
  have hbit := (bv8_eq_zero_iff_forall _).mp hb0 j hj
  rw [getLsbD_specialBits8 _ hj,
    CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 (probePos_lt_buckets h.validMask k s) hj] at hbit
  rw [← not_special_iff_full, hbit]

private theorem mask_ne_zero_of_mem_empty {bm : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    (h : RehashTableInv bm m ctrl slots) (k : BitVec 64) (s : Nat)
    (hemp : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k s)) :
    byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm k s))) ≠ 0#64 := by
  intro hz
  have hlen := h.mirror.1
  have hpos := probePos_lt_buckets h.validMask k s
  rw [mem_ctrlGroupAt_iff (by omega)] at hemp
  rcases hemp with ⟨j, hj, hj_emp⟩
  rw [CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 hpos hj] at hj_emp
  have hfj := all_lanes_full_of_mask_zero h k s hz j hj
  rw [hj_emp, isFullTag_tagEmpty] at hfj; cases hfj

private theorem lowest_special_lane_facts {bm : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    (h : RehashTableInv bm m ctrl slots) (k : BitVec 64) (step : Nat)
    (hnz : byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm k step))) ≠ 0#64) :
    ∃ lane new_i : Nat, lane < 8 ∧ new_i < bm.toNat + 1 ∧
      (probePos bm k step + lane) % (bm.toNat + 1) = new_i ∧
      (byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm k step)))).reverse.clz >>> 3 =
        BitVec.ofNat 64 lane ∧
      ((BitVec.ofNat 64 (probePos bm k step) + BitVec.ofNat 64 lane) &&& bm) = BitVec.ofNat 64 new_i ∧
      ∀ (hc : new_i < ctrl.length), isSpecialTag (ctrl[new_i]'hc) = true := by
  let b := specialBits8 (ctrlGroupWord ctrl (probePos bm k step))
  have hb_ne : b ≠ 0#8 := fun hb0 => hnz ((byteMaskOfBits_eq_zero_iff b).mpr hb0)
  rcases bv8_ctz_spec hb_ne with ⟨hlane, hbit, _⟩
  refine ⟨b.ctz.toNat, (probePos bm k step + b.ctz.toNat) % (bm.toNat + 1),
    hlane, Nat.mod_lt _ (by omega), rfl, byteMaskOfBits_lowestLane b,
    h.validMask.laneIdx_bv (probePos_lt_buckets h.validMask k step) hlane, fun _ => ?_⟩
  dsimp only [b] at hbit
  rwa [getLsbD_specialBits8 _ hlane,
    CtrlMirrorInv.lane_eq_mod_of_ge8 h.mirror h.ge8 (probePos_lt_buckets h.validMask k step) hlane] at hbit

private theorem ge8_entry_bv_facts {bm : BitVec 64} (hbm : ValidBucketMask bm)
    (_hge8 : 8 ≤ bm.toNat + 1) (hdvd8 : (bm.toNat + 1) % 8 = 0) :
    let buckets := bm.toNat + 1
    bm + 1#64 = BitVec.ofNat 64 buckets ∧ (bm + 1#64) >>> 3 = BitVec.ofNat 64 (buckets / 8) ∧
    BitVec.ofNat 64 buckets &&& 7#64 = 0#64 ∧ buckets / 8 ≤ 2 ^ 55 := by
  intro buckets; rcases hbm.buckets_bounds_dvd with ⟨_, hb58, _⟩
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  have h55 : (2 ^ 58 : Nat) / 8 = 2 ^ 55 := by decide
  have hbm1 : bm + 1#64 = BitVec.ofNat 64 buckets := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (1 : Nat) % 2 ^ 64 = 1 by decide, Nat.mod_eq_of_lt (by omega)]
  have hsh : (bm + 1#64) >>> 3 = BitVec.ofNat 64 (buckets / 8) := by
    rw [hbm1]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, show 2 ^ 3 = 8 by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hand7 : BitVec.ofNat 64 buckets &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change (buckets &&& (2 ^ 3 - 1)) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, show 2 ^ 3 = 8 by decide, hdvd8]
  exact ⟨hbm1, hsh, hand7, by omega⟩

private theorem sepStore8_ctrl {ctrlPtr : BitVec 64} {ctrl : List (BitVec 8)} {idx : Nat}
    {tag : BitVec 8} {F : SepProp} (hi : idx < ctrl.length) :
    SepStore8 (ctrlPtr + BitVec.ofNat 64 idx) tag
      ((ctrlPtr ↦ₛ ctrl) ∗ F) ((ctrlPtr ↦ₛ ByteSlice.write8 ctrl idx tag) ∗ F) :=
  SepStore8.left (SepStore8.of_pointsToBytes_here _ ctrlPtr ctrl idx tag hi rfl)

private theorem length_write8 {ctrl : List (BitVec 8)} {idx : Nat} (tag : BitVec 8)
    (hi : idx < ctrl.length) : (ByteSlice.write8 ctrl idx tag).length = ctrl.length := by
  rw [ByteSlice.write8, ← ByteSlice.set_eq_write ctrl idx tag hi, List.length_set]

/-! ## Subcase `≥ 8` and Top-Level Proof -/

section MachineProofs
arm64_proof_prelude
set_option proofLib.wpBranchAutoDecide false

local macro "s_norm" : tactic =>
  `(tactic| simp (config := { zetaDelta := false }) only [wp_norm, arm64_norm])
local macro "s_norm" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { zetaDelta := false }) only [wp_norm, arm64_norm, $ts,*])

local macro "mut_simp" h:term : tactic =>
  `(tactic| simp (config := { zetaDelta := false }) (discharger := decide) only
      [mutFrame_setPC, mutFrame_advancePC, mutFrame_setPState,
       mutFrame_writeReg64, mutFrame_writeVReg128, $h:term])

private theorem setMem_setPC (s : State) (pc : BitVec 64) (m : Memory) :
    (s.setPC pc).setMem m = (s.setMem m).setPC pc := by cases s; rfl
private theorem setMem_advancePC (s : State) (m : Memory) :
    s.advancePC.setMem m = (s.setMem m).advancePC := by cases s; rfl
private theorem setMem_setPState (s : State) (p : PState) (m : Memory) :
    (s.setPState p).setMem m = (s.setMem m).setPState p := by cases s; rfl
private theorem setMem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (m : Memory) :
    (s.writeReg64 r v).setMem m = (s.setMem m).writeReg64 r v := by cases s; cases r <;> rfl
private theorem setMem_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) (m : Memory) :
    (s.writeVReg128 r v).setMem m = (s.setMem m).writeVReg128 r v := by cases s; rfl
private theorem setMem_setMem (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
private theorem setMem_self (s : State) : s.setMem s.mem = s := by cases s; rfl

private theorem mutFrame_via_mem {s1 s0 st : State} (_h0 : MutFrame s1 s0)
    (hp : st.mem.perm = s0.mem.perm) (hr : MutFrame s1 (st.setMem s0.mem)) : MutFrame s1 st :=
  (mutFrame_setMem s1 st s0.mem hp.symm).1 hr

local macro "mut_mem_simp" h0:term:max hp:term:max : tactic =>
  `(tactic| refine mutFrame_via_mem $h0:term (by s_norm [$hp:term])
      (by simp (config := { zetaDelta := false }) only [setMem_setPC, setMem_advancePC,
            setMem_setPState, setMem_writeReg64, setMem_writeVReg128, setMem_setMem, setMem_self]
          mut_simp $h0:term))

private def LoopRegs (ctrlPtr bm : BitVec 64) (s1 st : State) : Prop :=
  st.readReg64 .x0 = s1.readReg64 .x0 ∧ st.readReg64 (.gpr 9#5) = fxSeed ∧
  st.readReg64 (.gpr 10#5) = 0xff#64 ∧ st.readReg64 (.gpr 19#5) = ctrlPtr ∧
  st.readReg64 (.gpr 20#5) = s1.readReg64 (.gpr 20#5) ∧
  st.readReg64 (.gpr 22#5) = s1.readReg64 (.gpr 22#5) ∧ st.readReg64 (.gpr 23#5) = bm

private theorem loopRegs_setPC {ctrlPtr bm : BitVec 64} {s1 st : State} (pc : BitVec 64) :
    LoopRegs ctrlPtr bm s1 (st.setPC pc) ↔ LoopRegs ctrlPtr bm s1 st := Iff.rfl
private theorem loopRegs_advancePC {ctrlPtr bm : BitVec 64} {s1 st : State} :
    LoopRegs ctrlPtr bm s1 st.advancePC ↔ LoopRegs ctrlPtr bm s1 st := Iff.rfl
private theorem loopRegs_setPState {ctrlPtr bm : BitVec 64} {s1 st : State} (ps : PState) :
    LoopRegs ctrlPtr bm s1 (st.setPState ps) ↔ LoopRegs ctrlPtr bm s1 st := Iff.rfl
private theorem loopRegs_setMem {ctrlPtr bm : BitVec 64} {s1 st : State} (m : Memory) :
    LoopRegs ctrlPtr bm s1 (st.setMem m) ↔ LoopRegs ctrlPtr bm s1 st := Iff.rfl
private theorem loopRegs_writeVReg128 {ctrlPtr bm : BitVec 64} {s1 st : State} (v : BitVec 5) (val : BitVec 128) :
    LoopRegs ctrlPtr bm s1 (st.writeVReg128 v val) ↔ LoopRegs ctrlPtr bm s1 st := Iff.rfl
private theorem loopRegs_writeReg64 {ctrlPtr bm : BitVec 64} {s1 st : State}
    (idx : BitVec 5) (val : BitVec 64)
    (h0 : idx ≠ 0#5 := by decide) (h9 : idx ≠ 9#5 := by decide) (h10 : idx ≠ 10#5 := by decide)
    (h19 : idx ≠ 19#5 := by decide) (h20 : idx ≠ 20#5 := by decide)
    (h22 : idx ≠ 22#5 := by decide) (h23 : idx ≠ 23#5 := by decide) :
    LoopRegs ctrlPtr bm s1 (st.writeReg64 (.gpr idx) val) ↔ LoopRegs ctrlPtr bm s1 st := by
  have ne0 : Reg.x0 ≠ Reg.gpr idx := fun h => by cases h; exact h0 rfl
  have ne (r : BitVec 5) (hne : idx ≠ r) : Reg.gpr r ≠ Reg.gpr idx := fun h => by cases h; exact hne rfl
  unfold LoopRegs
  simp only [State.readReg64_writeReg64_ne _ _ _ _ ne0, State.readReg64_writeReg64_ne _ _ _ _ (ne _ h9),
    State.readReg64_writeReg64_ne _ _ _ _ (ne _ h10), State.readReg64_writeReg64_ne _ _ _ _ (ne _ h19),
    State.readReg64_writeReg64_ne _ _ _ _ (ne _ h20), State.readReg64_writeReg64_ne _ _ _ _ (ne _ h22),
    State.readReg64_writeReg64_ne _ _ _ _ (ne _ h23)]

local macro "lregs_simp" h:term : tactic =>
  `(tactic| simp (config := { zetaDelta := false }) (discharger := decide) only
      [loopRegs_setPC, loopRegs_advancePC, loopRegs_setPState,
       loopRegs_setMem, loopRegs_writeVReg128, loopRegs_writeReg64, $h:term])

private theorem setWidth64_zeroExtend128_eq (x : BitVec 64) :
    BitVec.setWidth 64 (BitVec.zeroExtend 128 x) = x := by bv_robdd

private theorem hbRehash_probe_stride_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr bm k : BitVec 64} {m : Map64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {endStep : Nat} {s1 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : RehashTableInv bm m ctrl slots) (hend : endStep < numGroups bm)
    (hemp_end : tagEmpty ∈ ctrlGroupAt ctrl (probePos bm k endStep)) :
    ∀ (fuel : Nat) {step : Nat} {st : State}, fuel = endStep - step → step < endStep →
      (∀ s' < step + 1, ∀ j < 8, isFullTag (ctrl[(probePos bm k s' + j) % (bm.toNat + 1)]'(by
        have := h.mirror.1; have := @Nat.mod_lt (probePos bm k s' + j) (bm.toNat + 1) (by omega); omega)) = true) →
      st.pc = P.pl.base + 384#64 → st.status = .Running → MutFrame s1 st → LoopRegs ctrlPtr bm s1 st →
      st.readReg64 (.gpr 15#5) = BitVec.ofNat 64 (probePos bm k step) →
      st.readReg64 (.gpr 16#5) = BitVec.ofNat 64 (8 * step) + 8#64 →
      (∀ (step' : Nat) (st' : State), step' < numGroups bm →
        byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm k step'))) ≠ 0#64 →
        (∀ s' < step', ∀ j < 8, isFullTag (ctrl[(probePos bm k s' + j) % (bm.toNat + 1)]'(by
          have := h.mirror.1; have := @Nat.mod_lt (probePos bm k s' + j) (bm.toNat + 1) (by omega); omega)) = true) →
        st'.pc = P.pl.base + 248#64 → st'.status = .Running → MutFrame s1 st' → LoopRegs ctrlPtr bm s1 st' →
        st'.readReg64 (.gpr 8#5) = st.readReg64 (.gpr 8#5) → st'.readReg64 (.gpr 11#5) = st.readReg64 (.gpr 11#5) →
        st'.readReg64 (.gpr 12#5) = st.readReg64 (.gpr 12#5) → st'.readReg64 (.gpr 13#5) = st.readReg64 (.gpr 13#5) →
        st'.readReg64 (.gpr 14#5) = st.readReg64 (.gpr 14#5) →
        st'.readReg64 (.gpr 15#5) = BitVec.ofNat 64 (probePos bm k step') →
        st'.readReg64 (.gpr 17#5) = byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm k step'))) →
        SepWP ((hbProg P).rebase P.pl.base X) target_pc st' ((ctrlPtr ↦ₛ ctrl) ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st ((ctrlPtr ↦ₛ ctrl) ∗ F) post oom := by
  intro fuel; induction fuel with
  | zero => intro step st hfuel hlt; omega
  | succ fuel ih =>
    intro step st hfuel hlt hprev hpc hrun hmut hlregs hx15 hx16 hcont
    have hP := P.placeable
    have hx19 : st.readReg64 (.gpr 19#5) = ctrlPtr := hlregs.2.2.2.1
    have hx23 : st.readReg64 (.gpr 23#5) = bm := hlregs.2.2.2.2.2.2
    have hpos_next_lt := probePos_lt_buckets h.validMask k (step + 1)
    have hstep_bv := probePos_step_bv h.validMask k step
    conv at hstep_bv => lhs; simp only [wp_norm, arm64_norm]
    let g_next := ctrlGroupWord ctrl (probePos bm k (step + 1))
    have hcmlt := simd_cmlt_zero8 g_next
    conv at hcmlt => lhs; simp only [wp_norm, arm64_norm]
    wp_sym_steps 3
    wp_conv_pre =>
      rw [pointsToBytes_focus_ctrlGroupWord ctrlPtr ctrl (pos := probePos bm k (step + 1))
            (by have := h.mirror.1; omega), sepConj_assoc]
    wp_sym_steps 2; rw [hcmlt]; wp_sym_steps 1; rw [setWidth64_zeroExtend128_eq]
    wp_conv_pre =>
      rw [← sepConj_assoc,
          ← pointsToBytes_focus_ctrlGroupWord ctrlPtr ctrl (pos := probePos bm k (step + 1))
              (by have := h.mirror.1; omega)]
    wp_sym_steps 1; wp_if hnz
    · exact hcont (step + 1) _ (by omega) (by simpa only [bne_iff_ne, ne_eq, beq_iff_eq] using hnz) hprev
        (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs)
        (by s_norm) (by s_norm) (by s_norm) (by s_norm) (by s_norm) (by s_norm) (by s_norm; rfl)
    · have hmask_z : byteMaskOfBits (specialBits8 g_next) = 0#64 := by
        simpa only [bne_iff_ne, ne_eq, Decidable.not_not, beq_iff_eq] using hnz
      have hne_end : step + 1 ≠ endStep := fun heq => by
        dsimp only [g_next] at hmask_z; rw [heq] at hmask_z
        exact mask_ne_zero_of_mem_empty h k endStep hemp_end hmask_z
      have hprev' : ∀ s' < step + 2, ∀ j < 8,
          isFullTag (ctrl[(probePos bm k s' + j) % (bm.toNat + 1)]'(by
            have := h.mirror.1
            have := @Nat.mod_lt (probePos bm k s' + j) (bm.toNat + 1) (by omega)
            omega)) = true := fun s' hs' j hj => by
        by_cases hs1 : s' < step + 1
        · exact hprev s' hs1 j hj
        · have heq : s' = step + 1 := by omega
          subst heq; exact all_lanes_full_of_mask_zero h k (step + 1) hmask_z j hj
      wp_sym_steps 1
      refine ih (step := step + 1) (by omega) (by omega) hprev'
        (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs) (by s_norm)
        (by s_norm; rw [show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add]; bv_lin) ?_
      intro step' st' hs' hmnz hpr' hpc' hrun' hmut' hlr' r8 r11 r12 r13 r14 r15 r17
      exact hcont step' st' hs' hmnz hpr' hpc' hrun' hmut' hlr'
        (r8.trans (by s_norm)) (r11.trans (by s_norm)) (r12.trans (by s_norm))
        (r13.trans (by s_norm)) (r14.trans (by s_norm)) r15 r17

private theorem extractLsb'_pair_lo (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
private theorem extractLsb'_pair_hi (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

private theorem slotAddr_sub_lsl4_sub16' (ctrlPtr : BitVec 64) (idx : Nat) :
    (ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) - 16#64 = slotAddr ctrlPtr idx := by
  rw [show (ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) - 16#64 =
        (ctrlPtr - (BitVec.ofNat 64 idx <<< 4)) + 0xfffffffffffffff0#64 by bv_lin]
  exact slotAddr_sub_lsl4_sub16 ctrlPtr idx

private theorem toNat_lt_eight_of_ult {x : BitVec 64} (h : x.ult 8#64 = true) : x.toNat < 8 := by
  simpa [BitVec.ult] using h
private theorem not_toNat_lt_eight_of_not_ult {x : BitVec 64} (h : ¬ x.ult 8#64 = true) : ¬ x.toNat < 8 := by
  simpa [BitVec.ult] using h
private theorem false_of_special_getLsbD7 {t : BitVec 8}
    (ht : ValidTag t) (hs : isSpecialTag t = true) (hb : t.getLsbD 7 = false) : False := by
  rcases ValidTag.special_cases ht hs with rfl | rfl <;> revert hb <;> decide

private theorem hbRehash_not_same_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr bm : BitVec 64} {m : Map64} {i step lane new_i : Nat}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {s1 stN : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < bm.toNat + 1) (h : RehashTableInv bm m ctrl slots) {hi_sl : i < slots.length}
    (hnew : new_i < bm.toNat + 1) (hne_i : new_i ≠ i) (hlane : lane < 8)
    (hidx_new : (probePos bm (slots[i]'hi_sl).1 step + lane) % (bm.toNat + 1) = new_i)
    {hnew_ctrl : new_i < ctrl.length} (hspec_ni : isSpecialTag (ctrl[new_i]'hnew_ctrl) = true)
    (hdel_i : ctrl[i]'(by have := h.mirror.1; omega) = tagDeleted)
    (hpfx : ∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hstep : step < numGroups bm)
    (hprev : ∀ s' < step, ∀ j < 8, isFullTag (ctrl[(probePos bm (slots[i]'hi_sl).1 s' + j) % (bm.toNat + 1)]'(by
      have := h.mirror.1; have := @Nat.mod_lt (probePos bm (slots[i]'hi_sl).1 s' + j) (bm.toNat + 1) (by omega); omega)) = true)
    (hpcN : stN.pc = P.pl.base + 296#64) (hrunN : stN.status = .Running)
    (hmutN : MutFrame s1 stN) (hlrN : LoopRegs ctrlPtr bm s1 stN)
    (r8 : stN.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i) (r11 : stN.readReg64 (.gpr 11#5) = slotAddr ctrlPtr i)
    (r12 : stN.readReg64 (.gpr 12#5) = ctrlPtr - (BitVec.ofNat 64 i <<< 4))
    (r13 : stN.readReg64 (.gpr 13#5) = fxProd (slots[i]'hi_sl).1)
    (r15 : stN.readReg64 (.gpr 15#5) = BitVec.ofNat 64 new_i)
    (hcont : ∀ (ctrl' : List (BitVec 8)) (slots' : List (BitVec 64 × BitVec 64)) (st' : State),
      (h' : RehashTableInv bm m ctrl' slots') →
      (∀ (q : Nat) (hq : q < i + 1), ctrl'[q]'(by have := h'.mirror.1; omega) ≠ tagDeleted) →
      st'.pc = P.pl.base + 468#64 → st'.status = .Running → MutFrame s1 st' →
      LoopRegs ctrlPtr bm s1 st' → st'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
        ((ctrlPtr ↦ₛ ctrl') ∗ slotsDownFrom ctrlPtr slots' ∗ F) post oom)
    (hrec : ∀ (ctrl1 : List (BitVec 8)) (slots1 : List (BitVec 64 × BitVec 64)) (st1 : State),
      countDeletedTags bm ctrl1 < countDeletedTags bm ctrl → (h1 : RehashTableInv bm m ctrl1 slots1) →
      ctrl1[i]'(by have := h1.mirror.1; omega) = tagDeleted →
      (∀ (q : Nat) (hq : q < i), ctrl1[q]'(by have := h1.mirror.1; omega) ≠ tagDeleted) →
      st1.pc = P.pl.base + 212#64 → st1.status = .Running → MutFrame s1 st1 →
      LoopRegs ctrlPtr bm s1 st1 → st1.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      st1.readReg64 (.gpr 11#5) = slotAddr ctrlPtr i →
      st1.readReg64 (.gpr 12#5) = ctrlPtr - (BitVec.ofNat 64 i <<< 4) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st1
        ((ctrlPtr ↦ₛ ctrl1) ∗ slotsDownFrom ctrlPtr slots1 ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) target_pc stN
      ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom := by
  have hP := P.placeable
  have hx10N : stN.readReg64 (.gpr 10#5) = 0xff#64 := hlrN.2.2.1
  have hx19N : stN.readReg64 (.gpr 19#5) = ctrlPtr := hlrN.2.2.2.1
  have hx23N : stN.readReg64 (.gpr 23#5) = bm := hlrN.2.2.2.2.2.2
  have hnew_sl : new_i < slots.length := by have := h.slots_len; omega
  have hmir_i : setCtrlMirrorIdx bm i < (bm.toNat + 1) + 8 := by
    rw [setCtrlMirrorIdx_ge8 h.validMask h.ge8 hi]; split <;> omega
  have hmir_new : setCtrlMirrorIdx bm new_i < (bm.toNat + 1) + 8 := by
    rw [setCtrlMirrorIdx_ge8 h.validMask h.ge8 hnew]; split <;> omega
  have hmir_new_ctrl : setCtrlMirrorIdx bm new_i < ctrl.length := by have := h.mirror.1; omega
  let kv_i := slots[i]'hi_sl; let k := kv_i.1
  have hold_cases : ctrl[new_i]'hnew_ctrl = tagEmpty ∨ ctrl[new_i]'hnew_ctrl = tagDeleted :=
    ValidTag.special_cases (h.mirror.2.1 _ (List.getElem_mem _)) hspec_ni
  wp_conv_pre => rw [pointsToBytes_focus8_getElem ctrlPtr ctrl (off := new_i) hnew_ctrl]
  wp_sym_steps 1
  wp_conv_pre => rw [← pointsToBytes_focus8_getElem ctrlPtr ctrl (off := new_i) hnew_ctrl]
  wp_sym_steps 4
  refine step_str8_perm (pc := P.pl.base + 316#64) (ea := ctrlPtr + BitVec.ofNat 64 new_i) (wb := none) (val := h2Tag k)
    rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm [hx19N, r15])
    (by dsimp only [h2Tag, k, kv_i]; s_norm [r13]) (sepStore8_ctrl hnew_ctrl) fun m1 hm1 => ?_
  dsimp only [applyWriteback]; rw [show P.pl.base + 316#64 + 4#64 = P.pl.base + 320#64 by bv_lin]
  have hp_m1 : m1.perm = stN.mem.perm := by simpa using hm1
  wp_sym_steps 3
  (try rw [slotAddr_sub_lsl4_sub16' ctrlPtr new_i]); (try rw [slotAddr_sub_lsl4_sub16 ctrlPtr new_i])
  refine step_str8_perm (pc := P.pl.base + 332#64)
    (ea := ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm new_i)) (wb := none) (val := h2Tag k)
    rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl
    (by s_norm [hx19N, hx23N, r15]; exact congrArg (·, none) (setCtrlMirror_addr_eq ctrlPtr bm h.validMask))
    (by dsimp only [h2Tag, k, kv_i]; s_norm [r13])
    (sepStore8_ctrl (by rw [length_write8 _ hnew_ctrl]; exact hmir_new_ctrl)) fun m2 hm2 => ?_
  dsimp only [applyWriteback]; rw [show P.pl.base + 332#64 + 4#64 = P.pl.base + 336#64 by bv_lin]
  have hp_m2 : m2.perm = stN.mem.perm := (by simpa using hm2 : m2.perm = m1.perm).trans hp_m1
  rw [write8_write8_eq_setCtrlBytes bm ctrl (h2Tag k) hnew_ctrl hmir_new_ctrl]
  let ctrl1 := setCtrlBytes bm ctrl new_i (h2Tag k)
  wp_conv_pre => change (ctrlPtr ↦ₛ ctrl1) ∗ slotsDownFrom ctrlPtr slots ∗ F
  have hctrl1_len : ctrl1.length = (bm.toNat + 1) + 8 := by
    dsimp only [ctrl1]; rw [setCtrlBytes_length]; exact h.mirror.1
  have hi_ctrl1 : i < ctrl1.length := by omega
  have hmir_i_ctrl1 : setCtrlMirrorIdx bm i < ctrl1.length := by omega
  rcases slotsDownFrom_focus2 ctrlPtr slots (i := i) (j := new_i) hi_sl hnew_sl hne_i with ⟨R_sl, hfoc2, hupd2⟩
  let kv_new := slots[new_i]'hnew_sl
  wp_sym_steps 1; wp_if heq_emp
  · have hemp_new : ctrl[new_i]'hnew_ctrl = tagEmpty := hold_cases.elim id fun hD => by
      exfalso; simp [hD, tagDeleted] at heq_emp
    wp_sym_steps 1
    refine step_str8_perm (pc := P.pl.base + 512#64) (ea := ctrlPtr + BitVec.ofNat 64 i) (wb := none) (val := tagEmpty)
      rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm [hx19N, r8])
      (by dsimp only [tagEmpty]; s_norm [hx10N]) (sepStore8_ctrl hi_ctrl1) fun m3 hm3 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 512#64 + 4#64 = P.pl.base + 516#64 by bv_lin]
    have hp_m3 : m3.perm = stN.mem.perm := (by simpa using hm3 : m3.perm = m2.perm).trans hp_m2
    wp_sym_steps 2
    refine step_str8_perm (pc := P.pl.base + 524#64)
      (ea := ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm i)) (wb := none) (val := tagEmpty)
      rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl
      (by s_norm [hx19N, hx23N, r8]; exact congrArg (·, none) (setCtrlMirror_addr_eq ctrlPtr bm h.validMask))
      (by dsimp only [tagEmpty]; s_norm [hx10N])
      (sepStore8_ctrl (by rw [length_write8 _ hi_ctrl1]; exact hmir_i_ctrl1)) fun m4 hm4 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 524#64 + 4#64 = P.pl.base + 528#64 by bv_lin]
    have hp_m4 : m4.perm = stN.mem.perm := (by simpa using hm4 : m4.perm = m3.perm).trans hp_m3
    rw [write8_write8_eq_setCtrlBytes bm ctrl1 tagEmpty hi_ctrl1 hmir_i_ctrl1]
    let ctrl2 := setCtrlBytes bm ctrl1 i tagEmpty
    wp_conv_pre => rw [hfoc2]; dsimp only [slotPairAt]
    wp_sym_steps 1
    refine step_strSimd128_perm (pc := P.pl.base + 532#64)
      (ea := slotAddr ctrlPtr new_i) (ea2 := slotAddr ctrlPtr new_i + 8#64) (wb := none) (v1 := kv_i.1) (v2 := kv_i.2)
      rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm [hx19N, r15]) rfl
      (by dsimp only [kv_i]; s_norm [r11, extractLsb'_pair_lo]) (by dsimp only [kv_i]; s_norm [r11, extractLsb'_pair_hi])
      (.right (.left (.right (.left (.left (.here rfl))))))
      (.right (.left (.right (.left (.right (.here rfl)))))) fun m5 hm5 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 532#64 + 4#64 = P.pl.base + 536#64 by bv_lin]
    have hp_m5 : m5.perm = stN.mem.perm := (by simpa using hm5 : m5.perm = m4.perm).trans hp_m4
    wp_conv_pre =>
      change (ctrlPtr ↦ₛ ctrl2) ∗
        (slotPairAt (slotAddr ctrlPtr i) kv_i ∗ (slotPairAt (slotAddr ctrlPtr new_i) kv_i ∗ R_sl)) ∗ F
      rw [hupd2 kv_i kv_i]; dsimp only [kv_i]; rw [List.set_getElem_self]
    wp_sym_steps 1
    rcases h.move_to_empty hi hnew hne_i hdel_i hemp_new hpfx hstep hlane hidx_new hprev with ⟨hinv2, hpfx2⟩
    refine hcont ctrl2 (slots.set new_i kv_i) _ hinv2 hpfx2 ?_ ?_ ?_ ?_ ?_
    (· rfl); (· s_norm [hrunN]); (· mut_mem_simp hmutN hp_m5); (· lregs_simp hlrN); (· s_norm [r8])
  ·
    have hdel_new : ctrl[new_i]'hnew_ctrl = tagDeleted := hold_cases.elim
      (fun hE => by exfalso; simp [hE, tagEmpty] at heq_emp) id
    wp_conv_pre => rw [hfoc2]; dsimp only [slotPairAt]
    wp_sym_steps 2
    refine step_str64_perm (pc := P.pl.base + 348#64)
      (ea := slotAddr ctrlPtr i) (wb := none) (val := kv_new.1)
      rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm [r11]) (by dsimp only [kv_new]; s_norm)
      (.right (.left (.left (.left (.here rfl))))) fun m3 hm3 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 348#64 + 4#64 = P.pl.base + 352#64 by bv_lin]
    have hp_m3 : m3.perm = stN.mem.perm := (by simpa using hm3 : m3.perm = m2.perm).trans hp_m2
    refine step_str64_perm (pc := P.pl.base + 352#64)
      (ea := slotAddr ctrlPtr new_i) (wb := none) (val := kv_i.1)
      (by s_norm) (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm) (by dsimp only [kv_i]; s_norm)
      (.right (.left (.right (.left (.left (.here rfl)))))) fun m4 hm4 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 352#64 + 4#64 = P.pl.base + 356#64 by bv_lin]
    have hp_m4 : m4.perm = stN.mem.perm := (by simpa using hm4 : m4.perm = m3.perm).trans hp_m3
    wp_sym_steps 2
    refine step_str64_perm (pc := P.pl.base + 364#64)
      (ea := slotAddr ctrlPtr i + 8#64) (wb := none) (val := kv_new.2)
      rfl (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm [r11]) (by dsimp only [kv_new]; s_norm)
      (.right (.left (.left (.right (.here rfl))))) fun m5 hm5 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 364#64 + 4#64 = P.pl.base + 368#64 by bv_lin]
    have hp_m5 : m5.perm = stN.mem.perm := (by simpa using hm5 : m5.perm = m4.perm).trans hp_m4
    refine step_str64_perm (pc := P.pl.base + 368#64)
      (ea := slotAddr ctrlPtr new_i + 8#64) (wb := none) (val := kv_i.2)
      (by s_norm) (by s_norm [hrunN]) (by s_norm; rfl) rfl (by s_norm) (by dsimp only [kv_i]; s_norm)
      (.right (.left (.right (.left (.right (.here rfl)))))) fun m6 hm6 => ?_
    dsimp only [applyWriteback]; rw [show P.pl.base + 368#64 + 4#64 = P.pl.base + 372#64 by bv_lin]
    have hp_m6 : m6.perm = stN.mem.perm := (by simpa using hm6 : m6.perm = m5.perm).trans hp_m5
    wp_conv_pre =>
      change (ctrlPtr ↦ₛ ctrl1) ∗
        (slotPairAt (slotAddr ctrlPtr i) kv_new ∗ (slotPairAt (slotAddr ctrlPtr new_i) kv_i ∗ R_sl)) ∗ F
      rw [hupd2 kv_new kv_i]
    wp_sym_steps 1
    rcases h.swap_deleted hi hnew hne_i hdel_i hdel_new hpfx hstep hlane hidx_new hprev with
      ⟨hinv1, hdel1_i, hpfx1, hdec⟩
    refine hrec ctrl1 ((slots.set i kv_new).set new_i kv_i) _ hdec hinv1 hdel1_i hpfx1
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (· rfl); (· s_norm [hrunN]); (· mut_mem_simp hmutN hp_m6); (· lregs_simp hlrN)
    (· s_norm [r8]); (· s_norm [r11]); (· s_norm [r12])

private theorem hbRehash_inner_join_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr bm : BitVec 64} {m : Map64} {i step : Nat}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {s1 stJ : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < bm.toNat + 1) (h : RehashTableInv bm m ctrl slots) {hi_sl : i < slots.length}
    (hdel_i : ctrl[i]'(by have := h.mirror.1; omega) = tagDeleted)
    (hpfx : ∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hstep : step < numGroups bm)
    (hmnz : byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm (slots[i]'hi_sl).1 step))) ≠ 0#64)
    (hprev : ∀ s' < step, ∀ j < 8, isFullTag (ctrl[(probePos bm (slots[i]'hi_sl).1 s' + j) % (bm.toNat + 1)]'(by
      have := h.mirror.1; have := @Nat.mod_lt (probePos bm (slots[i]'hi_sl).1 s' + j) (bm.toNat + 1) (by omega); omega)) = true)
    (hpcJ : stJ.pc = P.pl.base + 248#64) (hrunJ : stJ.status = .Running)
    (hmutJ : MutFrame s1 stJ) (hlrJ : LoopRegs ctrlPtr bm s1 stJ)
    (r8 : stJ.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i) (r11 : stJ.readReg64 (.gpr 11#5) = slotAddr ctrlPtr i)
    (r12 : stJ.readReg64 (.gpr 12#5) = ctrlPtr - (BitVec.ofNat 64 i <<< 4))
    (r13 : stJ.readReg64 (.gpr 13#5) = fxProd (slots[i]'hi_sl).1)
    (r14 : stJ.readReg64 (.gpr 14#5) = BitVec.ofNat 64 (probePos bm (slots[i]'hi_sl).1 0))
    (r15 : stJ.readReg64 (.gpr 15#5) = BitVec.ofNat 64 (probePos bm (slots[i]'hi_sl).1 step))
    (r17 : stJ.readReg64 (.gpr 17#5) = byteMaskOfBits (specialBits8 (ctrlGroupWord ctrl (probePos bm (slots[i]'hi_sl).1 step))))
    (hcont : ∀ (ctrl' : List (BitVec 8)) (slots' : List (BitVec 64 × BitVec 64)) (st' : State),
      (h' : RehashTableInv bm m ctrl' slots') →
      (∀ (q : Nat) (hq : q < i + 1), ctrl'[q]'(by have := h'.mirror.1; omega) ≠ tagDeleted) →
      st'.pc = P.pl.base + 468#64 → st'.status = .Running → MutFrame s1 st' →
      LoopRegs ctrlPtr bm s1 st' → st'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
        ((ctrlPtr ↦ₛ ctrl') ∗ slotsDownFrom ctrlPtr slots' ∗ F) post oom)
    (hrec : ∀ (ctrl1 : List (BitVec 8)) (slots1 : List (BitVec 64 × BitVec 64)) (st1 : State),
      countDeletedTags bm ctrl1 < countDeletedTags bm ctrl → (h1 : RehashTableInv bm m ctrl1 slots1) →
      ctrl1[i]'(by have := h1.mirror.1; omega) = tagDeleted →
      (∀ (q : Nat) (hq : q < i), ctrl1[q]'(by have := h1.mirror.1; omega) ≠ tagDeleted) →
      st1.pc = P.pl.base + 212#64 → st1.status = .Running → MutFrame s1 st1 →
      LoopRegs ctrlPtr bm s1 st1 → st1.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      st1.readReg64 (.gpr 11#5) = slotAddr ctrlPtr i →
      st1.readReg64 (.gpr 12#5) = ctrlPtr - (BitVec.ofNat 64 i <<< 4) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st1
        ((ctrlPtr ↦ₛ ctrl1) ∗ slotsDownFrom ctrlPtr slots1 ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) target_pc stJ
      ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom := by
  have hP := P.placeable
  have hx19J : stJ.readReg64 (.gpr 19#5) = ctrlPtr := hlrJ.2.2.2.1
  have hx23J : stJ.readReg64 (.gpr 23#5) = bm := hlrJ.2.2.2.2.2.2
  have hi_ctrl : i < ctrl.length := by have := h.mirror.1; omega
  have hmir_i : setCtrlMirrorIdx bm i < (bm.toNat + 1) + 8 := by
    rw [setCtrlMirrorIdx_ge8 h.validMask h.ge8 hi]; split <;> omega
  have hmir_i_ctrl : setCtrlMirrorIdx bm i < ctrl.length := by have := h.mirror.1; omega
  rcases lowest_special_lane_facts h (slots[i]'hi_sl).1 step hmnz with
    ⟨lane, new_i, hlane, hnew, hnew_eq, hlow_bv, hlane_bv, hspec_fn⟩
  have hnew_ctrl : new_i < ctrl.length := by have := h.mirror.1; omega
  have hspec_ni : isSpecialTag (ctrl[new_i]'hnew_ctrl) = true := hspec_fn hnew_ctrl
  wp_sym_steps 4; rw [ProofLib.reverseBits_eq_reverse, hlow_bv, hlane_bv]
  wp_conv_pre => rw [pointsToBytes_focus8_getElem ctrlPtr ctrl (off := new_i) hnew_ctrl]
  wp_sym_steps 2
  wp_conv_pre => rw [← pointsToBytes_focus8_getElem ctrlPtr ctrl (off := new_i) hnew_ctrl]
  wp_if htbz
  · exact False.elim (false_of_special_getLsbD7 (h.mirror.2.1 _ (List.getElem_mem _)) hspec_ni htbz)
  · wp_sym_steps 6; wp_if hsame_br
    · have hsame_lt := toNat_lt_eight_of_ult hsame_br; rw [← hnew_eq] at hsame_lt
      rcases exists_lane_of_sameGroup h.validMask h.ge8 h.dvd8 hlane hi hsame_lt with ⟨lane_i, hlane_i, hidx_i⟩
      wp_sym_steps 3
      refine step_str8_perm (pc := P.pl.base + 456#64)
        (ea := ctrlPtr + BitVec.ofNat 64 i) (wb := none) (val := h2Tag (slots[i]'hi_sl).1)
        rfl (by s_norm [hrunJ]) (by s_norm; rfl) rfl (by s_norm [hx19J, r8])
        (by dsimp only [h2Tag]; s_norm) (sepStore8_ctrl hi_ctrl) fun m1 hm1 => ?_
      dsimp only [applyWriteback]; rw [show P.pl.base + 456#64 + 4#64 = P.pl.base + 460#64 by bv_lin]
      have hp_m1 : m1.perm = stJ.mem.perm := by simpa using hm1
      wp_sym_steps 1
      refine step_str8_perm (pc := P.pl.base + 464#64)
        (ea := ctrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm i)) (wb := none) (val := h2Tag (slots[i]'hi_sl).1)
        rfl (by s_norm [hrunJ]) (by s_norm; rfl) rfl
        (by s_norm; exact congrArg (·, none) (setCtrlMirror_addr_eq ctrlPtr bm h.validMask))
        (by dsimp only [h2Tag]; s_norm)
        (sepStore8_ctrl (by rw [length_write8 _ hi_ctrl]; exact hmir_i_ctrl)) fun m2 hm2 => ?_
      dsimp only [applyWriteback]; rw [show P.pl.base + 464#64 + 4#64 = P.pl.base + 468#64 by bv_lin]
      have hp_m2 : m2.perm = stJ.mem.perm := (by simpa using hm2 : m2.perm = m1.perm).trans hp_m1
      rw [write8_write8_eq_setCtrlBytes bm ctrl (h2Tag (slots[i]'hi_sl).1) hi_ctrl hmir_i_ctrl]
      rcases h.place_same hi hdel_i hpfx hstep hlane_i hidx_i hprev with ⟨hinv', hpfx'⟩
      refine hcont _ slots _ hinv' hpfx' ?_ ?_ ?_ ?_ ?_
      (· s_norm); (· s_norm [hrunJ]); (· mut_mem_simp hmutJ hp_m2); (· lregs_simp hlrJ); (· s_norm [r8])
    · exact hbRehash_not_same_wp P X hi h (hi_sl := hi_sl) hnew
        (ne_of_not_sameGroup (not_toNat_lt_eight_of_not_ult hsame_br)) hlane hnew_eq
        (hnew_ctrl := hnew_ctrl) hspec_ni hdel_i hpfx hstep hprev
        (by s_norm) (by s_norm [hrunJ]) (by mut_simp hmutJ) (by lregs_simp hlrJ)
        (by s_norm [r8]) (by s_norm [r11]) (by s_norm [r12]) (by s_norm [r13]) (by s_norm) hcont hrec

private theorem probePos0_bv (bm k : BitVec 64) :
    ((k * fxSeed ^^^ ((k * fxSeed) >>> 32)) &&& bm) = BitVec.ofNat 64 (probePos bm k 0) := by
  rw [← probePos_bv_eq bm k 0, triByteOff_zero]
  simp only [fxHash, fxProd, BitVec.add_zero]

private theorem hbRehash_inner_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr bm : BitVec 64} {m : Map64} {i : Nat}
    {s1 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < bm.toNat + 1) :
    ∀ (fuel : Nat) {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {st : State},
      countDeletedTags bm ctrl ≤ fuel → (h : RehashTableInv bm m ctrl slots) →
      ctrl[i]'(by have := h.mirror.1; omega) = tagDeleted →
      (∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted) →
      st.pc = P.pl.base + 212#64 → st.status = .Running → MutFrame s1 st →
      LoopRegs ctrlPtr bm s1 st → st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      st.readReg64 (.gpr 11#5) = slotAddr ctrlPtr i →
      st.readReg64 (.gpr 12#5) = ctrlPtr - (BitVec.ofNat 64 i <<< 4) →
      (∀ (ctrl' : List (BitVec 8)) (slots' : List (BitVec 64 × BitVec 64)) (st' : State),
        (h' : RehashTableInv bm m ctrl' slots') →
        (∀ (q : Nat) (hq : q < i + 1), ctrl'[q]'(by have := h'.mirror.1; omega) ≠ tagDeleted) →
        st'.pc = P.pl.base + 468#64 → st'.status = .Running → MutFrame s1 st' →
        LoopRegs ctrlPtr bm s1 st' → st'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
        SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
          ((ctrlPtr ↦ₛ ctrl') ∗ slotsDownFrom ctrlPtr slots' ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st
        ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom := by
  intro fuel; induction fuel with
  | zero =>
    intro ctrl slots st hfuel h hdel_i
    have hpos : 0 < countDeletedTags bm ctrl := by
      unfold countDeletedTags; rw [List.countP_pos_iff]; refine ⟨tagDeleted, List.mem_iff_getElem.mpr ?_, by decide⟩
      exact ⟨i, by have := h.mirror.1; simp only [List.length_take]; omega, by simp [List.getElem_take, hdel_i]⟩
    omega
  | succ fuel ih =>
    intro ctrl slots st hfuel h hdel_i hpfx hpc hrun hmut hlregs hx8 hx11 hx12 hcont
    have hP := P.placeable
    have hi_sl : i < slots.length := by have := h.slots_len; omega
    have hx9 : st.readReg64 (.gpr 9#5) = fxSeed := hlregs.2.1
    have hx19 : st.readReg64 (.gpr 19#5) = ctrlPtr := hlregs.2.2.2.1
    have hx23 : st.readReg64 (.gpr 23#5) = bm := hlregs.2.2.2.2.2.2
    have hpos0_bv := probePos0_bv bm (slots[i]'hi_sl).1
    conv at hpos0_bv => lhs; simp (config := { zetaDelta := false }) only [wp_norm, arm64_norm]
    let g0 := ctrlGroupWord ctrl (probePos bm (slots[i]'hi_sl).1 0)
    have hcmlt0 := simd_cmlt_zero8 g0
    conv at hcmlt0 => lhs; simp (config := { zetaDelta := false }) only [wp_norm, arm64_norm]
    wp_conv_pre => rw [slotsDownFrom_focus_ldur ctrlPtr slots (idx := i) hi_sl]
    wp_sym_steps 4
    wp_conv_pre =>
      rw [← slotsDownFrom_focus_ldur ctrlPtr slots (idx := i) hi_sl,
          pointsToBytes_focus_ctrlGroupWord ctrlPtr ctrl (pos := probePos bm (slots[i]'hi_sl).1 0)
            (by have := probePos_lt_buckets h.validMask (slots[i]'hi_sl).1 0; have := h.mirror.1; omega)]
    wp_sym_steps 2; rw [hcmlt0]; wp_sym_steps 1; rw [setWidth64_zeroExtend128_eq]
    wp_conv_pre =>
      rw [← pointsToBytes_focus_ctrlGroupWord ctrlPtr ctrl (pos := probePos bm (slots[i]'hi_sl).1 0)
            (by have := probePos_lt_buckets h.validMask (slots[i]'hi_sl).1 0; have := h.mirror.1; omega)]
    wp_sym_steps 1
    rcases exists_empty_probe_group_of_empty_slot h.validMask h.mirror h.has_empty (slots[i]'hi_sl).1 with
      ⟨endStep, hend_lt, hemp_end⟩
    wp_if hz0
    · have hm0_z : byteMaskOfBits (specialBits8 g0) = 0#64 := by
        simpa (config := { zetaDelta := false }) only [bne_iff_ne, ne_eq, Decidable.not_not, beq_iff_eq] using hz0
      have hend_pos : 0 < endStep := by
        rcases Nat.eq_zero_or_pos endStep with rfl | hp
        · exact False.elim (mask_ne_zero_of_mem_empty h (slots[i]'hi_sl).1 0 hemp_end hm0_z)
        · exact hp
      wp_sym_steps 2
      refine hbRehash_probe_stride_wp P X (s1 := s1) (ctrlPtr := ctrlPtr) (k := (slots[i]'hi_sl).1)
        h hend_lt hemp_end endStep (step := 0) (by omega) hend_pos
        (fun s' hs' j hj => by
          obtain rfl : s' = 0 := by omega
          exact all_lanes_full_of_mask_zero h (slots[i]'hi_sl).1 0 hm0_z j hj)
        (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs) (by s_norm) (by s_norm) ?_
      intro step' st' hs' hmnz hpr' hpc' hrun' hmut' hlr' r8 r11 r12 r13 r14 r15 r17
      exact hbRehash_inner_join_wp P X hi h (hi_sl := hi_sl) hdel_i hpfx hs' hmnz hpr' hpc' hrun' hmut' hlr'
        (r8.trans (by s_norm [hx8])) (r11.trans (by s_norm [hx11])) (r12.trans (by s_norm [hx12]))
        (r13.trans (by dsimp only [fxProd]; s_norm)) (r14.trans (by s_norm)) r15 r17 hcont
        fun ctrl1 slots1 st1 hdec h1 hd1 hp1 hpc1 hrun1 hmut1 hlr1 rx8 rx11 rx12 =>
          ih (by omega) h1 hd1 hp1 hpc1 hrun1 hmut1 hlr1 rx8 rx11 rx12 hcont
    · have hm0_nz : byteMaskOfBits (specialBits8 g0) ≠ 0#64 := by
        simpa (config := { zetaDelta := false }) only [bne_iff_ne, ne_eq, beq_iff_eq] using hz0
      wp_sym_steps 1
      exact hbRehash_inner_join_wp P X hi h (hi_sl := hi_sl) hdel_i hpfx (by omega) hm0_nz (fun _ hs => by omega)
        (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs)
        (by s_norm [hx8]) (by s_norm [hx11]) (by s_norm [hx12])
        (by dsimp only [fxProd]; s_norm) (by s_norm) (by s_norm) (by dsimp only [g0]; s_norm) hcont
        fun ctrl1 slots1 st1 hdec h1 hd1 hp1 hpc1 hrun1 hmut1 hlr1 rx8 rx11 rx12 =>
          ih (by omega) h1 hd1 hp1 hpc1 hrun1 hmut1 hlr1 rx8 rx11 rx12 hcont

private theorem hbRehash_step_468_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr bm : BitVec 64} {m : Map64} {i : Nat}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {s1 st : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : RehashTableInv bm m ctrl slots) (hi : i < bm.toNat + 1)
    (hpfx : ∀ (q : Nat) (hq : q < i + 1), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted)
    (hpc : st.pc = P.pl.base + 468#64) (hrun : st.status = .Running)
    (hmut : MutFrame s1 st) (hlregs : LoopRegs ctrlPtr bm s1 st)
    (hx8 : st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i)
    (hdone : ∀ st' : State, st'.pc = P.pl.base + 540#64 → st'.status = .Running →
      MutFrame s1 st' → LoopRegs ctrlPtr bm s1 st' →
      (∀ (q : Nat) (hq : q < bm.toNat + 1), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
        ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom)
    (hnext : i + 1 < bm.toNat + 1 → ∀ st' : State,
      st'.pc = P.pl.base + 480#64 → st'.status = .Running →
      MutFrame s1 st' → LoopRegs ctrlPtr bm s1 st' →
      st'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (i + 1) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
        ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) target_pc st
      ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom := by
  have hP := P.placeable
  have hx23 : st.readReg64 (.gpr 23#5) = bm := hlregs.2.2.2.2.2.2
  rcases h.validMask.buckets_bounds_dvd with ⟨_, hb58, _⟩
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  wp_sym_steps 3
  wp_if heq_bm
  · have hibm : i = bm.toNat := by
      have hnat := congrArg BitVec.toNat (by simpa using heq_bm : BitVec.ofNat 64 i = bm)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; exact hnat
    exact hdone _ (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs)
      (fun q hq => hpfx q (by omega))
  · have hine : i ≠ bm.toNat := by rintro rfl; simp at heq_bm
    exact hnext (by omega) _ (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs)
      (by s_norm; rw [BitVec.ofNat_add])

private theorem hbRehash_outer_wp (P : HbPlaced) (X : String → Option (State → State))
    {target_pc ctrlPtr bm : BitVec 64} {m : Map64}
    {s1 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (fuel : Nat) {i : Nat} {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {st : State},
      fuel = (bm.toNat + 1) - i → (hi : i < bm.toNat + 1) →
      (h : RehashTableInv bm m ctrl slots) →
      (∀ (q : Nat) (hq : q < i), ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted) →
      st.pc = P.pl.base + 480#64 → st.status = .Running → MutFrame s1 st →
      LoopRegs ctrlPtr bm s1 st → st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      (∀ (ctrl' : List (BitVec 8)) (slots' : List (BitVec 64 × BitVec 64)) (st' : State),
        (h' : RehashTableInv bm m ctrl' slots') →
        (∀ (q : Nat) (hq : q < bm.toNat + 1), ctrl'[q]'(by have := h'.mirror.1; omega) ≠ tagDeleted) →
        st'.pc = P.pl.base + 540#64 → st'.status = .Running → MutFrame s1 st' →
        LoopRegs ctrlPtr bm s1 st' →
        SepWP ((hbProg P).rebase P.pl.base X) target_pc st'
          ((ctrlPtr ↦ₛ ctrl') ∗ slotsDownFrom ctrlPtr slots' ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) target_pc st
        ((ctrlPtr ↦ₛ ctrl) ∗ slotsDownFrom ctrlPtr slots ∗ F) post oom := by
  intro fuel; induction fuel with
  | zero => intro i ctrl slots st hfuel hi; omega
  | succ fuel ih =>
    intro i ctrl slots st hfuel hi h hpfx hpc hrun hmut hlregs hx8 hcont
    have hP := P.placeable
    have hx19 : st.readReg64 (.gpr 19#5) = ctrlPtr := hlregs.2.2.2.1
    have hi_ctrl : i < ctrl.length := by have := h.mirror.1; omega
    wp_conv_pre => rw [pointsToBytes_focus8_getElem ctrlPtr ctrl (off := i) hi_ctrl]
    wp_sym_steps 3
    wp_conv_pre => rw [← pointsToBytes_focus8_getElem ctrlPtr ctrl (off := i) hi_ctrl]
    wp_if hne_del
    ·
      have hnot_del_i : ctrl[i]'hi_ctrl ≠ tagDeleted := fun heq => by simp [heq, tagDeleted] at hne_del
      have hpfx' : ∀ (q : Nat) (hq : q < i + 1),
          ctrl[q]'(by have := h.mirror.1; omega) ≠ tagDeleted := fun q hq => by
        by_cases hqi : q = i
        · subst hqi; exact hnot_del_i
        · exact hpfx q (by omega)
      exact hbRehash_step_468_wp P X h hi hpfx'
        (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs) (by s_norm [hx8])
        (fun st' hpc' hrun' hmut' hlr' hno => hcont ctrl slots st' h hno hpc' hrun' hmut' hlr')
        (fun hi1 st' hpc' hrun' hmut' hlr' hx8' =>
          ih (by omega) hi1 h hpfx' hpc' hrun' hmut' hlr' hx8' hcont)
    ·
      have hdel_i : ctrl[i]'hi_ctrl = tagDeleted := by
        revert hne_del; generalize ctrl[i]'hi_ctrl = b; unfold tagDeleted; bv_robdd
      wp_sym_steps 4
      refine hbRehash_inner_wp P X (s1 := s1) (ctrlPtr := ctrlPtr) hi
        (countDeletedTags bm ctrl) (Nat.le_refl _) h hdel_i hpfx
        (by s_norm) (by s_norm [hrun]) (by mut_simp hmut) (by lregs_simp hlregs)
        (by s_norm [hx8]) (by s_norm [slotAddr_mvn_lsl4]) (by s_norm) ?_
      intro ctrl' slots' st' h' hpfx' hpc' hrun' hmut' hlr' hx8'
      exact hbRehash_step_468_wp P X h' hi hpfx' hpc' hrun' hmut' hlr' hx8'
        (fun st'' hpc'' hrun'' hmut'' hlr'' hno => hcont ctrl' slots' st'' h' hno hpc'' hrun'' hmut'' hlr'')
        (fun hi1 st'' hpc'' hrun'' hmut'' hlr'' hx8'' =>
          ih (by omega) hi1 h' hpfx' hpc'' hrun'' hmut'' hlr'' hx8'' hcont)

/-- Subcase `8 ≤ bm.toNat + 1` (`8 ∣ bm.toNat + 1`) from `+ 120` to `+ 1080`. -/
theorem hbRehash_subcase_ge8_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s1 : State} {mapPtr bm : BitVec 64} {m : Map64} {w : HbHeapMapWitness} {oom : State → SepProp}
    (hge8 : 8 ≤ bm.toNat + 1) (hdvd8 : (bm.toNat + 1) % 8 = 0)
    (hpc : s1.pc = P.pl.base + 120#64) (hrun : s1.status = .Running)
    (hsp_al : s1.spAligned = true) (hx0 : s1.readReg64 .x0 = mapPtr)
    (hx8 : s1.readReg64 .x8 = (bm + 1#64) >>> 3) (hx20 : s1.readReg64 .x20 = bucketMaskToCapacityBV bm)
    (hx22 : s1.readReg64 .x22 = w.items) (hx23 : s1.readReg64 .x23 = bm)
    (hx24 : s1.readReg64 .x24 = bm + 1#64) (hal : mapPtr.toNat % 8 = 0)
    (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0)
    (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hle_half : m.length + 1 ≤ bucketMaskToCapacity bm / 2) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1080#64) s1
      (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
       A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl))
      (fun s2 P2 => MutFrame s1 s2 ∧ s2.readReg64 .x0 = 0xffffffffffffffff#64 ∧
        (P2 ⊢ U64MapRepReady P.pl A mapPtr m bm)) oom := by
  have hP := P.placeable
  have hctrl_fn : Unit → w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) := fun _ => hctrl
  clear hctrl
  let buckets := bm.toNat + 1; let G := buckets / 8
  rcases hinv.validMask.buckets_bounds_dvd with ⟨_, hb58, _⟩
  have h58 : 2 ^ 58 < 2 ^ 64 := by decide
  rcases ge8_entry_bv_facts hinv.validMask hge8 hdvd8 with ⟨hbm1_bv, hsh_bv, hand7_bv, hG_bound⟩
  have hx8_G : s1.readReg64 .x8 = BitVec.ofNat 64 G := hx8.trans hsh_bv
  have hx24_b : s1.readReg64 .x24 = BitVec.ofNat 64 buckets := hx24.trans hbm1_bv
  clear hbm1_bv hsh_bv hx8 hx24
  let F_prep := hbRodata P.pl ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
    ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ w.items)) ∗
    A.Block w.allocPtr (17 * buckets + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots
  wp_conv_pre => dsimp only [U64MapStruct]
  wp_sym_steps 1; wp_if hcbz
  · exfalso
    have h0 : BitVec.ofNat 64 buckets = 0#64 := by
      simpa (config := { zetaDelta := false }) only [wp_norm, arm64_norm, hx24_b, beq_iff_eq] using hcbz
    have hnat := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; simp at hnat
  wp_sym_steps 5
  wp_conv_pre =>
    rw [show hbRodata P.pl ∗ ((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
          ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗ ((mapPtr + 24#64) ↦₆₄ w.items)) ∗
          A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
          slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) =
        (w.ctrlPtr ↦ₛ prepPrefix w.ctrl (8 * 0)) ∗ F_prep by
      rw [prepPrefix_zero]; dsimp only [F_prep, buckets]; ac_rfl]
  refine hbRehash_prep_loop_wp P X (s1 := s1) (ctrlPtr := w.ctrlPtr) (G := G)
    (by have := hinv.mirror.1; omega) hG_bound G (g := 0) rfl (by omega)
    (by s_norm) (by s_norm [hrun]) (by mut_simp (MutFrame.refl hsp_al))
    (by s_norm [hand7_bv, hx8_G, hx24_b]; rfl) (by s_norm) (by s_norm) ?_
  intro st1 hpc1 hrun1 hmut1 hregs1
  have hx0_1 := (hregs1 .x0 (by decide) (by decide)).trans (by s_norm [hx0] : _ = mapPtr)
  have hx19_1 := (hregs1 (.gpr 19#5) (by decide) (by decide)).trans (by s_norm : _ = w.ctrlPtr)
  have hx20_1 := (hregs1 (.gpr 20#5) (by decide) (by decide)).trans
    (by s_norm [hx20] : _ = bucketMaskToCapacityBV bm)
  have hx22_1 := (hregs1 (.gpr 22#5) (by decide) (by decide)).trans (by s_norm [hx22] : _ = w.items)
  have hx23_1 := (hregs1 (.gpr 23#5) (by decide) (by decide)).trans (by s_norm [hx23] : _ = bm)
  have hx24_1 := (hregs1 (.gpr 24#5) (by decide) (by decide)).trans
    (by s_norm [hx24_b] : _ = BitVec.ofNat 64 buckets)
  rw [show 8 * G = buckets by dsimp only [G]; omega]
  wp_sym_steps 2; wp_if hlo8
  · exfalso
    have hlt_nat := toNat_lt_eight_of_ult
      (by simpa (config := { zetaDelta := false }) only [wp_norm, arm64_norm, hx24_1] using hlo8)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt_nat; omega
  let cur := prepPrefix w.ctrl buckets
  have hcur_len : cur.length = buckets + 8 :=
    (prepPrefix_length w.ctrl (by have := hinv.mirror.1; omega)).trans hinv.mirror.1
  have hfocus0 : (w.ctrlPtr ↦ₛ cur) = (w.ctrlPtr ↦₆₄ ctrlGroupWord cur 0) ∗
      (w.ctrlPtr ↦ₛ cur.take 0 ∗ (w.ctrlPtr + 8#64) ↦ₛ cur.drop 8) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      pointsToBytes_focus_ctrlGroupWord w.ctrlPtr cur (pos := 0) (by omega)
  wp_conv_pre => rw [hfocus0]
  wp_sym_steps 1
  wp_conv_pre => rw [← hfocus0]
  refine step_str64_perm (pc := P.pl.base + 180#64)
    (ea := w.ctrlPtr + BitVec.ofNat 64 buckets) (wb := none) (val := ctrlGroupWord cur 0)
    rfl (by s_norm [hrun1]) (by s_norm; rfl) rfl (by s_norm [hx19_1, hx24_1]) (by dsimp only [cur]; s_norm)
    (SepStore64.left (SepStore64.of_pointsToBytes_here _ w.ctrlPtr cur buckets _ (by omega) rfl))
    fun m1 hm1 => ?_
  dsimp only [applyWriteback]; rw [show P.pl.base + 180#64 + 4#64 = P.pl.base + 184#64 by bv_lin]
  have hp_m1 : m1.perm = st1.mem.perm := by simpa using hm1
  rw [prepPrefix_mirror_write64 hge8 hinv.mirror.1]
  let ctrl0 := (w.ctrl.take buckets).map prepCtrlByte ++ (w.ctrl.take 8).map prepCtrlByte
  have hreh0 : RehashTableInv bm m ctrl0 w.slots := RehashTableInv.of_prep hinv hge8 hdvd8
  wp_sym_steps 7
  let F_outer := hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
    A.Block w.allocPtr (17 * buckets + 8) 8
  wp_conv_pre =>
    rw [show (w.ctrlPtr ↦ₛ ctrl0) ∗ F_prep =
          (w.ctrlPtr ↦ₛ ctrl0) ∗ slotsDownFrom w.ctrlPtr w.slots ∗ F_outer by
      dsimp only [F_prep, F_outer, U64MapStruct]; ac_rfl]
  refine hbRehash_outer_wp P X (s1 := s1) (ctrlPtr := w.ctrlPtr) (bm := bm)
    buckets (i := 0) (by omega) (by omega) hreh0 (fun _ hq => by omega)
    (by s_norm) (by s_norm [hrun1]) (by mut_mem_simp hmut1 hp_m1)
    ⟨by s_norm [hx0_1, hx0], by s_norm; rfl, by s_norm, by s_norm [hx19_1],
     by s_norm [hx20_1, hx20], by s_norm [hx22_1, hx22], by s_norm [hx23_1]⟩
    (by s_norm) ?_
  intro ctrl_f slots_f st_f h_f hno_del hpc_f hrun_f hmut_f hlr_f
  wp_conv_pre =>
    rw [show (w.ctrlPtr ↦ₛ ctrl_f) ∗ slotsDownFrom w.ctrlPtr slots_f ∗ F_outer =
          U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
            (hbRodata P.pl ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
             slotsDownFrom w.ctrlPtr slots_f ∗ (w.ctrlPtr ↦ₛ ctrl_f)) by
      dsimp only [F_outer, buckets]; ac_rfl]
  refine hbRehash_epilogue_wp P A X (s1 := s1) hpc_f hrun_f hmut_f
    (hlr_f.1.trans hx0) (hlr_f.2.2.2.2.1.trans hx20) (hlr_f.2.2.2.2.2.1.trans hx22) ?_
  rcases h_f.to_swissTableInv hinv.items_eq hno_del hle_half with ⟨hswiss_f, hgl_pos⟩
  let wf_wit : HbHeapMapWitness :=
    { allocPtr := w.allocPtr, ctrlPtr := w.ctrlPtr, growthLeft := bucketMaskToCapacityBV bm - w.items,
      items := w.items, ctrl := ctrl_f, slots := slots_f }
  unfold U64MapRepReady
  refine Entails.pure_right ⟨hal, hnw, hinv.wf, hinv.validMask.ne_zero⟩ ?_
  have h1 : U64MapStruct mapPtr w.ctrlPtr bm (bucketMaskToCapacityBV bm - w.items) w.items ∗
      (hbRodata P.pl ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom w.ctrlPtr slots_f ∗ (w.ctrlPtr ↦ₛ ctrl_f)) =
      hbRodata P.pl ∗ (U64MapStruct mapPtr wf_wit.ctrlPtr bm wf_wit.growthLeft wf_wit.items ∗
       A.Block wf_wit.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom wf_wit.ctrlPtr wf_wit.slots ∗ (wf_wit.ctrlPtr ↦ₛ wf_wit.ctrl)) := by
    dsimp only [wf_wit]; ac_rfl
  rw [h1]
  exact sepConj_mono_right (Entails.sepExists_right wf_wit
    (Entails.pure_right ⟨hswiss_f, hgl_pos, rfl, ha_ne, ha_al, ha_nw, hctrl_fn ()⟩ (Entails.refl _)))

/-- Top-level `rehash_in_place` specification (`HbRehashInPlaceProp P A X`). -/
theorem hbRehashInPlace_wp (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    {s1 : State} {mapPtr bm : BitVec 64} {m : Map64} {w : HbHeapMapWitness} {oom : State → SepProp}
    (hpc : s1.pc = P.pl.base + 120#64) (hrun : s1.status = .Running)
    (hsp_al : s1.spAligned = true) (hCode : A.CodeInv s1.mem)
    (hx0 : s1.readReg64 .x0 = mapPtr) (hx8 : s1.readReg64 .x8 = (bm + 1#64) >>> 3)
    (hx20 : s1.readReg64 .x20 = bucketMaskToCapacityBV bm) (hx22 : s1.readReg64 .x22 = w.items)
    (hx23 : s1.readReg64 .x23 = bm) (hx24 : s1.readReg64 .x24 = bm + 1#64)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64)
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (ha_ne : w.allocPtr ≠ 0#64) (ha_al : w.allocPtr.toNat % 8 = 0)
    (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hle_half : m.length + 1 ≤ bucketMaskToCapacity bm / 2) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1080#64) s1
      (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
       A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl))
      (fun s2 P2 => s2.sp = s1.sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x0 = 0xffffffffffffffff#64 ∧
        s2.readReg64 (.gpr 28#5) = s1.readReg64 (.gpr 28#5) ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s1 ∧ StdStatePreserved s1 s2 ∧
        s1.mem.KeepsFrozen s2.mem ∧ (P2 ⊢ U64MapRepReady P.pl A mapPtr m bm)) oom := by
  refine SepWP.mono_frozen (s := s1) (Φ := fun m => s1.mem.KeepsFrozen m)
    (post := fun s2 P2 => MutFrame s1 s2 ∧ s2.readReg64 .x0 = 0xffffffffffffffff#64 ∧
      (P2 ⊢ U64MapRepReady P.pl A mapPtr m bm))
    (fun _ _ h1 h2 => Memory.KeepsFrozen.trans h1 h2) (Memory.KeepsFrozen.refl s1.mem) ?_
    (fun _ _ _ _ hkf ⟨⟨hsp, hspa, hx28, hvregs, hstd⟩, hx0_f, hent⟩ =>
      ⟨hsp, hspa, hx0_f, hx28, hvregs, hstd, hkf, hent⟩)
  rcases hinv.validMask.buckets_cases with hb4 | ⟨hge8, hdvd8⟩
  · exact hbRehash_subcase4_wp P A X hext hb4 hpc hrun hsp_al hCode hx0 hx8 hx20 hx22 hx23 hx24
      hal hnw hinv ha_ne ha_al ha_nw hctrl hle_half
  · exact hbRehash_subcase_ge8_wp P A X hge8 hdvd8 hpc hrun hsp_al hx0 hx8 hx20 hx22 hx23 hx24
      hal hnw hinv ha_ne ha_al ha_nw hctrl hle_half

end MachineProofs
end CaseStudies.Hashbrown.Proofs
