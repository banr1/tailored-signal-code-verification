/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaStage1
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers6f
public import LibsignalBinary.Heap.Fine.VendorFree.FreeGroupMono

/-!
# Stage 1 Helpers for Placed `nontrivial_free`

Defines the exact nesting-depth bound `nestFuel` (`<= 6`), parameterized `32`-byte stack-frame
splitting lemmas, the second-word relaxable `ADRP`+`ADD` step rule, and shared exit-block proofs
(`epilogue`, LL/SC `or32` commit, and `free_meta`) for `nontrivial_free` (`blk05`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection VerifiedLibraries.Mallocng

@[expose] public section

/-! ## Nesting Fuel and Stack Frames -/

/-- Exact nesting depth upper bound (`≤ 6`) for `g ∈ st.groups` under `MallocngWFInflight`:
    root groups (`0 < g.maplen`) have `nestFuel = 0`, and each nested parent step (`g.maplen = 0`)
    satisfies `1 + 2 * sizeClass g.sc ≤ sizeClass pg.sc ≤ 146`, strictly decreasing `nestFuel`. -/
def nestFuel (g : GroupDesc) : Nat :=
  if 0 < g.maplen then 0
  else if 36 ≤ sizeClass g.sc then 1
  else if 18 ≤ sizeClass g.sc then 2
  else if 9 ≤ sizeClass g.sc then 3
  else if 4 ≤ sizeClass g.sc then 4
  else if 2 ≤ sizeClass g.sc then 5
  else 6

theorem nestFuel_le_six (g : GroupDesc) : nestFuel g ≤ 6 := by
  unfold nestFuel
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals omega

@[scoped simp] theorem nestFuel_set_slots (g : GroupDesc) (s : List SlotState) :
    nestFuel { g with slots := s } = nestFuel g := rfl

private theorem sizeClass_pos_fin : ∀ i : Fin 48, 1 ≤ sizeClass i.val := by decide

private theorem sizeClass_le_146_fin : ∀ i : Fin 25, sizeClass i.val ≤ 146 := by decide

private theorem nested_parent_sizeClass_step {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {u : GroupDesc} (hu : u ∈ st.groups) (hMap0 : u.maplen = 0) :
    ∃ v ∈ st.groups, u.parentMeta = some v.metaPtr ∧
      1 ≤ sizeClass u.sc ∧
      1 + 2 * sizeClass u.sc ≤ sizeClass v.sc ∧
      sizeClass v.sc ≤ 146 := by
  have hUWf := hwf.groups_wf u hu
  obtain ⟨_, v, hv, _, _, hPar, hVSc48, hUScLt, hVSc24, _, _, _, hCapEq⟩ :=
    hUWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
  have hUSc48 : u.sc < 48 := by omega
  have hUPos : 1 ≤ sizeClass u.sc := sizeClass_pos_fin ⟨u.sc, hUSc48⟩
  have hVLe146 : sizeClass v.sc ≤ 146 := sizeClass_le_146_fin ⟨v.sc, by omega⟩
  have hVStride : slotStride v.sc = 16 * sizeClass v.sc := by simp [slotStride]
  have hUStride : u.stride = 16 * sizeClass u.sc := by simp [GroupDesc.stride, slotStride, hMap0]
  have hUTot : u.totalBytes = u.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
  have hCntGe2 : 2 ≤ u.cnt := by unfold GroupDesc.cnt; omega
  have hMulGe : 2 * u.stride ≤ u.cnt * u.stride := Nat.mul_le_mul_right u.stride hCntGe2
  have hFitTot := hUWf.2.2.2.2.2.2.2.1
  rw [hUTot] at hFitTot
  rw [hCapEq, hVStride, hUStride] at hFitTot
  rw [hUStride] at hMulGe
  exact ⟨v, hv, hPar, hUPos, by omega, hVLe146⟩

theorem nestFuel_parent_lt {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g pg0 : GroupDesc} (hg : g ∈ st.groups) (hpg : pg0 ∈ st.groups)
    (hMap0 : g.maplen = 0) (hPar : g.parentMeta = some pg0.metaPtr) :
    nestFuel pg0 < nestFuel g := by
  obtain ⟨v, hv, hParV, hGScPos, hStepG, hPgLe146⟩ := nested_parent_sizeClass_step hwf hg hMap0
  have hVEq : pg0 = v := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hv
    (Option.some.inj (hPar.symm.trans hParV))
  cases hVEq
  by_cases hPgMp : 0 < pg0.maplen
  · have hF0 : nestFuel pg0 = 0 := by unfold nestFuel; split <;> omega
    have hFGPos : 0 < nestFuel g := by
      unfold nestFuel; simp only [hMap0, Nat.lt_irrefl, ↓reduceIte]
      all_goals try split
      all_goals try split
      all_goals try split
      all_goals try split
      all_goals try split
      all_goals omega
    omega
  · have hPgMap0 : pg0.maplen = 0 := by omega
    obtain ⟨_, _, _, _, hStepPg, hPpgLe146⟩ := nested_parent_sizeClass_step hwf hpg hPgMap0
    have hPgLe72 : sizeClass pg0.sc ≤ 72 := by omega
    by_cases h36 : 36 ≤ sizeClass pg0.sc
    · have hF1 : nestFuel pg0 = 1 := by unfold nestFuel; simp [hPgMap0, h36]
      have hG : ¬ (36 ≤ sizeClass g.sc) := by omega
      have hFG : 2 ≤ nestFuel g := by
        unfold nestFuel; simp only [hMap0, Nat.lt_irrefl, hG, ↓reduceIte]
        all_goals try split
        all_goals try split
        all_goals try split
        all_goals try split
        all_goals omega
      omega
    · by_cases h18 : 18 ≤ sizeClass pg0.sc
      · have hF2 : nestFuel pg0 = 2 := by unfold nestFuel; simp [hPgMap0, h36, h18]
        have hG36 : ¬ (36 ≤ sizeClass g.sc) := by omega
        have hG18 : ¬ (18 ≤ sizeClass g.sc) := by omega
        have hFG : 3 ≤ nestFuel g := by
          unfold nestFuel; simp only [hMap0, Nat.lt_irrefl, hG36, hG18, ↓reduceIte]
          all_goals try split
          all_goals try split
          all_goals try split
          all_goals omega
        omega
      · by_cases h9 : 9 ≤ sizeClass pg0.sc
        · have hF3 : nestFuel pg0 = 3 := by unfold nestFuel; simp [hPgMap0, h36, h18, h9]
          have hG36 : ¬ (36 ≤ sizeClass g.sc) := by omega
          have hG18 : ¬ (18 ≤ sizeClass g.sc) := by omega
          have hG9 : ¬ (9 ≤ sizeClass g.sc) := by omega
          have hFG : 4 ≤ nestFuel g := by
            unfold nestFuel; simp only [hMap0, Nat.lt_irrefl, hG36, hG18, hG9, ↓reduceIte]
            all_goals try split
            all_goals try split
            all_goals omega
          omega
        · by_cases h4 : 4 ≤ sizeClass pg0.sc
          · have hF4 : nestFuel pg0 = 4 := by unfold nestFuel; simp [hPgMap0, h36, h18, h9, h4]
            have hG36 : ¬ (36 ≤ sizeClass g.sc) := by omega
            have hG18 : ¬ (18 ≤ sizeClass g.sc) := by omega
            have hG9 : ¬ (9 ≤ sizeClass g.sc) := by omega
            have hG4 : ¬ (4 ≤ sizeClass g.sc) := by omega
            have hFG : 5 ≤ nestFuel g := by
              unfold nestFuel; simp only [hMap0, Nat.lt_irrefl, hG36, hG18, hG9, hG4, ↓reduceIte]
              split <;> omega
            omega
          · by_cases h2 : 2 ≤ sizeClass pg0.sc
            · have hF5 : nestFuel pg0 = 5 := by unfold nestFuel; simp [hPgMap0, h36, h18, h9, h4, h2]
              have hG36 : ¬ (36 ≤ sizeClass g.sc) := by omega
              have hG18 : ¬ (18 ≤ sizeClass g.sc) := by omega
              have hG9 : ¬ (9 ≤ sizeClass g.sc) := by omega
              have hG4 : ¬ (4 ≤ sizeClass g.sc) := by omega
              have hG2 : ¬ (2 ≤ sizeClass g.sc) := by omega
              have hFG : nestFuel g = 6 := by
                unfold nestFuel; simp [hMap0, hG36, hG18, hG9, hG4, hG2]
              omega
            · omega

abbrev nfStackSaved (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x20)

theorem spAligned_sub32 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 32#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp0 &&& 15#64 = 0#64 := beq_iff_eq.mp h
  apply beq_iff_eq.mpr; revert h0; bv_bits

theorem stackFrameAt_succ_split (sp0 : BitVec 64) (fuel : Nat) (hFuel : fuel ≤ 6) :
    stackFrameAt sp0 (32 * (fuel + 1)) =
      (stackFrameAt (sp0 - 32#64) (32 * fuel) ∗ cells (sp0 - 32#64) 4) := by
  rw [stackFrameAt_eq_memRegion sp0 (32 * (fuel + 1)),
      stackFrameAt_eq_memRegion (sp0 - 32#64) (32 * fuel)]
  have hAdd : sp0 - BitVec.ofNat 64 (32 * (fuel + 1)) + BitVec.ofNat 64 (32 * fuel) =
      sp0 - 32#64 := by
    rcases (by omega : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 ∨ fuel = 5 ∨ fuel = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_arith
  have hSub : sp0 - 32#64 - BitVec.ofNat 64 (32 * fuel) =
      sp0 - BitVec.ofNat 64 (32 * (fuel + 1)) := by
    rcases (by omega : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 ∨ fuel = 5 ∨ fuel = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_arith
  have hSplit := memRegion_split (sp0 - BitVec.ofNat 64 (32 * (fuel + 1))) (32 * fuel) 32 (by omega)
  rw [show 32 * fuel + 32 = 32 * (fuel + 1) by omega, hAdd] at hSplit
  rw [hSplit, hSub, memRegion_cells (sp0 - 32#64) 4 (by decide)]

theorem repack_nfStack (sp0 : BitVec 64) (fuel : Nat) (hFuel : fuel ≤ 6) (s0 : State) :
    (stackFrameAt (sp0 - 32#64) (32 * fuel) ∗ nfStackSaved sp0 s0) ⊢
      stackFrameAt sp0 (32 * (fuel + 1)) := by
  rw [stackFrameAt_succ_split sp0 fuel hFuel]
  dsimp only [nfStackSaved]; cells_unfold; sep_frame

theorem repack_nfStack_rest (sp0 : BitVec 64) (fuel : Nat) (hFuel : fuel ≤ 6) (s0 : State) (R : SepProp) :
    (stackFrameAt (sp0 - 32#64) (32 * fuel) ∗
     ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
     ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x20) ∗ R) ⊢
      (stackFrameAt sp0 (32 * (fuel + 1)) ∗ R) := by
  have h : (stackFrameAt (sp0 - 32#64) (32 * fuel) ∗
     ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
     ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x20) ∗ R) =
     ((stackFrameAt (sp0 - 32#64) (32 * fuel) ∗ nfStackSaved sp0 s0) ∗ R) := by
    dsimp only [nfStackSaved]; ac_rfl
  rw [h]
  exact sepConj_mono_left (repack_nfStack sp0 fuel hFuel s0)

theorem stack224_split_fuel (sp0 : BitVec 64) (fuel : Nat) (hFuel : fuel ≤ 6) :
    stackFrameAt sp0 224 =
      (memRegion (sp0 - 224#64) (224 - 32 * (fuel + 1)) ∗ stackFrameAt sp0 (32 * (fuel + 1))) := by
  rw [stackFrameAt_eq_memRegion sp0 224, stackFrameAt_eq_memRegion sp0 (32 * (fuel + 1))]
  have hAdd : sp0 - 224#64 + BitVec.ofNat 64 (224 - 32 * (fuel + 1)) =
      sp0 - BitVec.ofNat 64 (32 * (fuel + 1)) := by
    rcases (by omega : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 ∨ fuel = 5 ∨ fuel = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_arith
  have hSplit := memRegion_split (sp0 - 224#64) (224 - 32 * (fuel + 1)) (32 * (fuel + 1)) (by omega)
  rw [show 224 - 32 * (fuel + 1) + 32 * (fuel + 1) = 224 by omega, hAdd] at hSplit
  simpa using hSplit

/-! ## Second-Word Relaxable Pair Rule -/

/-- Executing the second word (`off + 4`) of a relaxable `ADRP Xd` + `ADD Xd, Xd, :lo12:` pair
    when `Xd` already holds `pageOf (blk.target pl r)` sets `Xd := blk.target pl r` and advances
    `pc` to `pl.base + (off + 8)` whether or not the linker relaxed the pair at `off`. -/
theorem sepWP_secondWord_relaxablePair {blk : CodeBlock} {pl : Placement} {prog : Program}
    {off : Nat} {r : RelocEntry} {rd : BitVec 5} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : blk.Placeable pl) (hbase : prog.base = pl.base) (hcode : prog.code = blk.patched pl)
    (hrel : blk.relaxableAt off = true) (hr : blk.relocAt? off = some r)
    (hrd : (blk.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hh4 : prog.hookAtOff? (off + 4) = none)
    (hrd_page : s.readReg64 (.gpr rd) = pageOf (blk.target pl r))
    (hpc : s.pc = pl.base + BitVec.ofNat 64 (off + 4)) (hrun : s.status = .Running)
    (hnext : SepWP prog tgt
      ((s.writeReg64 (.gpr rd) (blk.target pl r)).setPC (pl.base + BitVec.ofNat 64 (off + 8)))
      P post oom) :
    SepWP prog tgt s P post oom := by
  have hNextPc : pl.base + BitVec.ofNat 64 (off + 8) = s.pc + 4#64 := by
    rw [hpc, show off + 8 = (off + 4) + 4 by omega, BitVec.ofNat_add, BitVec.add_assoc]
  rw [hNextPc] at hnext
  obtain ⟨r2, hr2, hk1, hk2, hsym, hadd, _, hw1, hm1, hm2⟩ := CodeBlock.relaxableAt_spec hrel hr
  have hT2 : blk.target pl r2 = blk.target pl r := by simp only [CodeBlock.target, hsym, hadd]
  have hr2off := CodeBlock.relocAt?_off hr2
  obtain ⟨hal2, hlen2, _⟩ := hP.relocs_ok r2 (CodeBlock.relocAt?_mem hr2)
  rw [hr2off] at hal2 hlen2
  have _hnw := hP.no_wrap
  obtain ⟨hrd1, hrn1⟩ := Arm64.Obj.rd_fields_of_pair hrd hm1 hm2
  have hf4 : prog.fetch (pl.base + BitVec.ofNat 64 (off + 4)) = decode (blk.patchedWord pl (off + 4)) := by
    rw [← hbase]
    exact Program.fetch_of_readWordOff (by omega) hh4
      (CodeBlock.readWordOff_patched hcode (by omega) (by omega))
  rw [← hpc] at hf4
  have hnr4 : blk.relaxedAt pl (off + 4) = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr2 (by rw [hk2]; decide))
  have hreg : Reg.fromZRBits rd = .gpr rd := Arm64.Obj.fromZRBits_of_ne hrd31
  cases hrx : pl.relax off with
  | false =>
    have h0 : blk.relaxedAt pl off = false := by simp [CodeBlock.relaxedAt, hrx]
    have hb2 : blk.b2bNext? r2 = none := by simp [CodeBlock.b2bNext?, hk2]
    have hw1' := CodeBlock.patchedWord_of_notRelaxed (pl := pl) hr2 hnr4 (.inr (by
      rw [show off + 4 - 4 = off by omega]; exact h0))
    rw [CodeBlock.relocTarget_of_b2bNext_none hb2, hk2, hT2] at hw1'
    rw [hw1'] at hf4
    simp only [patchRelocWord] at hf4
    rw [decode_addLo12Word hw1, hrd1, hrn1, Arm64.Obj.fromSPBits_of_ne hrd31] at hf4
    refine SepWP.step_pure
      (s' := (s.writeReg64 (.gpr rd) (blk.target pl r)).advancePC)
      rfl hrun hf4 ?_ rfl hnext
    simp only [Program.evalInst, execInstWithSvc, execAddSubImm, Bool.false_eq_true,
      ↓reduceIte, zeroExtend_truncate_lo12Of, evalAddSub_w64_add, State.readReg,
      State.setPC, hrd_page, State.writeReg, pageOf_add_lo12Of]
  | true =>
    have h0 : blk.relaxedAt pl off = true := by simp [CodeBlock.relaxedAt, hrel, hrx]
    have hw1' := CodeBlock.patchedWord_of_relaxedPrev (pl := pl) hr2 hnr4 (by omega)
      (by rw [show off + 4 - 4 = off by omega]; exact h0)
    have hadr := hP.relaxed_ok off r2 h0 hr2
    rw [hT2, ← hpc] at hadr
    rw [hw1', hT2, ← hpc, decode_adrWord (adrTemplate_mask _) hadr, adrTemplate_rd, hrd1, hreg] at hf4
    refine SepWP.step_pure
      (s' := (s.writeReg64 (.gpr rd) (blk.target pl r)).advancePC)
      rfl hrun hf4 ?_ rfl hnext
    simp only [Program.evalInst, execInstWithSvc, Bool.false_eq_true, ↓reduceIte, State.pc_setPC]
    congr 2
    bv_lin

theorem sepWP_blk_secondWord_relaxablePair {lib : PlacedLib} {pl : Placement} {svc : State → State}
    {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hP : lib.Placeable pl)
    {b : BitVec 64} {X : String → Option (State → State)}
    {off off4 off8 : Nat} {r : RelocEntry} {rd : BitVec 5} {v : BitVec 64}
    (hrel : lib.text.relaxableAt off = true)
    (hr : lib.text.relocAt? off = some r)
    (hrd : (lib.text.wordAt off).extractLsb' 0 5 = rd)
    (hrd31 : rd ≠ 31#5)
    (h4 : off + 4 = off4) (h8 : off + 8 = off8) (hlt4 : off + 4 < 4 * n)
    (hb : b = pl.base)
    (hv : b = pl.base → lib.text.target pl r = v)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hrd_page : s.readReg64 (.gpr rd) = pageOf v)
    (hpc : s.pc = b + BitVec.ofNat 64 off4)
    (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X) tgt
      ((s.writeReg64 (.gpr rd) v).setPC (b + BitVec.ofNat 64 off8)) P post oom) :
    SepWP ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b X) tgt s P post oom := by
  have hv' := hv hb; clear hv; subst hb hv' h4 h8
  have hh4 : ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase pl.base X).hookAtOff? (off + 4) = none :=
    GenPlacedFetches.hookAtOff?_rebase_of_placeable (b := pl.base) (X := X) hcode hsize hP hlt4
  exact sepWP_secondWord_relaxablePair hP.text rfl rfl hrel hr hrd hrd31 hh4 hrd_page hpc hrun hnext

private def b05Reloc188 : RelocEntry :=
  (blkLib_b05.text.relocAt? 188).getD { off := 0, kind := .abs64, sym := "" }
private def b05Reloc192 : RelocEntry :=
  (blkLib_b05.text.relocAt? 192).getD { off := 0, kind := .abs64, sym := "" }
private def b05Word188 : BitVec 32 :=
  let (b0, b1, b2, b3) := (blkTree_b05.getQuad? 47).getD (0, 0, 0, 0)
  wordOfBytesLE [b0, b1, b2, b3] 0
private def b05Word192 : BitVec 32 :=
  let (b0, b1, b2, b3) := (blkTree_b05.getQuad? 48).getD (0, 0, 0, 0)
  wordOfBytesLE [b0, b1, b2, b3] 0

theorem blkPC_b05_pairStep_0xc0 [MallocngMultiPlacement] (b : BitVec 64)
    (X : String → Option (State → State))
    {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : b = mbase 5)
    (hx20 : s.readReg64 (.gpr 20#5) = pageOf maddrs.ctx)
    (hpc : s.pc = b + 0xc0#64)
    (hrun : s.status = .Running)
    (hnext : SepWP (blkPC_b05.rebase b X) tgt
      ((s.writeReg64 (.gpr 20#5) maddrs.ctx).setPC (b + 0xc4#64)) P post oom) :
    SepWP (blkPC_b05.rebase b X) tgt s P post oom :=
  sepWP_blk_secondWord_relaxablePair blkCodeEq_b05 blkSizeEq_b05 blkPlaceable_b05 (r := b05Reloc188)
    (GenPlacedFetches.relaxableAt_of_words
      (r1 := b05Reloc188) (r2 := b05Reloc192)
      (by rfl_kernel) (by rfl_kernel)
      (blk_wordAt blkCodeEq_b05 blkSizeEq_b05 (j := 47) rfl (by rfl_kernel) (w := b05Word188) rfl)
      (blk_wordAt blkCodeEq_b05 blkSizeEq_b05 (j := 48) rfl (by rfl_kernel) (w := b05Word192) rfl)
      rfl)
    (by rfl_kernel)
    (blk_word_rd (blk_wordAt blkCodeEq_b05 blkSizeEq_b05 (j := 47) rfl (by rfl_kernel) (w := b05Word188) rfl) rfl)
    (by decide) rfl rfl (by decide) hb
    (fun _ => blk_target_ext_zero (lib := blkLib_b05) (pl := blkPl_b05) (r := b05Reloc188)
      (sym := "__malloc_context") rfl (by rfl_kernel) rfl)
    hx20 hpc hrun hnext

/-! ## Shared Exit Blocks: Epilogue, LL/SC Commit, and `free_meta` -/

scoped macro "wp_stp64_p" m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_sep_access); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _; try simp only [arm64_norm] at $hm:ident))

scoped macro "wp_str64_p" m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _; try simp only [arm64_norm] at $hm:ident))

scoped macro "wp_str32_p" m:ident hm:ident : tactic => `(tactic| (
  apply step_str32_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _; try simp only [arm64_norm] at $hm:ident))

scoped macro "wp_str16_p" m:ident hm:ident : tactic => `(tactic| (
  apply step_str16_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _; try simp only [arm64_norm] at $hm:ident))

scoped macro "wp_str8_p" m:ident hm:ident : tactic => `(tactic| (
  apply step_str8_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _; try simp only [arm64_norm] at $hm:ident))

def NfStaticRest (γ : GhostName) (A : MallocngAddrs) (st : MallocngSt) : SepProp :=
  MallocngLiveAuth γ st.liveMap ∗ (A.lock ↦₃₂ 0#32) ∗ (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap

theorem coreStInflightA_eq_nfParts (k : Nat) (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) :
    MallocngCoreStInflightA k γ A brkStart brk liveCost peakCost st =
      (⌜MallocngWFInflight k A.base brkStart brk liveCost peakCost st⌝ ∗
       NfStaticRest γ A st ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st)) := by
  unfold MallocngCoreStInflightA NfStaticRest; ac_rfl

def NfRetSep (st st' : MallocngSt) (x0 x1 : BitVec 64) : SepProp :=
  if x1 = 0#64 then
    ⌜dynamicRootRegions st' = dynamicRootRegions st⌝
  else
    let miBase := x0
    let miLen := x1.toNat
    ⌜0 < miLen ∧ 4096 ∣ miBase.toNat ∧ 4096 ∣ miLen ∧ miBase.toNat + miLen ≤ 2 ^ 48 ∧
     (∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st) a →
       InRegion miBase miLen a ∨ MallocngInIntervals (dynamicRootRegions st') a)⌝ ∗
    memRegion miBase miLen ∗ memMapped miBase miLen

theorem nfRetSep_congr_dyn {st0 st1 st2 : MallocngSt} (x0 x1 : BitVec 64)
    (hDyn : dynamicRootRegions st2 = dynamicRootRegions st1) :
    NfRetSep st0 st2 x0 x1 = NfRetSep st0 st1 x0 x1 := by unfold NfRetSep; rw [hDyn]

theorem nfRetSep_congr_left {st0 st1 st2 : MallocngSt} (x0 x1 : BitVec 64)
    (hDyn : dynamicRootRegions st1 = dynamicRootRegions st0) :
    NfRetSep st1 st2 x0 x1 = NfRetSep st0 st2 x0 x1 := by unfold NfRetSep; rw [hDyn]

def NfFuelPost [MallocngMultiPlacement]
    (k fuel : Nat) (γ : GhostName) (brkStart : BitVec 64) (bud : MallocngBudget)
    (st : MallocngSt) (s0 sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ ∃∗ st' : MallocngSt,
    ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
     sf.mem.perm = s0.mem.perm ∧ st'.reservedMetas = st.reservedMetas ∧
     st'.metaAreas = st.metaAreas ∧
     totalLiveCount st' ≤ totalLiveCount st ∧
     (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length ∧
     Cost.GroupsGrpMono st.groups st'.groups⌝ ∗
    stackFrameAt s0.sp (32 * (fuel + 1)) ∗ MallocngRoTablesA maddrs ∗
    MallocngCoreStInflightA k γ maddrs brkStart s0.brk bud.liveCost bud.peakCost st' ∗
    NfRetSep st st' (sf.readReg64 .x0) (sf.readReg64 .x1)) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem pointsToWords64_get_set (ptr : BitVec 64) (ws : List (BitVec 64))
    {i : Nat} (hi : i < ws.length) (v : BitVec 64) :
    (ptr ↦₆₄* ws) =
      (((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ ws[i]'hi) ∗
        ((ptr ↦₆₄* ws.take i) ∗ ((ptr + BitVec.ofNat 64 (8 * (i + 1))) ↦₆₄* ws.drop (i + 1)))) ∧
    (((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ v) ∗
      ((ptr ↦₆₄* ws.take i) ∗ ((ptr + BitVec.ofNat 64 (8 * (i + 1))) ↦₆₄* ws.drop (i + 1)))) =
      (ptr ↦₆₄* ws.set i v) := by
  have hDecomp : ws = ws.take i ++ ((ws[i]'hi) :: ws.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hSetDecomp : ∀ (ys : List (BitVec 64)) (k : Nat), k < ys.length →
      ys.set k v = ys.take k ++ (v :: ys.drop (k + 1)) := by
    intro ys; induction ys with
    | nil => intro _ hk; nomatch hk
    | cons y tl ih =>
      intro k hk; cases k with
      | zero => rfl
      | succ k' => simp [ih k' (Nat.lt_of_succ_lt_succ hk)]
  have hTakeL : (ws.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  have hAddr1 : ptr + BitVec.ofNat 64 (8 * i) + 8#64 = ptr + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]
  constructor
  · conv => lhs; rw [hDecomp]
    rw [pointsToWords64_append, hTakeL, pointsToWords64_cons, hAddr1]
    ac_rfl
  · conv => rhs; rw [hSetDecomp ws i hi]
    rw [pointsToWords64_append, hTakeL, pointsToWords64_cons, hAddr1]
    ac_rfl

theorem isAligned_w32_of_mod4 {a : BitVec 64} (h : a.toNat % 4 = 0) :
    MemWidth.isAligned .W32 a = true := by
  unfold MemWidth.isAligned
  apply beq_iff_eq.mpr; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& (2 ^ 2 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]; exact h

theorem step_stxr32_either_perm_next {prog : Program} {target_pc pc pc_next ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {v0 val : BitVec 32} {rel : Bool} {rs rn rt : Reg}
    (hpc : s.pc = pc) (hnext_pc : pc + 4#64 = pc_next) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true) (hval : s.readReg32 rt = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 rs 0#64).setPC pc_next).setMem m')
        ((ea ↦₃₂ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true →
      SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 rs 1#64).setPC pc_next)
        ((ea ↦₃₂ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  subst hnext_pc
  exact step_stxr32_either_perm hpc hrun hfetch hsp haddr halign hval hok hfail

theorem sepWP_nf_epilogue_490 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st st' : MallocngSt} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x490#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf' : MallocngWFInflight k maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st')
    (hRes : st'.reservedMetas = st.reservedMetas)
    (hMa : st'.metaAreas = st.metaAreas)
    (hCnt : totalLiveCount st' ≤ totalLiveCount st)
    (hDynLen : (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length)
    (hGrp : Cost.GroupsGrpMono st.groups st'.groups) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st') ∗
       NfRetSep st st' (s.readReg64 .x0) (s.readReg64 .x1))
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  have hspAl : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub32 (by simpa [State.spAligned] using hspAl0)
  have ha16 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_arith
  have ha24 : s0.sp - 16#64 + 8#64 = s0.sp - 8#64 := by bv_arith
  have ha8  : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_arith
  have ha32 : s0.sp - 32#64 + 32#64 = s0.sp := by bv_arith
  dsimp only [nfStackSaved]
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ⟨?_, by simp [arm64_norm], ?_⟩
  · refine Entails.sepExists_right st' ?_
    refine Entails.pure_right ⟨hProc, hbrk, hProc.2.2.1, hperm, hRes, hMa, hCnt, hDynLen, hGrp⟩ ?_
    rw [coreStInflightA_eq_nfParts, pure_sepConj_of_true hwf']
    simp only [arm64_norm]
    refine Entails.trans (repack_nfStack_rest s0.sp fuel hFuel s0 _) ?_
    sep_frame
  · obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs
    exact ⟨by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using h21, by simpa [arm64_norm] using h22,
      by simpa [arm64_norm] using h23, by simpa [arm64_norm] using h24,
      by simpa [arm64_norm] using h25, by simpa [arm64_norm] using h26,
      by simpa [arm64_norm] using h27, by simpa [arm64_norm] using h28,
      by simp [arm64_norm], by simpa [calleeSavedVRegs] using hv⟩

theorem sepWP_nf_or32_loop_478 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {ea : BitVec 64} {oldVal self32 : BitVec 32}
    (hAlign : MemWidth.isAligned .W32 ea = true)
    {Rest : SepProp} {s0 : State} {oom : State → SepProp} :
    ∀ (n : Nat) (s : State),
      s.exclFails.length < n →
      s.pc = b + 0x478#64 →
      s.status = .Running →
      s.readReg64 .x2 = ea →
      s.readReg32 .x1 = self32 →
      MallocngProcPreserved s0 s →
      Cs21Preserved s0 s →
      SepWP (blkPC_b05.rebase b (fun _ => none)) (b + 0x490#64) s
        ((ea ↦₃₂ oldVal) ∗ Rest)
        (fun s1 P1 =>
          s1.sp = s.sp ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
          MallocngProcPreserved s0 s1 ∧ Cs21Preserved s0 s1 ∧
          s1.readReg64 .x0 = 0#64 ∧ s1.readReg64 .x1 = 0#64 ∧
          (P1 ⊢ (ea ↦₃₂ (oldVal ||| self32)) ∗ Rest))
        oom := by
  intro n; induction n with
  | zero => intro _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    have _ := hb
    intro s hlt hpc hrun hx2 hx1 hProc hcs
    wp_steps 2
    refine step_stxr32_either_perm_next (pc := b + 0x480#64) (pc_next := b + 0x484#64)
      (ea := ea) (val := self32 ||| oldVal)
      (by simp [arm64_norm]) (by rw [BitVec.add_assoc]; rfl)
      (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm]) (by simpa [arm64_norm] using hx2) hAlign
      (by simp [arm64_norm]; rw [show BitVec.setWidth 32 (s.readReg64 (.gpr 1#5)) = self32 by simpa [arm64_norm] using hx1])
      (fun _ m' hm' _ => ?_) (fun hfail => ?_)
    · wp_step; wp_step; wp_step
      refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        ⟨by simp [arm64_norm],
         by simp [arm64_norm],
         by simpa [arm64_norm, State.stepExclOracle] using hm',
         ?_, ?_, by simp [arm64_norm], by simp [arm64_norm],
         by rw [BitVec.or_comm]; exact Entails.refl _⟩
      · obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc
        exact ⟨by simpa [State.stepExclOracle] using f1,
               by simpa [State.stepExclOracle] using f2,
               by simpa [State.stepExclOracle] using f3,
               by simpa [State.stepExclOracle] using f4,
               by simpa [State.stepExclOracle] using f5,
               by simpa [State.stepExclOracle] using f6,
               by simpa [State.stepExclOracle] using f7⟩
      · obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm, State.stepExclOracle] using c21,
               by simpa [arm64_norm, State.stepExclOracle] using c22,
               by simpa [arm64_norm, State.stepExclOracle] using c23,
               by simpa [arm64_norm, State.stepExclOracle] using c24,
               by simpa [arm64_norm, State.stepExclOracle] using c25,
               by simpa [arm64_norm, State.stepExclOracle] using c26,
               by simpa [arm64_norm, State.stepExclOracle] using c27,
               by simpa [arm64_norm, State.stepExclOracle] using c28,
               by simpa [calleeSavedVRegs, State.stepExclOracle] using cv⟩
    · wp_step
      have hTailLt : s.exclFails.tail.length < n := exclFails_tail_lt_free hlt hfail
      refine SepWP.mono (ih _ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        fun s1 P1 _ _ hpost =>
          ⟨by simpa [arm64_norm, State.stepExclOracle] using hpost.1,
           by simpa [arm64_norm, State.stepExclOracle] using hpost.2.1,
           by simpa [arm64_norm, State.stepExclOracle] using hpost.2.2.1,
           hpost.2.2.2⟩
      · simpa [arm64_norm, State.stepExclOracle] using hTailLt
      · simp [arm64_norm]
      · simp [arm64_norm, hrun]
      · simpa [arm64_norm] using hx2
      · simpa [arm64_norm] using hx1
      · obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc
        exact ⟨by simpa [State.stepExclOracle] using f1,
               by simpa [State.stepExclOracle] using f2,
               by simpa [State.stepExclOracle] using f3,
               by simpa [State.stepExclOracle] using f4,
               by simpa [State.stepExclOracle] using f5,
               by simpa [State.stepExclOracle] using f6,
               by simpa [State.stepExclOracle] using f7⟩
      · obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm, State.stepExclOracle] using c21,
               by simpa [arm64_norm, State.stepExclOracle] using c22,
               by simpa [arm64_norm, State.stepExclOracle] using c23,
               by simpa [arm64_norm, State.stepExclOracle] using c24,
               by simpa [arm64_norm, State.stepExclOracle] using c25,
               by simpa [arm64_norm, State.stepExclOracle] using c26,
               by simpa [arm64_norm, State.stepExclOracle] using c27,
               by simpa [arm64_norm, State.stepExclOracle] using c28,
               by simpa [calleeSavedVRegs, State.stepExclOracle] using cv⟩

theorem metaBytes_eq_cells (g : GroupDesc) :
    (g.metaPtr ↦ₛ g.metaBytes) =
      ((g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
       ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
       ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗ ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) := by
  unfold GroupDesc.metaBytes
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, unpack32_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  have h16 : (g.metaPtr + BitVec.ofNat 64 8) + BitVec.ofNat 64 8 = g.metaPtr + 16#64 := by bv_arith
  have h24 : (g.metaPtr + 16#64) + BitVec.ofNat 64 8 = g.metaPtr + 24#64 := by bv_arith
  have h28 : (g.metaPtr + 24#64) + BitVec.ofNat 64 4 = g.metaPtr + 28#64 := by bv_arith
  have h32 : (g.metaPtr + 28#64) + BitVec.ofNat 64 4 = g.metaPtr + 32#64 := by bv_arith
  rw [show BitVec.ofNat 64 8 = 8#64 from rfl, h16, h24, h28, h32]

theorem unpack32_pair_eq_unpack64 (a b : BitVec 32) :
    unpack32 a ++ unpack32 b = unpack64 (a.zeroExtend 64 ||| (b.zeroExtend 64 <<< 32)) := by
  simp only [unpack32, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_robdd

theorem metaBytes_eq_cells64 (g : GroupDesc) :
    ∃ w24 : BitVec 64,
      (g.metaPtr ↦ₛ g.metaBytes) =
        ((g.metaPtr ↦₆₄ g.prev) ∗ ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
         ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗ ((g.metaPtr + 24#64) ↦₆₄ w24) ∗
         ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) := by
  refine ⟨g.availMask.zeroExtend 64 ||| (g.freedMask.zeroExtend 64 <<< 32), ?_⟩
  have hEq : g.metaBytes = unpack64 g.prev ++ (unpack64 g.next ++ (unpack64 g.mem ++
      (unpack64 (g.availMask.zeroExtend 64 ||| (g.freedMask.zeroExtend 64 <<< 32)) ++
       unpack64 g.packedWord))) := by
    unfold GroupDesc.metaBytes
    rw [← unpack32_pair_eq_unpack64]
    simp only [List.append_assoc]
  rw [hEq]
  simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have h16 : (g.metaPtr + BitVec.ofNat 64 8) + BitVec.ofNat 64 8 = g.metaPtr + 16#64 := by bv_arith
  have h24 : (g.metaPtr + 16#64) + BitVec.ofNat 64 8 = g.metaPtr + 24#64 := by bv_arith
  have h32 : (g.metaPtr + 24#64) + BitVec.ofNat 64 8 = g.metaPtr + 32#64 := by bv_arith
  rw [show BitVec.ofNat 64 8 = 8#64 from rfl, h16, h24, h32]

theorem freeMeta_toBytes_cells (m prev next : BitVec 64) :
    (m ↦ₛ (⟨m, prev, next⟩ : FreeMetaDesc).toBytes) =
      ((m ↦₆₄ prev) ∗ ((m + 8#64) ↦₆₄ next) ∗
       ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₆₄ 0#64) ∗ ((m + 32#64) ↦₆₄ 0#64)) := by
  have hRep24 : List.replicate 24 0#8 = unpack64 0#64 ++ (unpack64 0#64 ++ unpack64 0#64) := by decide
  unfold FreeMetaDesc.toBytes
  rw [hRep24]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have h16 : (m + BitVec.ofNat 64 8) + BitVec.ofNat 64 8 = m + 16#64 := by bv_arith
  have h24 : (m + 16#64) + BitVec.ofNat 64 8 = m + 24#64 := by bv_arith
  have h32 : (m + 24#64) + BitVec.ofNat 64 8 = m + 32#64 := by bv_arith
  rw [show BitVec.ofNat 64 8 = 8#64 from rfl, h16, h24, h32]

theorem sepWP_nf_commit_474 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st st' : MallocngSt} {gPre gPost : GroupDesc} {self32 : BitVec 32}
    {ByteRest : SepProp} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x474#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = gPre.metaPtr) (hw1 : s.readReg32 .x1 = self32)
    (hmAlign : gPre.metaPtr.toNat % 8 = 0) (hmFit : gPre.metaPtr.toNat + 40 ≤ 2 ^ 48)
    (hMetaPtrEq : gPost.metaPtr = gPre.metaPtr)
    (hMetaBytesEq : { gPre with freedMask := gPre.freedMask ||| self32 }.metaBytes = gPost.metaBytes)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf' : MallocngWFInflight k maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st')
    (hRes : st'.reservedMetas = st.reservedMetas)
    (hMa : st'.metaAreas = st.metaAreas)
    (hCnt : totalLiveCount st' ≤ totalLiveCount st)
    (hDynEq : dynamicRootRegions st' = dynamicRootRegions st)
    (hGrp : Cost.GroupsGrpMono st.groups st'.groups)
    (hByteEq : ((gPost.metaPtr ↦ₛ gPost.metaBytes) ∗ ByteRest) =
      ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (gPre.metaPtr ↦ₛ gPre.metaBytes) ∗ ByteRest ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st'))
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  have hAl28 : MemWidth.isAligned .W32 (gPre.metaPtr + 28#64) = true := by
    apply isAligned_w32_of_mod4
    have h48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add_of_lt (by change gPre.metaPtr.toNat + 28 < 2 ^ 64; omega)]
    change (gPre.metaPtr.toNat + 28) % 4 = 0; omega
  wp_step
  have hFocus : (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (gPre.metaPtr ↦ₛ gPre.metaBytes) ∗ ByteRest ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st')) =
      (((gPre.metaPtr + 28#64) ↦₃₂ gPre.freedMask) ∗
       (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
        MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
        (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
        ((gPre.metaPtr ↦₆₄ gPre.prev) ∗ ((gPre.metaPtr + 8#64) ↦₆₄ gPre.next) ∗
         ((gPre.metaPtr + 16#64) ↦₆₄ gPre.mem) ∗ ((gPre.metaPtr + 24#64) ↦₃₂ gPre.availMask) ∗
         ((gPre.metaPtr + 32#64) ↦₆₄ gPre.packedWord)) ∗ ByteRest ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st'))) := by
    rw [metaBytes_eq_cells gPre]; ac_rfl
  rw [hFocus]
  refine SepWP.seq (sepWP_nf_or32_loop_478 hb hAl28 (_ + 1) _ (Nat.lt_succ_self _)
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm])
    (by simpa [arm64_norm] using hw1) hProc
    (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
        exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
               by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
               by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
               by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
               by simpa [calleeSavedVRegs] using cv⟩)) ?_
  intro s1 P1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx0_1, hx1_1, hP1⟩
  have hUnfocus : (((gPre.metaPtr + 28#64) ↦₃₂ (gPre.freedMask ||| self32)) ∗
       (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
        MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
        (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
        ((gPre.metaPtr ↦₆₄ gPre.prev) ∗ ((gPre.metaPtr + 8#64) ↦₆₄ gPre.next) ∗
         ((gPre.metaPtr + 16#64) ↦₆₄ gPre.mem) ∗ ((gPre.metaPtr + 24#64) ↦₃₂ gPre.availMask) ∗
         ((gPre.metaPtr + 32#64) ↦₆₄ gPre.packedWord)) ∗ ByteRest ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st'))) ⊢
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st' ∗
       (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st') ∗
       NfRetSep st st' (s1.readReg64 .x0) (s1.readReg64 .x1)) := by
    have hCellsUpd := metaBytes_eq_cells { gPre with freedMask := gPre.freedMask ||| self32 }
    dsimp only [] at hCellsUpd
    rw [hMetaBytesEq] at hCellsUpd
    rw [hx1_1]; unfold NfRetSep; simp only [↓reduceIte]
    rw [sepConj_comm (MappedSet st'.masterDom (OwnedMappedByte st')) ⌜_⌝, pure_sepConj_of_true hDynEq]
    rw [← hByteEq, hMetaPtrEq, hCellsUpd]
    sep_frame
  exact SepWP.weaken_pre (Entails.trans hP1 hUnfocus)
    (sepWP_nf_epilogue_490 hb hFuel hpc1 hrun1
      (hsp1.trans (by simpa [arm64_norm] using hsp)) hspAl0 hProc1
      (hbrk1.trans (by simpa [arm64_norm] using hbrk))
      (hperm1.trans (by simpa [arm64_norm] using hperm)) hcs1
      hwf' hRes hMa hCnt (by rw [hDynEq]; exact Nat.le_refl _) hGrp)

theorem sepWP_nf_freeMeta_224 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 5 b) {k fuel : Nat} (hFuel : fuel ≤ 6)
    {γ : GhostName} {brkStart : BitVec 64} {bud : MallocngBudget}
    {st st_m : MallocngSt} {gZero : GroupDesc} {s0 s : State} {oom : State → SepProp}
    (hpc : s.pc = b + 0x224#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = gZero.metaPtr) (hx20 : s.readReg64 .x20 = pageOf maddrs.ctx)
    (hmRes : gZero.metaPtr ∈ st_m.reservedMetas)
    (hsp : s.sp = s0.sp - 32#64) (hspAl0 : s0.spAligned = true)
    (hProc : MallocngProcPreserved s0 s) (hbrk : s.brk = s0.brk)
    (hperm : s.mem.perm = s0.mem.perm) (hcs : Cs21Preserved s0 s)
    (hwf_m : MallocngWFInflight (k + 1) maddrs.base brkStart s0.brk bud.liveCost bud.peakCost st_m)
    (hRes_m : st_m.reservedMetas.erase gZero.metaPtr = st.reservedMetas)
    (hMa_m : st_m.metaAreas = st.metaAreas)
    (hCnt_m : totalLiveCount st_m ≤ totalLiveCount st)
    (hDynLen_m : (dynamicRootRegions st_m).length ≤ (dynamicRootRegions st).length)
    (hGrp_m : Cost.GroupsGrpMono st.groups st_m.groups) :
    SepWP (blkPC_b05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackFrameAt (s0.sp - 32#64) (32 * fuel) ∗ nfStackSaved s0.sp s0 ∗
       MallocngRoTablesA maddrs ∗ NfStaticRest γ maddrs st_m ∗
       (maddrs.ctx ↦ₛ st_m.ctx.toBytes) ∗ (gZero.metaPtr ↦ₛ gZero.metaBytes) ∗
       ByteMap st_m.masterDom (OwnedRwByte st_m) st_m.byteVal ∗
       ProtNoneByteMap st_m.masterDom (OwnedProtNoneByte st_m) st_m.byteVal ∗
       MappedSet st_m.masterDom (OwnedMappedByte st_m) ∗
       NfRetSep st st_m (s.readReg64 .x0) (s.readReg64 .x1))
      (NfFuelPost k fuel γ brkStart bud st s0) oom := by
  have _ := hb
  let m := gZero.metaPtr
  obtain ⟨w24, hMetaCells⟩ := metaBytes_eq_cells64 gZero
  obtain ⟨CtxRest, hCtxRead, hCtxWrite⟩ :=
    ctx_focus_update_freeMetaHead maddrs.ctx st_m.ctx m
  have hm24 : (m + 16#64) + 8#64 = m + 24#64 := by bv_arith
  rw [hMetaCells, hCtxRead, ← hm24]
  wp_step
  have hCtx20 : pageOf maddrs.ctx + lo12Of maddrs.ctx = maddrs.ctx := pageOf_add_lo12Of maddrs.ctx
  wp_stp64_p m1 hm1
  wp_stp64_p m2 hm2
  wp_step
  wp_str64_p m3 hm3
  wp_step
  wp_if hHead0
  ·
    have hHd0 : st_m.ctx.freeMetaHead = 0#64 := by simpa [arm64_norm] using hHead0
    obtain ⟨hByte1, hProt1, hMap1, hWf1, hRes1, hDyn1, hCnt1⟩ :=
      free_recycle_reserved_meta_empty hwf_m hmRes hHd0
    wp_stp64_p m4 hm4
    wp_str64_p m5 hm5
    wp_step
    rw [hm24]
    refine SepWP.weaken_pre ?_ (sepWP_nf_epilogue_490 hb hFuel
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa [arm64_norm] using hbrk)
      (hm5.trans (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))))
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                 by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                 by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                 by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hWf1 (hRes1.trans hRes_m) hMa_m (by omega) (by rw [hDyn1]; exact hDynLen_m) hGrp_m)
    dsimp only [m, NfStaticRest] at hCtxWrite hByte1 ⊢
    simp only [arm64_norm]
    rw [← hCtxWrite, ← hByte1, freeMeta_toBytes_cells gZero.metaPtr gZero.metaPtr gZero.metaPtr,
        hProt1, hMap1, nfRetSep_congr_dyn _ _ hDyn1]
    sep_frame
  ·
    have hHdNe0 : st_m.ctx.freeMetaHead ≠ 0#64 := by simpa [arm64_norm] using hHead0
    let head := st_m.ctx.freeMetaHead
    obtain ⟨hdFm, _, tlFm, _, hHdPtr, hTlPtr, hSubHd, hSubTl, hReadHd0, hReadTl0,
            hReadHdAfterTl, hByte1, hProt1, hMap1, hWf1, hRes1, hDyn1, hCnt1⟩ :=
      free_recycle_reserved_meta_nonempty hwf_m hmRes hHdNe0
    let tlUpd : FreeMetaDesc := { tlFm with next := m }
    let hdMid : FreeMetaDesc := { hdFm with next := if head == hdFm.prev then m else hdFm.next }
    let hdUpd : FreeMetaDesc := { hdFm with prev := m, next := if head == hdFm.prev then m else hdFm.next }
    let bvTl := writeBytesToMap st_m.byteVal hdFm.prev tlUpd.toBytes
    wp_str64_p m4 hm4
    have hBmHd0 := (byteMap_update40 hwf_m.masterDom_wf.1 st_m.byteVal (m := head)
      (bs := hdFm.toBytes) (FreeMetaDesc.toBytes_length _) hSubHd).1
    have hHdCells0 : (head ↦ₛ hdFm.toBytes) =
        ((head ↦₆₄ hdFm.prev) ∗ ((head + 8#64) ↦₆₄ hdFm.next) ∗
         ((head + 16#64) ↦₆₄ 0#64) ∗ ((head + 24#64) ↦₆₄ 0#64) ∗ ((head + 32#64) ↦₆₄ 0#64)) := by
      have hc := freeMeta_toBytes_cells head hdFm.prev hdFm.next
      cases hdFm; dsimp only [] at hHdPtr hc ⊢; subst hHdPtr; exact hc
    rw [hBmHd0, hReadHd0, hHdCells0]
    wp_step
    rw [← hHdCells0, ← hReadHd0, ← hBmHd0]
    wp_str64_p m5 hm5
    have ⟨hBmTl0, hBmTlW⟩ := byteMap_update40 hwf_m.masterDom_wf.1 st_m.byteVal (m := hdFm.prev)
      (bs := tlUpd.toBytes) (FreeMetaDesc.toBytes_length _) hSubTl
    have hTlCells0 : (hdFm.prev ↦ₛ tlFm.toBytes) =
        ((hdFm.prev ↦₆₄ tlFm.prev) ∗ ((hdFm.prev + 8#64) ↦₆₄ tlFm.next) ∗
         ((hdFm.prev + 16#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 24#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 32#64) ↦₆₄ 0#64)) := by
      have hc := freeMeta_toBytes_cells hdFm.prev tlFm.prev tlFm.next
      cases tlFm; dsimp only [] at hTlPtr hc ⊢; subst hTlPtr; exact hc
    have hTlCells1 : ((hdFm.prev ↦₆₄ tlFm.prev) ∗ ((hdFm.prev + 8#64) ↦₆₄ m) ∗
         ((hdFm.prev + 16#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 24#64) ↦₆₄ 0#64) ∗ ((hdFm.prev + 32#64) ↦₆₄ 0#64)) =
        (hdFm.prev ↦ₛ tlUpd.toBytes) := by
      have hc := freeMeta_toBytes_cells hdFm.prev tlFm.prev m
      cases tlFm; dsimp only [tlUpd] at hTlPtr hc ⊢; subst hTlPtr; exact hc.symm
    rw [hBmTl0, hReadTl0, hTlCells0]
    wp_str64_p m6 hm6
    wp_step
    try rw [hx19]
    dsimp only [m] at hTlCells1
    rw [hTlCells1, hBmTlW]
    have ⟨hBmHd1, hBmHdW⟩ := byteMap_update40 hwf_m.masterDom_wf.1 bvTl (m := head)
      (bs := hdUpd.toBytes) (FreeMetaDesc.toBytes_length _) hSubHd
    have hHdCellsMid : (head ↦ₛ hdMid.toBytes) =
        ((head ↦₆₄ hdFm.prev) ∗ ((head + 8#64) ↦₆₄ hdMid.next) ∗
         ((head + 16#64) ↦₆₄ 0#64) ∗ ((head + 24#64) ↦₆₄ 0#64) ∗ ((head + 32#64) ↦₆₄ 0#64)) := by
      have hc := freeMeta_toBytes_cells head hdFm.prev hdMid.next
      cases hdFm; dsimp only [hdMid] at hHdPtr hc ⊢; subst hHdPtr; exact hc
    have hHdCellsUpd : ((head ↦₆₄ m) ∗ ((head + 8#64) ↦₆₄ hdMid.next) ∗
         ((head + 16#64) ↦₆₄ 0#64) ∗ ((head + 24#64) ↦₆₄ 0#64) ∗ ((head + 32#64) ↦₆₄ 0#64)) =
        (head ↦ₛ hdUpd.toBytes) := by
      have hc := freeMeta_toBytes_cells head m hdMid.next
      cases hdFm; dsimp only [hdUpd, hdMid] at hHdPtr hc ⊢; subst hHdPtr; exact hc.symm
    rw [hBmHd1, hReadHdAfterTl, hHdCellsMid]
    wp_str64_p m7 hm7
    wp_step
    rw [hm24]
    refine SepWP.weaken_pre ?_ (sepWP_nf_epilogue_490 hb hFuel
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hsp) hspAl0
      (by obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hProc; exact ⟨f1, f2, f3, f4, f5, f6, f7⟩)
      (by simpa [arm64_norm] using hbrk)
      (hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))))))
      (by obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, cv⟩ := hcs
          exact ⟨by simpa [arm64_norm] using c21, by simpa [arm64_norm] using c22,
                 by simpa [arm64_norm] using c23, by simpa [arm64_norm] using c24,
                 by simpa [arm64_norm] using c25, by simpa [arm64_norm] using c26,
                 by simpa [arm64_norm] using c27, by simpa [arm64_norm] using c28,
                 by simpa [calleeSavedVRegs] using cv⟩)
      hWf1 (hRes1.trans hRes_m) hMa_m (by omega) (by rw [hDyn1]; exact hDynLen_m) hGrp_m)
    dsimp only [m, NfStaticRest] at hHdCellsUpd ⊢
    simp only [arm64_norm]
    rw [hCtxRead, ← hByte1, freeMeta_toBytes_cells gZero.metaPtr hdFm.prev head,
        ← hBmHdW, ← hHdCellsUpd, hProt1, hMap1, nfRetSep_congr_dyn _ _ hDyn1]
    sep_frame

end

end LibsignalBinary.Heap.Fine.VendorFree
