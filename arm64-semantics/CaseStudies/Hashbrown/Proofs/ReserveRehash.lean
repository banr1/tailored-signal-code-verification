/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.ResizeCopy

/-!
# Verification of `RawTable::reserve_rehash`

Proves placement-generic total-correctness contracts for `RawTable::reserve_rehash`, covering old
table deallocation, post-allocation wrap-up, entry dispatch, and cold panic paths.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.ResizeInternal

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "hb_top " h:ident : tactic => `(tactic|
  exact ⟨by simpa using ($h).1, by simpa [calleeSavedVRegs] using ($h).2⟩)

theorem hbReserve_retFrom1080 (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 s : State} {mapPtr bm bm' vPad : BitVec 64} {m : Map64} {lc blk : Nat} {oom : State → SepProp}
    (hasp : AllocStatePreserved s0 s) (hvnm : ValidNextMask m bm bm')
    (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64) (hsp0_al : s0.spAligned = true)
    (hpc : s.pc = P.pl.base + 1080#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = 0xffffffffffffffff#64)
    (htop : HbTopSaved s0 s) :
    SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) s
      (hbReserveFrame s0 vPad ∗
       (U64MapRepReady P.pl A mapPtr m bm' ∗
        A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
               ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) s ∗
        stackAt (s0.sp - 96#64) (16 + A.stackBytes)))
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
          stackAt s0.sp (112 + A.stackBytes) ∗
          (∃∗ bm'' : BitVec 64,
            ⌜ValidNextMask m bm bm''⌝ ∗ U64MapRepReady P.pl A mapPtr m bm'' ∗
            A.Heap ((lc + hbMapCost A bm'') - hbMapCost A bm)
                   ((blk + tableAllocBlocks bm'') - tableAllocBlocks bm) sf))) oom := by
  refine hbReserve_epilogue P X hpc hrun hsp hsp0_al hx0 htop
    fun sf _ _ hspf hx0f hcsf hstd_sf hmem_sf => ⟨hspf, hcsf, ?_⟩
  have hasp_f : AllocStatePreserved s0 sf :=
    ⟨hstd_sf.1.trans hasp.1, hstd_sf.2.1.trans hasp.2.1, hstd_sf.2.2.2.1.trans hasp.2.2.1,
     hstd_sf.2.2.1.trans hasp.2.2.2.1, hmem_sf ▸ hasp.2.2.2.2⟩
  refine Entails.pure_right ⟨hx0f, hasp_f⟩ ?_
  rw [show 112 + A.stackBytes = (16 + A.stackBytes) + 96 by omega,
      stackAt_region s0.sp (16 + A.stackBytes) 96 (by omega)]
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ memRegion (s0.sp - 96#64) 96) ∗
    (U64MapRepReady P.pl A mapPtr m bm' ∗
     A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
            ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) s) by ac_rfl))
    (sepConj_mono_right ?_)
  refine Entails.sepExists_right bm' (Entails.pure_right hvnm ?_)
  exact sepConj_mono_right (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd_sf))

theorem hbResize_deallocOld (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    {target : BitVec 64} {s0 s : State} {bm oldItems : BitVec 64} {w : HbHeapMapWitness} {m : Map64}
    {lc_in blk_in : Nat} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hCode0 : A.CodeInv s0.mem) (hasp : AllocStatePreserved s0 s) (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64)
    (hinv : SwissTableInv bm w.growthLeft oldItems w.ctrl w.slots m)
    (ha_nw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)))
    (hpc : s.pc = P.pl.base + 1036#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = w.ctrlPtr) (hx23 : s.readReg64 .x23 = bm)
    (hx24 : s.readReg64 .x24 = bm + 1#64) (htop : HbTopSaved s0 s)
    (hcont : ∀ sf : State, sf.pc = P.pl.base + 548#64 → sf.status = .Running →
      sf.sp = s0.sp - 96#64 → sf.spAligned = true → HbTopSaved s0 sf → AllocStatePreserved s0 sf →
      SepWP ((hbProg P).rebase P.pl.base X) target sf
        (A.Heap (lc_in - hbMapCost A bm) (blk_in - tableAllocBlocks bm) sf ∗
         stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) target s
      (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗
       A.Heap lc_in blk_in s ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hv_bm := hinv.validMask; have hbm_ne := hv_bm.ne_zero
  obtain ⟨hsh4, hadd8, htab, htab_le, _, _⟩ := (ValidBucketMask.tableAlloc_machine_ok hv_bm)
  have hb_add : bm + 1#64 = BitVec.ofNat 64 (bm.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  let sz := 17 * (bm.toNat + 1) + 8; let szBV := BitVec.ofNat 64 sz
  have htab_eq : tableAllocBytes bm = sz := by simp only [tableAllocBytes, hbm_ne, ↓reduceIte, sz]
  have hsz_nat : szBV.toNat = sz := by simp only [szBV, BitVec.toNat_ofNat, ← htab_eq]; omega
  have hlay : LayoutOk szBV 8#64 := (ValidBucketMask.tableLayoutOk hv_bm)
  have hptr_eq : w.ctrlPtr - ((bm + 1#64) <<< 4) = w.allocPtr := by rw [hctrl, hb_add, hsh4]; bv_lin
  have hsz_eq : bm + ((bm + 1#64) <<< 4) + 9#64 = szBV := by
    rw [show bm + ((bm + 1#64) <<< 4) + 9#64 = ((bm + 1#64) + 8#64) + ((bm + 1#64) <<< 4) by bv_lin,
        hb_add, hadd8, hsh4, ← BitVec.ofNat_add, htab, htab_eq]
  have hcol : slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ⊢ memRegion w.allocPtr sz := by
    have hs1 : slotsDownFrom w.ctrlPtr w.slots ⊢ memRegion w.allocPtr (16 * (bm.toNat + 1)) := by
      have hsl := hinv.slots_len; rw [hctrl, ← hsl]; exact slotsDownFrom_to_memRegion w.slots w.allocPtr (by omega)
    have hs2 : (w.ctrlPtr ↦ₛ w.ctrl) ⊢ memRegion (w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (bm.toNat + 1 + 8) := by
      rw [← hctrl, ← hinv.mirror.1]; exact pointsToBytes_entails_memRegion w.ctrlPtr w.ctrl
    exact Entails.trans (sepConj_mono hs1 hs2)
      (by rw [← memRegion_split w.allocPtr (16 * (bm.toNat + 1)) (bm.toNat + 1 + 8) (by omega)]; exact Entails.of_eq (by congr 1; omega))
  have hstk_sh := stackAt_shrink (s0.sp - 96#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
  simp only [arm64_norm] at hx8 hx23 hx24
  wp_sym_steps 6
  suffices ∀ sc : State, sc.pc = P.pl.ρ hbDeallocSym → sc.status = .Running → sc.sp = s0.sp - 96#64 →
      sc.spAligned = true → sc.readReg64 Reg.lr = P.pl.base + 1060#64 →
      sc.readReg64 .x0 = w.allocPtr → sc.readReg64 .x1 = szBV → sc.readReg64 .x2 = 8#64 →
      HbTopSaved s0 sc → HbVmPreserved s sc → AllocStatePreserved s0 sc →
      SepWP ((hbProg P).rebase P.pl.base X) target sc
        (A.Block w.allocPtr sz 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗
         A.Heap lc_in blk_in s ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ F) post oom by
    refine this _
      (by dsimp only [hbDeallocSym]; simpa only [arm64_norm] using (by bv_lin :
          P.pl.base + 1056#64 + (P.pl.ρ hbDeallocSym - P.pl.base - 1056#64) = P.pl.ρ hbDeallocSym))
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simpa only [State.spAligned, arm64_norm, hsp] using hsp_al) (by simp only [arm64_norm])
      (by simp only [arm64_norm]; exact hctrl ▸ hptr_eq)
      (by simp only [arm64_norm]; exact hsz_eq) (by simp only [arm64_norm])
      ⟨by simpa only [arm64_norm] using htop.1, by simpa only [calleeSavedVRegs, arm64_norm] using htop.2⟩
      ⟨by simp, by simp, by simp, by simp, fun _ => rfl⟩
      ⟨by simpa using hasp.1, by simpa using hasp.2.1, by simpa using hasp.2.2.1,
       by simpa using hasp.2.2.2.1, by simpa using hasp.2.2.2.2⟩
  intro sc hpc_c hrun_c hsp_c hsp_c_al hlr_c hx0_c hx1_c hx2_c htop_c hvm_sc hasp_0c
  refine SepWP.weaken_pre (P' := A.Heap lc_in blk_in sc ∗ A.Block w.allocPtr sz 8 ∗ memRegion w.allocPtr sz ∗
    stackAt sc.sp A.stackBytes ∗
    (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes) ∗ F))
    (by rw [hsp_c, hstk_sh]
        exact Entails.trans (Entails.of_eq (show _ =
          (slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗
          (A.Heap lc_in blk_in s ∗ (A.Block w.allocPtr sz 8 ∗ stackAt (s0.sp - 96#64) A.stackBytes ∗
           (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes) ∗ F))) by ac_rfl))
          (Entails.trans (sepConj_mono hcol (sepConj_mono_left (A.heap_transport hvm_sc))) (Entails.of_eq (by ac_rfl)))) ?_
  refine SepWP.call_subroutine_frame hext.dealloc_ok (x := (w.allocPtr, szBV, 8#64, lc_in, blk_in))
    (F := memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes) ∗ F)
    (ret_pc := P.pl.base + 1060#64) hpc_c hrun_c hsp_c_al hlr_c
    (fun R' hm => by
      dsimp only [withCodeInv, hbDeallocSpec]; rw [hsz_nat, show (8#64 : BitVec 64).toNat = 8 from rfl, sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hasp_0c.2.2.2.2 hCode0, ?_⟩
      rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0_c, hx1_c, hx2_c, hlay⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sd hpcd hrund hspd hcsd => ?_) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  dsimp only [withCodeInv, hbDeallocSpec]; rw [hsz_nat, show (8#64 : BitVec 64).toNat = 8 from rfl, sepConj_assoc]
  refine sepWP_pure_elim fun hasp_d => ?_
  have hasp_0d : AllocStatePreserved s0 sd :=
    ⟨hasp_d.1.trans hasp_0c.1, hasp_d.2.1.trans hasp_0c.2.1, hasp_d.2.2.1.trans hasp_0c.2.2.1,
     hasp_d.2.2.2.1.trans hasp_0c.2.2.2.1, hasp_0c.2.2.2.2.trans hasp_d.2.2.2.2⟩
  have htop_d : HbTopSaved s0 sd := HbTopSaved.trans_cs htop_c hcsd
  have hcost_eq : A.cost sz 8 = hbMapCost A bm := by simp only [hbMapCost, hbm_ne, ↓reduceIte, htab_eq]
  have hblk_eq : 1 = tableAllocBlocks bm := by simp only [tableAllocBlocks, hbm_ne, ↓reduceIte]
  wp_step
  refine SepWP.weaken_pre ?_ (hcont _ (by simp) (by simp [hrund]) (by simp [hspd, hsp_c])
    (by simpa [State.spAligned, hspd, hsp_c, hsp] using hsp_al)
    (by hb_top htop_d)
    ⟨by simpa using hasp_0d.1, by simpa using hasp_0d.2.1, by simpa using hasp_0d.2.2.1,
     by simpa using hasp_0d.2.2.2.1, by simpa using hasp_0d.2.2.2.2⟩)
  rw [hcost_eq, hblk_eq, hsp_c, hstk_sh]
  exact Entails.trans (Entails.of_eq (show _ =
    A.Heap (lc_in - hbMapCost A bm) (blk_in - tableAllocBlocks bm) sd ∗
    (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes) ∗
     stackAt (s0.sp - 96#64) A.stackBytes) ∗ F by ac_rfl))
    (sepConj_mono_left (@HbAlloc.heap_transport A _ _ sd (sd.setPC (P.pl.base + 548#64))
      ⟨by simp, by simp, by simp, by simp, fun _ => by simp⟩))

theorem hbResize_retFrom548 (P : HbPlaced) (A : HbAlloc) (X : String → Option (State → State))
    {s0 s : State} {mapPtr bm bm' vPad : BitVec 64} {m : Map64} {lc blk : Nat} {oom : State → SepProp}
    (hasp : AllocStatePreserved s0 s) (hvnm : ValidNextMask m bm bm')
    (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64) (hsp0_al : s0.spAligned = true)
    (hpc : s.pc = P.pl.base + 548#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (htop : HbTopSaved s0 s) :
    SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) s
      (hbReserveFrame s0 vPad ∗
       (U64MapRepReady P.pl A mapPtr m bm' ∗
        A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
               ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) s ∗
        stackAt (s0.sp - 96#64) (16 + A.stackBytes)))
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
          stackAt s0.sp (112 + A.stackBytes) ∗
          (∃∗ bm'' : BitVec 64,
            ⌜ValidNextMask m bm bm''⌝ ∗ U64MapRepReady P.pl A mapPtr m bm'' ∗
            A.Heap ((lc + hbMapCost A bm'') - hbMapCost A bm)
                   ((blk + tableAllocBlocks bm'') - tableAllocBlocks bm) sf))) oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  wp_sym_steps 2
  refine SepWP.weaken_pre ?_ (hbReserve_retFrom1080 P A X (lc := lc) (blk := blk) (vPad := vPad)
    ⟨by simpa using hasp.1, by simpa using hasp.2.1, by simpa using hasp.2.2.1,
     by simpa using hasp.2.2.2.1, by simpa using hasp.2.2.2.2⟩
    hvnm hstk_nw hsp0_al (by simp) (by simp [hrun]) (by simp [hsp])
    (by simp [Reg.x0]) (by hb_top htop))
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (A.heap_transport ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩)))

theorem hbResize_finishAt1020 (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    {s0 s3 : State} {mapPtr oldCtrlPtr oldGl bm bm' items newAllocPtr newCtrlPtr vPad : BitVec 64}
    {newCtrlF : List (BitVec 8)} {newSlotsF : List (BitVec 64 × BitVec 64)}
    {m : Map64} {oldRest : SepProp} {lc blk : Nat} {oom : State → SepProp}
    (hCode0 : A.CodeInv s0.mem) (hasp : AllocStatePreserved s0 s3)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hwf : Map64Wf m)
    (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64) (hsp0_al : s0.spAligned = true)
    (hvnm : ValidNextMask m bm bm') (hbm' : ValidBucketMask bm')
    (ha_ne : newAllocPtr ≠ 0#64) (ha_al : newAllocPtr.toNat % 8 = 0)
    (ha_nw : newAllocPtr.toNat + (17 * (bm'.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl_new : newCtrlPtr = newAllocPtr + BitVec.ofNat 64 (16 * (bm'.toNat + 1)))
    (hinv_new : SwissTableInv bm' (bucketMaskToCapacityBV bm' - items) items newCtrlF newSlotsF m)
    (hgl_pos : 0 < (bucketMaskToCapacityBV bm' - items).toNat)
    (hold_cases : (bm = 0#64 ∧ oldRest = emp) ∨
      ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧
        SwissTableInv bm w.growthLeft items w.ctrl w.slots m ∧
        w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
        w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
        oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)))
    (hpc3 : s3.pc = P.pl.base + 1020#64) (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 96#64) (hsp3_al : s3.spAligned = true)
    (hx8 : s3.readReg64 .x8 = oldCtrlPtr) (hx9 : s3.readReg64 .x9 = mapPtr)
    (hx19 : s3.readReg64 .x19 = newCtrlPtr) (hx21 : s3.readReg64 .x21 = bm')
    (hx22 : s3.readReg64 .x22 = items) (hx23 : s3.readReg64 .x23 = bm)
    (hx24 : s3.readReg64 .x24 = bm + 1#64) (hx25 : s3.readReg64 .x25 = bucketMaskToCapacityBV bm')
    (htop3 : HbTopSaved s0 s3) :
    SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) s3
      (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
       hbRodata P.pl ∗ A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗
       slotsDownFrom newCtrlPtr newSlotsF ∗ (newCtrlPtr ↦ₛ newCtrlF) ∗
       oldRest ∗ A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s3 ∗
       stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
          stackAt s0.sp (112 + A.stackBytes) ∗
          (∃∗ bm'' : BitVec 64,
            ⌜ValidNextMask m bm bm''⌝ ∗ U64MapRepReady P.pl A mapPtr m bm'' ∗
            A.Heap ((lc + hbMapCost A bm'') - hbMapCost A bm)
                   ((blk + tableAllocBlocks bm'') - tableAllocBlocks bm) sf))) oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  refine sepWP_seq_frozen (mid := P.pl.base + 1032#64) (Φ := fun m => s0.mem.KeepsFrozen m)
    (fun _ _ => Memory.KeepsFrozen.trans) hasp.2.2.2.2 ?_
  wp_conv_pre => unfold U64MapStruct
  wp_step
  refine step_stp64_perm (pc := P.pl.base + 1024#64) (rt1 := .x19) (rt2 := .x21)
    (addr := .Offset .x9 0#64) (ea := mapPtr) (ea2 := mapPtr + 8#64)
    (v1 := newCtrlPtr) (v2 := bm') (wb := none)
    (by simp) (by simp [hrun3]) (by simp) rfl
    (by simp [evalAddrMode, hx9]) rfl
    (by simpa [Reg.x19] using hx19) (by simpa [Reg.x21] using hx21)
    (by wp_sep_access_fast) (by wp_sep_access_fast) fun m1 hm1 => ?_
  dsimp only [applyWriteback]
  refine step_str64_perm (pc := P.pl.base + 1028#64) (rt := .x10) (addr := .Offset .x9 16#64)
    (ea := mapPtr + 16#64) (val := bucketMaskToCapacityBV bm' - items) (wb := none)
    (by simp) (by simp [hrun3]) (by simp) rfl
    (by simp [evalAddrMode, hx9]) (by simp [Reg.x10])
    (by wp_sep_access_fast) fun m2 hm2 => ?_
  dsimp only [applyWriteback]
  have hready := U64MapRepReady_of_parts (pl := P.pl) (A := A) hal hnw hwf hbm' hinv_new hgl_pos ha_ne ha_al ha_nw hctrl_new
  wp_conv_pre => change ((mapPtr ↦₆₄ newCtrlPtr ∗ ((mapPtr + 8#64) ↦₆₄ bm' ∗
    ((mapPtr + 16#64) ↦₆₄ (bucketMaskToCapacityBV bm' - items) ∗ (mapPtr + 24#64) ↦₆₄ items))) ∗
    hbRodata P.pl ∗ A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗
    slotsDownFrom newCtrlPtr newSlotsF ∗ (newCtrlPtr ↦ₛ newCtrlF) ∗
    oldRest ∗ A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s3 ∗
    stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad)
  have hrearr1 :
      ((mapPtr ↦₆₄ newCtrlPtr ∗ ((mapPtr + 8#64) ↦₆₄ bm' ∗
        ((mapPtr + 16#64) ↦₆₄ (bucketMaskToCapacityBV bm' - items) ∗ (mapPtr + 24#64) ↦₆₄ items))) ∗
       hbRodata P.pl ∗ A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗
       slotsDownFrom newCtrlPtr newSlotsF ∗ (newCtrlPtr ↦ₛ newCtrlF) ∗
       oldRest ∗ A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s3 ∗
       stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad) =
      ((hbRodata P.pl ∗ U64MapStruct mapPtr newCtrlPtr bm' (bucketMaskToCapacityBV bm' - items) items ∗
        A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗
        slotsDownFrom newCtrlPtr newSlotsF ∗ (newCtrlPtr ↦ₛ newCtrlF)) ∗
       (A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s3 ∗
        (oldRest ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad))) := by
    dsimp only [U64MapStruct]; ac_rfl
  suffices ∀ s4 : State, s4.pc = P.pl.base + 1032#64 → s4.status = .Running → s4.sp = s0.sp - 96#64 →
      s4.spAligned = true → s4.readReg64 .x8 = oldCtrlPtr → s4.readReg64 .x23 = bm →
      s4.readReg64 .x24 = bm + 1#64 → HbTopSaved s0 s4 → AllocStatePreserved s0 s4 →
      SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) s4
        (U64MapRepReady P.pl A mapPtr m bm' ∗ oldRest ∗
         A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s4 ∗
         stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad)
        (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (Pf ⊢ ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
            stackAt s0.sp (112 + A.stackBytes) ∗
            (∃∗ bm'' : BitVec 64,
              ⌜ValidNextMask m bm bm''⌝ ∗ U64MapRepReady P.pl A mapPtr m bm'' ∗
              A.Heap ((lc + hbMapCost A bm'') - hbMapCost A bm)
                     ((blk + tableAllocBlocks bm'') - tableAllocBlocks bm) sf))) oom by
    let s3' := ((((((s3.writeReg64 (.gpr 10#5) (bucketMaskToCapacityBV bm' - items)).setPC
      (P.pl.base + 1024#64)).setPC (P.pl.base + 1024#64 + 4#64)).setMem m1).setPC
      (P.pl.base + 1028#64 + 4#64)).setMem m2)
    refine SepWP.weaken_pre (P' := U64MapRepReady P.pl A mapPtr m bm' ∗ oldRest ∗
      A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s3' ∗
      stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad) ?_ ?_
    · rw [hrearr1]
      exact Entails.trans (sepConj_mono hready (sepConj_mono_left
        (@HbAlloc.heap_transport A _ _ s3 s3'
          ⟨by simp [s3'], by simp [s3'], by simp [s3'], by simp [s3'],
           fun a => by simpa [s3'] using congrFun (hm2.trans hm1) a⟩)))
        (Entails.of_eq (by ac_rfl))
    · refine SepWP.done (by simp) (by simp [hrun3]) fun hkf4 => ?_
      exact this s3' (by simp [s3']) (by simp [s3', hrun3]) (by simp [s3', hsp3])
        (by simpa [s3', State.spAligned, hsp3] using hsp3_al)
        (by simpa [s3', Reg.x8] using hx8) (by simpa [s3', Reg.x23] using hx23)
        (by simpa [s3', Reg.x24] using hx24) (by dsimp only [s3']; hb_top htop3)
        ⟨by simpa [s3'] using hasp.1, by simpa [s3'] using hasp.2.1, by simpa [s3'] using hasp.2.2.1,
         by simpa [s3'] using hasp.2.2.2.1, hkf4⟩
  intro s4 hpc4 hrun4 hsp4 hsp4_al hx8_4 hx23_4 hx24_4 htop4 hasp4
  rcases hold_cases with ⟨rfl, rfl⟩ | ⟨w, rfl, hinv_old, ha_nw_old, hctrl_old, rfl⟩
  · wp_step
    refine SepWP.weaken_pre ?_ (hbResize_retFrom548 P A X (lc := lc) (blk := blk) (vPad := vPad)
      ⟨by simpa using hasp4.1, by simpa using hasp4.2.1, by simpa using hasp4.2.2.1,
       by simpa using hasp4.2.2.2.1, by simpa using hasp4.2.2.2.2⟩ hvnm hstk_nw hsp0_al
      (by simp) (by simp [hrun4]) (by simp [hsp4]) (by hb_top htop4))
    rw [emp_sepConj, hbMapCost_zero, show tableAllocBlocks 0#64 = 0 from rfl, Nat.sub_zero, Nat.sub_zero]
    exact Entails.trans (Entails.of_eq (show _ =
      hbReserveFrame s0 vPad ∗
      (U64MapRepReady P.pl A mapPtr m bm' ∗ A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s4 ∗
       stackAt (s0.sp - 96#64) (16 + A.stackBytes)) by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (@HbAlloc.heap_transport A _ _ s4 (s4.setPC (P.pl.base + 548#64))
          ⟨by simp, by simp, by simp, by simp, fun _ => by simp⟩))))
  · have hbm_ne := hinv_old.validMask.ne_zero
    wp_step; apply SepWP.ite_false rfl (by simpa [hx23_4] using hbm_ne)
    refine SepWP.weaken_pre ?_ (hbResize_deallocOld P A X hext
      (lc_in := lc + hbMapCost A bm') (blk_in := blk + tableAllocBlocks bm')
      (F := hbReserveFrame s0 vPad ∗ U64MapRepReady P.pl A mapPtr m bm') hCode0
      ⟨by simpa using hasp4.1, by simpa using hasp4.2.1, by simpa using hasp4.2.2.1,
       by simpa using hasp4.2.2.2.1, by simpa using hasp4.2.2.2.2⟩ hstk_nw hinv_old ha_nw_old hctrl_old
      (by simp) (by simp [hrun4]) (by simp [hsp4])
      (by simpa [State.spAligned, hsp4] using hsp4_al)
      (by simpa [Reg.x8] using hx8_4) (by simpa [Reg.x23] using hx23_4)
      (by simpa [Reg.x24] using hx24_4) (by hb_top htop4) fun s5 hpc5 hrun5 hsp5 _ htop5 hasp5 => ?_)
    · exact Entails.trans (Entails.of_eq (show _ =
        A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗
        A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') s4 ∗
        stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ (hbReserveFrame s0 vPad ∗ U64MapRepReady P.pl A mapPtr m bm') by ac_rfl))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (A.heap_transport ⟨by simp, by simp, by simp, by simp, fun _ => by simp⟩)))))
    · refine SepWP.weaken_pre ?_ (hbResize_retFrom548 P A X (lc := lc) (blk := blk) (vPad := vPad)
        hasp5 hvnm hstk_nw hsp0_al hpc5 hrun5 hsp5 htop5)
      exact Entails.of_eq (by ac_rfl)

theorem hbResize_postAlloc (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    {s0 sa : State} {mapPtr oldCtrlPtr oldGl bm items vPad : BitVec 64} {m : Map64}
    {oldRest : SepProp} {lc blk : Nat} {oom : State → SepProp}
    (hCode0 : A.CodeInv s0.mem) (hasp : AllocStatePreserved s0 sa)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hwf : Map64Wf m)
    (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64) (hsp0_al : s0.spAligned = true)
    (hvnm : ValidNextMask m bm (nextResizeMask bm))
    (hcap_lt : bucketMaskToCapacity bm < MaxHashbrownCapacity)
    (hitems_eq : items = BitVec.ofNat 64 m.length) (hm_le : m.length ≤ bucketMaskToCapacity bm)
    (hold_cases : (bm = 0#64 ∧ items = 0#64 ∧ oldRest = emp) ∨
      ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧
        SwissTableInv bm w.growthLeft items w.ctrl w.slots m ∧
        w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
        w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
        oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)))
    (hpc : sa.pc = P.pl.base + 684#64) (hrun : sa.status = .Running)
    (hsp : sa.sp = s0.sp - 96#64) (hsp_al : sa.spAligned = true)
    (hne0 : sa.readReg64 .x0 ≠ 0#64)
    (hx20 : sa.readReg64 .x20 = BitVec.ofNat 64 ((nextResizeMask bm).toNat + 1 + 8))
    (hx22 : sa.readReg64 .x22 = items) (hx23 : sa.readReg64 .x23 = bm)
    (hx24 : sa.readReg64 .x24 = bm + 1#64)
    (hx25 : sa.readReg64 .x25 = BitVec.ofNat 64 ((nextResizeMask bm).toNat + 1))
    (hx26 : sa.readReg64 .x26 = BitVec.ofNat 64 (16 * ((nextResizeMask bm).toNat + 1)))
    (hx27 : sa.readReg64 .x27 = mapPtr)
    (hbm' : ValidBucketMask (nextResizeMask bm)) (htop : HbTopSaved s0 sa) :
    let bm' := nextResizeMask bm
    SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) sa
      (stackAt (s0.sp - 96#64) A.stackBytes ∗
       (⌜(sa.readReg64 .x0).toNat % (8#64).toNat = 0 ∧
          (sa.readReg64 .x0).toNat + (BitVec.ofNat 64 (tableAllocBytes bm')).toNat < 2 ^ 64⌝ ∗
        A.Heap (lc + A.cost (BitVec.ofNat 64 (tableAllocBytes bm')).toNat (8#64).toNat) (blk + 1) sa ∗
        A.Block (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm')).toNat (8#64).toNat ∗
        memRegion (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm')).toNat) ∗
       ((hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ hbReserveFrame s0 vPad) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)))
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
          stackAt s0.sp (112 + A.stackBytes) ∗
          (∃∗ bm'' : BitVec 64,
            ⌜ValidNextMask m bm bm''⌝ ∗ U64MapRepReady P.pl A mapPtr m bm'' ∗
            A.Heap ((lc + hbMapCost A bm'') - hbMapCost A bm)
                   ((blk + tableAllocBlocks bm'') - tableAllocBlocks bm) sf))) oom := by
  intro bm'; generalize hx0 : sa.readReg64 .x0 = newAllocPtr at hne0 ⊢
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hbm'_ne : bm' ≠ 0#64 := hbm'.ne_zero
  obtain ⟨_, _, _, htab_le, _, hcap_mach⟩ := (ValidBucketMask.tableAlloc_machine_ok hbm')
  have htab_eq : tableAllocBytes bm' = 17 * (bm'.toNat + 1) + 8 := by
    simp only [tableAllocBytes, hbm'_ne, ↓reduceIte]
  have hsz_nat : (BitVec.ofNat 64 (tableAllocBytes bm')).toNat = tableAllocBytes bm' := by
    dsimp only [bm']; simp only [BitVec.toNat_ofNat]; omega
  have hcost_eq : A.cost (tableAllocBytes bm') 8 = hbMapCost A bm' := by
    simp only [hbMapCost, hbm'_ne, ↓reduceIte]
  have hblk_eq : blk + 1 = blk + tableAllocBlocks bm' := by
    simp only [tableAllocBlocks, hbm'_ne, ↓reduceIte]
  have hstk_sh := stackAt_shrink (s0.sp - 96#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
  have hlen_lt : bm'.toNat + 1 + 8 < 2 ^ 64 := by
    obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hbm'; have := ValidBucketMask.buckets_eq hlo hhi hbm_eq
    have : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi; omega
  let newCtrlPtr := newAllocPtr + BitVec.ofNat 64 (16 * (bm'.toNat + 1))
  refine SepWP.weaken_pre (P' := ⌜newAllocPtr.toNat % 8 = 0 ∧ newAllocPtr.toNat + (17 * (bm'.toNat + 1) + 8) ≤ 2 ^ 64⌝ ∗
    ((∃∗ newSlots : List (BitVec 64 × BitVec 64), ⌜newSlots.length = bm'.toNat + 1⌝ ∗ slotsDownFrom newCtrlPtr newSlots) ∗
     (memRegion newCtrlPtr (bm'.toNat + 1 + 8) ∗ hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
      A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ oldRest ∗
      A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
      stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad)))
    (by rw [hsz_nat, show (8#64).toNat = 8 from rfl, hcost_eq, hblk_eq, hstk_sh,
            memRegion_tableAllocBytes_split newAllocPtr hbm', htab_eq]
        refine Entails.trans (Entails.of_eq (show _ =
          ⌜newAllocPtr.toNat % 8 = 0 ∧ newAllocPtr.toNat + (17 * (bm'.toNat + 1) + 8) < 2 ^ 64⌝ ∗
          (memRegion newAllocPtr (16 * (bm'.toNat + 1)) ∗
           (memRegion newCtrlPtr (bm'.toNat + 1 + 8) ∗ hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
            A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ oldRest ∗
            A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
            (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes) ∗
             stackAt (s0.sp - 96#64) A.stackBytes) ∗ hbReserveFrame s0 vPad)) by dsimp only [newCtrlPtr]; ac_rfl)) ?_
        exact sepConj_mono (Entails.pure_mono fun ⟨h1, h2⟩ => ⟨h1, Nat.le_of_lt h2⟩)
          (sepConj_mono_left (memRegion_to_slotsDownFrom (bm'.toNat + 1) newAllocPtr (by omega))))
    (sepWP_pure_elim fun ⟨ha_al, ha_nw⟩ => ?_)
  clear hstk_sh hsz_nat hcost_eq hblk_eq
  rw [sepExists_sepConj_left]; apply SepWP.exists_elim; intro newSlots
  rw [sepConj_assoc]; refine sepWP_pure_elim fun hsl => ?_
  refine sepWP_seq_frozen (mid := P.pl.base + 732#64) (Φ := fun m => s0.mem.KeepsFrozen m)
    (fun _ _ => Memory.KeepsFrozen.trans) hasp.2.2.2.2 ?_
  wp_step; apply SepWP.ite_false rfl (by simpa [hx0] using hne0); wp_steps
  refine SepWP.call_subroutine_frame hext.memset_ok (x := (newCtrlPtr, 0xff#8, bm'.toNat + 1 + 8))
    (F := slotsDownFrom newCtrlPtr newSlots ∗ hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
      A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ oldRest ∗
      A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
      stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad)
    (ret_pc := P.pl.base + 732#64)
    (by dsimp only [hbMemsetSym]; simpa using (by bv_omega :
        P.pl.base + 728#64 + (P.pl.ρ hbMemsetSym - P.pl.base - 728#64) = P.pl.ρ hbMemsetSym))
    (by simp [hrun]) (by simpa [State.spAligned, hsp] using hsp_al) (by simp [Reg.lr])
    (fun R hm => by
      dsimp only [withCodeInv, stdMemsetSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨by simpa using A.codeInv_keepsFrozen hasp.2.2.2.2 hCode0, ?_⟩
      rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨by simp [Reg.x0, newCtrlPtr, bm'],
        by simp [Reg.x1, State.readReg32], by simp [Reg.x2, bm'], hlen_lt⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sm hpcm hrunm hspm hcsm => ?_) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  dsimp only [withCodeInv, stdMemsetSpec]; rw [sepConj_assoc]; refine sepWP_pure_elim fun ⟨_, hstd_m⟩ => ?_
  refine SepWP.done hpcm hrunm fun hkf_m => ?_
  have hstd_am : StdStatePreserved sa sm :=
    stdStatePreserved_congr_left (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hstd_m
  have hasp_0m : AllocStatePreserved s0 sm :=
    ⟨hstd_am.1.trans hasp.1, hstd_am.2.1.trans hasp.2.1, hstd_am.2.2.2.1.trans hasp.2.2.1,
     hstd_am.2.2.1.trans hasp.2.2.2.1, hkf_m⟩
  have htop_m : HbTopSaved s0 sm := HbTopSaved.trans_cs (by hb_top htop) hcsm
  have hb_add' : bm' + 1#64 = BitVec.ofNat 64 (bm'.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show nextResizeMask bm = bm' from rfl] at hcap_mach
  rw [← hb_add', show bm' + 1#64 - 1#64 = bm' by bv_omega] at hcap_mach
  have hx19_m : sm.readReg64 .x19 = newCtrlPtr := hcsm.readReg64_x19.trans (by simp [newCtrlPtr, bm'])
  have hx21_m : sm.readReg64 .x21 = bm' := hcsm.readReg64_x21.trans (by simp [bm'])
  have hx22_m : sm.readReg64 .x22 = items := hcsm.readReg64_x22.trans (by simpa [Reg.x22] using hx22)
  have hx23_m : sm.readReg64 .x23 = bm := hcsm.readReg64_x23.trans (by simpa [Reg.x23] using hx23)
  have hx24_m : sm.readReg64 .x24 = bm + 1#64 := hcsm.readReg64_x24.trans (by simpa [Reg.x24] using hx24)
  have hx25_m : sm.readReg64 .x25 = bucketMaskToCapacityBV bm' :=
    hcsm.readReg64_x25.trans (by simpa [BitVec.ult_iff_lt, hb_add', bm'] using hcap_mach)
  have hx27_m : sm.readReg64 .x27 = mapPtr := hcsm.readReg64_x27.trans (by simpa [Reg.x27] using hx27)
  wp_conv_pre => unfold U64MapStruct
  wp_sym_steps 2
  wp_conv_pre => change ((newCtrlPtr ↦ₛ List.replicate (bm'.toNat + 1 + 8) 0xff#8) ∗
    (slotsDownFrom newCtrlPtr newSlots ∗ hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
     A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ oldRest ∗
     A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
     stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad))
  by_cases hitems0 : items = 0#64
  · subst hitems0
    have hm_nil : m = [] := by
      have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
      have h0 : m.length = 0 := by
        have := congrArg BitVec.toNat hitems_eq.symm
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m.length < 2 ^ 64)] using this
      exact List.eq_nil_of_length_eq_zero h0
    subst hm_nil
    wp_step
    have hinv_init : SwissTableInv bm' (bucketMaskToCapacityBV bm' - 0#64) 0#64
        (List.replicate (bm'.toNat + 1 + 8) 0xff#8) newSlots [] := by
      rw [BitVec.sub_zero]; exact SwissTableInv_init_of_mask hbm' hsl
    have hgl_pos : 0 < (bucketMaskToCapacityBV bm' - 0#64).toNat := by
      rw [BitVec.sub_zero]; change 0 < bucketMaskToCapacity (nextResizeMask bm)
      have := hbm'.capacity_bounds.1; omega
    have hold_cases' : (bm = 0#64 ∧ oldRest = emp) ∨
        ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧
          SwissTableInv bm w.growthLeft 0#64 w.ctrl w.slots [] ∧
          w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
          w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
          oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) := by
      rcases hold_cases with ⟨h1, _, h3⟩ | hw
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr hw
    refine SepWP.weaken_pre ?_ (hbResize_finishAt1020 P A X hext (oldGl := oldGl) (vPad := vPad) hCode0
      ⟨by simpa using hasp_0m.1, by simpa using hasp_0m.2.1, by simpa using hasp_0m.2.2.1,
       by simpa using hasp_0m.2.2.2.1, by simpa using hasp_0m.2.2.2.2⟩
      hal hnw hwf hstk_nw hsp0_al hvnm hbm' hne0 ha_al ha_nw rfl hinv_init hgl_pos hold_cases'
      (by simp) (by simp [hrunm]) (by simp [hspm, hsp])
      (by simpa [State.spAligned, hspm, hsp] using hsp_al)
      (by simp [Reg.x8]) (by simp [Reg.x9])
      (by simpa [Reg.x19] using hx19_m) (by simpa [Reg.x21] using hx21_m)
      (by simpa [Reg.x22] using hx22_m) (by simpa [Reg.x23] using hx23_m)
      (by simpa [Reg.x24] using hx24_m) (by simpa [Reg.x25] using hx25_m) (by hb_top htop_m))
    exact Entails.trans (Entails.of_eq (show _ =
      U64MapStruct mapPtr oldCtrlPtr bm oldGl 0#64 ∗ hbRodata P.pl ∗
      A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ slotsDownFrom newCtrlPtr newSlots ∗
      (newCtrlPtr ↦ₛ List.replicate (bm'.toNat + 1 + 8) 0xff#8) ∗ oldRest ∗
      A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
      stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (A.heap_transport ((StdStatePreserved.toHbVmPreserved hstd_am).trans
            ⟨by simp, by simp, by simp, by simp, fun _ => by simp⟩)))))))))
  · rcases hold_cases with ⟨_, h0, _⟩ | ⟨w, hw_ctrl, hinv_old, ha_nw_old, hctrl_old, rfl⟩
    · exact absurd h0 hitems0
    have hge8 : 8 ≤ bm'.toNat + 1 := by
      obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hinv_old.validMask
      have hbkt := ValidBucketMask.buckets_eq hlo hhi hbm_eq
      have h2 := (ValidBucketMask.nextResizeMask_valid hinv_old.validMask hcap_lt).2
      have : 2 ^ 2 ≤ 2 ^ exp := Nat.pow_le_pow_right (by decide) hlo
      dsimp only [bm']; omega
    have hcap_gt : m.length < bucketMaskToCapacity bm' :=
      Nat.lt_of_le_of_lt hm_le (nextResizeMask_capacity_gt hinv_old.validMask hcap_lt)
    wp_step; apply SepWP.ite_false rfl (by simpa [hx22_m, ← hitems_eq] using hitems0)
    refine sepWP_seq_frozen (mid := P.pl.base + 1020#64) (Φ := fun m => s0.mem.KeepsFrozen m)
      (fun _ _ => Memory.KeepsFrozen.trans) (by simpa using hasp_0m.2.2.2.2) ?_
    refine SepWP.weaken_pre (P' := (newCtrlPtr ↦ₛ List.replicate (bm'.toNat + 1 + 8) tagEmpty) ∗
      (oldCtrlPtr ↦ₛ w.ctrl) ∗ slotsDownFrom oldCtrlPtr w.slots ∗ slotsDownFrom newCtrlPtr newSlots ∗
      (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ hbRodata P.pl ∗
       A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
       A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
       stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad))
      (Entails.of_eq (by rw [hw_ctrl]; dsimp only [tagEmpty]; ac_rfl)) ?_
    refine hbResize_copyLoop P X (oldCtrlPtr := oldCtrlPtr) (newCtrlPtr := newCtrlPtr)
      hinv_old hitems0 hbm' hge8 hcap_gt hsl
      (by simp) (by simp [hrunm]) (by simp [Reg.x8]) (by simpa [Reg.x19] using hx19_m)
      (by simpa [Reg.x21] using hx21_m) (by simpa [Reg.x22] using hx22_m)
      fun s3 newCtrlF newSlotsF hpc3 hrun3 hinv_new hgl_pos hcp => SepWP.done hpc3 hrun3 fun hkf3 => ?_
    have hstd_m3 : StdStatePreserved sm s3 :=
      (stdStatePreserved_congr_left (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩).trans hcp.2.2.2.1
    have hasp_03 : AllocStatePreserved s0 s3 :=
      ⟨hstd_m3.1.trans hasp_0m.1, hstd_m3.2.1.trans hasp_0m.2.1, hstd_m3.2.2.2.1.trans hasp_0m.2.2.1,
       hstd_m3.2.2.1.trans hasp_0m.2.2.2.1, hkf3⟩
    have htop3 : HbTopSaved s0 s3 :=
      ⟨hcp.2.2.1.1.trans (by simpa using htop_m.1), hcp.2.2.1.2.trans (by simpa [calleeSavedVRegs] using htop_m.2)⟩
    have hold_cases3 : (bm = 0#64 ∧ (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) = emp) ∨
        ∃ w' : HbHeapMapWitness, w'.ctrlPtr = oldCtrlPtr ∧
          SwissTableInv bm w'.growthLeft items w'.ctrl w'.slots m ∧
          w'.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
          w'.ctrlPtr = w'.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
          (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) =
            (A.Block w'.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w'.ctrlPtr w'.slots ∗ (w'.ctrlPtr ↦ₛ w'.ctrl)) :=
      Or.inr ⟨w, hw_ctrl, hinv_old, ha_nw_old, hctrl_old, rfl⟩
    refine SepWP.weaken_pre ?_ (hbResize_finishAt1020 P A X hext (oldGl := oldGl) (vPad := vPad) hCode0 hasp_03
      hal hnw hwf hstk_nw hsp0_al hvnm hbm' hne0 ha_al ha_nw rfl hinv_new hgl_pos hold_cases3
      hpc3 hrun3 (hcp.1.trans (by simp [hspm, hsp]))
      (by simpa [State.spAligned, hcp.1, hspm, hsp] using hsp_al)
      ((hcp.2.2.2.2 8#5 (by decide)).trans (by simp))
      ((hcp.2.2.2.2 9#5 (by decide)).trans (by simp))
      ((hcp.2.2.2.2 19#5 (by decide)).trans (by simpa [Reg.x19] using hx19_m))
      ((hcp.2.2.2.2 21#5 (by decide)).trans (by simpa [Reg.x21] using hx21_m))
      ((hcp.2.2.2.2 22#5 (by decide)).trans (by simpa [Reg.x22] using hx22_m))
      ((hcp.2.2.2.2 23#5 (by decide)).trans (by simpa [Reg.x23] using hx23_m))
      ((hcp.2.2.2.2 24#5 (by decide)).trans (by simpa [Reg.x24] using hx24_m))
      ((hcp.2.2.2.2 25#5 (by decide)).trans (by simpa [Reg.x25] using hx25_m)) htop3)
    exact Entails.trans (Entails.of_eq (show _ =
      U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ hbRodata P.pl ∗
      A.Block newAllocPtr (17 * (bm'.toNat + 1) + 8) 8 ∗ slotsDownFrom newCtrlPtr newSlotsF ∗
      (newCtrlPtr ↦ₛ newCtrlF) ∗
      (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗
      A.Heap (lc + hbMapCost A bm') (blk + tableAllocBlocks bm') sa ∗
      stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ hbReserveFrame s0 vPad by rw [hw_ctrl]; ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (A.heap_transport ((StdStatePreserved.toHbVmPreserved hstd_am).trans
            (StdStatePreserved.toHbVmPreserved hstd_m3))))))))))

/-! ## Entry Dispatch and Top-Level Subroutine Proofs -/

theorem csel_bucketMaskToCapacityBV {bm : BitVec 64}
    (hbm0 : bm = 0#64 ∨ ValidBucketMask bm) :
    (if bm.ult 8#64 = true then bm else ((bm + 1#64) >>> 3 <<< 3) - ((bm + 1#64) >>> 3)) =
      bucketMaskToCapacityBV bm := by
  rcases hbm0 with rfl | hv
  · decide
  · obtain ⟨_, _, _, _, h5, h6⟩ := (ValidBucketMask.tableAlloc_machine_ok hv)
    have h1 : bm + 1#64 = BitVec.ofNat 64 (bm.toNat + 1) := by rw [← h5]; bv_omega
    have hlt : (bm.ult 8#64 = true) ↔ BitVec.ofNat 64 (bm.toNat + 1) < 9#64 := by
      rw [← h5, BitVec.ult_iff_lt]; bv_omega
    simp only [h5] at h6
    simp only [h1, hlt]; exact h6

theorem ule_half_cap_iff {bm : BitVec 64} {mLen : Nat}
    (hbm0 : bm = 0#64 ∨ ValidBucketMask bm) (hm_le : mLen ≤ bucketMaskToCapacity bm) :
    ((BitVec.ofNat 64 (mLen + 1)).ule (bucketMaskToCapacityBV bm >>> 1) = true) ↔
      mLen + 1 ≤ bucketMaskToCapacity bm / 2 := by
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  have hcap_le : bucketMaskToCapacity bm ≤ MaxHashbrownCapacity :=
    (hbResize_cap_after_csinc hbm0 hm_le).1
  have hbv_nat : (bucketMaskToCapacityBV bm).toNat = bucketMaskToCapacity bm := rfl
  rw [BitVec.ule_iff_le, BitVec.le_def, BitVec.toNat_ushiftRight, hbv_nat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : mLen + 1 < 2 ^ 64)]
  rfl

theorem hbReserve_call_coldPanic {mpl : Obj.MultiPlacement} {prog : Program}
    {ret entry ret_pc spBase : BitVec 64}
    {s : State} {F R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp}
    {φ : Prop} {stkTotal : Nat}
    (hcall : subroutine_ok prog entry (hashbrownLib.withCodeLoaded mpl (hbColdPanicSpec φ)))
    (hcl : hashbrownLib.CodeLoaded mpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hsp : s.sp = spBase) (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg32 .x0 = 1#32)
    (hφ : φ) (hge16 : 16 ≤ stkTotal) (hnw_stk : spBase.toNat < 2 ^ 64 ∧ stkTotal ≤ 2 ^ 64) :
    SepWPp prog ret s (stackAt spBase stkTotal ∗ F) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜φ⌝ ∗ R)) oom := by
  have hsh := stackAt_shrink spBase stkTotal 16 hge16 hnw_stk.2
  refine SepWPp.call (x := ()) hcall hpc hrun hsp_al hlr
    (F := memRegion (spBase - BitVec.ofNat 64 stkTotal) (stkTotal - 16) ∗ F)
    (fun R' hm => by
      dsimp only [MultiPlacedLib.withCodeLoaded]
      rw [sepConj_comm ((hbColdPanicSpec φ).pre () s), sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨hcl, ?_⟩
      dsimp only [hbColdPanicSpec]; rw [sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0, hφ⟩, ?_⟩
      rw [hsh] at hm; rw [hsp]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ hmf => satisfies_pure_frame_of_sepConj hφ hmf)
    (fun _ _ _ _ _ => SepWPp.pure_left False.elim) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)

theorem sepWP_seq_frame {prog : Program} {mid target : BitVec 64} {s : State}
    {P1 F : SepProp} {Mid post : State → SepProp → Prop} {φ : Prop}
    (h1 : SepWP prog mid s P1 Mid (fun _ => ⌜φ⌝))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Mid sm Pm →
      SepWP prog target sm (Pm ∗ F) post (fun _ => ⌜φ⌝)) :
    SepWP prog target s (P1 ∗ F) post (fun _ => ⌜φ⌝) := by
  apply SepWP.of_reaches_pc; intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_seq (SepWP.to_reaches_pc h1 hm) ?_ ?_
  · rintro sm hpcm hrunm ⟨Pm, hPm, hMid⟩
    rw [← sepConj_assoc] at hPm
    exact SepWP.to_reaches_pc (h2 sm Pm hpcm hrunm hMid) hPm
  · intro sf _ ho
    have hφ : φ := ((satisfies_pure_sepConj _ _ _).mp ho).1
    rw [← sepConj_assoc] at ho
    exact satisfies_pure_frame_of_sepConj hφ ho

theorem unpack_U64MapRep_pre {pl : Obj.Placement} {A : HbAlloc}
    {mapPtr bm : BitVec 64} {m : Map64} {u : Nat} {Rest R : SepProp} {mem : Memory}
    (hm : mem ⊨ (U64MapRep pl A mapPtr m bm u ∗ Rest) ∗ R) :
    mapPtr.toNat % 8 = 0 ∧ mapPtr.toNat + 32 ≤ 2 ^ 64 ∧ Map64Wf m ∧
    ∃ (oldCtrlPtr oldGl items : BitVec 64) (oldRest : SepProp),
      items = BitVec.ofNat 64 m.length ∧
      m.length ≤ bucketMaskToCapacity bm ∧
      (bm = 0#64 ∨ ValidBucketMask bm) ∧
      ((bm = 0#64 ∧ m = [] ∧ items = 0#64 ∧ oldRest = emp) ∨
       (bm ≠ 0#64 ∧ ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧ w.growthLeft = oldGl ∧
         w.items = items ∧ SwissTableInv bm w.growthLeft items w.ctrl w.slots m ∧
         w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
         w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
         w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
         oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
                    slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)))) ∧
      (mem ⊨ (hbRodata pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ Rest) ∗ R) := by
  unfold U64MapRep at hm
  simp only [sepConj_assoc] at hm
  obtain ⟨⟨hal, hnw, hwf⟩, hm⟩ := (satisfies_pure_sepConj _ _ _).mp hm
  refine ⟨hal, hnw, hwf, ?_⟩
  by_cases hbm0 : bm = 0#64
  · subst hbm0; simp only [↓reduceIte] at hm
    have hm1 : mem ⊨ ⌜m = []⌝ ∗ ((hbRodata pl ∗ U64MapStruct mapPtr (pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64 ∗ emp ∗ Rest) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by simp only [emp_sepConj]; ac_rfl)) hm
    obtain ⟨hm_nil, hm2⟩ := (satisfies_pure_sepConj _ _ _).mp hm1; subst hm_nil
    exact ⟨pl.ρ hbEmptyCtrlSym, 0#64, 0#64, emp, rfl, Nat.zero_le _, Or.inl rfl,
      Or.inl ⟨rfl, rfl, rfl, rfl⟩, hm2⟩
  · simp only [hbm0, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
    obtain ⟨w, hm⟩ := hm
    have hm1 : mem ⊨ ⌜SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m ∧
        bucketMaskToCapacity bm - w.growthLeft.toNat ≤ u ∧
        w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
        w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
        w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
      ((hbRodata pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
        (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗ slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗
        Rest) ∗ R) := Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    obtain ⟨⟨hinv, _hu, ha_ne, ha_al, ha_nw, hctrl⟩, hm2⟩ := (satisfies_pure_sepConj _ _ _).mp hm1
    have hm_le : m.length ≤ bucketMaskToCapacity bm := by have := hinv.conservation; omega
    exact ⟨w.ctrlPtr, w.growthLeft, w.items, _, hinv.items_eq, hm_le, Or.inr hinv.validMask,
      Or.inr ⟨hbm0, w, rfl, rfl, rfl, hinv, ha_ne, ha_al, ha_nw, hctrl, rfl⟩, hm2⟩

theorem hbReserve_stepToBranch (P : HbPlaced) (X : String → Option (State → State))
    {target : BitVec 64} {s0 : State} {mapPtr oldCtrlPtr oldGl bm items : BitVec 64}
    {mLen : Nat} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = P.pl.base) (hrun : s0.status = .Running) (hsp0_al : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = mapPtr) (hx1 : s0.readReg64 .x1 = 1#64) (hw3 : s0.readReg32 .x3 = 1#32)
    (hitems_eq : items = BitVec.ofNat 64 mLen)
    (hm_le : mLen ≤ bucketMaskToCapacity bm) (hbm0 : bm = 0#64 ∨ ValidBucketMask bm)
    (hInPlace : ∀ (s1 : State) (vPad : BitVec 64),
      mLen + 1 ≤ bucketMaskToCapacity bm / 2 →
      s1.pc = P.pl.base + 120#64 → s1.status = .Running →
      s1.sp = s0.sp - 96#64 → s1.spAligned = true →
      s1.readReg64 .x0 = mapPtr → s1.readReg64 .x8 = (bm + 1#64) >>> 3 →
      s1.readReg64 .x20 = bucketMaskToCapacityBV bm → s1.readReg64 .x22 = items →
      s1.readReg64 .x23 = bm → s1.readReg64 .x24 = bm + 1#64 →
      HbTopSaved s0 s1 → StdStatePreserved s0 s1 → s0.mem.KeepsFrozen s1.mem →
      SepWP ((hbProg P).rebase P.pl.base X) target s1
        (hbReserveFrame s0 vPad ∗ (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ F)) post oom)
    (hResize : ∀ (s2 : State) (vPad : BitVec 64),
      ¬ (mLen + 1 ≤ bucketMaskToCapacity bm / 2) →
      s2.pc = P.pl.base + 76#64 → s2.status = .Running →
      s2.sp = s0.sp - 96#64 → s2.spAligned = true →
      s2.readReg64 .x0 = mapPtr → s2.readReg32 .x3 = 1#32 →
      s2.readReg64 .x9 = BitVec.ofNat 64 (mLen + 1) →
      s2.readReg64 .x20 = bucketMaskToCapacityBV bm → s2.readReg64 .x22 = items →
      s2.readReg64 .x23 = bm → s2.readReg64 .x24 = bm + 1#64 →
      HbTopSaved s0 s2 → StdStatePreserved s0 s2 → s0.mem.KeepsFrozen s2.mem →
      SepWP ((hbProg P).rebase P.pl.base X) target s2
        (hbReserveFrame s0 vPad ∗ (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ F)) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) target s0
      (memRegion (s0.sp - 96#64) 96 ∗ (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ F)) post oom := by
  subst hitems_eq
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  have hcap_le : bucketMaskToCapacity bm ≤ MaxHashbrownCapacity :=
    (hbResize_cap_after_csinc hbm0 hm_le).1
  have hx9_eq : BitVec.ofNat 64 mLen + 1#64 = BitVec.ofNat 64 (mLen + 1) := by
    rw [← BitVec.ofNat_add]
  have hcsel := csel_bucketMaskToCapacityBV hbm0
  have hule := ule_half_cap_iff hbm0 hm_le
  refine sepWP_seq_frozen (mid := P.pl.base + 28#64) (Φ := fun m => s0.mem.KeepsFrozen m)
    (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem) ?_
  refine hbReserve_prologue P X hpc hrun hsp0_al
    fun s1 vPad hpc1 hrun1 hsp1 hsp1_al hx0_1 hx1_1 hw3_1 htop1 hstd1 =>
      SepWP.done hpc1 hrun1 fun hkf1 => ?_
  have hx0_1' : s1.readReg64 .x0 = mapPtr := hx0_1.trans hx0
  have hx1_1' : s1.readReg64 .x1 = 1#64 := hx1_1.trans hx1
  have hw3_1' : s1.readReg32 .x3 = 1#32 := hw3_1.trans hw3
  wp_conv_pre => unfold U64MapStruct
  wp_steps
  apply SepWP.ite_false rfl (by
    rw [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
  wp_steps
  by_cases hle : mLen + 1 ≤ bucketMaskToCapacity bm / 2
  · apply SepWP.ite_true rfl hle
    refine SepWP.weaken_pre ?_ (hInPlace _ vPad hle (by simp) (by simp [hrun1]) (by simp [hsp1])
      (by simpa [State.spAligned, hsp1] using hsp1_al)
      (by simpa [Reg.x0] using hx0_1') (by simp [Reg.x8])
      (by simp [Reg.x20]) (by simp [Reg.x22])
      (by simp [Reg.x23]) (by simp [Reg.x24])
      (by hb_top htop1)
      (hstd1.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩)
      (by simpa using hkf1))
    exact Entails.of_eq (by unfold U64MapStruct; ac_rfl)
  · apply SepWP.ite_false rfl hle
    refine SepWP.weaken_pre ?_ (hResize _ vPad hle (by simp) (by simp [hrun1]) (by simp [hsp1])
      (by simpa [State.spAligned, hsp1] using hsp1_al)
      (by simpa [Reg.x0] using hx0_1') (by simpa [Reg.x3, State.readReg32] using hw3_1')
      (by simp [Reg.x9])
      (by simp [Reg.x20]) (by simp [Reg.x22])
      (by simp [Reg.x23]) (by simp [Reg.x24])
      (by hb_top htop1)
      (hstd1.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩)
      (by simpa using hkf1))
    exact Entails.of_eq (by unfold U64MapStruct; ac_rfl)

theorem hbReserve_infallible_wp (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    (hInPlace : HbRehashInPlaceProp P A X)
    {s0 : State} {mapPtr oldCtrlPtr oldGl bm items : BitVec 64} {m : Map64}
    {oldRest R : SepProp} {lc blk : Nat}
    (hpc : s0.pc = P.pl.base) (hrun : s0.status = .Running) (hsp0_al : s0.spAligned = true)
    (hCode0 : A.CodeInv s0.mem)
    (hx0 : s0.readReg64 .x0 = mapPtr) (hx1 : s0.readReg64 .x1 = 1#64) (hw3 : s0.readReg32 .x3 = 1#32)
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hwf : Map64Wf m)
    (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64) (hcan0 : HbCanReserveOne A m bm lc blk)
    (hitems_eq : items = BitVec.ofNat 64 m.length) (hm_le : m.length ≤ bucketMaskToCapacity bm)
    (hbm0 : bm = 0#64 ∨ ValidBucketMask bm)
    (hold : (bm = 0#64 ∧ m = [] ∧ items = 0#64 ∧ oldRest = emp) ∨
      (bm ≠ 0#64 ∧ ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧ w.growthLeft = oldGl ∧
        w.items = items ∧ SwissTableInv bm w.growthLeft items w.ctrl w.slots m ∧
        w.allocPtr ≠ 0#64 ∧ w.allocPtr.toNat % 8 = 0 ∧
        w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
        w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
        oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
                   slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)))) :
    SepWP ((hbProg P).rebase P.pl.base X) (s0.readReg64 Reg.lr) s0
      (hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗
       A.Heap lc blk s0 ∗ stackAt s0.sp (112 + A.stackBytes))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
          (⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
           stackAt s0.sp (112 + A.stackBytes) ∗
           (∃∗ bm' : BitVec 64,
             ⌜ValidNextMask m bm bm'⌝ ∗ U64MapRepReady P.pl A mapPtr m bm' ∗
             A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
                    ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sf)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜A.allowOom⌝) := by
  refine SepWP.mono (post := fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (Pf ⊢ ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ AllocStatePreserved s0 sf⌝ ∗
        stackAt s0.sp (112 + A.stackBytes) ∗
        (∃∗ bm' : BitVec 64,
          ⌜ValidNextMask m bm bm'⌝ ∗ U64MapRepReady P.pl A mapPtr m bm' ∗
          A.Heap ((lc + hbMapCost A bm') - hbMapCost A bm)
                 ((blk + tableAllocBlocks bm') - tableAllocBlocks bm) sf))) ?_
    fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ => ⟨Satisfies.mono (sepConj_mono_left hPf), hspf, hcsf⟩
  refine SepWP.weaken_pre (P' := memRegion (s0.sp - 96#64) 96 ∗
    (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
     (hbRodata P.pl ∗ oldRest ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes))))
    (Entails.of_eq (by
      rw [show 112 + A.stackBytes = (16 + A.stackBytes) + 96 by omega,
          stackAt_region s0.sp (16 + A.stackBytes) 96 (by omega)]; ac_rfl)) ?_
  refine hbReserve_stepToBranch P X hpc hrun hsp0_al hx0 hx1 hw3 hitems_eq hm_le hbm0 ?_ ?_
  · intro s1 vPad hle hpc1 hrun1 hsp1 hsp1_al hx0_1 hx8_1 hx20_1 hx22_1 hx23_1 hx24_1 htop1 hstd1 hkf1
    rcases hold with ⟨hbm_z, _, _, _⟩ |
        ⟨_, w, hw_ctrl, hw_gl, hw_items, hinv, ha_ne, ha_al, ha_nw, hctrl, hrest⟩
    · subst hbm_z; change m.length + 1 ≤ 0 at hle; omega
    · refine SepWP.weaken_pre (P' :=
        (hbRodata P.pl ∗ U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
         A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
         slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗
        (hbReserveFrame s0 vPad ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes)))
        (Entails.of_eq (by rw [hrest, hw_ctrl, hw_gl, hw_items]; ac_rfl)) ?_
      refine sepWP_seq_frame (hInPlace hext hpc1 hrun1 hsp1_al (A.codeInv_keepsFrozen hkf1 hCode0)
        hx0_1 hx8_1 hx20_1 (hx22_1.trans hw_items.symm) hx23_1 hx24_1 hal hnw
        (hw_items.symm ▸ hinv) ha_ne ha_al ha_nw hctrl hle) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, _, hx0_2, hx28_2, hvregs_2, hstd_12, hkf_12, hP2⟩
      have hstd_02 : StdStatePreserved s0 s2 := hstd1.trans hstd_12
      have hasp_02 : AllocStatePreserved s0 s2 :=
        StdStatePreserved.toAllocStatePreserved hstd_02 (hkf1.trans hkf_12)
      refine SepWP.weaken_pre ?_ (hbReserve_retFrom1080 P A X (vPad := vPad) (lc := lc) (blk := blk)
        hasp_02 (Or.inl rfl) hstk_nw hsp0_al hpc2 hrun2 (hsp2.trans hsp1) hx0_2
        ⟨hx28_2.trans htop1.1, hvregs_2.trans htop1.2⟩)
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
      exact Entails.trans (sepConj_mono hP2
          (sepConj_mono_right (sepConj_mono_left
            (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd_02)))))
        (Entails.of_eq (by ac_rfl))
  · intro s2 vPad hnle hpc2 hrun2 hsp2 hsp2_al hx0_2 hw3_2 hx9_2 hx20_2 hx22_2 hx23_2 hx24_2 htop2 hstd2 hkf2
    obtain ⟨hcap_lt, hcan_alloc⟩ := hcan0.resolve_left hnle
    have hold_cases : (bm = 0#64 ∧ items = 0#64 ∧ oldRest = emp) ∨
        ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧
          SwissTableInv bm w.growthLeft items w.ctrl w.slots m ∧
          w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
          w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
          oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
                     slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) := by
      rcases hold with ⟨h1, _, h3, h4⟩ | ⟨_, w, hw_c, _, _, hinv, _, _, ha_nw, hctrl, hrest⟩
      · exact Or.inl ⟨h1, h3, h4⟩
      · exact Or.inr ⟨w, hw_c, hinv, ha_nw, hctrl, hrest⟩
    refine SepWP.weaken_pre (P' := A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗
      (hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ hbReserveFrame s0 vPad))
      (Entails.of_eq (by ac_rfl)) ?_
    refine hbResize_runToPostAlloc P A X hext hCode0 hkf2 hstk_nw hpc2 hrun2 hsp2 hsp2_al
      hx0_2 hw3_2 hx9_2 hx20_2 hx22_2 hx23_2 hx24_2 htop2 hstd2 hbm0 hm_le hcap_lt (fun _ => hcan_alloc)
      fun sa hpca hruna hspa hspa_al _ hx20_a _ hx22_a hx23_a hx24_a hx25_a hx26_a hx27_a hbm' htop_a hasp_a => ?_
    have hsz_nat : (BitVec.ofNat 64 (tableAllocBytes (nextResizeMask bm))).toNat =
        tableAllocBytes (nextResizeMask bm) := by
      have := (ValidBucketMask.tableAlloc_machine_ok hbm').2.2.2.1; simp only [BitVec.toNat_ofNat]; omega
    by_cases hret0 : sa.readReg64 .x0 = 0#64
    · simp only [hret0, ↓reduceIte]
      refine SepWP.weaken_pre (P' := ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk
          (BitVec.ofNat 64 (tableAllocBytes (nextResizeMask bm))).toNat (8#64).toNat⌝ ∗
        (stackAt (s0.sp - 96#64) A.stackBytes ∗ A.Heap lc blk sa ∗
         ((hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ hbReserveFrame s0 vPad) ∗
          memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes))))
        (Entails.of_eq (by ac_rfl)) ?_
      exact sepWP_pure_elim fun ⟨_, hncan⟩ => False.elim (hncan (by simpa [hsz_nat] using hcan_alloc))
    · simp only [hret0, ↓reduceIte]
      exact hbResize_postAlloc P A X hext hCode0 hasp_a hal hnw hwf hstk_nw hsp0_al
        (Or.inr ⟨by omega, hcap_lt, rfl⟩) hcap_lt hitems_eq hm_le hold_cases
        hpca hruna hspa hspa_al hret0 hx20_a hx22_a hx23_a hx24_a hx25_a hx26_a hx27_a hbm' htop_a

theorem hashbrown_reserve_rehash_one_infallible_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State))
    (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    (hInPlace : HbRehashInPlaceProp P A X) :
    let prog := (hbProg P).rebase P.pl.base X
    subroutine_ok prog (prog.fnAddr hbReserveRehashSym)
      (withCodeInv A (hashbrownReserveRehashOneInfallibleSpec P.pl A)) := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  dsimp only; apply subroutine_ok_of_sepWP_init
  rintro ⟨mapPtr, m, bm, _u, lc, blk⟩ R s0 hpc hrun hpre hsp0_al
  simp only [hbReserveRehashSym, arm64_norm] at hpc
  dsimp only [withCodeInv, hashbrownReserveRehashOneInfallibleSpec] at hpre ⊢
  rw [sepConj_assoc] at hpre; obtain ⟨hCode0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  rw [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx1, hw3, hstk_nw, hcan0⟩, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  obtain ⟨hal, hnw, hwf, oldCtrlPtr, oldGl, items, oldRest, hitems_eq, hm_le, hbm0, hold, hpre'⟩ :=
    unpack_U64MapRep_pre hpre
  exact ⟨_, hpre', hbReserve_infallible_wp P A X hext hInPlace hpc hrun hsp0_al hCode0
    hx0 hx1 hw3 hal hnw hwf hstk_nw hcan0 hitems_eq hm_le hbm0 hold⟩

theorem hashbrown_reserve_rehash_one_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State))
    (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    (hInPlace : HbRehashInPlaceProp P A X) :
    let prog := (hbProg P).rebase P.pl.base X
    subroutine_ok prog (prog.fnAddr hbReserveRehashSym)
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownReserveRehashOneSpec P.pl A))) := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  dsimp only; apply subroutine_ok_of_sepWPp_init
  rintro ⟨mapPtr, m, bm, _u, lc, blk⟩ R s0 hpc hrun hpre hsp0_al
  simp only [hbReserveRehashSym, arm64_norm] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre ⊢
  rw [sepConj_comm ((withCodeInv A (hashbrownReserveRehashOneSpec P.pl A)).pre _ s0), sepConj_assoc] at hpre
  obtain ⟨hcl0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  dsimp only [withCodeInv, hashbrownReserveRehashOneSpec] at hpre ⊢
  rw [sepConj_assoc] at hpre; obtain ⟨hCode0, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  rw [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx1, hw3, hstk_nw, himp_can⟩, hpre⟩ := (satisfies_pure_sepConj _ _ _).mp hpre
  obtain ⟨hal, hnw, hwf, oldCtrlPtr, oldGl, items, oldRest, hitems_eq, hm_le, hbm0, hold, hpre'⟩ :=
    unpack_U64MapRep_pre hpre
  refine ⟨_, hpre', ?_⟩
  by_cases hcan : HbCanReserveOne A m bm lc blk
  · exact SepWPp.of_sepWP_ret (hbReserve_infallible_wp P A X hext hInPlace hpc hrun hsp0_al hCode0
      hx0 hx1 hw3 hal hnw hwf hstk_nw hcan hitems_eq hm_le hbm0 hold)
  · have hao : A.allowOom := Classical.byContradiction fun hna => hcan (himp_can hna)
    have hnle : ¬ (m.length + 1 ≤ bucketMaskToCapacity bm / 2) := fun hle => hcan (Or.inl hle)
    have hold_cases : (bm = 0#64 ∧ items = 0#64 ∧ oldRest = emp) ∨
        ∃ w : HbHeapMapWitness, w.ctrlPtr = oldCtrlPtr ∧
          SwissTableInv bm w.growthLeft items w.ctrl w.slots m ∧
          w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
          w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1)) ∧
          oldRest = (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
                     slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) := by
      rcases hold with ⟨h1, _, h3, h4⟩ | ⟨_, w, hw_c, _, _, hinv, _, _, ha_nw, hctrl, hrest⟩
      · exact Or.inl ⟨h1, h3, h4⟩
      · exact Or.inr ⟨w, hw_c, hinv, ha_nw, hctrl, hrest⟩
    refine SepWPp.congr_pre (P' := memRegion (s0.sp - 96#64) 96 ∗
      (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
       (hbRodata P.pl ∗ oldRest ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes))))
      (by rw [show 112 + A.stackBytes = (16 + A.stackBytes) + 96 by omega,
              stackAt_region s0.sp (16 + A.stackBytes) 96 (by omega)]; ac_rfl) ?_
    by_cases hcap_lt : bucketMaskToCapacity bm < MaxHashbrownCapacity
    · apply SepWPp.of_sepWP (mid := P.pl.base + 684#64)
      refine hbReserve_stepToBranch P X hpc hrun hsp0_al hx0 hx1 hw3 hitems_eq hm_le hbm0
        (fun _ _ hle => absurd hle hnle)
        fun s2 vPad _ hpc2 hrun2 hsp2 hsp2_al hx0_2 hw3_2 hx9_2 hx20_2 hx22_2 hx23_2 hx24_2 htop2 hstd2 hkf2 => ?_
      refine SepWP.weaken_pre (P' := A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗
        (hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ hbReserveFrame s0 vPad))
        (Entails.of_eq (by ac_rfl)) ?_
      refine hbResize_runToPostAlloc P A X hext hCode0 hkf2 hstk_nw hpc2 hrun2 hsp2 hsp2_al
        hx0_2 hw3_2 hx9_2 hx20_2 hx22_2 hx23_2 hx24_2 htop2 hstd2 hbm0 hm_le hcap_lt (fun hna => (hna hao).elim)
        fun sa hpca hruna hspa hspa_al hx19_a hx20_a hx21_a hx22_a hx23_a hx24_a hx25_a hx26_a hx27_a hbm' htop_a hasp_a =>
          SepWP.done hpca hruna ?_
      by_cases hret0 : sa.readReg64 .x0 = 0#64
      · simp only [hret0, ↓reduceIte]
        have hstk_sh := stackAt_shrink (s0.sp - 96#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
        refine SepWPp.congr_pre (P' := ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk
            (BitVec.ofNat 64 (tableAllocBytes (nextResizeMask bm))).toNat (8#64).toNat⌝ ∗
          (stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗
           (A.Heap lc blk sa ∗ hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ hbReserveFrame s0 vPad)))
          (by rw [hstk_sh]; ac_rfl) (SepWPp.pure_left fun _ => ?_)
        apply SepWPp.of_sepWP_at (mid := P.pl12.base)
        refine SepWP.mono_frozen (Φ := fun m => sa.mem.KeepsFrozen m)
          (post := fun sm Pm => Pm = stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗
              (A.Heap lc blk sa ∗ hbRodata P.pl ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ oldRest ∗ hbReserveFrame s0 vPad) ∧
            sm.sp = s0.sp - 96#64 ∧ sm.spAligned = true ∧ sm.readReg32 .x0 = 1#32)
          (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl sa.mem) ?_ ?_
        · wp_steps
          exact SepWP.done (by simp; bv_lin) (by simp [hruna])
            ⟨rfl, by simp [hspa], by simpa [State.spAligned, hspa] using hspa_al, by simp only [arm64_norm]⟩
        · rintro sm Pm _ _ hkf_am ⟨rfl, hspm, hspm_al, hx0_m⟩ hpcm hrunm
          have hpan_fn := hbFallibilityAllocErr_crossBlock_ok P X (i := 0) (by decide)
            (hbProg_rebase P X) (φ := A.allowOom ∧ ¬ HbCanReserveOne A m bm lc blk) (hext.panic_hooks hao).2
          exact hbReserve_call_coldPanic (stkTotal := 16 + A.stackBytes) hpan_fn
            (hcl0.of_keepsFrozen (hasp_a.2.2.2.2.trans hkf_am))
            hpcm hrunm hspm_al hspm rfl hx0_m ⟨hao, hcan⟩ (by omega) ⟨(s0.sp - 96#64).isLt, by omega⟩
      · simp only [hret0, ↓reduceIte]
        exact SepWPp.of_sepWP_ret (SepWP.mono
          (hbResize_postAlloc P A X hext hCode0 hasp_a hal hnw hwf hstk_nw hsp0_al
            (Or.inr ⟨by omega, hcap_lt, rfl⟩) hcap_lt hitems_eq hm_le hold_cases
            hpca hruna hspa hspa_al hret0 hx20_a hx22_a hx23_a hx24_a hx25_a hx26_a hx27_a hbm' htop_a)
          fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ => ⟨Satisfies.mono (sepConj_mono_left hPf), hspf, hcsf⟩)
    · apply SepWPp.of_sepWP_at (mid := P.pl11.base)
      refine SepWP.mono_frozen (Φ := fun m => s0.mem.KeepsFrozen m)
        (post := fun sm Pm => ∃ vPad, Pm = hbReserveFrame s0 vPad ∗
          (U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗
           (hbRodata P.pl ∗ oldRest ∗ A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes))) ∧
          sm.sp = s0.sp - 96#64 ∧ sm.spAligned = true ∧ sm.readReg64 Reg.lr = P.pl.base + 1016#64 ∧ sm.readReg32 .x0 = 1#32)
        (fun _ _ => Memory.KeepsFrozen.trans) (Memory.KeepsFrozen.refl s0.mem)
        ?_ ?_
      · refine hbReserve_stepToBranch P X hpc hrun hsp0_al hx0 hx1 hw3 hitems_eq hm_le hbm0
          (fun _ _ hle => absurd hle hnle)
          fun s2 vPad _ hpc2 hrun2 hsp2 hsp2_al _ hw3_2 hx9_2 hx20_2 _ _ _ _ _ _ => ?_
        rw [← hbPl_ρ_capOverflow P]
        refine SepWP.mono (hbResize_overflow_toPanic P X
            hpc2 hrun2 hsp2 hsp2_al hw3_2 hx9_2 hx20_2 hbm0 hm_le hcap_lt) ?_
        rintro sm Pm _ _ ⟨rfl, hspm, hspm_al, hlrm, hx0_m⟩
        exact ⟨vPad, rfl, hspm, hspm_al, hlrm, hx0_m⟩
      · rintro sm Pm _ _ hkf_0m ⟨vPad, rfl, hspm, hspm_al, hlrm, hx0_m⟩ hpcm hrunm
        refine SepWPp.congr_pre (P' := stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗
          (hbReserveFrame s0 vPad ∗ U64MapStruct mapPtr oldCtrlPtr bm oldGl items ∗ hbRodata P.pl ∗ oldRest ∗ A.Heap lc blk s0))
          (by ac_rfl) ?_
        have hpan_fn := hbCapOverflow_crossBlock_ok P X (i := 0) (by decide)
          (hbProg_rebase P X) (φ := A.allowOom ∧ ¬ HbCanReserveOne A m bm lc blk) (hext.panic_hooks hao).1
        exact hbReserve_call_coldPanic (stkTotal := 16 + A.stackBytes) hpan_fn
          (hcl0.of_keepsFrozen hkf_0m) hpcm hrunm hspm_al hspm hlrm hx0_m ⟨hao, hcan⟩
          (by omega) ⟨(s0.sp - 96#64).isLt, by omega⟩

end CaseStudies.Hashbrown.Proofs.ResizeInternal

namespace CaseStudies.Hashbrown.Proofs
export ResizeInternal (hashbrown_reserve_rehash_one_infallible_ok hashbrown_reserve_rehash_one_ok)
end CaseStudies.Hashbrown.Proofs
