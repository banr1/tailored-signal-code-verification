/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.ResizePure

/-!
# Machine-Code Copy Loop for `resize_inner`

Allocation setup (`hbResize_runToPostAlloc`), control-group scanning, empty-slot probing,
and the key-value bucket copy loop (`hbResize_copyLoop`) for `RawTable::resize_inner`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.ResizeInternal

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "hb_top " h:ident : tactic => `(tactic|
  exact ⟨by simpa using ($h).1, by simpa [calleeSavedVRegs] using ($h).2⟩)

theorem hbResize_runToPostAlloc (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State)) (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A)
    {target : BitVec 64} {s0 s2 : State} {mapPtr bm items : BitVec 64} {mLen lc blk : Nat} {F : SepProp}
    {post : State → SepProp → Prop} (hCode0 : A.CodeInv s0.mem) (hkf2 : s0.mem.KeepsFrozen s2.mem)
    (hstk_nw : A.stackBytes + 112 ≤ 2 ^ 64)
    (hpc : s2.pc = P.pl.base + 76#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = s0.sp - 96#64) (hsp_al : s2.spAligned = true)
    (hx0 : s2.readReg64 .x0 = mapPtr) (hw3 : s2.readReg32 .x3 = 1#32)
    (hx9 : s2.readReg64 .x9 = BitVec.ofNat 64 (mLen + 1))
    (hx20 : s2.readReg64 .x20 = bucketMaskToCapacityBV bm)
    (hx22 : s2.readReg64 .x22 = items) (hx23 : s2.readReg64 .x23 = bm)
    (hx24 : s2.readReg64 .x24 = bm + 1#64)
    (htop : HbTopSaved s0 s2) (hstd : StdStatePreserved s0 s2)
    (hbm0 : bm = 0#64 ∨ ValidBucketMask bm) (hm_le : mLen ≤ bucketMaskToCapacity bm)
    (hcap_lt : bucketMaskToCapacity bm < MaxHashbrownCapacity)
    (himp_can : ¬ A.allowOom → A.CanAlloc lc blk (tableAllocBytes (nextResizeMask bm)) 8)
    (hcont : ∀ sa : State,
      let bm' := nextResizeMask bm; let b' := bm'.toNat + 1
      sa.pc = P.pl.base + 684#64 → sa.status = .Running → sa.sp = s0.sp - 96#64 →
      sa.spAligned = true → sa.readReg64 .x19 = BitVec.ofNat 64 (tableAllocBytes bm') →
      sa.readReg64 .x20 = BitVec.ofNat 64 (b' + 8) → sa.readReg64 .x21 = 1#64 →
      sa.readReg64 .x22 = items → sa.readReg64 .x23 = bm → sa.readReg64 .x24 = bm + 1#64 →
      sa.readReg64 .x25 = BitVec.ofNat 64 b' → sa.readReg64 .x26 = BitVec.ofNat 64 (16 * b') →
      sa.readReg64 .x27 = mapPtr → ValidBucketMask bm' → HbTopSaved s0 sa →
      AllocStatePreserved s0 sa →
      SepWP ((hbProg P).rebase P.pl.base X) target sa
        (stackAt (s0.sp - 96#64) A.stackBytes ∗
         (if sa.readReg64 .x0 = 0#64 then
            ⌜A.allowOom ∧ ¬ A.CanAlloc lc blk (BitVec.ofNat 64 (tableAllocBytes bm')).toNat (8#64).toNat⌝ ∗ A.Heap lc blk sa
          else
            ⌜(sa.readReg64 .x0).toNat % (8#64).toNat = 0 ∧
              (sa.readReg64 .x0).toNat + (BitVec.ofNat 64 (tableAllocBytes bm')).toNat < 2 ^ 64⌝ ∗
            A.Heap (lc + A.cost (BitVec.ofNat 64 (tableAllocBytes bm')).toNat (8#64).toNat) (blk + 1) sa ∗
            A.Block (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm')).toNat (8#64).toNat ∗
            memRegion (sa.readReg64 .x0) (BitVec.ofNat 64 (tableAllocBytes bm')).toNat) ∗
         (F ∗ memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)))
        post (fun _ => ⌜A.allowOom⌝)) :
    SepWP ((hbProg P).rebase P.pl.base X) target s2
      (A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ F) post (fun _ => ⌜A.allowOom⌝) := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  let bm' := nextResizeMask bm; let b' := bm'.toNat + 1
  obtain ⟨hle_max, hcap_next⟩ := capToBucketMask_succ_capacity_eq_nextResizeMask hbm0 hcap_lt
  let cap := BitVec.ofNat 64 (bucketMaskToCapacity bm + 1)
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  have hcap_nat : cap.toNat = bucketMaskToCapacity bm + 1 := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap0 : cap ≠ 0#64 := fun hz => by have := congrArg BitVec.toNat hz; simp [hcap_nat] at this
  have hbm' : ValidBucketMask bm' := by
    dsimp only [bm']; rw [← hcap_next, ← hcap_nat]; exact capToBucketMask_valid (by omega) (by omega)
  obtain ⟨_, hcsinc⟩ := hbResize_cap_after_csinc hbm0 hm_le
  have hcap_s2 : (if (s2.readReg64 (.gpr 20#5) + 1#64).ule (s2.readReg64 (.gpr 9#5)) = true
      then s2.readReg64 (.gpr 9#5) else s2.readReg64 (.gpr 20#5) + 1#64) = cap := by
    rw [show s2.readReg64 (.gpr 20#5) = bucketMaskToCapacityBV bm from hx20,
        show s2.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (mLen + 1) from hx9]; exact hcsinc
  refine SepWP.seq (mid := P.pl.base + 632#64)
    (Mid := fun s3 P3 => P3 = (A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ F) ∧
      s3.sp = s0.sp - 96#64 ∧ s3.spAligned = true ∧
      s3.readReg64 .x0 = mapPtr ∧ s3.readReg32 .x3 = 1#32 ∧ s3.readReg64 .x22 = items ∧
      s3.readReg64 .x23 = bm ∧ s3.readReg64 .x24 = bm + 1#64 ∧
      s3.readReg64 .x25 = BitVec.ofNat 64 b' ∧
      HbTopSaved s0 s3 ∧ StdStatePreserved s0 s3 ∧ s0.mem.KeepsFrozen s3.mem) ?_ ?_
  · wp_steps
    by_cases hlt15 : cap < 15#64
    · apply SepWP.ite_false rfl (by rw [BitVec.ule_iff_le]; bv_omega); wp_steps
      refine SepWP.done (by simp) (by simp [hrun]) ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp_al,
        by simpa [Reg.x0] using hx0, by simpa [Reg.x3, State.readReg32] using hw3,
        by simpa [Reg.x22] using hx22, by simpa [Reg.x23] using hx23, by simpa [Reg.x24] using hx24, ?_,
        by hb_top htop, hstd.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩,
        by simpa using hkf2⟩
      have hsm := capToBucketMask_small_buckets hcap0 hlt15
      rw [hcap_nat, hcap_next] at hsm; dsimp only [b', bm']; simpa only [arm64_norm, BitVec.ult_iff_lt] using hsm
    · apply SepWP.ite_true rfl (by rw [BitVec.ule_iff_le]; bv_omega)
      obtain ⟨hsh61, _, hmask_eq, _, hle_lim, hadd1⟩ := capToBucketMask_large_ok hlt15 (by omega)
      have humulh : (BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64) +
          (cap <<< 3 - BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64)) >>> 1) >>> 2 =
          BitVec.ofNat 64 ((cap.toNat * 8) / 7) := umulh_div7_bv hsh61
      wp_step; wp_step; apply SepWP.ite_false rfl (by rw [hsh61]; decide); wp_steps
      apply SepWP.ite_false rfl (by rw [humulh, ← hmask_eq, BitVec.ult_iff_lt]; exact BitVec.not_lt.mpr hle_lim)
      wp_steps
      refine SepWP.done (by simp) (by simp [hrun]) ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp_al,
        by simpa [Reg.x0] using hx0, by simpa [Reg.x3, State.readReg32] using hw3,
        by simpa [Reg.x22] using hx22, by simpa [Reg.x23] using hx23, by simpa [Reg.x24] using hx24, ?_,
        by hb_top htop, hstd.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩,
        by simpa using hkf2⟩
      simp only [arm64_norm]; rw [humulh, ← hmask_eq, hadd1]; dsimp only [b', bm']; rw [hcap_nat, hcap_next]
  · rintro s3 P3 hpc3 hrun3 ⟨rfl, hsp3, hsp3_al, hx0_3, hw3_3, hx22_3, hx23_3, hx24_3, hx25_3, htop3, hstd3, hkf3⟩
    obtain ⟨hsh4, hadd8, htab, htab_le, _, _⟩ := (ValidBucketMask.tableAlloc_machine_ok hbm'); wp_steps
    apply SepWP.ite_false rfl (by
      dsimp only [b']; rw [hsh4, hadd8, ← BitVec.ofNat_add, htab, BitVec.ult_iff_lt, BitVec.lt_def]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tableAllocBytes bm' < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : bm'.toNat + 1 + 8 < 2 ^ 64)]; omega)
    wp_steps
    apply SepWP.ite_false rfl (by
      dsimp only [b']; rw [hsh4, hadd8, ← BitVec.ofNat_add, htab, BitVec.ult_iff_lt, BitVec.lt_def]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tableAllocBytes bm' < 2 ^ 64),
        Nat.reducePow, Nat.reduceMod]; omega)
    wp_steps
    refine SepWP.call_subroutine hext.allocShim_ok (x := ()) (ret_pc := P.pl.base + 672#64)
      (by dsimp only [hbAllocShimSym]; simpa using (by bv_omega :
          P.pl.base + 668#64 + (P.pl.ρ hbAllocShimSym - P.pl.base - 668#64) = P.pl.ρ hbAllocShimSym))
      (by simp [hrun3]) (by simpa [State.spAligned, hsp3] using hsp3_al) (by simp [Reg.lr])
      (fun _ hm => by
        dsimp only [withCodeInv, hbAllocShimSpec]; rw [sepConj_emp]
        exact (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hkf3 hCode0, hm⟩)
      (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sc0 hpcc0 hrunc0 ⟨hpost_c0, hspc0, hcsc0⟩ => ?_) (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
    dsimp only [withCodeInv, hbAllocShimSpec] at hpost_c0
    obtain ⟨hstd_a, hkf_a⟩ := ((satisfies_pure_sepConj _ emp _).mp (by rwa [sepConj_emp])).1
    have hstd_0c0 : StdStatePreserved s0 sc0 :=
      (hstd3.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩).trans hstd_a
    have htop_0c0 : HbTopSaved s0 sc0 := HbTopSaved.trans_cs (by hb_top htop3) hcsc0
    have hkf_0c0 : s0.mem.KeepsFrozen sc0.mem := hkf3.trans (by simpa using hkf_a)
    have hx19_c : sc0.readReg64 .x19 = BitVec.ofNat 64 (tableAllocBytes bm') :=
      hcsc0.readReg64_x19.trans (by simp only [arm64_norm]; dsimp only [b']; rw [hadd8, hsh4, ← BitVec.ofNat_add, htab])
    have hx20_c : sc0.readReg64 .x20 = BitVec.ofNat 64 (b' + 8) :=
      hcsc0.readReg64_x20.trans (by simp only [arm64_norm]; dsimp only [b']; exact hadd8)
    have hx21_c : sc0.readReg64 .x21 = 1#64 :=
      hcsc0.readReg64_x21.trans (by simpa [Reg.x3, State.readReg32] using congrArg (BitVec.zeroExtend 64) hw3_3)
    have hx22_c : sc0.readReg64 .x22 = items := hcsc0.readReg64_x22.trans (by simpa [Reg.x22] using hx22_3)
    have hx23_c : sc0.readReg64 .x23 = bm := hcsc0.readReg64_x23.trans (by simpa [Reg.x23] using hx23_3)
    have hx24_c : sc0.readReg64 .x24 = bm + 1#64 := hcsc0.readReg64_x24.trans (by simpa [Reg.x24] using hx24_3)
    have hx25_c : sc0.readReg64 .x25 = BitVec.ofNat 64 b' :=
      hcsc0.readReg64_x25.trans (by simpa [Reg.x25] using hx25_3)
    have hx26_c : sc0.readReg64 .x26 = BitVec.ofNat 64 (16 * b') :=
      hcsc0.readReg64_x26.trans (by simp only [arm64_norm]; dsimp only [b']; exact hsh4)
    have hx27_c : sc0.readReg64 .x27 = mapPtr := hcsc0.readReg64_x27.trans (by simp)
    wp_steps
    suffices ∀ sc : State, sc.pc = P.pl.ρ hbAllocSym → sc.status = .Running → sc.sp = s0.sp - 96#64 →
        sc.spAligned = true → sc.readReg64 Reg.lr = P.pl.base + 684#64 →
        sc.readReg64 .x0 = BitVec.ofNat 64 (tableAllocBytes bm') → sc.readReg64 .x1 = 8#64 →
        sc.readReg64 .x19 = BitVec.ofNat 64 (tableAllocBytes bm') → sc.readReg64 .x20 = BitVec.ofNat 64 (b' + 8) →
        sc.readReg64 .x21 = 1#64 → sc.readReg64 .x22 = items → sc.readReg64 .x23 = bm →
        sc.readReg64 .x24 = bm + 1#64 → sc.readReg64 .x25 = BitVec.ofNat 64 b' →
        sc.readReg64 .x26 = BitVec.ofNat 64 (16 * b') → sc.readReg64 .x27 = mapPtr →
        HbTopSaved s0 sc → StdStatePreserved s0 sc → s0.mem.KeepsFrozen sc.mem →
        SepWP ((hbProg P).rebase P.pl.base X) target sc
          (A.Heap lc blk s0 ∗ stackAt (s0.sp - 96#64) (16 + A.stackBytes) ∗ F) post (fun _ => ⌜A.allowOom⌝) by
      exact this _
        (by dsimp only [hbAllocSym]; simpa using (by bv_omega :
            P.pl.base + 680#64 + (P.pl.ρ hbAllocSym - P.pl.base - 680#64) = P.pl.ρ hbAllocSym))
        (by simp [hrunc0]) (by simp [hspc0, hsp3]) (by simpa [State.spAligned, hspc0, hsp3] using hsp3_al)
        (by simp [Reg.lr]) (by simp [Reg.x0, bm']) (by simp [Reg.x1])
        (by simpa [Reg.x19] using hx19_c) (by simpa [Reg.x20] using hx20_c)
        (by simpa [Reg.x21] using hx21_c) (by simpa [Reg.x22] using hx22_c)
        (by simpa [Reg.x23] using hx23_c) (by simpa [Reg.x24] using hx24_c)
        (by simpa [Reg.x25] using hx25_c) (by simpa [Reg.x26] using hx26_c)
        (by simpa [Reg.x27] using hx27_c) (by hb_top htop_0c0)
        (hstd_0c0.trans ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩)
        (by simpa using hkf_0c0)
    intro sc hpc_c hrun_c hsp_c hsp_c_al hlr_c hx0_c hx1_c hx19_c' hx20_c' hx21_c' hx22_c' hx23_c'
      hx24_c' hx25_c' hx26_c' hx27_c' htop_c hstd_c hkf_c
    have hstk_sh := stackAt_shrink (s0.sp - 96#64) (16 + A.stackBytes) A.stackBytes (by omega) (by omega)
    have htab_eq : tableAllocBytes bm' = 17 * (bm'.toNat + 1) + 8 := by
      simp only [tableAllocBytes, hbm'.ne_zero, ↓reduceIte]
    have hlay : LayoutOk (BitVec.ofNat 64 (tableAllocBytes bm')) 8#64 := htab_eq ▸ (ValidBucketMask.tableLayoutOk hbm')
    have hsz_nat : (BitVec.ofNat 64 (tableAllocBytes bm')).toNat = tableAllocBytes bm' := by
      simp only [BitVec.toNat_ofNat]; omega
    refine SepWP.weaken_pre (P' := A.Heap lc blk sc ∗ stackAt sc.sp A.stackBytes ∗
      (F ∗ memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)))
      (by rw [hsp_c, hstk_sh]
          exact Entails.trans (Entails.of_eq (show _ = A.Heap lc blk s0 ∗
            stackAt (s0.sp - 96#64) A.stackBytes ∗
            (F ∗ memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes)) by ac_rfl))
            (sepConj_mono_left (A.heap_transport (StdStatePreserved.toHbVmPreserved hstd_c)))) ?_
    refine SepWP.call_subroutine_frame hext.alloc_ok (x := (BitVec.ofNat 64 (tableAllocBytes bm'), 8#64, lc, blk))
      (F := F ∗ memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 (16 + A.stackBytes)) (16 + A.stackBytes - A.stackBytes))
      (ret_pc := P.pl.base + 684#64) hpc_c hrun_c hsp_c_al hlr_c
      (fun R' hm => by
        dsimp only [withCodeInv, hbAllocSpec]; rw [sepConj_assoc]
        refine (satisfies_pure_sepConj _ _ _).mpr ⟨A.codeInv_keepsFrozen hkf_c hCode0, ?_⟩; rw [sepConj_assoc]
        refine (satisfies_pure_sepConj _ _ _).mpr ⟨⟨hx0_c, hx1_c, hlay, fun hna => by simpa [hsz_nat] using himp_can hna⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
      (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sa hpca hruna hspa hcsa => ?_)
      (fun R' sf _ h => by
        dsimp only [withCodeInv, hbAllocSpec] at h
        have h' := (satisfies_pure_sepConj _ _ _).mp h; exact satisfies_pure_frame_of_sepConj h'.1 h'.2)
    dsimp only [withCodeInv, hbAllocSpec]; rw [sepConj_assoc]; refine sepWP_pure_elim fun hasp_ca => ?_
    have hasp_0c : AllocStatePreserved s0 sc := StdStatePreserved.toAllocStatePreserved hstd_c hkf_c
    have hasp_0a : AllocStatePreserved s0 sa :=
      ⟨hasp_ca.1.trans hasp_0c.1, hasp_ca.2.1.trans hasp_0c.2.1, hasp_ca.2.2.1.trans hasp_0c.2.2.1,
       hasp_ca.2.2.2.1.trans hasp_0c.2.2.2.1, hasp_0c.2.2.2.2.trans hasp_ca.2.2.2.2⟩
    rw [hsp_c, sepConj_assoc]
    exact hcont sa hpca hruna (hspa.trans hsp_c) (by simpa [State.spAligned, hspa] using hsp_c_al)
      (hcsa.readReg64_x19.trans hx19_c') (hcsa.readReg64_x20.trans hx20_c')
      (hcsa.readReg64_x21.trans hx21_c') (hcsa.readReg64_x22.trans hx22_c')
      (hcsa.readReg64_x23.trans hx23_c') (hcsa.readReg64_x24.trans hx24_c')
      (hcsa.readReg64_x25.trans hx25_c') (hcsa.readReg64_x26.trans hx26_c')
      (hcsa.readReg64_x27.trans hx27_c') hbm' (htop_c.trans_cs hcsa) hasp_0a

theorem hbResize_overflow_toPanic (P : HbPlaced) (X : String → Option (State → State))
    {s0 s2 : State} {bm : BitVec 64} {mLen : Nat} {F : SepProp} {oom : State → SepProp}
    (hpc : s2.pc = P.pl.base + 76#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = s0.sp - 96#64) (hsp_al : s2.spAligned = true)
    (hw3 : s2.readReg32 .x3 = 1#32)
    (hx9 : s2.readReg64 .x9 = BitVec.ofNat 64 (mLen + 1))
    (hx20 : s2.readReg64 .x20 = bucketMaskToCapacityBV bm)
    (hbm0 : bm = 0#64 ∨ ValidBucketMask bm) (hm_le : mLen ≤ bucketMaskToCapacity bm)
    (hge_max : ¬ (bucketMaskToCapacity bm < MaxHashbrownCapacity)) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.ρ hbCapOverflowSym) s2 F
      (fun sm Pm => Pm = F ∧ sm.sp = s0.sp - 96#64 ∧ sm.spAligned = true ∧
        sm.readReg64 Reg.lr = P.pl.base + 1016#64 ∧ sm.readReg32 .x0 = 1#32) oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  obtain ⟨hcap_le_max, hcsinc⟩ := hbResize_cap_after_csinc hbm0 hm_le
  let cap := BitVec.ofNat 64 (bucketMaskToCapacity bm + 1)
  have hcap_s2 : (if (s2.readReg64 (.gpr 20#5) + 1#64).ule (s2.readReg64 (.gpr 9#5)) = true
      then s2.readReg64 (.gpr 9#5) else s2.readReg64 (.gpr 20#5) + 1#64) = cap := by
    rw [show s2.readReg64 (.gpr 20#5) = bucketMaskToCapacityBV bm from hx20,
        show s2.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (mLen + 1) from hx9]; exact hcsinc
  have hmax : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  have hov : MaxHashbrownCapacity < cap.toNat := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hnlt15, hor⟩ := capToBucketMask_overflow_cases hov
  refine SepWP.seq (mid := P.pl.base + 1008#64)
    (Mid := fun s3 P3 => P3 = F ∧ s3.sp = s0.sp - 96#64 ∧ s3.spAligned = true ∧ s3.readReg32 .x3 = 1#32) ?_ ?_
  · wp_steps
    apply SepWP.ite_true rfl (by rw [BitVec.ule_iff_le]; bv_omega)
    rcases hor with hsh_ne | ⟨hsh_eq, _, hmask_or⟩
    · wp_step; wp_step; apply SepWP.ite_true rfl (by simpa [hcap_s2] using hsh_ne)
      exact SepWP.done (by simp) (by simp [hrun])
        ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp_al, by simpa [Reg.x3, State.readReg32] using hw3⟩
    · wp_step; wp_step; apply SepWP.ite_false rfl (by simpa [hcap_s2] using hsh_eq)
      have humulh : (BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64) +
          (cap <<< 3 - BitVec.truncate 64 ((BitVec.zeroExtend 128 (cap <<< 3) * 2635249153387078803#128) >>> 64)) >>> 1) >>> 2 =
          BitVec.ofNat 64 ((cap.toNat * 8) / 7) := umulh_div7_bv hsh_eq
      wp_steps; rcases hmask_or with hgt_lim | ⟨hmask_59, hle_lim⟩
      · apply SepWP.ite_true rfl (by rw [humulh, BitVec.ult_iff_lt]; exact hgt_lim)
        exact SepWP.done (by simp) (by simp [hrun])
          ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp_al, by simpa [Reg.x3, State.readReg32] using hw3⟩
      · apply SepWP.ite_false rfl (by rw [humulh, BitVec.ult_iff_lt, BitVec.not_lt]; exact hle_lim)
        wp_steps
        apply SepWP.ite_false rfl (by rw [humulh, hmask_59]; decide)
        wp_steps
        apply SepWP.ite_true rfl (by rw [humulh, hmask_59]; decide)
        exact SepWP.done (by simp) (by simp [hrun])
          ⟨rfl, by simp [hsp], by simpa [State.spAligned, hsp] using hsp_al, by simpa [Reg.x3, State.readReg32] using hw3⟩
  · rintro s3 P3 hpc3 hrun3 ⟨rfl, hsp3, hsp3_al, hw3_3⟩; wp_step; wp_step
    exact SepWP.done (by simp; bv_lin) (by simp [hrun3])
      ⟨rfl, by simp [hsp3], by simpa [State.spAligned, hsp3] using hsp3_al,
       by simp [Reg.lr], by simpa [Reg.x0, Reg.x3, State.readReg32] using hw3_3⟩

@[local simp] private theorem sigActions_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).sigActions = s.sigActions := rfl
@[local simp] private theorem sigActions_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).sigActions = s.sigActions := rfl

def PureStepEq (p : BitVec 5 → Bool) (s sm : State) : Prop :=
  sm.sp = s.sp ∧ sm.mem = s.mem ∧ HbTopSaved s sm ∧ StdStatePreserved s sm ∧
  ∀ r : BitVec 5, p r = false → sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)

theorem PureStepEq.refl (p : BitVec 5 → Bool) (s : State) : PureStepEq p s s :=
  ⟨rfl, rfl, ⟨rfl, rfl⟩, StdStatePreserved.rfl s, fun _ _ => rfl⟩

theorem PureStepEq.trans {p : BitVec 5 → Bool} {s1 s2 s3 : State}
    (h12 : PureStepEq p s1 s2) (h23 : PureStepEq p s2 s3) : PureStepEq p s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1,
   ⟨h23.2.2.1.1.trans h12.2.2.1.1, h23.2.2.1.2.trans h12.2.2.1.2⟩,
   h12.2.2.2.1.trans h23.2.2.2.1, fun r hr => (h23.2.2.2.2 r hr).trans (h12.2.2.2.2 r hr)⟩

theorem hbResize_skipZeroGroups_loop (P : HbPlaced) (X : String → Option (State → State))
    (fuel : Nat) :
    ∀ (grpBase : Nat) {s : State} {bm oldCtrlPtr : BitVec 64} {oldCtrl : List (BitVec 8)}
      {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp},
      (bm.toNat + 1) - grpBase ≤ fuel →
      s.pc = P.pl.base + 792#64 → s.status = .Running →
      s.readReg64 .x10 = BitVec.ofNat 64 grpBase →
      s.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase →
      OldScanInv bm oldCtrl grpBase 0#8 →
      0 < cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase 0#8) (bm.toNat + 1) →
      (∀ (sm : State) (grpBase' : Nat) (b' : BitVec 8),
        sm.pc = P.pl.base + 816#64 → sm.status = .Running → b' ≠ 0#8 →
        sm.readReg64 .x10 = BitVec.ofNat 64 grpBase' →
        sm.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase' →
        sm.readReg64 .x14 = highBitMaskOfBits b' →
        OldScanInv bm oldCtrl grpBase' b' →
        (∀ r < bm.toNat + 1, copiedAt oldCtrl (bm.toNat + 1) grpBase' b' r =
          copiedAt oldCtrl (bm.toNat + 1) grpBase 0#8 r) →
        cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase' b') (bm.toNat + 1) =
          cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase 0#8) (bm.toNat + 1) →
        PureStepEq (fun r => r == 10#5 || r == 13#5 || r == 14#5) s sm →
        SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm ((oldCtrlPtr ↦ₛ oldCtrl) ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s ((oldCtrlPtr ↦ₛ oldCtrl) ∗ F) post oom := by
  induction fuel with
  | zero => intro grpBase _ _ _ _ _ _ _ hfuel _ _ _ _ hscan hrem _; obtain ⟨_, h16, _, _, _⟩ := hscan.advance_zero hrem; omega
  | succ fuel ih =>
    intro grpBase s bm oldCtrlPtr oldCtrl F post oom hfuel hpc hrun hx10 hx13 hscan hrem hcont
    have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
    obtain ⟨_, h16, hscan1, hcop1, hcnt1⟩ := hscan.advance_zero hrem
    let g1 := ctrlGroupWord oldCtrl (grpBase + 8); let b1 := fullBits8 g1
    have hlen1 : (grpBase + 8) + 8 ≤ oldCtrl.length := hscan.mirror.1 ▸ Nat.le_trans h16 (Nat.le_add_right _ 8)
    have hea : s.readReg64 .x13 + 8#64 = oldCtrlPtr + BitVec.ofNat 64 (grpBase + 8) := by
      rw [hx13, BitVec.ofNat_add]; exact BitVec.add_assoc _ _ _
    refine SepWP.step_ldrSimd64 (vt := 0#5) (addr := .PreIndex .x13 8#64)
      (ea := oldCtrlPtr + BitVec.ofNat 64 (grpBase + 8))
      (wb := some (.x13, oldCtrlPtr + BitVec.ofNat 64 (grpBase + 8))) (v := g1)
      hpc hrun (by simp) rfl (by simp [evalAddrMode, hea])
      (sepLoad64_ctrlGroupWord rfl hlen1 rfl) rfl ?_
    dsimp only [applyWriteback]
    rw [show P.pl.base + 792#64 + 4#64 = P.pl.base + 796#64 by simp]
    wp_steps
    have hm := simd_cmge_zero8 g1; conv at hm => lhs; simp only [wp_norm, arm64_norm]
    rw [hm]
    wp_if hcond
    · have hb1 : b1 = 0#8 := (highBitMaskOfBits_eq_zero_iff b1).mp (by simpa [byteMaskOfBits_and_highBits] using hcond)
      refine ih (grpBase + 8) (by omega) (by simp) (by simp [hrun])
        (by simp [Reg.x10, BitVec.ofNat_add]) (by simp [Reg.x13])
        (hb1 ▸ hscan1) (by rw [← hb1, hcnt1]; exact hrem)
        fun sm grpBase' b' hpcm hrunm hb' hx10m hx13m hx14m hscanm hcopm hcntm hpem =>
          hcont sm grpBase' b' hpcm hrunm hb' hx10m hx13m hx14m hscanm
            (fun r hr => (hcopm r hr).trans (hb1 ▸ hcop1 r hr)) (hcntm.trans (hb1 ▸ hcnt1))
            (PureStepEq.trans ?_ hpem)
      refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
        ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
      simp [hr.1.1, hr.1.2, hr.2]
    · have hb1 : b1 ≠ 0#8 := fun hz => hcond (by dsimp only [b1] at hz; simp [hz])
      refine hcont _ (grpBase + 8) b1 (by simp) (by simp [hrun]) hb1
        (by simp [Reg.x10, BitVec.ofNat_add]) (by simp [Reg.x13])
        (by simp [Reg.x14, byteMaskOfBits_and_highBits]; rfl) hscan1 hcop1 hcnt1 ?_
      refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
        ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
      simp [hr.1.1, hr.1.2, hr.2]

theorem hbResize_skipZeroGroups (P : HbPlaced) (X : String → Option (State → State))
    {s : State} {bm oldCtrlPtr : BitVec 64} {oldCtrl : List (BitVec 8)} {grpBase : Nat} {b : BitVec 8}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = P.pl.base + 788#64) (hrun : s.status = .Running)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 grpBase)
    (hx13 : s.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase)
    (hx14 : s.readReg64 .x14 = highBitMaskOfBits b)
    (hscan : OldScanInv bm oldCtrl grpBase b)
    (hrem : 0 < cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase b) (bm.toNat + 1))
    (hcont : ∀ (sm : State) (grpBase' : Nat) (b' : BitVec 8),
      sm.pc = P.pl.base + 816#64 → sm.status = .Running → b' ≠ 0#8 →
      sm.readReg64 .x10 = BitVec.ofNat 64 grpBase' →
      sm.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase' →
      sm.readReg64 .x14 = highBitMaskOfBits b' →
      OldScanInv bm oldCtrl grpBase' b' →
      (∀ r < bm.toNat + 1, copiedAt oldCtrl (bm.toNat + 1) grpBase' b' r =
        copiedAt oldCtrl (bm.toNat + 1) grpBase b r) →
      cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase' b') (bm.toNat + 1) =
        cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase b) (bm.toNat + 1) →
      PureStepEq (fun r => r == 10#5 || r == 13#5 || r == 14#5) s sm →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm ((oldCtrlPtr ↦ₛ oldCtrl) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s ((oldCtrlPtr ↦ₛ oldCtrl) ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hpe_set : ∀ pc', PureStepEq (fun r => r == 10#5 || r == 13#5 || r == 14#5) s (s.setPC pc') :=
    fun _ => ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, fun _ _ => rfl⟩
  wp_step; wp_if hcond
  · have hb0 : b ≠ 0#8 := fun hz => hcond (by simp [hz])
    exact hcont _ grpBase b (by simp) (by simp [hrun]) hb0
      (by simpa [Reg.x10] using hx10) (by simpa [Reg.x13] using hx13) (by simpa [Reg.x14] using hx14)
      hscan (fun _ _ => rfl) rfl (hpe_set _)
  · have hb0 : b = 0#8 := (highBitMaskOfBits_eq_zero_iff b).mp (by simpa [hx14] using hcond)
    subst hb0
    exact hbResize_skipZeroGroups_loop P X (bm.toNat + 1 - grpBase) grpBase (Nat.le_refl _)
      (by simp) (by simp [hrun]) (by simpa [Reg.x10] using hx10) (by simpa [Reg.x13] using hx13)
      hscan hrem fun sm grpBase' b' hpcm hrunm hb' hx10m hx13m hx14m hscanm hcopm hcntm hpem =>
        hcont sm grpBase' b' hpcm hrunm hb' hx10m hx13m hx14m hscanm hcopm hcntm
          (PureStepEq.trans (hpe_set _) hpem)

theorem specialBits8_zero_not_mem_empty {bm' : BitVec 64} {newCtrl : List (BitVec 8)} {pos : Nat}
    (hmir : CtrlMirrorInv (bm'.toNat + 1) newCtrl) (hpos : pos < bm'.toNat + 1)
    (hz : specialBits8 (ctrlGroupWord newCtrl pos) = 0#8) :
    tagEmpty ∉ ctrlGroupAt newCtrl pos := by
  have hlen : pos + 8 ≤ newCtrl.length := hmir.1 ▸ Nat.add_le_add_right (Nat.le_of_lt hpos) 8
  intro hmem; obtain ⟨je, hje, hlane⟩ := (mem_ctrlGroupAt_iff hlen tagEmpty).mp hmem
  have hbit := (bv8_eq_zero_iff_forall _).mp hz je hje
  rw [getLsbD_specialBits8 _ hje, hlane] at hbit; cases hbit

theorem simd_cmlt_zero8_norm (g : BitVec 64) :
    (0#128 |||
      ((if (BitVec.zeroExtend 128 g >>> 0 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
      ((if (BitVec.zeroExtend 128 g >>> 8 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
      ((if (BitVec.zeroExtend 128 g >>> 16 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
      ((if (BitVec.zeroExtend 128 g >>> 24 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
      ((if (BitVec.zeroExtend 128 g >>> 32 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
      ((if (BitVec.zeroExtend 128 g >>> 40 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
      ((if (BitVec.zeroExtend 128 g >>> 48 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
      ((if (BitVec.zeroExtend 128 g >>> 56 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 56) =
    BitVec.zeroExtend 128 (byteMaskOfBits (specialBits8 g)) := by
  have hm := simd_cmlt_zero8 g
  conv at hm => lhs; simp only [wp_norm, arm64_norm]
  exact hm

theorem hbResize_probeEmpty_adv (P : HbPlaced) (X : String → Option (State → State))
    {s : State} {bm' newCtrlPtr k : BitVec 64} (hv : ValidBucketMask bm') (step : Nat)
    {P0 : SepProp} {oom : State → SepProp}
    (hpc : s.pc = P.pl.base + 948#64) (hrun : s.status = .Running)
    (hx17 : s.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k step))
    (hx18 : s.readReg64 .x18 = BitVec.ofNat 64 (8 * step) + 8#64)
    (hx19 : s.readReg64 .x19 = newCtrlPtr) (hx21 : s.readReg64 .x21 = bm') :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 960#64) s P0
      (fun s1 P1 => P1 = P0 ∧
        s1.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k (step + 1)) ∧
        s1.readReg64 .x18 = BitVec.ofNat 64 (8 * (step + 1)) + 8#64 ∧
        s1.readReg64 .x19 = newCtrlPtr ∧ s1.readReg64 .x21 = bm' ∧
        PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s s1) oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hstep_bv := probePos_step_bv hv k step
  wp_steps
  refine SepWP.done (by simp) (by simp [hrun]) ⟨rfl, by simp [Reg.x17],
    by simp [Reg.x18, show 8 * (step + 1) = 8 * step + 8 by omega, BitVec.ofNat_add, BitVec.add_assoc],
    by simpa [Reg.x19] using hx19, by simpa [Reg.x21] using hx21, ?_⟩
  refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
  simp [hr.1.2, hr.2]

theorem hbResize_probeEmpty_chk (P : HbPlaced) (X : String → Option (State → State))
    {s1 : State} {bm' newCtrlPtr : BitVec 64} {newCtrl : List (BitVec 8)} {pos1 step1 : Nat}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen1 : pos1 + 8 ≤ newCtrl.length)
    (hpc1 : s1.pc = P.pl.base + 960#64) (hrun1 : s1.status = .Running)
    (hx17_1 : s1.readReg64 .x17 = BitVec.ofNat 64 pos1)
    (hx18_1 : s1.readReg64 .x18 = BitVec.ofNat 64 (8 * step1) + 8#64)
    (hx19_1 : s1.readReg64 .x19 = newCtrlPtr) (hx21_1 : s1.readReg64 .x21 = bm')
    (hExit : ∀ (sm : State),
      let sb1 := specialBits8 (ctrlGroupWord newCtrl pos1)
      sm.pc = P.pl.base + 864#64 → sm.status = .Running → sb1 ≠ 0#8 →
      sm.readReg64 .x0 = byteMaskOfBits sb1 →
      sm.readReg64 .x17 = BitVec.ofNat 64 pos1 →
      PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s1 sm →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom)
    (hNext : ∀ (s2 : State),
      specialBits8 (ctrlGroupWord newCtrl pos1) = 0#8 →
      s2.pc = P.pl.base + 948#64 → s2.status = .Running →
      s2.readReg64 .x17 = BitVec.ofNat 64 pos1 →
      s2.readReg64 .x18 = BitVec.ofNat 64 (8 * step1) + 8#64 →
      s2.readReg64 .x19 = newCtrlPtr → s2.readReg64 .x21 = bm' →
      PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s1 s2 →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s2 ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s1 ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  let sb1 := specialBits8 (ctrlGroupWord newCtrl pos1)
  wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord newCtrlPtr newCtrl (pos := pos1) hlen1]
  wp_steps
  wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord newCtrlPtr newCtrl (pos := pos1) hlen1]
  rw [simd_cmlt_zero8_norm]
  wp_if hcond
  · have hsb1 : sb1 ≠ 0#8 := fun hz => hcond (by dsimp only [sb1] at hz; simp [hz])
    refine hExit _ (by simp) (by simp [hrun1]) hsb1
      (by simp [Reg.x0]) (by simpa [Reg.x17] using hx17_1) ?_
    refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
    simp [hr.1.1]
  · have hsb1 : sb1 = 0#8 := (byteMaskOfBits_eq_zero_iff sb1).mp (by simpa using hcond)
    wp_step
    refine hNext _ hsb1 (by simp) (by simp [hrun1])
      (by simpa [Reg.x17] using hx17_1) (by simpa [Reg.x18] using hx18_1)
      (by simpa [Reg.x19] using hx19_1) (by simpa [Reg.x21] using hx21_1) ?_
    refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
    simp [hr.1.1]

theorem hbResize_probeEmpty_step (P : HbPlaced) (X : String → Option (State → State))
    {s : State} {bm oldGl oldItems bm' newCtrlPtr k : BitVec 64}
    {oldCtrl newCtrl : List (BitVec 8)} {oldSlots newSlots : List (BitVec 64 × BitVec 64)}
    {m : Map64} {oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m} {copied : Nat → Bool}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnew : NewTablePartialInv oldInv bm' copied newCtrl newSlots) (step : Nat)
    (hpc : s.pc = P.pl.base + 948#64) (hrun : s.status = .Running)
    (hx17 : s.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k step))
    (hx18 : s.readReg64 .x18 = BitVec.ofNat 64 (8 * step) + 8#64)
    (hx19 : s.readReg64 .x19 = newCtrlPtr) (hx21 : s.readReg64 .x21 = bm')
    (hExit : ∀ (sm : State),
      let sb1 := specialBits8 (ctrlGroupWord newCtrl (probePos bm' k (step + 1)))
      sm.pc = P.pl.base + 864#64 → sm.status = .Running → sb1 ≠ 0#8 →
      sm.readReg64 .x0 = byteMaskOfBits sb1 →
      sm.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k (step + 1)) →
      PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s sm →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom)
    (hNext : ∀ (s2 : State),
      specialBits8 (ctrlGroupWord newCtrl (probePos bm' k (step + 1))) = 0#8 →
      s2.pc = P.pl.base + 948#64 → s2.status = .Running →
      s2.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k (step + 1)) →
      s2.readReg64 .x18 = BitVec.ofNat 64 (8 * (step + 1)) + 8#64 →
      s2.readReg64 .x19 = newCtrlPtr → s2.readReg64 .x21 = bm' →
      PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s s2 →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s2 ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom := by
  have hpos1 : probePos bm' k (step + 1) < bm'.toNat + 1 := probePos_lt_buckets hnew.validMask k (step + 1)
  have hlen1 : probePos bm' k (step + 1) + 8 ≤ newCtrl.length :=
    hnew.mirror.1 ▸ Nat.add_le_add_right (Nat.le_of_lt hpos1) 8
  refine SepWP.seq (hbResize_probeEmpty_adv P X hnew.validMask step hpc hrun hx17 hx18 hx19 hx21) ?_
  rintro s1 P1 hpc1 hrun1 ⟨rfl, hx17_1, hx18_1, hx19_1, hx21_1, hpe01⟩
  exact hbResize_probeEmpty_chk P X hlen1 hpc1 hrun1 hx17_1 hx18_1 hx19_1 hx21_1
    (fun sm hpcm hrunm hsb1 hx0m hx17m hpe1m =>
      hExit sm hpcm hrunm hsb1 hx0m hx17m (PureStepEq.trans hpe01 hpe1m))
    (fun s2 hsb1 hpc2 hrun2 hx17_2 hx18_2 hx19_2 hx21_2 hpe12 =>
      hNext s2 hsb1 hpc2 hrun2 hx17_2 hx18_2 hx19_2 hx21_2 (PureStepEq.trans hpe01 hpe12))

theorem hbResize_probeEmpty_loop (P : HbPlaced) (X : String → Option (State → State))
    (fuel : Nat) {bm oldGl oldItems bm' newCtrlPtr k : BitVec 64}
    {oldCtrl newCtrl : List (BitVec 8)} {oldSlots newSlots : List (BitVec 64 × BitVec 64)}
    {m : Map64} {oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m} {copied : Nat → Bool}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {step_end : Nat} (hend_lt : step_end < numGroups bm')
    (hemp_end : tagEmpty ∈ ctrlGroupAt newCtrl (probePos bm' k step_end))
    (hnew : NewTablePartialInv oldInv bm' copied newCtrl newSlots) :
    ∀ (step : Nat) {s : State},
      step_end - step ≤ fuel → step < step_end →
      (∀ s' ≤ step, tagEmpty ∉ ctrlGroupAt newCtrl (probePos bm' k s')) →
      s.pc = P.pl.base + 948#64 → s.status = .Running →
      s.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k step) →
      s.readReg64 .x18 = BitVec.ofNat 64 (8 * step) + 8#64 →
      s.readReg64 .x19 = newCtrlPtr → s.readReg64 .x21 = bm' →
      (∀ (sm : State) (step' : Nat) (sb : BitVec 8),
        sm.pc = P.pl.base + 864#64 → sm.status = .Running →
        step' < numGroups bm' → sb ≠ 0#8 →
        sb = specialBits8 (ctrlGroupWord newCtrl (probePos bm' k step')) →
        (∀ s' < step', tagEmpty ∉ ctrlGroupAt newCtrl (probePos bm' k s')) →
        sm.readReg64 .x0 = byteMaskOfBits sb →
        sm.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k step') →
        PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s sm →
        SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom := by
  induction fuel with
  | zero => intro step _ hfuel hlt _ _ _ _ _ _ _ _; omega
  | succ fuel ih =>
    intro step s hfuel hlt hprev hpc hrun hx17 hx18 hx19 hx21 hcont
    refine hbResize_probeEmpty_step P X hnew step hpc hrun hx17 hx18 hx19 hx21
      (fun sm hpcm hrunm hsb1 hx0m hx17m hpe =>
        hcont sm (step + 1) _ hpcm hrunm (by omega) hsb1 rfl
          (fun s' hs' => hprev s' (by omega)) hx0m hx17m hpe)
      fun s2 hsb1 hpc2 hrun2 hx17_2 hx18_2 hx19_2 hx21_2 hpe02 => ?_
    have hpos1 : probePos bm' k (step + 1) < bm'.toNat + 1 := probePos_lt_buckets hnew.validMask k (step + 1)
    have hnot_emp1 := specialBits8_zero_not_mem_empty hnew.mirror hpos1 hsb1
    have hlt' : step + 1 < step_end := Classical.byContradiction fun hge =>
      hnot_emp1 ((by omega : step_end = step + 1) ▸ hemp_end)
    exact ih (step + 1) (by omega) hlt'
      (fun s' hs' => if hle : s' ≤ step then hprev s' hle else (by omega : s' = step + 1) ▸ hnot_emp1)
      hpc2 hrun2 hx17_2 hx18_2 hx19_2 hx21_2
      fun sm step' sb hpcm hrunm hst' hsb' hsbeq hpr' hx0m hx17m hpem =>
        hcont sm step' sb hpcm hrunm hst' hsb' hsbeq hpr' hx0m hx17m (PureStepEq.trans hpe02 hpem)

theorem hbResize_probeEmpty (P : HbPlaced) (X : String → Option (State → State))
    {s : State} {bm oldGl oldItems bm' newCtrlPtr k : BitVec 64}
    {oldCtrl newCtrl : List (BitVec 8)} {oldSlots newSlots : List (BitVec 64 × BitVec 64)}
    {m : Map64} {oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m} {copied : Nat → Bool}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = P.pl.base + 848#64) (hrun : s.status = .Running)
    (hx17 : s.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k 0))
    (hx19 : s.readReg64 .x19 = newCtrlPtr) (hx21 : s.readReg64 .x21 = bm')
    (hnew : NewTablePartialInv oldInv bm' copied newCtrl newSlots)
    (hcont : ∀ (sm : State) (step : Nat) (sb : BitVec 8),
      sm.pc = P.pl.base + 864#64 → sm.status = .Running →
      step < numGroups bm' → sb ≠ 0#8 →
      sb = specialBits8 (ctrlGroupWord newCtrl (probePos bm' k step)) →
      (∀ s' < step, tagEmpty ∉ ctrlGroupAt newCtrl (probePos bm' k s')) →
      sm.readReg64 .x0 = byteMaskOfBits sb →
      sm.readReg64 .x17 = BitVec.ofNat 64 (probePos bm' k step) →
      PureStepEq (fun r => r == 0#5 || r == 17#5 || r == 18#5) s sm →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  obtain ⟨step_end, hend_lt, hemp_end⟩ := hnew.exists_empty_probe_group k
  let pos0 := probePos bm' k 0; let g0 := ctrlGroupWord newCtrl pos0; let sb0 := specialBits8 g0
  have hpos0 : pos0 < bm'.toNat + 1 := probePos_lt_buckets hnew.validMask k 0
  have hlen0 : pos0 + 8 ≤ newCtrl.length := hnew.mirror.1 ▸ Nat.add_le_add_right (Nat.le_of_lt hpos0) 8
  wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord newCtrlPtr newCtrl (pos := pos0) hlen0]
  wp_steps
  wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord newCtrlPtr newCtrl (pos := pos0) hlen0]
  have hm := simd_cmlt_zero8 g0; conv at hm => lhs; simp only [wp_norm, arm64_norm]
  rw [hm]
  wp_if hcond
  · have hsb0 : sb0 = 0#8 := (byteMaskOfBits_eq_zero_iff sb0).mp (by simpa using hcond)
    wp_step
    have hnot_emp0 := specialBits8_zero_not_mem_empty hnew.mirror hpos0 hsb0
    have hlt0 : 0 < step_end := Classical.byContradiction fun hge => by
      dsimp only [pos0] at hnot_emp0; exact hnot_emp0 ((by omega : step_end = 0) ▸ hemp_end)
    refine hbResize_probeEmpty_loop P X step_end hend_lt hemp_end hnew 0 (by omega) hlt0
      (fun s' hs' => (by omega : s' = 0) ▸ hnot_emp0) (by simp) (by simp [hrun])
      (by simpa [Reg.x17] using hx17) (by simp [Reg.x18]) (by simpa [Reg.x19] using hx19) (by simpa [Reg.x21] using hx21)
      fun sm step' sb hpcm hrunm hst' hsb' hsbeq hpr' hx0m hx17m hpem =>
        hcont sm step' sb hpcm hrunm hst' hsb' hsbeq hpr' hx0m hx17m (PureStepEq.trans ?_ hpem)
    refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
    simp [hr.1.1, hr.2]
  · have hsb0 : sb0 ≠ 0#8 := fun hz => hcond (by dsimp only [sb0] at hz; simp [hz])
    refine hcont _ 0 sb0 (by simp) (by simp [hrun]) (Nat.lt_of_le_of_lt (Nat.zero_le _) hend_lt)
      hsb0 rfl (fun _ hs => by omega) (by simp [Reg.x0]; rfl) (by simpa [Reg.x17] using hx17) ?_
    refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
    simp [hr.1.1]

def copyLoopModReg (r : BitVec 5) : Bool :=
  r == 0#5 || r == 10#5 || r == 11#5 || r == 12#5 || r == 13#5 ||
  r == 14#5 || r == 15#5 || r == 16#5 || r == 17#5 || r == 18#5

def CopyLoopPreserved (s0 sf : State) : Prop :=
  sf.sp = s0.sp ∧ sf.mem.perm = s0.mem.perm ∧ HbTopSaved s0 sf ∧ StdStatePreserved s0 sf ∧
  ∀ r : BitVec 5, copyLoopModReg r = false → sf.readReg64 (.gpr r) = s0.readReg64 (.gpr r)

theorem CopyLoopPreserved.refl (s : State) : CopyLoopPreserved s s :=
  ⟨rfl, rfl, ⟨rfl, rfl⟩, StdStatePreserved.rfl s, fun _ _ => rfl⟩

theorem CopyLoopPreserved.trans {s1 s2 s3 : State}
    (h12 : CopyLoopPreserved s1 s2) (h23 : CopyLoopPreserved s2 s3) : CopyLoopPreserved s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1,
   ⟨h23.2.2.1.1.trans h12.2.2.1.1, h23.2.2.1.2.trans h12.2.2.1.2⟩,
   h12.2.2.2.1.trans h23.2.2.2.1, fun r hr => (h23.2.2.2.2 r hr).trans (h12.2.2.2.2 r hr)⟩

theorem PureStepEq.to_copyLoopPreserved {p : BitVec 5 → Bool} {s1 s2 : State}
    (hp : ∀ r, copyLoopModReg r = false → p r = false) (h : PureStepEq p s1 s2) :
    CopyLoopPreserved s1 s2 :=
  ⟨h.1, congrArg Memory.perm h.2.1, h.2.2.1, h.2.2.2.1, fun r hr => h.2.2.2.2 r (hp r hr)⟩

theorem extractLsb'_pair_lo (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
theorem extractLsb'_pair_hi (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

theorem hbResize_setNewCtrl (P : HbPlaced) (X : String → Option (State → State))
    {s2 : State} {bm' newCtrlPtr k : BitVec 64} {newCtrl : List (BitVec 8)}
    {pos k_rem : Nat} {sb : BitVec 8} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbm' : ValidBucketMask bm') (hge8 : 8 ≤ bm'.toNat + 1) (hmir : CtrlMirrorInv (bm'.toNat + 1) newCtrl)
    (hpos : pos < bm'.toNat + 1) (hlane : sb.ctz.toNat < 8)
    (hgetD_emp : newCtrl.getD ((pos + sb.ctz.toNat) % (bm'.toNat + 1)) 0#8 = 0xff#8)
    (hpc2 : s2.pc = P.pl.base + 864#64) (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 (.gpr 0#5) = byteMaskOfBits sb)
    (hx12_2 : s2.readReg64 (.gpr 12#5) = BitVec.ofNat 64 (k_rem + 1))
    (hx16_2 : s2.readReg64 (.gpr 16#5) = k * fxSeed)
    (hx17_2 : s2.readReg64 (.gpr 17#5) = BitVec.ofNat 64 pos)
    (hx19_2 : s2.readReg64 (.gpr 19#5) = newCtrlPtr)
    (hx21_2 : s2.readReg64 (.gpr 21#5) = bm')
    (hcont : ∀ s3 : State,
      s3.pc = P.pl.base + 916#64 → s3.status = .Running →
      s3.readReg64 (.gpr 12#5) = BitVec.ofNat 64 k_rem →
      s3.readReg64 (.gpr 17#5) = BitVec.ofNat 64 ((pos + sb.ctz.toNat) % (bm'.toNat + 1)) →
      CopyLoopPreserved s2 s3 →
      (∀ r : BitVec 5, (r == 12#5 || r == 16#5 || r == 17#5 || r == 18#5) = false →
        s3.readReg64 (.gpr r) = s2.readReg64 (.gpr r)) →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s3
        ((newCtrlPtr ↦ₛ setCtrl bm' newCtrl ((pos + sb.ctz.toNat) % (bm'.toNat + 1)) (h2Tag k)) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s2
      ((newCtrlPtr ↦ₛ newCtrl) ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  let newIdx := (pos + sb.ctz.toNat) % (bm'.toNat + 1)
  have hnewIdx : newIdx < bm'.toNat + 1 := Nat.mod_lt _ (Nat.succ_pos _)
  have hnew_ctrl_len : newIdx + 1 ≤ newCtrl.length := hmir.1 ▸ Nat.le_trans hnewIdx (Nat.le_add_right _ 8)
  wp_sym_steps 4
  rw [ProofLib.reverseBits_eq_reverse, byteMaskOfBits_lowestLane _, hbm'.laneIdx_bv hpos hlane]
  have hfold_idx : (pos + sb.ctz.toNat) % (bm'.toNat + 1) = newIdx := rfl
  conv => arg 3; rw [hfold_idx]
  refine SepWP.step_ldrsb (pc := P.pl.base + 880#64) (ea := newCtrlPtr + BitVec.ofNat 64 newIdx)
    (wb := none) (v := 0xff#8) rfl (by simp only [arm64_norm, hrun2]) (by simp only [arm64_norm]; rfl) rfl
    (by simp only [arm64_norm, evalAddrMode, extendVal, hx19_2])
    ((SepLoad8.of_pointsToBytes rfl hnew_ctrl_len rfl).congr_val hgetD_emp) rfl ?_
  dsimp only [applyWriteback, State.writeReg]
  conv => arg 3; rw [show P.pl.base + 880#64 + 4#64 = P.pl.base + 884#64 by bv_lin]
  wp_step; wp_sym_steps 4
  obtain ⟨_, hmir_bv, hmir_lt⟩ := setCtrlMirrorIdx_eq_of_ge8 hbm' hge8 hnewIdx
  refine step_str8_perm (pc := P.pl.base + 904#64) (ea := newCtrlPtr + BitVec.ofNat 64 newIdx) (val := h2Tag k)
    (wb := none) rfl (by simp only [arm64_norm, hrun2]) (by simp only [arm64_norm]; rfl) rfl
    (by simp only [arm64_norm, evalAddrMode, extendVal, hx19_2])
    (by simp only [wp_norm, arm64_norm, h2Tag, fxProd])
    (sepStore8_pointsToBytes_set rfl hnew_ctrl_len rfl) ?_
  intro m1 hm1_perm; dsimp only [applyWriteback]
  conv => arg 3; rw [show P.pl.base + 904#64 + 4#64 = P.pl.base + 908#64 by bv_lin]
  wp_sym_steps 1
  have hmir_len : setCtrlMirrorIdx bm' newIdx < (newCtrl.set newIdx (h2Tag k)).length := by
    rw [List.length_set, hmir.1]; exact hmir_lt
  have hea_mir : newCtrlPtr + ((BitVec.ofNat 64 newIdx - 8#64) &&& bm') + 8#64 =
      newCtrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm' newIdx) := by
    rw [BitVec.add_assoc, hmir_bv]
  refine step_str8_perm (pc := P.pl.base + 912#64)
    (ea := newCtrlPtr + BitVec.ofNat 64 (setCtrlMirrorIdx bm' newIdx)) (val := h2Tag k)
    (wb := none) rfl (by simp only [arm64_norm, hrun2]) (by simp only [arm64_norm]; rfl) rfl
    (by simp only [arm64_norm, evalAddrMode, hea_mir])
    (by simp only [wp_norm, arm64_norm, h2Tag, fxProd])
    (sepStore8_pointsToBytes_set rfl hmir_len rfl) ?_
  intro m2 hm2_perm; dsimp only [applyWriteback]
  wp_conv_pre => change (newCtrlPtr ↦ₛ setCtrl bm' newCtrl newIdx (h2Tag k)) ∗ F
  refine hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun2])
    (by simp only [arm64_norm, BitVec.ofNat_add]) (by simp only [arm64_norm, newIdx]) ?_ (fun r hr => by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
      simp [hr.1.1.1, hr.1.1.2, hr.1.2, hr.2])
  refine ⟨by simp, by simp; exact hm2_perm.trans hm1_perm,
    ⟨by simp, by simp [calleeSavedVRegs]⟩,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     fun a => congrFun (hm2_perm.trans hm1_perm) a⟩, fun r hr => by
      simp only [copyLoopModReg, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
      simp [hr.1.1.1.1.1.1.2, hr.1.1.2, hr.1.2, hr.2]⟩

theorem hbResize_storeSlot (P : HbPlaced) (X : String → Option (State → State))
    {s3 : State} {oldCtrlPtr newCtrlPtr : BitVec 64}
    {oldSlots newSlots : List (BitVec 64 × BitVec 64)} {oldIdx newIdx : Nat} {b' : BitVec 8}
    (hold_sl : oldIdx < oldSlots.length) (hnew_sl : newIdx < newSlots.length)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc3 : s3.pc = P.pl.base + 916#64) (hrun3 : s3.status = .Running)
    (hx14_3 : s3.readReg64 (.gpr 14#5) = highBitMaskOfBits b')
    (hx15_3 : s3.readReg64 (.gpr 15#5) = oldCtrlPtr - (BitVec.ofNat 64 oldIdx <<< 4))
    (hx17_3 : s3.readReg64 (.gpr 17#5) = BitVec.ofNat 64 newIdx)
    (hx19_3 : s3.readReg64 (.gpr 19#5) = newCtrlPtr)
    (hcont : ∀ s4 : State,
      s4.pc = P.pl.base + 936#64 → s4.status = .Running →
      s4.readReg64 (.gpr 14#5) = highBitMaskOfBits ((b' - 1#8) &&& b') →
      CopyLoopPreserved s3 s4 →
      (∀ r : BitVec 5, (r == 14#5 || r == 15#5 || r == 16#5) = false →
        s4.readReg64 (.gpr r) = s3.readReg64 (.gpr r)) →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s4
        (slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr (newSlots.set newIdx (oldSlots[oldIdx]'hold_sl)) ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s3
      (slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  let kv := oldSlots[oldIdx]'hold_sl
  wp_sym_steps 1
  wp_conv_pre => rw [slotsDownFrom_focus_ldur oldCtrlPtr oldSlots hold_sl]
  let ea_old := (oldCtrlPtr - (BitVec.ofNat 64 oldIdx <<< 4)) + 0xfffffffffffffff0#64
  have hea_old2 : ea_old + 8#64 = (oldCtrlPtr - (BitVec.ofNat 64 oldIdx <<< 4)) + 0xfffffffffffffff8#64 := by
    dsimp only [ea_old]; bv_lin
  refine SepWP.step_ldrSimd128 (pc := P.pl.base + 920#64) (vt := 0#5) (ea := ea_old)
    (ea2 := (oldCtrlPtr - (BitVec.ofNat 64 oldIdx <<< 4)) + 0xfffffffffffffff8#64)
    (wb := none) (v1 := kv.1) (v2 := kv.2)
    rfl (by simp only [arm64_norm, hrun3]) (by simp only [arm64_norm]; rfl) rfl
    (by simp only [arm64_norm, evalAddrMode, hx15_3, ea_old]; exact congrArg (·, none) (by bv_lin)) hea_old2
    (by wp_sep_access_fast) (by wp_sep_access_fast) rfl ?_
  dsimp only [applyWriteback]
  wp_conv_pre => rw [← slotsDownFrom_focus_ldur oldCtrlPtr oldSlots hold_sl]
  conv => arg 3; rw [show P.pl.base + 920#64 + 4#64 = P.pl.base + 924#64 by bv_lin]
  wp_sym_steps 2
  have hpre_swap :
      (slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) =
      ((((newCtrlPtr - (BitVec.ofNat 64 newIdx <<< 4)) + 0xfffffffffffffff0#64) ↦₆₄ (newSlots[newIdx]'hnew_sl).1) ∗
       (((newCtrlPtr - (BitVec.ofNat 64 newIdx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ (newSlots[newIdx]'hnew_sl).2) ∗
       (slotsDownFrom newCtrlPtr (newSlots.take newIdx) ∗
        slotsDownFrom (slotAddr newCtrlPtr newIdx) (newSlots.drop (newIdx + 1))) ∗
       (slotsDownFrom oldCtrlPtr oldSlots ∗ F)) := by
    rw [slotsDownFrom_focus_ldur newCtrlPtr newSlots hnew_sl]; ac_rfl
  wp_conv_pre => rw [hpre_swap]
  let ea_new := (newCtrlPtr - (BitVec.ofNat 64 newIdx <<< 4)) + 0xfffffffffffffff0#64
  have hea_new2 : ea_new + 8#64 = (newCtrlPtr - (BitVec.ofNat 64 newIdx <<< 4)) + 0xfffffffffffffff8#64 := by
    dsimp only [ea_new]; bv_lin
  refine step_strSimd128_perm (pc := P.pl.base + 932#64) (vt := 0#5) (ea := ea_new)
    (ea2 := (newCtrlPtr - (BitVec.ofNat 64 newIdx <<< 4)) + 0xfffffffffffffff8#64)
    (v1 := kv.1) (v2 := kv.2) (wb := none)
    rfl (by simp only [arm64_norm, hrun3]) (by simp only [arm64_norm]; rfl) rfl
    (by simp only [arm64_norm, evalAddrMode, ea_new]; exact congrArg (·, none) (by bv_lin)) hea_new2
    (by simp only [arm64_norm, extractLsb'_pair_lo]) (by simp only [arm64_norm, extractLsb'_pair_hi])
    (SepStore64.left (SepStore64.here rfl))
    (SepStore64.right (SepStore64.left (SepStore64.here rfl))) ?_
  intro m3 hm3_perm; dsimp only [applyWriteback]
  have hpost_swap :
      ((ea_new ↦₆₄ kv.1) ∗
       (((newCtrlPtr - (BitVec.ofNat 64 newIdx <<< 4)) + 0xfffffffffffffff8#64) ↦₆₄ kv.2) ∗
       (slotsDownFrom newCtrlPtr (newSlots.take newIdx) ∗
        slotsDownFrom (slotAddr newCtrlPtr newIdx) (newSlots.drop (newIdx + 1))) ∗
       (slotsDownFrom oldCtrlPtr oldSlots ∗ F)) =
      (slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr (newSlots.set newIdx kv) ∗ F) := by
    dsimp only [ea_new]
    rw [slotAddr_sub_lsl4_sub16 newCtrlPtr newIdx, slotAddr_sub_lsl4_sub8 newCtrlPtr newIdx,
        ← slotsDownFrom_update newCtrlPtr newSlots hnew_sl kv, slotPairAt]
    ac_rfl
  wp_conv_pre => rw [hpost_swap]
  refine hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun3])
    (by simpa only [arm64_norm] using highBitMaskOfBits_clear_lowest b') ?_ (fun r hr => by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
      simp [hr.1.1, hr.1.2, hr.2])
  refine ⟨by simp, by simp; exact hm3_perm,
    ⟨by simp, by simp [calleeSavedVRegs]⟩,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     fun a => congrFun hm3_perm a⟩, fun r hr => by
      simp only [copyLoopModReg, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
      simp [hr.1.1.1.1.2, hr.1.1.1.2, hr.1.1.2]⟩

theorem hbResize_copyOneItem (P : HbPlaced) (X : String → Option (State → State))
    {s : State} {bm oldGl oldItems bm' oldCtrlPtr newCtrlPtr : BitVec 64}
    {oldCtrl newCtrl : List (BitVec 8)} {oldSlots newSlots : List (BitVec 64 × BitVec 64)}
    {m : Map64} {oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m}
    {copied : Nat → Bool} {grpBase' k_rem : Nat} {b' : BitVec 8}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = P.pl.base + 816#64) (hrun : s.status = .Running) (hb' : b' ≠ 0#8)
    (hx8 : s.readReg64 .x8 = oldCtrlPtr) (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 grpBase')
    (hx11 : s.readReg64 .x11 = fxSeed) (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 (k_rem + 1))
    (hx13 : s.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase')
    (hx14 : s.readReg64 .x14 = highBitMaskOfBits b')
    (hx19 : s.readReg64 .x19 = newCtrlPtr) (hx21 : s.readReg64 .x21 = bm')
    (hscan : OldScanInv bm oldCtrl grpBase' b')
    (hcop1 : ∀ r < bm.toNat + 1, copiedAt oldCtrl (bm.toNat + 1) grpBase' b' r = copied r)
    (hnew : NewTablePartialInv oldInv bm' copied newCtrl newSlots)
    (hcont : ∀ (sm : State) (newCtrl' : List (BitVec 8)) (newSlots' : List (BitVec 64 × BitVec 64)),
      sm.pc = P.pl.base + 936#64 → sm.status = .Running →
      sm.readReg64 .x10 = BitVec.ofNat 64 grpBase' →
      sm.readReg64 .x11 = fxSeed →
      sm.readReg64 .x12 = BitVec.ofNat 64 k_rem →
      sm.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase' →
      sm.readReg64 .x14 = highBitMaskOfBits ((b' - 1#8) &&& b') →
      NewTablePartialInv oldInv bm' (copiedAt oldCtrl (bm.toNat + 1) grpBase' ((b' - 1#8) &&& b')) newCtrl' newSlots' →
      CopyLoopPreserved s sm →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sm
        ((newCtrlPtr ↦ₛ newCtrl') ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗
         slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots' ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s
      ((newCtrlPtr ↦ₛ newCtrl) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗
       slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  obtain ⟨hold_lt, hold_full, hcop_false1, _, _, hcop_step1, _⟩ := hscan.clear_lowest hb'
  let oldIdx := grpBase' + b'.ctz.toNat
  have hold_sl : oldIdx < oldSlots.length := oldInv.slots_len ▸ hold_lt
  let kv := oldSlots[oldIdx]'hold_sl
  wp_sym_steps 4
  rw [ProofLib.reverseBits_eq_reverse, highBitMaskOfBits_lowestLane b', ← BitVec.ofNat_add]
  wp_conv_pre => rw [slotsDownFrom_focus_ldur oldCtrlPtr oldSlots hold_sl]
  wp_sym_steps 4
  wp_conv_pre => rw [← slotsDownFrom_focus_ldur oldCtrlPtr oldSlots hold_sl]
  refine hbResize_probeEmpty P X (k := kv.1) rfl (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, probePos_zero, BitVec.ofNat_toNat, fxHash, fxProd]; rfl)
    (by simpa only [arm64_norm] using hx19)
    (by simpa only [arm64_norm] using hx21) hnew ?_
  rintro s2 step sb hpc2 hrun2 hstep hsb_ne rfl hprev hx0_2 hx17_2 hpe2
  simp only [arm64_norm] at hx0_2 hx17_2
  have hx10_2 : s2.readReg64 (.gpr 10#5) = BitVec.ofNat 64 grpBase' :=
    (hpe2.2.2.2.2 10#5 (by decide)).trans (by simpa only [arm64_norm] using hx10)
  have hx11_2 : s2.readReg64 (.gpr 11#5) = fxSeed :=
    (hpe2.2.2.2.2 11#5 (by decide)).trans (by simpa only [arm64_norm] using hx11)
  have hx12_2 : s2.readReg64 (.gpr 12#5) = BitVec.ofNat 64 (k_rem + 1) :=
    (hpe2.2.2.2.2 12#5 (by decide)).trans (by simpa only [arm64_norm] using hx12)
  have hx13_2 : s2.readReg64 (.gpr 13#5) = oldCtrlPtr + BitVec.ofNat 64 grpBase' :=
    (hpe2.2.2.2.2 13#5 (by decide)).trans (by simpa only [arm64_norm] using hx13)
  have hx14_2 : s2.readReg64 (.gpr 14#5) = highBitMaskOfBits b' :=
    (hpe2.2.2.2.2 14#5 (by decide)).trans (by simpa only [arm64_norm] using hx14)
  have hx15_2 : s2.readReg64 (.gpr 15#5) = oldCtrlPtr - (BitVec.ofNat 64 oldIdx <<< 4) :=
    (hpe2.2.2.2.2 15#5 (by decide)).trans (by simp only [arm64_norm]; rfl)
  have hx16_2 : s2.readReg64 (.gpr 16#5) = kv.1 * fxSeed :=
    (hpe2.2.2.2.2 16#5 (by decide)).trans (by simp only [arm64_norm]; rfl)
  have hx19_2 : s2.readReg64 (.gpr 19#5) = newCtrlPtr :=
    (hpe2.2.2.2.2 19#5 (by decide)).trans (by simpa only [arm64_norm] using hx19)
  have hx21_2 : s2.readReg64 (.gpr 21#5) = bm' :=
    (hpe2.2.2.2.2 21#5 (by decide)).trans (by simpa only [arm64_norm] using hx21)
  let pos := probePos bm' kv.1 step
  let lane := (specialBits8 (ctrlGroupWord newCtrl pos)).ctz.toNat
  let newIdx := (pos + lane) % (bm'.toNat + 1)
  have hpos : pos < bm'.toNat + 1 := probePos_lt_buckets hnew.validMask kv.1 step
  rcases bv8_ctz_spec hsb_ne with ⟨hlane, hsb_bit, _⟩
  have hnewIdx : newIdx < bm'.toNat + 1 := Nat.mod_lt _ (Nat.succ_pos _)
  have hnew_ctrl_len : newIdx + 1 ≤ newCtrl.length := hnew.mirror.1 ▸ Nat.le_trans hnewIdx (Nat.le_add_right _ 8)
  have hemp_idx : newCtrl[newIdx]'hnew_ctrl_len = tagEmpty := by
    have hspec : isSpecialTag (getLane8 (ctrlGroupWord newCtrl pos) lane) = true := by
      rw [← getLsbD_specialBits8 _ hlane]; exact hsb_bit
    rw [CtrlMirrorInv.lane_eq_mod_of_ge8 hnew.mirror hnew.ge8 hpos hlane] at hspec
    exact (hnew.special_eq_empty (List.getElem_mem _)).mp hspec
  have hgetD_emp : newCtrl.getD newIdx 0#8 = 0xff#8 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnew_ctrl_len]; exact hemp_idx
  have hnew_sl : newIdx < newSlots.length := hnew.slots_len ▸ hnewIdx
  let newCtrl' := setCtrl bm' newCtrl newIdx (h2Tag kv.1)
  have hslot_swap : ∀ (c : List (BitVec 8)) (sl : List (BitVec 64 × BitVec 64)),
      ((newCtrlPtr ↦ₛ c) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗ slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr sl ∗ F) =
      (slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr sl ∗ ((newCtrlPtr ↦ₛ c) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗ F)) :=
    fun _ _ => by ac_rfl
  refine hbResize_setNewCtrl P X hnew.validMask hnew.ge8 hnew.mirror hpos hlane hgetD_emp
    hpc2 hrun2 hx0_2 hx12_2 hx16_2 hx17_2 hx19_2 hx21_2 ?_
  intro s3 hpc3 hrun3 hx12_3 hx17_3 hc23 hreg23
  wp_conv_pre => rw [hslot_swap]
  refine hbResize_storeSlot P X hold_sl hnew_sl hpc3 hrun3
    ((hreg23 14#5 (by decide)).trans hx14_2) ((hreg23 15#5 (by decide)).trans hx15_2)
    hx17_3 ((hreg23 19#5 (by decide)).trans hx19_2) ?_
  intro s4 hpc4 hrun4 hx14_4 hc34 hreg34
  wp_conv_pre => rw [← hslot_swap]
  have hnew' : NewTablePartialInv oldInv bm'
      (copiedAt oldCtrl (bm.toNat + 1) grpBase' ((b' - 1#8) &&& b')) newCtrl' (newSlots.set newIdx kv) :=
    hnew.insert_step hold_lt hold_full ((hcop1 oldIdx hold_lt).symm.trans hcop_false1)
      hstep hlane hprev hemp_idx fun r hr => (hcop_step1 r hr).trans (by rw [hcop1 r hr])
  have hc2 := PureStepEq.to_copyLoopPreserved (fun r hr => by
    simp only [copyLoopModReg, Bool.or_eq_false_iff] at hr ⊢
    exact ⟨⟨hr.1.1.1.1.1.1.1.1.1, hr.1.2⟩, hr.2⟩) hpe2
  have hc12 : CopyLoopPreserved s s2 := CopyLoopPreserved.trans ?_ hc2
  · exact hcont s4 newCtrl' (newSlots.set newIdx kv) hpc4 hrun4
      (by simpa only [arm64_norm] using (hreg34 10#5 (by decide)).trans ((hreg23 10#5 (by decide)).trans hx10_2))
      (by simpa only [arm64_norm] using (hreg34 11#5 (by decide)).trans ((hreg23 11#5 (by decide)).trans hx11_2))
      (by simpa only [arm64_norm] using (hreg34 12#5 (by decide)).trans hx12_3)
      (by simpa only [arm64_norm] using (hreg34 13#5 (by decide)).trans ((hreg23 13#5 (by decide)).trans hx13_2))
      (by simpa only [arm64_norm] using hx14_4) hnew'
      (CopyLoopPreserved.trans (CopyLoopPreserved.trans hc12 hc23) hc34)
  · refine ⟨by simp only [arm64_norm], by simp only [arm64_norm],
      ⟨by simp (config := { decide := true }) only [arm64_norm],
       by simp (config := { decide := true }) only [arm64_norm, calleeSavedVRegs]⟩,
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], fun _ => rfl⟩, fun r hr => ?_⟩
    simp only [copyLoopModReg, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
    simp [hr.1.1.1.2, hr.1.1.2, hr.1.2]

theorem hbResize_copyLoop_iter (P : HbPlaced) (X : String → Option (State → State))
    (fuel : Nat) {bm oldGl oldItems bm' oldCtrlPtr newCtrlPtr : BitVec 64}
    {oldCtrl : List (BitVec 8)} {oldSlots : List (BitVec 64 × BitVec 64)}
    {m : Map64} {oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (k_rem grpBase : Nat) (b : BitVec 8) {s : State}
      {newCtrl : List (BitVec 8)} {newSlots : List (BitVec 64 × BitVec 64)},
      k_rem < fuel →
      s.pc = P.pl.base + 788#64 → s.status = .Running →
      s.readReg64 .x8 = oldCtrlPtr → s.readReg64 .x10 = BitVec.ofNat 64 grpBase →
      s.readReg64 .x11 = fxSeed → s.readReg64 .x12 = BitVec.ofNat 64 (k_rem + 1) →
      s.readReg64 .x13 = oldCtrlPtr + BitVec.ofNat 64 grpBase →
      s.readReg64 .x14 = highBitMaskOfBits b →
      s.readReg64 .x19 = newCtrlPtr → s.readReg64 .x21 = bm' →
      OldScanInv bm oldCtrl grpBase b →
      cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase b) (bm.toNat + 1) = k_rem + 1 →
      NewTablePartialInv oldInv bm' (copiedAt oldCtrl (bm.toNat + 1) grpBase b) newCtrl newSlots →
      (∀ (sf : State) (newCtrlF : List (BitVec 8)) (newSlotsF : List (BitVec 64 × BitVec 64)),
        sf.pc = P.pl.base + 1020#64 → sf.status = .Running →
        SwissTableInv bm' (bucketMaskToCapacityBV bm' - oldItems) oldItems newCtrlF newSlotsF m →
        0 < (bucketMaskToCapacityBV bm' - oldItems).toNat →
        CopyLoopPreserved s sf →
        SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sf
          ((newCtrlPtr ↦ₛ newCtrlF) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗
           slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlotsF ∗ F) post oom) →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s
        ((newCtrlPtr ↦ₛ newCtrl) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗
         slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) post oom := by
  induction fuel with
  | zero => intro k_rem _ _ _ _ _ hfuel; omega
  | succ fuel ih =>
    intro k_rem grpBase b s newCtrl newSlots hfuel hpc hrun hx8 hx10 hx11 hx12 hx13 hx14 hx19 hx21 hscan hcnt hnew hcont
    have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
    have hswap : ∀ c1 c2,
        ((newCtrlPtr ↦ₛ c1) ∗ (oldCtrlPtr ↦ₛ c2) ∗ slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) =
        ((oldCtrlPtr ↦ₛ c2) ∗ (newCtrlPtr ↦ₛ c1) ∗ slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) :=
      fun _ _ => by ac_rfl
    wp_conv_pre => rw [hswap]
    refine hbResize_skipZeroGroups P X hpc hrun hx10 hx13 hx14 hscan (by omega) ?_
    intro s1 grpBase' b' hpc1 hrun1 hb' hx10_1 hx13_1 hx14_1 hscan1 hcop1 hcnt1 hpe1
    wp_conv_pre => rw [← hswap]
    have hcp01 : CopyLoopPreserved s s1 := PureStepEq.to_copyLoopPreserved (fun r hr => by
      simp only [copyLoopModReg, Bool.or_eq_false_iff] at hr ⊢
      exact ⟨⟨hr.1.1.1.1.1.1.1.1.2, hr.1.1.1.1.1.2⟩, hr.1.1.1.1.2⟩) hpe1
    obtain ⟨_, _, _, _, hscan_next, _, hcnt_next0⟩ := hscan1.clear_lowest hb'
    have hcnt_next : cntTrue (uncopiedAt oldCtrl (bm.toNat + 1) grpBase' ((b' - 1#8) &&& b')) (bm.toNat + 1) = k_rem := by
      rw [hcnt_next0, hcnt1, hcnt]; exact Nat.add_sub_cancel _ _
    refine hbResize_copyOneItem P X hpc1 hrun1 hb'
      ((hcp01.2.2.2.2 8#5 (by decide)).trans hx8) hx10_1
      ((hpe1.2.2.2.2 11#5 (by decide)).trans hx11) ((hpe1.2.2.2.2 12#5 (by decide)).trans hx12)
      hx13_1 hx14_1 ((hcp01.2.2.2.2 19#5 (by decide)).trans hx19)
      ((hcp01.2.2.2.2 21#5 (by decide)).trans hx21) hscan1 hcop1 hnew ?_
    intro s3 newCtrl' newSlots' hpc3 hrun3 hx10_3 hx11_3 hx12_3 hx13_3 hx14_3 hnew' hcp13
    have hcp03 := CopyLoopPreserved.trans hcp01 hcp13
    have hcp_pc : ∀ pc', CopyLoopPreserved s3 (s3.setPC pc') :=
      fun _ => ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, fun _ _ => rfl⟩
    cases k_rem with
    | zero =>
      wp_sym_steps 2
      obtain ⟨hinvF, hgl_pos⟩ := hnew'.to_swissTableInv
        (copiedAt_done (oldInv.mirror.1 ▸ Nat.le_add_right _ 8) hcnt_next)
      exact hcont _ newCtrl' newSlots' rfl (by simp only [arm64_norm, hrun3]) hinvF hgl_pos
        (CopyLoopPreserved.trans hcp03 (hcp_pc _))
    | succ k' =>
      have hk_lt : k' + 1 < 2 ^ 64 := by
        have hsum := copiedAt_uncopiedAt_sum oldCtrl (bm.toNat + 1) grpBase b (oldInv.mirror.1 ▸ Nat.le_add_right _ 8)
        rw [hcnt, oldInv.countFull_eq] at hsum
        have h1 : k' + 1 ≤ m.length := Nat.le_trans (Nat.le_succ _) (hsum ▸ Nat.le_add_left _ _)
        have h2 : m.length < 2 ^ 58 := Nat.lt_of_lt_of_le hnew.cap_gt
          (Nat.le_trans (Nat.le_of_lt hnew.validMask.capacity_bounds.2) hnew.validMask.buckets_bounds_dvd.2.1)
        exact Nat.lt_trans (Nat.lt_of_le_of_lt h1 h2) (by decide : 2 ^ 58 < 2 ^ 64)
      have hne0 : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := fun hz => by
        have h0 := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at h0; simp at h0
      wp_step; wp_if hcbnz
      · refine ih k' grpBase' ((b' - 1#8) &&& b') (by omega) rfl (by simp only [arm64_norm, hrun3])
          (by simpa only [arm64_norm] using (hcp03.2.2.2.2 8#5 (by decide)).trans hx8)
          (by simpa only [arm64_norm] using hx10_3)
          (by simpa only [arm64_norm] using hx11_3)
          (by simpa only [arm64_norm] using hx12_3) (by simpa only [arm64_norm] using hx13_3)
          (by simpa only [arm64_norm] using hx14_3)
          (by simpa only [arm64_norm] using (hcp03.2.2.2.2 19#5 (by decide)).trans hx19)
          (by simpa only [arm64_norm] using (hcp03.2.2.2.2 21#5 (by decide)).trans hx21)
          hscan_next hcnt_next hnew' fun sf newCtrlF newSlotsF hpcf hrunf hinvf hglf hcp_rem =>
            hcont sf newCtrlF newSlotsF hpcf hrunf hinvf hglf
              (CopyLoopPreserved.trans (CopyLoopPreserved.trans hcp03 (hcp_pc _)) hcp_rem)
      · exact False.elim (hne0 (by simpa using hcbnz))

theorem hbResize_copyLoop (P : HbPlaced) (X : String → Option (State → State))
    {s : State} {bm oldGl oldItems bm' oldCtrlPtr newCtrlPtr : BitVec 64}
    {oldCtrl : List (BitVec 8)} {oldSlots newSlots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (oldInv : SwissTableInv bm oldGl oldItems oldCtrl oldSlots m)
    (hitems_ne : oldItems ≠ 0#64) (hbm' : ValidBucketMask bm') (hge8 : 8 ≤ bm'.toNat + 1)
    (hcap_gt : m.length < bucketMaskToCapacity bm') (hsl : newSlots.length = bm'.toNat + 1)
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = P.pl.base + 744#64) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = oldCtrlPtr) (hx19 : s.readReg64 .x19 = newCtrlPtr)
    (hx21 : s.readReg64 .x21 = bm') (hx22 : s.readReg64 .x22 = oldItems)
    (hcont : ∀ (sf : State) (newCtrlF : List (BitVec 8)) (newSlotsF : List (BitVec 64 × BitVec 64)),
      sf.pc = P.pl.base + 1020#64 → sf.status = .Running →
      SwissTableInv bm' (bucketMaskToCapacityBV bm' - oldItems) oldItems newCtrlF newSlotsF m →
      0 < (bucketMaskToCapacityBV bm' - oldItems).toNat →
      CopyLoopPreserved s sf →
      SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) sf
        ((newCtrlPtr ↦ₛ newCtrlF) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗
         slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlotsF ∗ F) post oom) :
    SepWP ((hbProg P).rebase P.pl.base X) (P.pl.base + 1020#64) s
      ((newCtrlPtr ↦ₛ List.replicate (bm'.toNat + 1 + 8) tagEmpty) ∗ (oldCtrlPtr ↦ₛ oldCtrl) ∗
       slotsDownFrom oldCtrlPtr oldSlots ∗ slotsDownFrom newCtrlPtr newSlots ∗ F) post oom := by
  have hP := P.placeable; have hb : (hbProg P).base = P.pl.base := rfl
  have hm_pos : 0 < m.length := Classical.byContradiction fun hle =>
    hitems_ne (oldInv.items_eq_zero_iff_nil.mpr (List.eq_nil_of_length_eq_zero (by omega)))
  have hlen0 : 0 + 8 ≤ oldCtrl.length := oldInv.mirror.1 ▸ Nat.add_le_add_right (Nat.zero_le _) 8
  obtain ⟨hscan0, hcop0, hcnt0⟩ := OldScanInv.init oldInv.validMask oldInv.mirror
  have hnew0 := NewTablePartialInv.init oldInv hbm' hge8 hcap_gt hsl hcop0
  wp_conv_pre => rw [pointsToBytes_focus_ctrlGroupWord oldCtrlPtr oldCtrl (pos := 0) hlen0]
  wp_sym_steps 11
  wp_conv_pre => rw [← pointsToBytes_focus_ctrlGroupWord oldCtrlPtr oldCtrl (pos := 0) hlen0]
  have hm := simd_cmge_zero8 (ctrlGroupWord oldCtrl 0); conv at hm => lhs; simp only [wp_norm, arm64_norm]
  conv => arg 3; simp only [wp_norm]; rw [hm]
  refine hbResize_copyLoop_iter P X m.length (m.length - 1) 0 (fullBits8 (ctrlGroupWord oldCtrl 0))
    (by omega) rfl (by simp only [arm64_norm, hrun]) (by simpa only [arm64_norm] using hx8)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, oldInv.items_eq, show m.length - 1 + 1 = m.length by omega])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, byteMaskOfBits_and_highBits])
    (by simpa only [arm64_norm] using hx19) (by simpa only [arm64_norm] using hx21)
    hscan0 (by rw [hcnt0, oldInv.countFull_eq]; omega) hnew0
    fun sf newCtrlF newSlotsF hpcf hrunf hinvf hglf hcp_rem =>
      hcont sf newCtrlF newSlotsF hpcf hrunf hinvf hglf (CopyLoopPreserved.trans ?_ hcp_rem)
  refine ⟨by simp, by simp, ⟨by simp, by simp [calleeSavedVRegs]⟩,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, fun _ => rfl⟩, fun r hr => ?_⟩
  simp only [copyLoopModReg, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hr
  simp [hr.1.1.1.1.1.1.1.1.2, hr.1.1.1.1.1.1.1.2, hr.1.1.1.1.1.1.2, hr.1.1.1.1.1.2, hr.1.1.1.1.2]

theorem U64MapRepReady_of_parts {pl : Obj.Placement} {A : HbAlloc}
    {mapPtr allocPtr ctrlPtr bm items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hal : mapPtr.toNat % 8 = 0) (hnw : mapPtr.toNat + 32 ≤ 2 ^ 64) (hwf : Map64Wf m)
    (hbm : ValidBucketMask bm) (hinv : SwissTableInv bm (bucketMaskToCapacityBV bm - items) items ctrl slots m)
    (hgl_pos : 0 < (bucketMaskToCapacityBV bm - items).toNat) (ha_ne : allocPtr ≠ 0#64) (ha_al : allocPtr.toNat % 8 = 0)
    (ha_nw : allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : ctrlPtr = allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) :
    hbRodata pl ∗ U64MapStruct mapPtr ctrlPtr bm (bucketMaskToCapacityBV bm - items) items ∗
      A.Block allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      slotsDownFrom ctrlPtr slots ∗ (ctrlPtr ↦ₛ ctrl) ⊢
      U64MapRepReady pl A mapPtr m bm := by
  unfold U64MapRepReady
  refine Entails.pure_right ⟨hal, hnw, hwf, hbm.ne_zero⟩ (sepConj_mono_right ?_)
  exact Entails.sepExists_right
    { allocPtr := allocPtr, ctrlPtr := ctrlPtr, growthLeft := bucketMaskToCapacityBV bm - items, items := items, ctrl := ctrl, slots := slots }
    (Entails.pure_right ⟨hinv, hgl_pos, rfl, ha_ne, ha_al, ha_nw, hctrl⟩ (Entails.refl _))


end CaseStudies.Hashbrown.Proofs.ResizeInternal
