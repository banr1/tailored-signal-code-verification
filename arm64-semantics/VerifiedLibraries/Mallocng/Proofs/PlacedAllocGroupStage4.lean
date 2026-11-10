/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage3

/-!
# Root `mmap` Path for Placed `alloc_group` (`blk08`)

Symbolic execution lemmas for the root `mmap` group-allocation path of `alloc_group` on
`mallocngBlockProg mmpl 8 msvc`: size and slot-count selection, disjointness of freshly mapped
regions from `dynamicRootRegions`, header-slice decompositions, and post-`mmap` group setup.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Root `mmap` Size and Count Selection -/

theorem wp_root_mmap_prep [MallocngMultiPlacement]
    (s : State) (sc req cnt' : Nat) (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hgt2048 : 2048 < cnt' * slotStride sc + 16)
    (hprod : cnt' * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hpc : s.pc = mbase 8 + allocSlotOff_mmap_prep) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧
        Cost.RootLenOk sc cnt' len (s.readReg64 .x2) (s.readReg64 .x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have h1M := stride_prod_plus16_le hsc hprod
  have hc_25 : sc ≤ 25 → cnt' * slotStride sc + 16 ≤ 65536 := fun hs => by have := h25 hs; omega
  have h1_25 : sc ≤ 25 → slotStride sc + 16 ≤ 65536 := fun hs => by
    have : 1 * slotStride sc ≤ cnt' * slotStride sc := Nat.mul_le_mul hlo (Nat.le_refl _)
    have := h25 hs; omega
  have hc1_24 : cnt' = 1 → 24 ≤ sc := fun hc1 => by
    subst hc1; apply Classical.byContradiction; intro hlt24
    have := slotStride_le_2032_of_le_23 (by omega : sc ≤ 23)
    omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := cnt' * slotStride sc + 16) (by omega) h1M
  have hOk_c := rootMmapParams_of_cnt (by omega) hlo hhi h1M hc_25 hc1_24
  have hadd16 : BitVec.ofNat 64 (cnt' * slotStride sc) + 16#64 =
      BitVec.ofNat 64 (cnt' * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  dsimp only [allocSlotOff_mmap_prep, allocSlotOff_mmap_go] at hpc ⊢
  wp_sym_steps
  wp_if hne
  · refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
      (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
        sj.readReg64 .x3 = 4095#64 ∧ sj.readReg64 .x4 = 4096#64 ∧
        sj.readReg64 .x20 = BitVec.ofNat 64 cnt' ∧
        sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
        sj.readReg64 .x25 = BitVec.ofNat 64 req ∧
        sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (cnt' * slotStride sc + 16)) ∧
        ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x26 → r ≠ .x27 → sj.readReg64 r = s.readReg64 r) ?_ ?_
    · dsimp only [allocSlotOff_req_round]
      refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
        by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24,
        by simpa using hx25, ?_, ?_⟩, by sep_entail⟩
      · rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c]
      · intro r r0 r1 r3 r26 r27
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ r26, State.readReg64_writeReg64_ne _ _ _ _ r27,
          State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r1,
          State.readReg64_writeReg64_ne _ _ _ _ r3]
    · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
      have hr := wp_root_req_round sj sc req cnt'
        (pageAlignUp (cnt' * slotStride sc + 16)) Frame hw768 hsc hReq h1_25 hOk_c rfl
        hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26
      dsimp only [allocSlotOff_mmap_go] at hr
      refine SepWP.mono hr ?_
      intro sf P_f _ _ ⟨cnt_f, len, hOk, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
      have hx2j : sj.readReg64 .x2 = s.readReg64 .x2 :=
        hjr _ (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨cnt_f, len, hOk, by rw [← hx2j]; exact hLen _, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2,
        h6, h7, fun r r0 r1 r3 r20 r25 r26 r27 =>
          (hregs r r0 r20 r25 r26).trans (hjr r r0 r1 r3 r26 r27), hPf⟩
  · refine SepWP.done rfl (by simp [hrun]) ⟨cnt', pageAlignUp (cnt' * slotStride sc + 16), hOk_c,
      Or.inr ⟨rfl, fun hc hx5 _ => (root_skip_x5_ne hc hx5 hne).elim⟩,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20, ?_, ?_, rfl⟩
    · rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c]
    · intro r r0 r1 r3 _ _ r26 r27
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ r26, State.readReg64_writeReg64_ne _ _ _ _ r27,
        State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r1,
        State.readReg64_writeReg64_ne _ _ _ _ r3]

private theorem sc_and3_decode {x : BitVec 64} {sc : Nat} (hx : x = BitVec.ofNat 64 sc) (hsc : sc < 48) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) &&& 12884901891#64) = 1#32 ↔
      sc % 4 = 1) ∧
    (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 x) &&& 3#64) = 2#32 ↔ sc % 4 = 2) ∧
    (BitVec.zeroExtend 64 (BitVec.setWidth 32 x) &&& 3#64 = 0#64 ↔ sc % 4 = 0) := by
  subst hx
  revert sc
  decide +kernel

private theorem bv64_cmp_decode {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true ↔ a ≤ b) ∧
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true ↔ a < b) := by
  simp [BitVec.ule, BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem root_blo_lt {x7 x2 : BitVec 64} {sc cnt' : Nat} (hc : cnt' ≤ 32)
    (hx7 : 38 < sc → x7 = 1#64)
    (h : (if BitVec.setWidth 32 x7 ≠ 0#32 then x2.ult (BitVec.ofNat 64 (4 * cnt'))
      else ConditionHolds CondCode.CC { c := true }) = true) : 38 < sc → x2.toNat < 4 * cnt' := by
  intro hs; rw [hx7 hs] at h
  simp only [ne_eq, show ¬ BitVec.setWidth 32 (1#64) = 0#32 by decide, not_false_eq_true, ↓reduceIte,
    BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h; exact h

private theorem root_not_blo_ge {x7 x2 : BitVec 64} {sc cnt' : Nat} (hc : cnt' ≤ 32)
    (hx7 : 38 < sc → x7 = 1#64)
    (h : ¬ (if BitVec.setWidth 32 x7 ≠ 0#32 then x2.ult (BitVec.ofNat 64 (4 * cnt'))
      else ConditionHolds CondCode.CC { c := true }) = true) : 38 < sc → 4 * cnt' ≤ x2.toNat := by
  intro hs; rw [hx7 hs] at h
  simp only [ne_eq, show ¬ BitVec.setWidth 32 (1#64) = 0#32 by decide, not_false_eq_true, ↓reduceIte,
    BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h; omega

set_option maxHeartbeats 800000 in
theorem wp_root_size_select_core [MallocngMultiPlacement]
    (s : State) (sc cnt' : Nat) (Frame : SepProp) (Post : State → SepProp → Prop)
    (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hhi : cnt' ≤ 32) (hprod : cnt' * slotStride sc ≤ 1048575)
    (hpc : s.pc = mbase 8 + allocSlotOff_bounces_cap) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc))
    (hx4 : s.readReg64 .x4 = 4096#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt'))
    (hx7 : 38 < sc → s.readReg64 .x7 = 1#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hprep : Cost.RootCntRel sc cnt' cnt' (s.readReg64 .x2) → ∀ (sm : State), sm.pc = mbase 8 + allocSlotOff_mmap_prep → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = s.spAligned → PureStatePres s sm →
      (∀ r, r ≠ .x1 → sm.readReg64 r = s.readReg64 r) →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go)
        sm Frame Post (fun _ => ⌜False⌝))
    (hmul : ∀ (c : Nat) (sm : State), 2 ≤ c → c ≤ 5 → Cost.RootCntRel sc cnt' c (s.readReg64 .x2) →
      sm.pc = mbase 8 + allocSlotOff_cnt_mul → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = s.spAligned → PureStatePres s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 c → sm.readReg64 .x20 = BitVec.ofNat 64 c →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → sm.readReg64 r = s.readReg64 r) →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go)
        sm Frame Post (fun _ => ⌜False⌝)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame Post
      (fun _ => ⌜False⌝) := by
  have hjoin_mul : ∀ (c : Nat) (sj : State), 2 ≤ c → c ≤ 5 → Cost.RootCntRel sc cnt' c (s.readReg64 .x2) →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_cnt_mul)
        sj Frame
        (fun sm Pm =>
          (sm.sp = s.sp ∧ sm.spAligned = s.spAligned ∧ PureStatePres s sm ∧
           sm.readReg64 .x0 = BitVec.ofNat 64 c ∧ sm.readReg64 .x20 = BitVec.ofNat 64 c ∧
           ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → sm.readReg64 r = s.readReg64 r) ∧ Pm = Frame)
        (fun _ => ⌜False⌝) →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go)
        sj Frame Post (fun _ => ⌜False⌝) := by
    intro c sj hclo hchi hrel h1
    refine SepWP.seq h1 ?_
    intro sm Pm hmp hmrun ⟨⟨hsp, hal, hpsp, hm0, hm20, hmr⟩, hPm⟩
    rw [hPm]; exact hmul c sm hclo hchi hrel hmp hmrun hsp hal hpsp hm0 hm20 hmr
  have hA : cnt' * slotStride sc < 2 ^ 64 := Nat.lt_of_le_of_lt hprod (by decide)
  have hd := sc_and3_decode (x := BitVec.ofNat 64 sc) rfl hsc
  have hred : (if BitVec.setWidth 32 (s.readReg64 .x7) ≠ 0#32 then
        (s.readReg64 .x2).ult (BitVec.ofNat 64 (4 * cnt'))
      else ConditionHolds CondCode.CC { c := true }) = true →
      ∀ c, c = Cost.reduceCnt sc cnt' → Cost.RootCntRel sc cnt' c (s.readReg64 .x2) := fun h c hc =>
    Cost.rootCntRel_reduce hc (root_blo_lt hhi hx7 h)
  dsimp only [allocSlotOff_bounces_cap] at hpc
  wp_sym_steps
  wp_if hblo
  · wp_sym_steps
    wp_if heq1
    · wp_sym_steps
      wp_if hls1
      · have hm := hd.1.mp heq1
        have hP := (bv64_cmp_decode (a := cnt' * slotStride sc) (b := 32768) hA (by decide)).1.mp hls1
        have hrel := hred hblo cnt' (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
        exact hprep hrel _ (by dsimp only [allocSlotOff_mmap_prep]; rfl) (by simp [hrun]) (by simp)
          (by simp [State.spAligned]) psp_rfl fun r h1 => by simp [State.readReg64_writeReg64_ne _ _ _ _ h1]
      · have hm := hd.1.mp heq1
        have hP := (not_congr (bv64_cmp_decode (a := cnt' * slotStride sc) (b := 32768) hA (by decide)).1).mp hls1
        have hrel := hred hblo 2 (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
        refine hjoin_mul 2 _ (by omega) (by omega) hrel ?_
        dsimp only [allocSlotOff_cnt_mul]; wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, fun r h0 h1 h20 => by
            simp [State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h0,
              State.readReg64_writeReg64_ne _ _ _ _ h1]⟩, rfl⟩
    · wp_sym_steps
      wp_if heq2
      · wp_sym_steps
        wp_if hls2
        · have hm := hd.2.1.mp heq2
          have hP := (bv64_cmp_decode (a := cnt' * slotStride sc) (b := 16384) hA (by decide)).1.mp hls2
          have hrel := hred hblo cnt' (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
          exact hprep hrel _ (by dsimp only [allocSlotOff_mmap_prep]; rfl) (by simp [hrun]) (by simp)
            (by simp [State.spAligned]) psp_rfl fun r h1 => by simp [State.readReg64_writeReg64_ne _ _ _ _ h1]
        · have hm := hd.2.1.mp heq2
          have hP := (not_congr (bv64_cmp_decode (a := cnt' * slotStride sc) (b := 16384) hA (by decide)).1).mp hls2
          have hrel := hred hblo 3 (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
          refine hjoin_mul 3 _ (by omega) (by omega) hrel ?_
          dsimp only [allocSlotOff_cnt_mul]; wp_sym_steps
          refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
            by simp, by simp, fun r h0 h1 h20 => by
              simp [State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h0,
                State.readReg64_writeReg64_ne _ _ _ _ h1]⟩, rfl⟩
      · wp_sym_steps
        wp_if hcbnz
        · have hm1 := (not_congr hd.1).mp heq1
          have hm2 := (not_congr hd.2.1).mp heq2
          have hm0 := (not_congr hd.2.2).mp hcbnz
          have hrel := hred hblo cnt' (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
          exact hprep hrel _ (by dsimp only [allocSlotOff_mmap_prep]; rfl) (by simp [hrun]) (by simp)
            (by simp [State.spAligned]) psp_rfl fun r h1 => by simp [State.readReg64_writeReg64_ne _ _ _ _ h1]
        · wp_sym_steps
          wp_if hhi3
          · have hm := hd.2.2.mp hcbnz
            have hP := (bv64_cmp_decode (a := 32768) (b := cnt' * slotStride sc) (by decide) hA).2.mp hhi3
            have hrel := hred hblo 3 (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
            refine hjoin_mul 3 _ (by omega) (by omega) hrel ?_
            dsimp only [allocSlotOff_cnt_mul]; wp_sym_steps
            refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
              by simp, by simp, fun r h0 h1 h20 => by
                simp [State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h0,
                  State.readReg64_writeReg64_ne _ _ _ _ h1]⟩, rfl⟩
          · wp_sym_steps
            wp_if hls3
            · have hm := hd.2.2.mp hcbnz
              have hP := (not_congr (bv64_cmp_decode (a := 32768) (b := cnt' * slotStride sc) (by decide) hA).2).mp hhi3
              have hQ := (bv64_cmp_decode (a := cnt' * slotStride sc) (b := 8192) hA (by decide)).1.mp hls3
              have hrel := hred hblo cnt' (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
              exact hprep hrel _ (by dsimp only [allocSlotOff_mmap_prep]; rfl) (by simp [hrun]) (by simp)
                (by simp [State.spAligned]) psp_rfl fun r h1 => by simp [State.readReg64_writeReg64_ne _ _ _ _ h1]
            · have hm := hd.2.2.mp hcbnz
              have hP := (not_congr (bv64_cmp_decode (a := 32768) (b := cnt' * slotStride sc) (by decide) hA).2).mp hhi3
              have hQ := (not_congr (bv64_cmp_decode (a := cnt' * slotStride sc) (b := 8192) hA (by decide)).1).mp hls3
              have hrel := hred hblo 5 (by simp only [Cost.reduceCnt, Nat.mul_comm (slotStride sc) cnt']; (repeat' split) <;> omega)
              refine hjoin_mul 5 _ (by omega) (by omega) hrel ?_
              dsimp only [allocSlotOff_cnt_mul]; wp_sym_steps
              refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
                by simp, by simp, fun r h0 h1 h20 => by
                  simp [State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h0,
                    State.readReg64_writeReg64_ne _ _ _ _ h1]⟩, rfl⟩
  · exact hprep (Cost.rootCntRel_keep (root_not_blo_ge hhi hx7 hblo)) _ (by dsimp only [allocSlotOff_mmap_prep]; rfl) (by simp [hrun]) (by simp)
      (by simp [State.spAligned]) psp_rfl fun r _ => by simp

set_option maxHeartbeats 800000 in
theorem wp_root_size_select [MallocngMultiPlacement]
    (s : State) (sc req cnt' : Nat) (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hgt2048 : 2048 < cnt' * slotStride sc + 16)
    (hprod : cnt' * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hpc : s.pc = mbase 8 + allocSlotOff_bounces_cap) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc))
    (hx4 : s.readReg64 .x4 = 4096#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt'))
    (hx7 : 38 < sc → s.readReg64 .x7 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧
        (∃ c, Cost.RootCntRel sc cnt' c (s.readReg64 .x2) ∧
          Cost.RootLenOk sc c len (s.readReg64 .x2) (s.readReg64 .x5)) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  let Post : State → SepProp → Prop := fun sf P_f =>
    ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧
        (∃ c, Cost.RootCntRel sc cnt' c (s.readReg64 .x2) ∧
          Cost.RootLenOk sc c len (s.readReg64 .x2) (s.readReg64 .x5)) ∧
      sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
      PureStatePres s sf ∧
      sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
      sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
        sf.readReg64 r = s.readReg64 r) ∧
      P_f = Frame
  have hprep : Cost.RootCntRel sc cnt' cnt' (s.readReg64 .x2) → ∀ (sm : State), sm.pc = mbase 8 + allocSlotOff_mmap_prep → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = s.spAligned → PureStatePres s sm →
      (∀ r, r ≠ .x1 → sm.readReg64 r = s.readReg64 r) →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go)
        sm Frame Post (fun _ => ⌜False⌝) := by
    intro hrel sm hmp hmrun hsp hal hpsp hmr
    refine SepWP.mono (wp_root_mmap_prep sm sc req cnt' Frame hw768 hsc hReq
      hlo hhi hgt2048 hprod h25 hmp hmrun (by rw [hmr .x4 (by decide), hx4])
      (by rw [hmr .x20 (by decide), hx20]) (by rw [hmr .x24 (by decide), hx24])
      (by rw [hmr .x25 (by decide), hx25]) (by rw [hmr .x27 (by decide), hx27])) ?_
    intro sf P_f _ _ ⟨cnt_f, len, hOk, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
    refine ⟨cnt_f, len, hOk, ⟨cnt', hrel, ?_⟩, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2,
      h6, h7, fun r r0 r1 r3 r20 r25 r26 r27 =>
        (hregs r r0 r1 r3 r20 r25 r26 r27).trans (hmr r r1), hPf⟩
    rw [← hmr .x2 (by decide), ← hmr .x5 (by decide)]; exact hLen
  have hmul : ∀ (c : Nat) (sm : State), 2 ≤ c → c ≤ 5 → Cost.RootCntRel sc cnt' c (s.readReg64 .x2) →
      sm.pc = mbase 8 + allocSlotOff_cnt_mul → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = s.spAligned → PureStatePres s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 c → sm.readReg64 .x20 = BitVec.ofNat 64 c →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → sm.readReg64 r = s.readReg64 r) →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go)
        sm Frame Post (fun _ => ⌜False⌝) := by
    intro c sm hclo hchi hrel hmp hmrun hsp hal hpsp hm0 hm20 hmr
    refine SepWP.mono (wp_root_cnt_mul sm sc req c Frame hw768 hsc hReq hclo hchi
      hmp hmrun hm0 (by rw [hmr .x4 (by decide) (by decide) (by decide), hx4]) hm20
      (by rw [hmr .x24 (by decide) (by decide) (by decide), hx24])
      (by rw [hmr .x25 (by decide) (by decide) (by decide), hx25])) ?_
    intro sf P_f _ _ ⟨cnt_f, len, hOk, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
    refine ⟨cnt_f, len, hOk, ⟨c, hrel, ?_⟩, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2,
      h6, h7, fun r r0 r1 r3 r20 r25 r26 _ =>
        (hregs r r0 r3 r20 r25 r26).trans (hmr r r0 r1 r20), hPf⟩
    rw [← hmr .x2 (by decide) (by decide) (by decide)]; exact hLen _
  exact wp_root_size_select_core s sc cnt' Frame Post hw768 hsc hhi hprod hpc hrun hx0 hx4 hx6 hx7 hx21 hprep hmul

/-! ## Fresh `mmap` Disjointness and Header Slice Decompositions -/

theorem root_sc_pos {sc cnt' : Nat} (hhi : cnt' ≤ 32)
    (hgt : 2048 < cnt' * slotStride sc + 16) : 0 < sc := by
  by_cases h0 : sc = 0
  · subst h0
    have hs0 : slotStride 0 = 16 := by decide
    rw [hs0] at hgt; omega
  · omega

private theorem page_overlap_inRegion {mb rBase : BitVec 64} {len k : Nat}
    (hMbAl : 4096 ∣ mb.toNat) (hLenAl : 4096 ∣ len) (hLenPos : 4096 ≤ len)
    (hMbHi : mb.toNat + len ≤ 2 ^ 48)
    (hrAl : rBase.toNat % 4096 = 0) (hrHi : rBase.toNat + 4096 ≤ 2 ^ 48)
    (hNotDisj : ¬ DisjointRegions mb len rBase 4096) (hk : k < 4096) :
    InRegion mb len (rBase + BitVec.ofNat 64 k) := by
  obtain ⟨qm, hqm⟩ := hMbAl
  obtain ⟨ql, hql⟩ := hLenAl
  have hqr : rBase.toNat = 4096 * (rBase.toNat / 4096) := by omega
  have hOv : ¬ (mb.toNat + len ≤ rBase.toNat ∨ rBase.toNat + 4096 ≤ mb.toNat) := fun h =>
    hNotDisj (disjointRegions_of_bounds (by omega) (by omega) (by omega) (by omega) h)
  have hSub : mb.toNat ≤ rBase.toNat ∧ rBase.toNat + 4096 ≤ mb.toNat + len := by omega
  have hkEq : (rBase + BitVec.ofNat 64 k).toNat = rBase.toNat + k :=
    add_ofNat_toNat (by omega)
  exact (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩

private theorem ma_base_ownedRw {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {ma : MetaAreaDesc} (hma : ma ∈ st.metaAreas) :
    OwnedRwByte st ma.base := by
  obtain ⟨hMaLo, _, hMaHi, _⟩ := hwf.metaAreas_wf.2.1 ma hma
  have hInMa : InRegion ma.base 4096 ma.base :=
    (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
  refine ⟨Or.inl ⟨ma, hma, hInMa⟩, ?_, ?_⟩
  · intro hCu
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, gr, hgr, hgrPos, hInGr⟩ :=
      carvedUserByte_witness hwf hCu
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgr hgrPos) hInMa hInGr
  · rintro ⟨m', hm'Res, hm'In⟩
    have hm'All : m' ∈ allMetaSlots st :=
      (hwf.free_bump_metas_wf.2.2.2.2.2 m').mp (List.mem_append_right _ hm'Res)
    unfold allMetaSlots at hm'All
    obtain ⟨ma', hma', hm'Map⟩ := List.mem_flatMap.mp hm'All
    obtain ⟨k, hkr, rfl⟩ := List.mem_map.mp hm'Map
    obtain ⟨hLo', hAl', hHi', _⟩ := hwf.metaAreas_wf.2.1 ma' hma'
    obtain ⟨hEq', _, _, _, hSub'⟩ := slotAddr_bounds hLo' hAl' hHi' (List.mem_range.mp hkr)
    by_cases hEqMa : ma = ma'
    · subst hEqMa; have := (inRegion_bounds (by omega)).mp hm'In; omega
    · obtain ⟨i₁, hi₁, hg₁⟩ := List.getElem_of_mem hma
      obtain ⟨i₂, hi₂, hg₂⟩ := List.getElem_of_mem hma'
      have hij : i₁ ≠ i₂ := fun h => hEqMa (hg₁.symm.trans (h ▸ hg₂))
      have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
      rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
      let mrs := st.metaAreas.map fun x => (x.base, 4096)
      have hlen : mrs.length = st.metaAreas.length := List.length_map _
      have hd := PairwiseDisjointRegions.getElem_disjoint hpd.1 (hlen ▸ hi₁) (hlen ▸ hi₂) hij
      have hm1 : mrs[i₁]'(hlen ▸ hi₁) = (ma.base, 4096) := by
        simp only [mrs, List.getElem_map]; exact congrArg (fun x => (x.base, 4096)) hg₁
      have hm2 : mrs[i₂]'(hlen ▸ hi₂) = (ma'.base, 4096) := by
        simp only [mrs, List.getElem_map]; exact congrArg (fun x => (x.base, 4096)) hg₂
      rw [hm1, hm2] at hd; dsimp only at hd
      exact DisjointRegions.not_both hd hInMa (hSub' ma.base hm'In)

private theorem fresh_mmap_disjoint_roots {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {mem : Memory}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {mb : BitVec 64} {len : Nat}
    (hMbAl : 4096 ∣ mb.toNat) (hLenAl : 4096 ∣ len) (hLenPos : 4096 ≤ len)
    (hMbHi : mb.toNat + len ≤ 2 ^ 48) {R : SepProp}
    (hm : mem ⊨ memRegion mb len ∗ memMapped mb len ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :
    ∀ r ∈ dynamicRootRegions st, DisjointRegions mb len r.1 r.2 := by
  have hPermRw : ∀ x, InRegion mb len x → mem.perm x = some Perm.rw :=
    fun x hx => (IsBlock.memRegion mb len).perm_rw hm hx
  have hNoPn : ∀ (p : BitVec 64), p.toNat % 4096 = 0 → p.toNat + 4096 ≤ 2 ^ 48 →
      OwnedProtNoneByte st p → DisjointRegions mb len p 4096 := by
    intro p hpAl hpHi hOwn
    refine Classical.byContradiction fun hNot => ?_
    have hInMb : InRegion mb len p := by
      simpa using page_overlap_inRegion hMbAl hLenAl hLenPos hMbHi hpAl hpHi hNot (k := 0) (by omega)
    have hDom : p ∈ st.masterDom := hwf.masterDom_wf.2.1 p (Or.inr (Or.inl hOwn))
    have hFoc : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
        ((p ↦₈ₙ st.byteVal p) ∗
         SetSep st.masterDom (fun x => OwnedProtNoneByte st x ∧ x ≠ p)
           (fun x => x ↦₈ₙ st.byteVal x)) :=
      SetSep_focus hwf.masterDom_wf.1 _ hDom hOwn
    have hmPn : mem ⊨ (p ↦₈ₙ st.byteVal p) ∗
        (SetSep st.masterDom (fun x => OwnedProtNoneByte st x ∧ x ≠ p)
          (fun x => x ↦₈ₙ st.byteVal x) ∗
         memRegion mb len ∗ memMapped mb len ∗
         ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st) ∗ R) := by
      have hEq : (memRegion mb len ∗ memMapped mb len ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗ R) =
          ((p ↦₈ₙ st.byteVal p) ∗
           (SetSep st.masterDom (fun x => OwnedProtNoneByte st x ∧ x ≠ p)
             (fun x => x ↦₈ₙ st.byteVal x) ∗
            memRegion mb len ∗ memMapped mb len ∗
            ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
            MappedSet st.masterDom (OwnedMappedByte st) ∗ R)) := by
        rw [hFoc]; ac_rfl
      exact hEq ▸ hm
    have h1 := hPermRw p hInMb
    have h2 := (IsBlockProtNone.pointsTo8ProtNone p (st.byteVal p)).perm_protNone hmPn
      (a := p) (by simp [InRegion])
    rw [h1] at h2; cases h2
  intro r hr
  unfold dynamicRootRegions at hr
  simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hr
  rcases hr with (((⟨ma, hma, rfl⟩ | ⟨gp, hgp, rfl⟩) | ⟨ap, hap, rfl⟩) | ⟨g, ⟨hg, hgPos⟩, rfl⟩)
  · obtain ⟨_, hMaAl, hMaHi, _⟩ := hwf.metaAreas_wf.2.1 ma hma
    have hOwn := ma_base_ownedRw hwf hma
    refine Classical.byContradiction fun hNot => ?_
    have hInMb : InRegion mb len ma.base := by
      simpa using page_overlap_inRegion hMbAl hLenAl hLenPos hMbHi hMaAl hMaHi hNot (k := 0) (by omega)
    have hDom : ma.base ∈ st.masterDom := hwf.masterDom_wf.2.1 ma.base (Or.inl hOwn)
    have hFoc : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ((ma.base ↦₈ st.byteVal ma.base) ∗
         SetSep st.masterDom (fun x => OwnedRwByte st x ∧ x ≠ ma.base)
           (fun x => x ↦₈ st.byteVal x)) :=
      SetSep_focus hwf.masterDom_wf.1 _ hDom hOwn
    have hmRw : mem ⊨ (ma.base ↦₈ st.byteVal ma.base) ∗
        (memRegion mb len ∗
         (SetSep st.masterDom (fun x => OwnedRwByte st x ∧ x ≠ ma.base)
           (fun x => x ↦₈ st.byteVal x) ∗
          memMapped mb len ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗ R)) := by
      have hEq : (memRegion mb len ∗ memMapped mb len ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗ R) =
          ((ma.base ↦₈ st.byteVal ma.base) ∗
           (memRegion mb len ∗
            (SetSep st.masterDom (fun x => OwnedRwByte st x ∧ x ≠ ma.base)
              (fun x => x ↦₈ st.byteVal x) ∗
             memMapped mb len ∗
             ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
             MappedSet st.masterDom (OwnedMappedByte st) ∗ R))) := by
        rw [hFoc]; ac_rfl
      exact hEq ▸ hm
    exact not_satisfies_ownsRW_ownsRW (ownsRW_pointsTo8 ma.base _)
      (ownsRW_sepConj_left (ownsRW_memRegion mb len ma.base hInMb)) hmRw
  · obtain ⟨_, hGpAl, hGpHi⟩ := hwf.guard_avail_wf.2.1 gp hgp
    exact hNoPn gp hGpAl hGpHi (Or.inl ⟨gp, hgp, (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩⟩)
  · obtain ⟨_, hApAl, hApHi, _⟩ := hwf.guard_avail_wf.2.2.2 ap hap
    exact hNoPn ap hApAl hApHi (Or.inr ⟨ap, hap, (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩⟩)
  · have hgHi : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 := by
      simpa [GroupDesc.totalBytes, hgPos] using (hwf.groups_wf g hg).2.2.2.2.2.2.1
    have hSubOwn : ∀ x, InRegion g.mem (g.maplen * 4096) x → OwnedMappedByte st x :=
      fun x hx => Or.inr (Or.inr (Or.inr ⟨g, hg, hgPos, hx⟩))
    have hSubDom : ∀ x, InRegion g.mem (g.maplen * 4096) x → x ∈ st.masterDom :=
      fun x hx => hwf.masterDom_wf.2.1 x (Or.inr (Or.inr (hSubOwn x hx)))
    have hExt := MappedSet_extract_slice hwf.masterDom_wf.1 g.mem (by omega) hSubDom hSubOwn
    have hmMap : mem ⊨ memMapped mb len ∗ (memMapped g.mem (g.maplen * 4096) ∗
        (MappedSet st.masterDom (fun x => OwnedMappedByte st x ∧ ¬ InRegion g.mem (g.maplen * 4096) x) ∗
         memRegion mb len ∗
         ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ R)) := by
      have hEq : (memRegion mb len ∗ memMapped mb len ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗ R) =
          (memMapped mb len ∗ (memMapped g.mem (g.maplen * 4096) ∗
           (MappedSet st.masterDom (fun x => OwnedMappedByte st x ∧ ¬ InRegion g.mem (g.maplen * 4096) x) ∗
            memRegion mb len ∗
            ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
            ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ R))) := by
        rw [hExt]; ac_rfl
      exact hEq ▸ hm
    exact Satisfies.disjointRegions_of_memMapped (by omega) (by omega) hmMap

theorem fresh_mmap_disjoint_placed {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {mem : Memory}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {mb : BitVec 64} {maplen : Nat}
    (hMapPos : 0 < maplen) (hMbNe0 : mb ≠ 0#64)
    (hMbAl : 4096 ∣ mb.toNat) (hMbHi : mb.toNat + maplen * 4096 ≤ 2 ^ 48) {R : SepProp}
    (hm : mem ⊨ (mb ↦ₛ List.replicate (maplen * 4096) 0#8) ∗ memMapped mb (maplen * 4096) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st) ∗ R) :
    4096 ≤ mb.toNat ∧
    ∀ r ∈ dynamicRootRegions st, DisjointRegions mb (maplen * 4096) r.1 r.2 := by
  have hMbLo : 4096 ≤ mb.toNat := by
    obtain ⟨q, hq⟩ := hMbAl
    have hne : mb.toNat ≠ 0 := fun h => hMbNe0 (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have hEnt : (mb ↦ₛ List.replicate (maplen * 4096) 0#8) ⊢ memRegion mb (maplen * 4096) :=
    (IsBlock.pointsToBytes_len (by simp)).entails (IsBlock.memRegion mb (maplen * 4096))
      fun _ _ => trivial
  have hmReg : mem ⊨ memRegion mb (maplen * 4096) ∗ memMapped mb (maplen * 4096) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st) ∗ R := by
    rw [← sepConj_assoc] at hm
    exact Satisfies.mono (sepConj_mono_left hEnt) (by simpa [sepConj_assoc] using hm)
  exact ⟨hMbLo,
    fresh_mmap_disjoint_roots hwf hMbAl ⟨maplen, by omega⟩ (by omega) hMbHi hmReg⟩

theorem split_rep40_zero (m : BitVec 64) :
    (m ↦ₛ List.replicate 40 0#8) =
      ((m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗
       ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32) ∗ ((m + 32#64) ↦₆₄ 0#64)) := by
  have h : List.replicate 40 0#8 =
      unpack64 0#64 ++ (unpack64 0#64 ++ (unpack64 0#64 ++
        (unpack32 0#32 ++ (unpack32 0#32 ++ unpack64 0#64)))) := by decide
  rw [h, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes,
    pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem split_mmap_hdr9 (mb : BitVec 64) {n : Nat} (hn : 9 ≤ n) :
    (mb ↦ₛ List.replicate n 0#8) =
      ((mb ↦₆₄ 0#64) ∗ ((mb + 8#64) ↦₈ 0#8) ∗
       ((mb + 9#64) ↦ₛ List.replicate (n - 9) 0#8)) := by
  have heq : n = 8 + (1 + (n - 9)) := by omega
  have h8 : List.replicate 8 0#8 = unpack64 0#64 := by decide
  conv => lhs; rw [heq, List.replicate_add, List.replicate_add, h8]
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    pointsToBytes_append]
  have h1 : List.replicate 1 0#8 = [0#8] := rfl
  rw [h1, List.length_singleton, pointsToBytes_singleton, BitVec.add_assoc]
  have ha : (8#64 : BitVec 64) + 1#64 = 9#64 := rfl
  rw [ha]

theorem fold_mmap_hdr9 (mb m : BitVec 64) (actB : BitVec 8) (k : Nat) :
    ((mb ↦₆₄ m) ∗ ((mb + 8#64) ↦₈ actB) ∗ ((mb + 9#64) ↦ₛ List.replicate k 0#8)) =
      (mb ↦ₛ (unpack64 m ++ [actB] ++ List.replicate k 0#8)) := by
  rw [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    List.singleton_append, pointsToBytes_cons, BitVec.add_assoc]
  have ha : (8#64 : BitVec 64) + 1#64 = 9#64 := rfl
  rw [ha]

/-! ## Post-`mmap` Group Setup and Saved Frame -/

private theorem root_clamp_check :
    ((List.range 256).all fun q =>
      ((List.range 32).all fun cm1 =>
        let c := cm1 + 1
        let w1 := BitVec.setWidth 32 (BitVec.ofNat 64 q) - 1#32
        let w20 := BitVec.setWidth 32 (BitVec.ofNat 64 c)
        let w2 := w20 - 1#32
        let w1' := if w1.slt w20 then w1 else w2
        let w1'' := if (0#32).sle w1' then w1' else 0#32
        BitVec.setWidth 64 w1'' == BitVec.ofNat 64 (min (q - 1) (c - 1)))) = true := by
  decide +kernel

private theorem root_clamp_eq {q cnt_f : Nat} (hq : q < 256) (hlo : 1 ≤ cnt_f) (hhi : cnt_f ≤ 32) :
    let w1 := BitVec.setWidth 32 (BitVec.ofNat 64 q) - 1#32
    let w20 := BitVec.setWidth 32 (BitVec.ofNat 64 cnt_f)
    let w2 := w20 - 1#32
    let w1' := if w1.slt w20 then w1 else w2
    let w1'' := if (0#32).sle w1' then w1' else 0#32
    BitVec.setWidth 64 w1'' = BitVec.ofNat 64 (min (q - 1) (cnt_f - 1)) := by
  have h1 := List.all_eq_true.mp root_clamp_check q (List.mem_range.mpr hq)
  have h2 := List.all_eq_true.mp h1 (cnt_f - 1) (List.mem_range.mpr (by omega))
  have hc : cnt_f - 1 + 1 = cnt_f := by omega
  rw [hc, beq_iff_eq] at h2; exact h2

set_option maxHeartbeats 800000 in
theorem wp_root_after_mmap [MallocngMultiPlacement]
    (s : State) (m mb : BitVec 64) (mmapCtr : BitVec 32)
    (sc cnt_f maplen : Nat) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hsc : sc < 48) (hlo : 1 ≤ cnt_f) (hhi : cnt_f ≤ 32)
    (hMapLo : 1 ≤ maplen) (hMapHi : maplen ≤ 256)
    (hMbNeg1 : mb ≠ BitVec.allOnes 64)
    (hpc : s.pc = mbase 8 + allocSlotOff_after_mmap) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = mb) (hx19 : s.readReg64 .x19 = m)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt_f)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (maplen * 4096)) :
    let lastIdx := cnt_f - 1
    let activeIdx := min (4080 / slotStride sc - 1) (cnt_f - 1)
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_pub_add) s
      (((maddrs.ctx + 12#64) ↦₃₂ mmapCtr) ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x0 = mb ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 activeIdx ∧
        sf.readReg64 .x2 = BitVec.ofNat 64 lastIdx ∧
        sf.readReg64 .x28 = BitVec.ofNat 64 (lastIdx + 1) ∧
        (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x26 → r ≠ .x28 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = (((maddrs.ctx + 12#64) ↦₃₂ (mmapCtr + 1#32)) ∗
               ((m + 32#64) ↦₆₄ (BitVec.ofNat 64 maplen <<< 12)) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  intro lastIdx activeIdx
  dsimp only [allocSlotOff_after_mmap, allocSlotOff_pub_add] at hpc ⊢
  have ⟨hsLo, hsHi⟩ := slotStride_bounds_48 hsc
  have hqLt : 4080 / slotStride sc < 256 := Nat.div_lt_of_lt_mul (by omega)
  have hsNe0 : BitVec.ofNat 64 (slotStride sc) ≠ 0#64 := by
    intro h; have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat] at ht; change slotStride sc % 2 ^ 64 = 0 at ht
    rw [Nat.mod_eq_of_lt (by omega)] at ht; omega
  have hMapSh : BitVec.ofNat 64 (maplen * 4096) >>> 12 = BitVec.ofNat 64 maplen := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    change (maplen * 4096 % 2 ^ 64) / 4096 = maplen % 2 ^ 64
    rw [Nat.mod_eq_of_lt (by omega : maplen * 4096 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : maplen < 2 ^ 64), Nat.mul_div_cancel _ (by omega)]
  have hMapHi52 : BitVec.ofNat 64 maplen &&& BitVec.ofNat 64 (2 ^ 52 - 1) = BitVec.ofNat 64 maplen := by
    apply BitVec.eq_of_toNat_eq
    change (maplen % 2 ^ 64) &&& (2 ^ 52 - 1) = maplen % 2 ^ 64
    rw [Nat.mod_eq_of_lt (by omega : maplen < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod _ 52,
        Nat.mod_eq_of_lt (by omega : maplen < 2 ^ 52)]
  have hDiv : (4080#64 / BitVec.ofNat 64 (slotStride sc)) = BitVec.ofNat 64 (4080 / slotStride sc) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat]
    change (4080 / (slotStride sc % (2 ^ 64))) = (4080 / slotStride sc) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : slotStride sc < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 4080 / slotStride sc < 2 ^ 64)]
  have hClamp := root_clamp_eq hqLt hlo hhi
  dsimp only at hClamp
  have hwQ : BitVec.setWidth 32 (BitVec.ofNat 64 (4080 / slotStride sc)) =
      BitVec.ofNat 32 (4080 / slotStride sc) := by bv_omega
  have hwC : BitVec.setWidth 32 (BitVec.ofNat 64 cnt_f) = BitVec.ofNat 32 cnt_f := by bv_omega
  have hwC1 : BitVec.ofNat 32 cnt_f - 1#32 = BitVec.ofNat 32 (cnt_f - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (2 ^ 32 - 1 + cnt_f % 2 ^ 32) % 2 ^ 32 = (cnt_f - 1) % 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega : cnt_f < 2 ^ 32),
        show (2 ^ 32 - 1 + cnt_f) % 2 ^ 32 = cnt_f - 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
  rw [hwQ, hwC, hwC1] at hClamp
  have h31 : (BitVec.ofNat 64 cnt_f)[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
    change Nat.testBit (cnt_f % 2 ^ 64) 31 = false
    rw [Nat.mod_eq_of_lt (by omega : cnt_f < 2 ^ 64)]
    exact Nat.testBit_lt_two_pow (by omega : cnt_f < 2 ^ 31)
  wp_sym_steps
  wp_if hneg1
  · exfalso; apply hMbNeg1
    have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := by decide
    apply BitVec.eq_of_toNat_eq; rw [hall]
    have ht := congrArg BitVec.toNat hneg1
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
    change (mb.toNat + 1) % 2 ^ 64 = 0 at ht; omega
  · wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨by simp [hrun], by simp, by simp [State.spAligned],
      psp_rfl, by simpa using hx0, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [activeIdx, hsNe0, hDiv, hwQ] using hClamp
    · simp [lastIdx]; bv_omega
    · simp [lastIdx, h31]
      rw [show cnt_f - 1 + 1 = cnt_f by omega]
      apply BitVec.eq_of_toNat_eq
      change (cnt_f % 2 ^ 64) &&& (2 ^ 32 - 1) = cnt_f % 2 ^ 64
      rw [Nat.mod_eq_of_lt (by omega : cnt_f < 2 ^ 64),
          Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt (by omega : cnt_f < 2 ^ 32)]
    · intro r r1 r2 r3 r4 r26 r28
      simp only [State.readReg64_setPC, State.readReg64_setMem, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r2,
        State.readReg64_writeReg64_ne _ _ _ _ r3, State.readReg64_writeReg64_ne _ _ _ _ r4,
        State.readReg64_writeReg64_ne _ _ _ _ r26, State.readReg64_writeReg64_ne _ _ _ _ r28]
    · congr 2; congr 2; congr 1
      rw [hMapSh]; exact hMapHi52

theorem wp_mmap_call_prep [MallocngMultiPlacement]
    (s : State) (len : Nat) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hpc : s.pc = mbase 8 + allocSlotOff_mmap_go) (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 len) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 16) s Frame
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x0 = 0#64 ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 len ∧
        sf.readReg32 .x2 = 3#32 ∧
        sf.readReg32 .x3 = 0x22#32 ∧
        sf.readReg32 .x4 = BitVec.allOnes 32 ∧
        sf.readReg64 .x5 = 0#64 ∧
        sf.readReg64 .lr = mbase 8 + allocSlotOff_after_mmap ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x30 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_mmap_go, allocSlotOff_after_mmap] at hpc ⊢
  wp_sym_steps
  refine SepWP.done (by simp [mbase]; bv_omega) (by simp [hrun]) ⟨by simp [hrun], by simp,
    by simp [State.spAligned], psp_rfl, by simp, by simp,
    by simp [State.readReg32], by simp [State.readReg32], by simp [State.readReg32],
    by simp, by simp, fun r r0 r1 r2 r3 r4 r5 r30 => ?_, rfl⟩
  simp only [State.readReg64_setPC,
    State.readReg64_writeReg64_ne _ _ _ _ r30, State.readReg64_writeReg64_ne _ _ _ _ r0,
    State.readReg64_writeReg64_ne _ _ _ _ r2, State.readReg64_writeReg64_ne _ _ _ _ r3,
    State.readReg64_writeReg64_ne _ _ _ _ r4, State.readReg64_writeReg64_ne _ _ _ _ r5,
    State.readReg64_writeReg64_ne _ _ _ _ r1]

def AllocSlotSaved12 (sp0 r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 : BitVec 64) :
    SepProp :=
  ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
  ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
  ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
  ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
  ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26) ∗
  ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28)

theorem saved12_entails_stackFrame96
    (sp0 r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 : BitVec 64) :
    AllocSlotSaved12 sp0 r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 ⊢
      stackFrameAt sp0 96 := by
  rw [show (96 : Nat) = 8 * 12 from rfl, stackFrameAt_eq_exists_pointsToWords64 sp0 12]
  refine Entails.trans ?_
    (Entails.sepExists_intro [r29, ret_pc, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28])
  rw [pure_sepConj_of_true (by simp :
    [r29, ret_pc, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28].length = 12)]
  simp only [AllocSlotSaved12, pointsToWords64_cons, pointsToWords64_nil, sepConj_emp]
  have h1 : sp0 - 96#64 + 8#64 = sp0 - 88#64 := by bv_omega
  have h2 : sp0 - 88#64 + 8#64 = sp0 - 80#64 := by bv_omega
  have h3 : sp0 - 80#64 + 8#64 = sp0 - 72#64 := by bv_omega
  have h4 : sp0 - 72#64 + 8#64 = sp0 - 64#64 := by bv_omega
  have h5 : sp0 - 64#64 + 8#64 = sp0 - 56#64 := by bv_omega
  have h6 : sp0 - 56#64 + 8#64 = sp0 - 48#64 := by bv_omega
  have h7 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_omega
  have h8 : sp0 - 40#64 + 8#64 = sp0 - 32#64 := by bv_omega
  have h9 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_omega
  have h10 : sp0 - 24#64 + 8#64 = sp0 - 16#64 := by bv_omega
  have h11 : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_omega
  have h96 : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  rw [h96, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  exact Entails.refl _

end VerifiedLibraries.Mallocng.Proofs
