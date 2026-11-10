/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.FinishGrow

/-!
# Placement-Generic `RawVecInner::do_reserve_and_handle`

Placement-generic and allocator-generic (`RustStdAlloc oom`) verification of
`<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<Global>` (block `12` of
`rustStdIoMultiLib`), together with `rustSmallProbeRead_ok'` discharging its reserve premise.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd.Io

open Arm64 Arm64.Obj Arm64.Process ProofLib VerifiedLibraries.Musl
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup

private def rvgLib12 : PlacedLib := rustStdIoMultiLib.blockLib 12
private def rvgPl12 [RawVecGrowPlacement] : Placement :=
  rustStdIoMultiLib.blockPlacement RawVecGrowPlacement.mpl 12
private theorem rvgPlaceable12 [RawVecGrowPlacement] : rvgLib12.Placeable rvgPl12 :=
  rustStdIoMultiLib.placeable_blockLib (by decide) RawVecGrowPlacement.placeable
private def rvgPC12 [RawVecGrowPlacement] : Program := rvgLib12.program rvgPl12

private def rvgProg12 : Program :=
  { code := rvgLib12.text.code, symbols := rvgLib12.text.symbols }
private def rvgTree12 : WordTree := word_tree_of% rvgProg12
private theorem rvg12_code_eq : rvgLib12.text.code = rvgTree12.toBytes := by rfl_kernel
private theorem rvg12_tree_size : rvgTree12.checkSize? = some 35 := by rfl_kernel

gen_placed_fetches rvgPC12 rvgLib12 rvgTree12 rvg12_code_eq rvg12_tree_size
  via_placement rvgPl12 rvgPlaceable12 [0x0 → 0x78]

theorem rustIoBlockNoSvc0_12 : checkBlockNoSvc0 (rustStdIoMultiLib.blockLib 12).text = true := by
  decide

section
arm64_proof_prelude

private def errnoCell (tp : BitVec 64) : SepProp := StdErrnoCell tp
private theorem errnoCell_eq (tp : BitVec 64) : StdErrnoCell tp = errnoCell tp := rfl

private def rvgSavedSlots12 (s0 : State) (st0 : BitVec 64) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ st0) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem rvgFinish_pc [RawVecGrowPlacement] :
    rvgPl12.base + 84#64 + (rvgPl12.ρ finishGrowIoSym - rvgPl12.base - 84#64) =
      rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl finishGrowIoSym := by
  change rvgPl12.base + 84#64 +
    (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl finishGrowIoSym - rvgPl12.base - 84#64) =
    rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl finishGrowIoSym
  bv_lin

private theorem csel_hi_ofNat_eq_max {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = true
     then BitVec.ofNat 64 a else BitVec.ofNat 64 b) = BitVec.ofNat 64 (max a b) := by
  by_cases h : b < a
  · have hult : (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, h]
    rw [hult]; simp [Nat.max_eq_left (Nat.le_of_lt h)]
  · have hult : (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; omega
    rw [hult]; simp [Nat.max_eq_right (by omega : a ≤ b)]

/-- Placement-generic, allocator-generic (`RustStdAlloc oom`) total-correctness and OOM-explicit
    contract for `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<Global>`
    (block `12` of `rustStdIoMultiLib`) under `CodeLoadedWhere keep` (`--gc-sections`-compatible). -/
theorem rustDoReserveAndHandle_okWhere {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {keep : Nat → Bool} (hk12 : keep 12 = true := by decide) (hk22 : keep 22 = true := by decide)
    {P : Program} {reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : 64 + 48 + Rust.hookStack ≤ reserveStack ∧ reserveStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.resolve mpl doReserveAndHandleIoSym)
      (rustStdIoMultiLib.withCodeLoadedWhere keep mpl (rustDoReserveAndHandleSpec A reserveStack)) := by
  letI : RawVecGrowPlacement := ⟨mpl, hpl⟩
  apply subroutine_ok_of_sepWP_init
  rintro ⟨vecPtr, ptr, cap, bs, additional, lb, lk⟩ R s0 hpc hrun hpre hsp
  rw [resolve_eq_base hpl 12 doReserveAndHandleIoSym (by decide) (by decide)] at hpc
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustDoReserveAndHandleSpec] at hpre ⊢
  rw [errnoCell_eq] at hpre ⊢
  rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoadedWhere keep mpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, _hgt, hno_null, hcan⟩, hpre⟩
  let growCap := rustVecGrowCap cap bs.length additional
  have hgrow_lt62 : growCap < 2 ^ 62 := by
    change ¬ NullAllowed growCap 1 at hno_null; unfold NullAllowed at hno_null; omega
  have hgrow_ge8 : 8 ≤ growCap := by
    show 8 ≤ rustVecGrowCap cap bs.length additional; unfold rustVecGrowCap; omega
  have hadd_le : bs.length + additional ≤ growCap := by
    show bs.length + additional ≤ rustVecGrowCap cap bs.length additional; unfold rustVecGrowCap; omega
  have hcap2_le : 2 * cap ≤ growCap := by
    show 2 * cap ≤ rustVecGrowCap cap bs.length additional; unfold rustVecGrowCap; omega
  let finishStack := reserveStack - 112
  rw [show reserveStack = (48 + finishStack) + 8 * 8 by omega,
      stackAt_split_cells s0.sp (48 + finishStack) 8 (by omega)] at hpre
  dsimp only [cells] at hpre
  simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, st2, st3, st4, st5, st6, st7, hpre⟩
  refine ⟨_, hpre, ?_⟩
  wp_conv_pre => simp only [sepConj_assoc]
  have hadd_eq : BitVec.ofNat 64 additional + BitVec.ofNat 64 bs.length =
      BitVec.ofNat 64 (bs.length + additional) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hcs1 : BitVec.ult (BitVec.ofNat 64 (bs.length + additional))
      (BitVec.ofNat 64 additional) = false := by
    simp [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : bs.length + additional < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : additional < 2 ^ 64)]
  have hlsl_eq : (BitVec.ofNat 64 cap) <<< 1 = BitVec.ofNat 64 (2 * cap) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * cap < 2 ^ 64), Nat.shiftLeft_eq]
    omega
  apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
    hext 12 ⟨by decide, hk12⟩ rustIoBlockNoSvc0_12 hcl
    (mid := rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl finishGrowIoSym)
  intro s0' hcpu0; change SepWP (rvgPC12.rebase rvgPl12.base (fun _ => none)) _ _ _ _
  have hpc0' : s0'.pc = rvgPl12.base := hcpu0.toSameCpuState.pc_eq.trans hpc
  have hrun0' : s0'.status = .Running := hcpu0.toSameCpuState.status_eq.trans hrun
  have hsp0' : s0'.spAligned = true := hcpu0.toSameCpuState.spAligned.trans hsp
  have hx0' : s0'.readReg64 (.gpr 0#5) = vecPtr := (hcpu0.toSameCpuState.readReg64 .x0).trans hx0
  have hx1' : s0'.readReg64 (.gpr 1#5) = BitVec.ofNat 64 bs.length :=
    (hcpu0.toSameCpuState.readReg64 .x1).trans hx1
  have hx2' : s0'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 additional :=
    (hcpu0.toSameCpuState.readReg64 .x2).trans hx2
  have hx3' : s0'.readReg64 (.gpr 3#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x3).trans hx3
  have hx4' : s0'.readReg64 (.gpr 4#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x4).trans hx4
  wp_conv_pre => simp only [← hcpu0.toSameCpuState.sp_eq]
  clear hpc; wp_sym_steps
  refine SepWP.done rvgFinish_pc (by simpa [arm64_norm] using hrun0')
    fun sm1 hcpu_m1 hcl1 hnsp1 hsym1 => ?_
  obtain ⟨hpres_01, hpool_01⟩ :=
    allocCallPreserved_of_seg hcpu0 hcpu_m1 hnsp1 hsym1
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq1 : A.pool lb lk s0 = A.pool lb lk sm1 :=
    (A.pool_transport lb lk s0 sm1 hpool_01).symm
  have hhi_m1 : RvgHiCS s0 sm1 :=
    (RvgHiCS.refl s0).of_seg hcpu0 hcpu_m1 (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
  have hx21_m1 : sm1.readReg64 .x21 = s0.readReg64 .x21 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x21]; simp only [arm64_norm]
    exact hcpu0.toSameCpuState.readReg64 .x21
  have hpc1 : sm1.pc = rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl finishGrowIoSym :=
    hcpu_m1.toSameCpuState.pc_eq.trans rvgFinish_pc
  have hrun1 : sm1.status = .Running :=
    hcpu_m1.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun0')
  have hsp1_eq : sm1.sp = s0.sp - 64#64 := by
    rw [hcpu_m1.toSameCpuState.sp_eq]; simp [arm64_norm, hcpu0.toSameCpuState.sp_eq]
  have hsp1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 64#64 hsp
  have hlr1 : sm1.readReg64 .lr = rvgPl12.base + 88#64 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .lr]; simp [arm64_norm]
  have hx0_m1 : sm1.readReg64 .x0 = s0.sp - 56#64 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x0]; simp only [arm64_norm, hcpu0.toSameCpuState.sp_eq]
  have hx1_m1 : sm1.readReg64 .x1 = BitVec.ofNat 64 cap := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x1]; simp [arm64_norm]
  have hx2_m1 : sm1.readReg64 .x2 = ptr := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x2]; simp [arm64_norm]
  have hx20_m1 : sm1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 growCap := by
    rw [hcpu_m1.toSameCpuState.readReg64 (.gpr 20#5)]; simp only [arm64_norm, hlsl_eq]
    rw [csel_hi_ofNat_eq_max (a := bs.length + additional) (b := 2 * cap) (by omega) (by omega)]
    exact csel_hi_ofNat_eq_max (a := max (bs.length + additional) (2 * cap)) (b := 8) (by omega) (by omega)
  have hx3_m1 : sm1.readReg64 .x3 = BitVec.ofNat 64 growCap := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x3]; simp only [arm64_norm, hlsl_eq]
    rw [csel_hi_ofNat_eq_max (a := bs.length + additional) (b := 2 * cap) (by omega) (by omega)]
    exact csel_hi_ofNat_eq_max (a := max (bs.length + additional) (2 * cap)) (b := 8) (by omega) (by omega)
  have hx4_m1 : sm1.readReg64 .x4 = 1#64 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x4]; simp [arm64_norm]
  have hx5_m1 : sm1.readReg64 .x5 = 1#64 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x5]; simp [arm64_norm]
  have hx19_m1 : sm1.readReg64 (.gpr 19#5) = vecPtr := by
    rw [hcpu_m1.toSameCpuState.readReg64 (.gpr 19#5)]; simp [arm64_norm]
  refine SepWP.weaken_pre (P' :=
      stackAt sm1.sp (48 + finishStack) ∗
      vecHeader (s0.sp - 56#64) st1 st2 st3 ∗
      rustStdVecBuf A cap ptr bs ∗ A.pool lb lk sm1 ∗
      StdErrnoCell sm1.tpidrEl0 ∗
      rvgSavedSlots12 s0 st0 ∗
      (vecPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr))
    (by
      rw [← errnoCell_eq, ← hpool_01.2.2]
      dsimp only [vecHeader, rvgSavedSlots12]
      simp only [hcpu0.toSameCpuState.sp_eq, hcpu0.toSameCpuState.readReg64,
        hpool_eq1, hsp1_eq, bv_lin_norm]
      sep_entail) ?_
  have hfg := rustFinishGrow_okWhere A hpl (keep := keep) hext hk22 (finishStack := finishStack)
    ⟨by omega, by omega⟩ hshim halloc hrealloc
  apply seqCodeLoadedWhere hcl1 (mid := rvgPl12.base + 88#64)
  apply (SepWP.call_subroutine_frame hfg
    (x := (s0.sp - 56#64, st1, st2, st3, cap, ptr, bs, growCap, lb, lk))
    hpc1 hrun1 hsp1 hlr1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R' sf _ ho => by
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustFinishGrowSpec] at ho
      rw [satisfies_pure_sepConj] at ho
      rcases ho.1 with ⟨_, sm_o, hio_o, hfs_o, _, hoom_o⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨sm_o, ⟨hio_o.1.trans hpres_01.2.1, hio_o.2.trans hpres_01.2.2.1⟩,
        hfs_o.trans hpres_01.1, hoom_o⟩, Satisfies.drop_left ho.2⟩))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustFinishGrowSpec]
    rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoadedWhere keep mpl sm1.mem⌝,
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_m1, hx1_m1, hx2_m1, hx3_m1, hx4_m1, hx5_m1,
      by omega, by omega, by omega, fun _ => hcan⟩,
      Satisfies.mono (by sep_frame) hm'⟩
  · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
    refine SepWP.done hpc_sf1 hrun_sf1 fun hcl_sf1 => ?_
    dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustFinishGrowSpec]
    wp_conv_pre => simp only [sepExists_sepConj_left]
    apply SepWP.exists_elim; rintro (_ | _)
    · wp_conv_pre => simp only [Bool.false_eq_true, ↓reduceIte,
        sepExists_sepConj_left, sepConj_assoc, hsp1_eq, hpool_01.2.2, errnoCell_eq]
      apply SepWP.exists_elim; intro newPtr
      apply SepWP.pure_elim; rintro ⟨hpres_1f, _⟩
      have hpres_0f : AllocCallPreserved s0 sf1 := allocCallPreserved_trans hpres_01 hpres_1f
      have hsp_sf1_eq : sf1.sp = s0.sp - 64#64 := hsp_sf1.trans hsp1_eq
      have hhi_sf1 : RvgHiCS s0 sf1 := hhi_m1.of_cs hcs_sf1
      have hx19_sf1 : sf1.readReg64 (.gpr 19#5) = vecPtr :=
        hcs_sf1.readReg64_x19.trans hx19_m1
      have hx20_sf1 : sf1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 growCap :=
        hcs_sf1.readReg64_x20.trans hx20_m1
      have hx21_sf1 : sf1.readReg64 .x21 = s0.readReg64 .x21 :=
        hcs_sf1.readReg64_x21.trans hx21_m1
      apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
        hext 12 ⟨by decide, hk12⟩ rustIoBlockNoSvc0_12 hcl_sf1 (mid := s0.readReg64 .lr)
      intro s1' hcpu1; change SepWP (rvgPC12.rebase rvgPl12.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = rvgPl12.base + 88#64 := hcpu1.toSameCpuState.pc_eq.trans hpc_sf1
      have hrun1' : s1'.status = .Running := hcpu1.toSameCpuState.status_eq.trans hrun_sf1
      have hsp1_in : s1'.sp = s0.sp - 64#64 := hcpu1.toSameCpuState.sp_eq.trans hsp_sf1_eq
      have hsp1' : s1'.spAligned = true := by
        simp only [State.spAligned]; rw [hsp1_in]; exact s0.spAligned_sub 64#64 hsp
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = vecPtr :=
        (hcpu1.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19_sf1
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 growCap :=
        (hcpu1.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20_sf1
      wp_conv_pre => simp only [rvgSavedSlots12, vecHeader, ← hsp1_in,
        show s0.sp - 56#64 = s1'.sp + 8#64 by rw [hsp1_in]; bv_lin,
        show s0.sp - 48#64 = s1'.sp + 16#64 by rw [hsp1_in]; bv_lin,
        show s0.sp - 40#64 = s1'.sp + 24#64 by rw [hsp1_in]; bv_lin,
        show s0.sp - 32#64 = s1'.sp + 32#64 by rw [hsp1_in]; bv_lin,
        show s0.sp - 24#64 = s1'.sp + 40#64 by rw [hsp1_in]; bv_lin,
        show s0.sp - 16#64 = s1'.sp + 48#64 by rw [hsp1_in]; bv_lin,
        show s0.sp - 8#64 = s1'.sp + 56#64 by rw [hsp1_in]; bv_lin]
      wp_sym_steps
      refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun1')
        fun sf hcpu_f _hcl_f hnsp_f hsym_f => ?_
      obtain ⟨hpres_ff, hpool_ff⟩ :=
        allocCallPreserved_of_seg hcpu1 hcpu_f hnsp_f hsym_f
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpres_end : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres_0f hpres_ff
      have hpool_eq_end :
          A.pool (rustVecGrowLb A lb cap growCap) (rustVecGrowLk lk cap) sf1 =
            A.pool (rustVecGrowLb A lb cap growCap) (rustVecGrowLk lk cap) sf :=
        (A.pool_transport _ _ sf1 sf hpool_ff).symm
      have hpc_end : sf.pc = s0.readReg64 .lr := by rw [hcpu_f.toSameCpuState.pc_eq]; rfl
      have hrun_end : sf.status = .Running :=
        hcpu_f.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun1')
      have hsp_end : sf.sp = s0.sp := by rw [hcpu_f.toSameCpuState.sp_eq]; simp [arm64_norm]
      have hcs_end : CalleeSavedPreserved s0 sf :=
        (hhi_sf1.of_seg hcpu1 hcpu_f (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])).to_cs
          (by rw [hcpu_f.toSameCpuState.readReg64 .x19]; simp [arm64_norm])
          (by rw [hcpu_f.toSameCpuState.readReg64 .x20]; simp [arm64_norm])
          (by rw [hcpu_f.toSameCpuState.readReg64 .x21]; simp only [arm64_norm]
              exact (hcpu1.toSameCpuState.readReg64 .x21).trans hx21_sf1)
          (by rw [hcpu_f.toSameCpuState.readReg64 .fp]; simp [arm64_norm])
      refine SepWP.weaken_pre ?_
        (SepWP.done hpc_end hrun_end ⟨fun hm_f => hm_f, hsp_end, hcs_end⟩)
      refine Entails.sepExists_right newPtr ?_
      rw [pure_sepConj_of_true (φ := AllocCallPreserved s0 sf) hpres_end,
          hpool_eq_end, hsp1_in, show reserveStack = (48 + finishStack) + 8 * 8 by omega,
          stackAt_split_cells s0.sp (48 + finishStack) 8 (by omega)]
      dsimp only [cells]
      simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_lin_norm]
      refine Entails.sepExists_right st0 <|
        Entails.sepExists_right 0#64 <|
        Entails.sepExists_right newPtr <|
        Entails.sepExists_right (BitVec.ofNat 64 growCap) <|
        Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
        Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
        Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
        Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)
    · wp_conv_pre => simp only [↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro errW1
      apply SepWP.exists_elim; intro errW2
      apply SepWP.pure_elim; rintro ⟨_, hnull_bad⟩
      exact False.elim (hno_null hnull_bad)

/-- Placement-generic, allocator-generic (`RustStdAlloc oom`) total-correctness and OOM-explicit
    contract for `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<Global>`
    (block `12` of `rustStdIoMultiLib`), discharging `hreserve` of `rustSmallProbeRead_ok`. -/
theorem rustDoReserveAndHandle_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {P : Program} {reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : 64 + 48 + Rust.hookStack ≤ reserveStack ∧ reserveStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.resolve mpl doReserveAndHandleIoSym)
      (rustStdIoMultiLib.withCodeLoaded mpl (rustDoReserveAndHandleSpec A reserveStack)) :=
  rustStdIoMultiLib.subroutine_ok_withCodeLoaded_of_where
    (rustDoReserveAndHandle_okWhere A hpl (keep := fun _ => true) (hk12 := rfl) (hk22 := rfl)
      hext hstk hshim halloc hrealloc)

/-- `rustSmallProbeRead_ok` with `hreserve` (`do_reserve_and_handle`) discharged via
    `rustDoReserveAndHandle_ok`. -/
theorem rustSmallProbeRead_ok' {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {P : Program} {fd : BitVec 64} {reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : 64 + 48 + Rust.hookStack ≤ reserveStack ∧ 144 + reserveStack ≤ 2 ^ 64 := by decide)
    (hread : subroutine_ok P (rustStdIoMultiLib.resolve mpl "read")
      (rustStdIoMultiLib.withCodeLoaded mpl muslRead32ClampedSpec))
    (hmemcpy : subroutine_ok P (rustStdIoMultiLib.resolve mpl "memcpy")
      (rustStdIoMultiLib.withCodeLoaded mpl stdMemcpySpec))
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr mpl smallProbeReadFileSym)
      (rustStdIoMultiLib.withCodeLoaded mpl (rustSmallProbeReadSpec A fd reserveStack)) :=
  rustSmallProbeRead_ok A hpl hext ⟨by omega, hstk.2⟩ hread hmemcpy
    (rustDoReserveAndHandle_ok A hpl hext ⟨hstk.1, by omega⟩ hshim halloc hrealloc)

end

end VerifiedLibraries.RustStd.Io
