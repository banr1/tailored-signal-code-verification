/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.DevPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseSidFsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable Binary Refinement Proof of `signal_session::address` (Block `580`)

Proves `address_blk580_ok` on `lsProg_580 H` with `withLsCodeRoLoaded lsmpl`, lifting it to any
caller block (`address_placed_ok_rocl`) and to Block `617` (`address_placed_ok`).
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (lsRetAddr624_of_lr_eq_blockPlacement_base_add subroutine_ok_withLsRet withLsRet
   withLsRet_withLsRoCl)
open Address.Helpers

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem bv_ult_of_lt_p {i n : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 n) = true ∧
      (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hi hn), Nat.mod_eq_of_lt hn]
  exact ⟨decide_eq_true hi, decide_eq_false (by omega)⟩

set_option maxHeartbeats 800000 in
private theorem address_wp_gen_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (memrchrSpec extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (x : AddressCall) (s0 : State)
    (hal0 : s0.spAligned = true)
    (hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc0 : s0.pc = (blkPl_580).base)
    (hrun0 : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.out)
    (hx1 : s0.readReg64 .x1 = x.p)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length)
    (hbs_lt64 : x.bs.length < 2 ^ 64) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s0
      ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ A.pool ∗ stackAt s0.sp resStack)
      (AddrGoalPost A resStack x s0)
      (AddrPanicAllow s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2] at hx0 hx1 hx2
  have hstkle : resStack ≤ 2 ^ 64 := Nat.le_trans hres64 (by decide)
  have hpsid' := parseSid_placed_okFs_rocl (prog := lsProg_580 H) (i := 580)
    extHookStack (by decide) (by decide)
  have hexit := @step_none_exit_placed _ A H resStack hres hstkle x
  have hdev := @step_dev_dispatch_placed _ A H resStack hCF hpan hres hstkle x
  clear hres64
  dsimp only [lsProg_580] at hmemrchr hpsid'
  rw [stackAt_addr_split s0.sp resStack hres hstkle, cells64_open s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v64 => SepWPp.exists_elim fun v56 =>
    SepWPp.exists_elim fun v48 => SepWPp.exists_elim fun v40 =>
    SepWPp.exists_elim fun v32 => SepWPp.exists_elim fun v24 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v8 => ?_
  apply sepWPp_of_sepWP_lscro (mid := lsρ lsMemrchrSym) hcrl0
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, *]; try (clear * -; bv_omega))
    (by simp only [arm64_norm, *])
  intro hcrl1
  apply bind_sepWPp_state; intro s_mr
  have hal_mr : s_mr.spAligned = true :=
    sp_sub_96_spAligned hal0 (by simp only [s_mr, arm64_norm])
  have hcs_mr : AddrUpperSaved s0 s_mr := by
    simp only [s_mr, AddrUpperSaved, arm64_norm]
  refine addr_call_rocl ⟨46#8, x.p, x.bs⟩ hmemrchr hcrl1
    (by simp only [s_mr, arm64_norm])
    (by simp only [s_mr, arm64_norm, *]; try (clear * -; bv_omega))
    (by simp only [s_mr, arm64_norm, *])
    hal_mr
    (ret_pc := (blkPl_580).base + memrchrRetOff)
    (by simp only [s_mr, memrchrRetOff, arm64_norm, *])
    (F := memRegion x.out 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
      memRegion (s0.sp - 96#64) 32 ∗
      addrSavedRegs s0.sp s0 ∗ A.pool)
    ?_
    (hnext := ?_)
  · dsimp only [withLsRet, memrchrSpec]
    unfold addrSavedRegs
    have hlr_mr : LsRetAddr624 (s_mr.readReg64 .lr) :=
      lsRetAddr624_of_lr_eq_blockPlacement_base_add 580 memrchrRetOff
        (by simp only [s_mr, memrchrRetOff, arm64_norm])
    have hpure_mr :
        ((s_mr.readReg64 .x0).setWidth 8 = 46#8 ∧ s_mr.readReg64 .x1 = x.p ∧
          s_mr.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64) = True :=
      eq_true ⟨by simp only [s_mr, arm64_norm],
        by simp only [s_mr, arm64_norm, hx1],
        by simp only [s_mr, arm64_norm, hx2],
        hbs_lt64⟩
    have hsp_mr : s_mr.sp = s0.sp - 96#64 := by simp only [s_mr, arm64_norm]
    rw [eq_true hlr_mr, pure_true, emp_sepConj, hpure_mr, pure_true, emp_sepConj, hsp_mr,
      stackAt_sub_hook (s0.sp - 96#64)]
    generalize subStackSize = ssz
    generalize extHookStack = hsz
    exact Entails.of_eq (by ac_rfl)
  · intro s_after_mr hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [withLsRet, memrchrSpec]
    try dsimp only [memrchrRetOff] at hpc2
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hpure2 => ?_
    rcases hpure2 with ⟨htr2, hfs2, hmr_res⟩
    have hx19_2 : s_after_mr.readReg64 (Reg.gpr 19#5) = x.out := by
      simpa only [Reg.x19] using (hcsp2.1.trans (by simp only [s_mr, arm64_norm, hx0]))
    have hx21_2 : s_after_mr.readReg64 (Reg.gpr 21#5) = x.p := by
      simpa only [Reg.x21] using (hcsp2.2.2.1.trans (by simp only [s_mr, arm64_norm, hx1]))
    have hx22_2 : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 x.bs.length := by
      simpa only [Reg.x22] using (hcsp2.2.2.2.1.trans (by simp only [s_mr, arm64_norm, hx2]))
    have hsp_mr0 : s_mr.sp = s0.sp - 96#64 := by simp only [s_mr, arm64_norm]
    have hsp2' : s_after_mr.sp = s0.sp - 96#64 := hsp2.trans hsp_mr0
    clear hsp2
    have htr2' : s_after_mr.trace = s0.trace := by
      rw [htr2]; simp only [s_mr, arm64_norm]
    have hcs2 : AddrUpperSaved s0 s_after_mr := hcs_mr.trans_calleeSaved_fs hcsp2 hfs2
    clear hfs2 htr2
    have hrepack_common :
        ((x.p ↦ₛ x.bs) ∗ stackAt s_mr.sp extHookStack ∗
          (memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
            memRegion (s0.sp - 96#64) 32 ∗
            addrSavedRegs s0.sp s0 ∗ A.pool)) ⊢
        ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
      rw [hsp_mr0]
      unfold AddrFrameCommon
      rw [stackAt_sub_hook (s0.sp - 96#64)]
      generalize subStackSize = ssz
      generalize extHookStack = hsz
      exact Entails.of_eq (by ac_rfl)
    rw [sepConj_assoc]
    refine SepWPp.weaken_pre hrepack_common ?_
    cases hmr : memrchrIdx 46#8 x.bs with
    | none =>
      rw [hmr] at hmr_res
      try dsimp only [Reg.x0] at hmr_res
      have hnone : addrParse uuidTryParse x.bs = none := by
        simp only [addrParse, (memrchrIdx_none_iff_rsplitDot x.bs).mp hmr]
      apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
      wp_steps
      apply SepWP.done
        (by simp only [noneExitOff, arm64_norm, hmr_res, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      exact hexit hnone hal0
        (by simp only [noneExitOff, arm64_norm, hmr_res, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp2'])
        (by simp only [arm64_norm, htr2'])
        (by simp only [arm64_norm, hx19_2])
        (by rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
            simp only [AddrUpperSaved, arm64_norm, *])
    | some idx =>
      rw [hmr] at hmr_res
      rcases hmr_res with ⟨hx0_mr, hx1_mr⟩
      try dsimp only [Reg.x0, Reg.x1] at hx0_mr hx1_mr
      obtain ⟨hidx_lt, _, hbs_split, hrsplit⟩ := memrchrIdx_some_props hmr
      set name := x.bs.take idx
      set dev := x.bs.drop (idx + 1)
      have hname_len : name.length = idx := List.length_take_of_le (Nat.le_of_lt hidx_lt)
      have hbs_eq : x.bs = name ++ (46#8 :: dev) := by simpa [List.append_assoc] using hbs_split
      have hname_lt : name.length < x.bs.length := hname_len ▸ hidx_lt
      have hx1_name : s_after_mr.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 name.length := by
        rw [hx1_mr, hname_len]
      have hbs_sep :
          (x.p ↦ₛ x.bs) =
            (x.p ↦ₛ name) ∗
              ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
              ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) := by
        rw [hbs_eq, pointsToBytes_append, pointsToBytes_cons]
      have hbslen_restore : ∃ bslen : Nat, bslen = x.bs.length := ⟨x.bs.length, rfl⟩
      rcases hbslen_restore with ⟨bslen, hbslen_eq⟩
      have hbslen_lt64 : bslen < 2 ^ 64 := hbslen_eq ▸ hbs_lt64
      have hname_lt' : name.length < bslen := hbslen_eq ▸ hname_lt
      have hx22_bslen : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 bslen :=
        hbslen_eq ▸ hx22_2
      obtain ⟨hname_ult, hname_ule_f⟩ := bv_ult_of_lt_p hname_lt' hbslen_lt64
      have hrestore_x22 : ∀ r : BitVec 64, r = BitVec.ofNat 64 bslen → r = BitVec.ofNat 64 x.bs.length :=
        fun _ hr => hr.trans (congrArg (BitVec.ofNat 64) hbslen_eq)
      clear hbslen_eq hx22_2 hname_len hx1_mr hidx_lt hbs_split hname_lt
      rw [hbs_sep]
      unfold AddrFrameCommon
      rw [scratch32_split_17 (s0.sp - 96#64)]
      simp only [sepConj_assoc]
      apply sepWPp_of_sepWP_lscro (mid := lsmpl.base 206) hcrl2
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, hx0_mr, hx1_name, hx22_bslen, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      intro hcrl3
      have hx22_2 : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 x.bs.length :=
        hrestore_x22 _ hx22_bslen
      apply bind_sepWPp_state; intro s_ps
      have hal_ps : s_ps.spAligned = true :=
        sp_sub_96_spAligned hal0 (by simp only [s_ps, arm64_norm, hsp2'])
      have hcs_ps : AddrUpperSaved s0 s_ps := by
        rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
        simp only [s_ps, AddrUpperSaved, arm64_norm, *]; try rfl
      have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine addr_call_rocl (x.p, name, (s0.sp - 96#64) + 12#64) hpsid' hcrl3
        (by simp only [s_ps, arm64_norm, htr2'])
        (by simp only [s_ps, arm64_norm, *]; try (clear * -; bv_omega))
        (by simp only [s_ps, arm64_norm, *])
        hal_ps
        (ret_pc := (blkPl_580).base + parseSidRetOff)
        (by simp only [s_ps, parseSidRetOff, arm64_norm, *])
        (F := ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          memRegion (s0.sp - 96#64) 12 ∗
          memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
          addrSavedRegs s0.sp s0 ∗ A.pool)
        ?_
        (hnext := ?_)
      · dsimp only [Spec.keepsFs, parseSidCodeStackSpec, parseSidSpec]
        have hpure_ps :
            (s_ps.readReg64 .x0 = x.p ∧ (s_ps.readReg64 .x1).toNat = name.length ∧
              s_ps.readReg64 .x8 = (s0.sp - 96#64) + 12#64) = True :=
          eq_true ⟨by simp only [s_ps, arm64_norm, hx21_2],
            by simp only [s_ps, arm64_norm, hx1_name, hname_toNat],
            by simp only [s_ps, arm64_norm, hsp2']⟩
        have hsp_ps : s_ps.sp = s0.sp - 96#64 := by simp only [s_ps, arm64_norm, hsp2']
        rw [hpure_ps, pure_true, emp_sepConj, hsp_ps, stackAt_sub_parseSid (s0.sp - 96#64)]
        generalize parseSidFrameStack = pf
        generalize extHookStack = hsz
        exact Entails.of_eq (by ac_rfl)
      · intro s_after_ps hcrl4 hpc4 hrun4 hsp4 hcsp4
        dsimp only [Spec.keepsFs, parseSidCodeStackSpec, parseSidSpec]
        try dsimp only [parseSidRetOff] at hpc4
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun hfs4 => ?_
        refine SepWPp.pure_elim fun htr4 => ?_
        have hx19_4 : s_after_ps.readReg64 .x19 = x.out := by
          rw [hcsp4.1]; simp only [s_ps, arm64_norm, hx19_2]
        have hx20_4 : s_after_ps.readReg64 .x20 = BitVec.ofNat 64 name.length := by
          rw [hcsp4.2.1]; simp only [s_ps, arm64_norm, hx1_name]
        have hx21_4 : s_after_ps.readReg64 .x21 = x.p := by
          rw [hcsp4.2.2.1]; simp only [s_ps, arm64_norm, hx21_2]
        have hx22_4 : s_after_ps.readReg64 .x22 = BitVec.ofNat 64 x.bs.length := by
          rw [hcsp4.2.2.2.1]; simp only [s_ps, arm64_norm, hx22_2]
        have hsp_ps0 : s_ps.sp = s0.sp - 96#64 := by simp only [s_ps, arm64_norm, hsp2']
        have hsp4' : s_after_ps.sp = s0.sp - 96#64 := hsp4.trans hsp_ps0
        clear hsp4
        have htr4' : s_after_ps.trace = s0.trace := by
          rw [htr4]; simp only [s_ps, arm64_norm, htr2']
        have hcs4 : AddrUpperSaved s0 s_after_ps := hcs_ps.trans_calleeSaved_fs hcsp4 hfs4
        clear hfs4 htr4
        have hstk_ps :
            ∀ R : SepProp,
              stackAt (s0.sp - 96#64 - 80#64) extHookStack ∗
                (stackAt (s0.sp - 96#64) parseSidFrameStack ∗ R) =
              stackAt (s0.sp - 96#64) subStackSize ∗ R := by
          intro R; rw [← sepConj_assoc, ← stackAt_sub_parseSid (s0.sp - 96#64)]
        rw [hsp_ps0, hstk_ps]
        exact hdev name dev hbs_eq hbs_lt64 hrsplit
          hal0 hcrl4 hpc4 hrun4 hsp4' htr4' hx19_4 hx20_4 hx21_4 hx22_4 hcs4

/-- `signal_session::address` (Block `580`) satisfies
`withLsCodeRoLoaded lsmpl (addressSpec A uuidTryParse resStack)` on `lsProg_580 H` under the
`withLsRet`-narrowed `memrchr` contract. -/
theorem address_blk580_ok_ls [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (memrchrSpec extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_580 H) (lsmpl.base 580)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (addressSpec A uuidTryParse resStack)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc0 hrun0 hpre0 hal0 hL0
  have ⟨hcrl0, hpre0⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre0
  dsimp only [addressSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2⟩, hm0⟩
  have hbs_lt64 : x.bs.length < 2 ^ 64 :=
    slice_lt_addr_space (by simpa only [sepConj_assoc] using hm0)
  have hwp := address_wp_gen_placed hCF hpan hmemrchr hres hres64
    x s0 hal0 hcrl0 hpc0 hrun0 hx0 hx1 hx2 hbs_lt64
  dsimp only [lsProg_580] at hL0
  obtain ⟨sf, hsteps, hout⟩ := hwp R (by simpa only [sepConj_assoc] using hm0) hL0
  rcases hout with ⟨hpcsf, hruns, P_f, hm_f, hsp_f, hcs_f, hpost_f⟩ |
      ⟨hpan_f, P_f, hm_f, halloc_f⟩ | ⟨_, hmo⟩
  · refine ⟨sf, hsteps, Or.inl ⟨⟨hpcsf, hsp_f, hruns⟩, ⟨hsp_f, hcs_f⟩, ?_⟩⟩
    exact Satisfies.mono (sepConj_mono_left hpost_f) hm_f
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_f, halloc_f R hm_f⟩)⟩
  · exact (not_satisfies_false_sepConj hmo).elim

/-- Lift `address_blk580_ok_ls` to any caller block `prog` (`IsLsBlockProg prog i H`, `i < 619`)
with `withLsRoCl lsmpl`. -/
theorem address_placed_ok_rocl_ls [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (memrchrSpec extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) :=
  ls_subroutine_ok_rocl_of_block (callerProg := prog) (i := i) (j := 580)
    (address_blk580_ok_ls hCF hpan hmemrchr hres hres64) hi (by decide) (by decide)

/-- Block-`617` (`lsProg_617 H`) `address_placed_ok_ls` under `withLsRet (memrchrSpec extHookStack)`. -/
theorem address_placed_ok_ls [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (memrchrSpec extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) :=
  address_placed_ok_rocl_ls (prog := lsProg_617 H) (i := 617)
    hCF hpan hmemrchr hres hres64 (by decide)

/-- Legacy corollary of `address_blk580_ok_ls` over unnarrowed `memrchrSpec extHookStack`. -/
theorem address_blk580_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (memrchrSpec extHookStack)))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_580 H) (lsmpl.base 580)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (addressSpec A uuidTryParse resStack)) :=
  address_blk580_ok_ls hCF hpan
    (withLsRet_withLsRoCl lsmpl (memrchrSpec extHookStack) ▸ subroutine_ok_withLsRet hmemrchr)
    hres hres64

/-- Legacy corollary of `address_placed_ok_rocl_ls` over unnarrowed `memrchrSpec extHookStack`. -/
theorem address_placed_ok_rocl [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (memrchrSpec extHookStack)))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) :=
  address_placed_ok_rocl_ls (prog := prog) (i := i) hCF hpan
    (withLsRet_withLsRoCl lsmpl (memrchrSpec extHookStack) ▸ subroutine_ok_withLsRet hmemrchr)
    hres hres64 hi

theorem address_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (memrchrSpec extHookStack)))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidTryParse resStack)) :=
  address_placed_ok_ls hCF hpan
    (withLsRet_withLsRoCl lsmpl (memrchrSpec extHookStack) ▸ subroutine_ok_withLsRet hmemrchr)
    hres hres64

end CryptoVerification.SignalSession.Cli.MainHops
