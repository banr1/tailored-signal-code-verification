/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.DevRoPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.ParseSidRoPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Placed Budgeted Read-Only `signal_session::address` Refinement

Assembles `address_ro_blk580_ok`, `address_ro_placed_ok_rocl`, and `address_ro_placed_ok` for
`signal_session::address` (Block `580`) on read-only (`↦ᵣ`) input slices.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack parseSidFrameStack)
open CryptoVerification.SignalSession (lsMemrchrSym)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_580 blkPl_580 lsProg_580)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (AddressCall addrParse memrchrIdx)
open CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
  (AddrUpperSaved addrSavedRegs bind_sepWPp_state cells64_open memrchrIdx_none_iff_rsplitDot
   memrchrIdx_some_props memrchrRetOff noneExitOff parseSidRetOff scratch32_split_17
   sepWPp_of_sepWP_lscro sp_sub_96_spAligned stackAt_addr_split stackAt_sub_hook
   stackAt_sub_parseSid subStackSize)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved tpidrEl0_applyWriteback vmPreserved_advancePC vmPreserved_appendTrace
   vmPreserved_applyWriteback vmPreserved_refl_iff vmPreserved_setFs vmPreserved_setMem_write16
   vmPreserved_setMem_write32 vmPreserved_setMem_write64 vmPreserved_setMem_write8
   vmPreserved_setMem_writeBytes vmPreserved_setPC vmPreserved_setPState vmPreserved_setStatus
   vmPreserved_stepExclLoop vmPreserved_writeReg vmPreserved_writeReg32 vmPreserved_writeReg64
   vmPreserved_writeVReg128 vmPreserved_writeVReg32 vmPreserved_writeVReg64)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (lsRetAddr624_of_lr_eq_blockPlacement_base_add subroutine_ok_withLsRet withLsRet
   withLsRet_withLsRoCl)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoBudget (AddrGoalPostRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoPlacedBudget
  (step_none_exit_ro_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.DevRoPlacedBudget
  (step_dev_dispatch_ro_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.ParseSidRoPlacedBudget
  (parseSidCodeStackROSpec parseSidROSpec parseSid_ro_placed_vm_ok_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (addressSpecRO memrchrSpecRO sliceRO_lt_addr_space_32)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget (AddrFrameCommon)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
  (AddrPanicFalse addr_call_rocl_nopan)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_placed (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

private theorem sepWPp_lscro_vm_step [LibsignalPlacement] {P : Program} {b mid ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp} {post Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧
      (LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → SepWPp (P.rebase b Hk) ret sm Pm post Qp))) :
    SepWPp (P.rebase b Hk) ret s Pre post Qp :=
  sepWPp_of_sepWP_lscro (mid := mid) hcrl (SepWP.mono hwp fun _ _ _ _ ⟨hvm, hk⟩ hcrl' => hk hcrl' hvm)

attribute [local irreducible] VmPreserved

private theorem bv_ult_of_lt_p {i n : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 n) = true ∧
      (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hi hn), Nat.mod_eq_of_lt hn]
  exact ⟨decide_eq_true hi, decide_eq_false (by omega)⟩

set_option maxHeartbeats 800000 in
private theorem address_ro_wp_gen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {resStack : Nat} (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (withVmPreserved (memrchrSpecRO extHookStack)))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (x : AddressCall) (hfit : FitsEnv M lim st (AddressEnv uuidTryParse x))
    (s0 : State) (hal0 : s0.spAligned = true) (hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc0 : s0.pc = (blkPl_580).base) (hrun0 : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.out) (hx1 : s0.readReg64 .x1 = x.p)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length) (hbs_lt64 : x.bs.length < 2 ^ 64) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s0
      ((x.p ↦ᵣ x.bs) ∗ memRegion x.out 32 ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack)
      (AddrGoalPostRO A lim resStack x st s0) AddrPanicFalse := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2] at hx0 hx1 hx2
  have hstkle : resStack ≤ 2 ^ 64 := Nat.le_trans hres64 (by decide)
  have hpsid' := parseSid_ro_placed_vm_ok_rocl (prog := lsProg_580 H) (i := 580)
    extHookStack (by decide) (by decide)
  have hexit := @step_none_exit_ro_placed _ M A lim st H resStack hres hstkle x
  have hdev := @step_dev_dispatch_ro_placed _ M A lim st H resStack hFs hres hstkle x hfit
  clear hres64; dsimp only [lsProg_580] at hmemrchr hpsid'
  rw [stackAt_addr_split s0.sp resStack hres hstkle, cells64_open s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v64 => SepWPp.exists_elim fun v56 =>
    SepWPp.exists_elim fun v48 => SepWPp.exists_elim fun v40 =>
    SepWPp.exists_elim fun v32 => SepWPp.exists_elim fun v24 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v8 => ?_
  apply sepWPp_lscro_vm_step (mid := lsρ lsMemrchrSym) hcrl0
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm], fun hcrl1 hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved hvm1]
    apply bind_sepWPp_state; intro s_mr
    have hal_mr : s_mr.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_mr, arm64_norm])
    have hcs_mr : AddrUpperSaved s0 s_mr := by simp only [s_mr, AddrUpperSaved, arm64_norm]
    refine addr_call_rocl_nopan ⟨46#8, x.p, x.bs⟩ hmemrchr hcrl1
      (by simp only [s_mr, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [s_mr, arm64_norm, *]) hal_mr
      (ret_pc := (blkPl_580).base + memrchrRetOff) (by simp only [s_mr, memrchrRetOff, arm64_norm, *])
      (F := memRegion x.out 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
        memRegion (s0.sp - 96#64) 32 ∗ addrSavedRegs s0.sp s0 ∗ A.pool lim st s_mr) ?_ (hnext := ?_)
    · dsimp only [withLsRet, withVmPreserved, memrchrSpecRO]; unfold addrSavedRegs
      have hlr_mr : LsRetAddr624 (s_mr.readReg64 .lr) :=
        lsRetAddr624_of_lr_eq_blockPlacement_base_add 580 memrchrRetOff
          (by simp only [s_mr, memrchrRetOff, arm64_norm])
      have hpure_mr :
          ((s_mr.readReg64 .x0).setWidth 8 = 46#8 ∧ s_mr.readReg64 .x1 = x.p ∧
            s_mr.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64) = True :=
        eq_true ⟨by simp only [s_mr, arm64_norm], by simp only [s_mr, arm64_norm, hx1],
          by simp only [s_mr, arm64_norm, hx2], hbs_lt64⟩
      have hsp_mr : s_mr.sp = s0.sp - 96#64 := by simp only [s_mr, arm64_norm]
      rw [eq_true hlr_mr, pure_true, emp_sepConj, hpure_mr, pure_true, emp_sepConj, hsp_mr,
        stackAt_sub_hook (s0.sp - 96#64)]
      generalize subStackSize = ssz; generalize extHookStack = hsz
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after_mr hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [withLsRet, withVmPreserved, memrchrSpecRO]
      try dsimp only [memrchrRetOff] at hpc2
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun hvm_mr => SepWPp.pure_elim fun ⟨htr2, hfs2, hmr_res⟩ => ?_
      rw [← A.pool_of_vmPreserved hvm_mr]
      have hx19_2 : s_after_mr.readReg64 (Reg.gpr 19#5) = x.out := by
        simpa only [Reg.x19] using (hcsp2.1.trans (by simp only [s_mr, arm64_norm, hx0]))
      have hx21_2 : s_after_mr.readReg64 (Reg.gpr 21#5) = x.p := by
        simpa only [Reg.x21] using (hcsp2.2.2.1.trans (by simp only [s_mr, arm64_norm, hx1]))
      have hx22_2 : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 x.bs.length := by
        simpa only [Reg.x22] using (hcsp2.2.2.2.1.trans (by simp only [s_mr, arm64_norm, hx2]))
      have hsp_mr0 : s_mr.sp = s0.sp - 96#64 := by simp only [s_mr, arm64_norm]
      have hsp2' : s_after_mr.sp = s0.sp - 96#64 := hsp2.trans hsp_mr0; clear hsp2
      have htr2' : s_after_mr.trace = s0.trace := by rw [htr2]; simp only [s_mr, arm64_norm]
      have hcs2 : AddrUpperSaved s0 s_after_mr := hcs_mr.trans_calleeSaved_fs hcsp2 hfs2
      clear hfs2 htr2
      have hrepack_common :
          ((x.p ↦ᵣ x.bs) ∗ stackAt s_mr.sp extHookStack ∗ memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
            memRegion (s0.sp - 96#64) 32 ∗ addrSavedRegs s0.sp s0 ∗ A.pool lim st s_after_mr) ⊢
          ((x.p ↦ᵣ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s_after_mr) := by
        rw [hsp_mr0]; unfold AddrFrameCommon; rw [stackAt_sub_hook (s0.sp - 96#64)]
        generalize subStackSize = ssz; generalize extHookStack = hsz
        generalize addrSavedRegs s0.sp s0 = asr; exact Entails.of_eq (by sep_ac_rfl)
      refine SepWPp.weaken_pre hrepack_common ?_
      cases hmr : memrchrIdx 46#8 x.bs with
      | none =>
        rw [hmr] at hmr_res; try dsimp only [Reg.x0] at hmr_res
        have hnone : addrParse uuidTryParse x.bs = none := by
          simp only [addrParse, (memrchrIdx_none_iff_rsplitDot x.bs).mp hmr]
        apply sepWPp_lscro_vm_step (mid := (blkPl_580).base + noneExitOff) hcrl2
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [noneExitOff, arm64_norm, hmr_res, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm], fun _hcrl_exit hvm_exit => ?_⟩
          apply bind_sepWPp_state; intro s_ex
          rw [show AddrFrameCommon A lim resStack st s0 s_after_mr = AddrFrameCommon A lim resStack st s0 s_ex by
            unfold AddrFrameCommon; dsimp only [s_ex]; rw [A.pool_of_vmPreserved hvm_exit]]
          exact hexit hnone hal0
            (by simp only [s_ex, noneExitOff, arm64_norm, hmr_res, *]; try (clear * -; bv_omega))
            (by simp only [s_ex, arm64_norm, *]) (by simp only [s_ex, arm64_norm, hsp2'])
            (by simp only [s_ex, arm64_norm, htr2']) (by simp only [s_ex, arm64_norm, hx19_2])
            (by rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
                simp only [s_ex, AddrUpperSaved, arm64_norm, *]; try rfl)
      | some idx =>
        rw [hmr] at hmr_res; rcases hmr_res with ⟨hx0_mr, hx1_mr⟩
        try dsimp only [Reg.x0, Reg.x1] at hx0_mr hx1_mr
        obtain ⟨hidx_lt, _, hbs_split, hrsplit⟩ := memrchrIdx_some_props hmr
        set name := x.bs.take idx; set dev := x.bs.drop (idx + 1)
        have hname_len : name.length = idx := List.length_take_of_le (Nat.le_of_lt hidx_lt)
        have hbs_eq : x.bs = name ++ (46#8 :: dev) := by simpa [List.append_assoc] using hbs_split
        have hname_lt : name.length < x.bs.length := hname_len ▸ hidx_lt
        have hx1_name : s_after_mr.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 name.length := by rw [hx1_mr, hname_len]
        have hbs_sep : (x.p ↦ᵣ x.bs) = (x.p ↦ᵣ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦₈ᵣ 46#8) ∗
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ᵣ dev) := by
          rw [hbs_eq, pointsToBytesRO_append, pointsToBytesRO_cons]
        rcases (⟨x.bs.length, rfl⟩ : ∃ bslen : Nat, bslen = x.bs.length) with ⟨bslen, hbslen_eq⟩
        have hbslen_lt64 : bslen < 2 ^ 64 := hbslen_eq ▸ hbs_lt64
        have hname_lt' : name.length < bslen := hbslen_eq ▸ hname_lt
        have hx22_bslen : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 bslen := hbslen_eq ▸ hx22_2
        obtain ⟨hname_ult, hname_ule_f⟩ := bv_ult_of_lt_p hname_lt' hbslen_lt64
        have hrestore_x22 : ∀ r : BitVec 64, r = BitVec.ofNat 64 bslen → r = BitVec.ofNat 64 x.bs.length :=
          fun _ hr => hr.trans (congrArg (BitVec.ofNat 64) hbslen_eq)
        clear hbslen_eq hx22_2 hname_len hx1_mr hidx_lt hbs_split hname_lt
        rw [hbs_sep]; unfold AddrFrameCommon; rw [scratch32_split_17 (s0.sp - 96#64)]; simp only [sepConj_assoc]
        apply sepWPp_lscro_vm_step (mid := lsmpl.base 206) hcrl2
        by_vm_steps
          wp_steps
          refine SepWP.done
            (by simp only [arm64_norm, hx0_mr, hx1_name, hx22_bslen, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm], fun hcrl3 hvm3 => ?_⟩
          rw [← A.pool_of_vmPreserved hvm3]
          have hx22_2 : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 x.bs.length := hrestore_x22 _ hx22_bslen
          apply bind_sepWPp_state; intro s_ps
          have hal_ps : s_ps.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_ps, arm64_norm, hsp2'])
          have hcs_ps : AddrUpperSaved s0 s_ps := by
            rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
            simp only [s_ps, AddrUpperSaved, arm64_norm, *]; try rfl
          have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          refine addr_call_rocl_nopan (x.p, name, (s0.sp - 96#64) + 12#64) hpsid' hcrl3
            (by simp only [s_ps, arm64_norm, *]; try (clear * -; bv_omega))
            (by simp only [s_ps, arm64_norm, *]) hal_ps
            (ret_pc := (blkPl_580).base + parseSidRetOff) (by simp only [s_ps, parseSidRetOff, arm64_norm, *])
            (F := ((x.p + BitVec.ofNat 64 name.length) ↦₈ᵣ 46#8) ∗
              ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ᵣ dev) ∗ memRegion x.out 32 ∗
              memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
              memRegion (s0.sp - 96#64) 12 ∗ memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
              addrSavedRegs s0.sp s0 ∗ A.pool lim st s_ps) ?_ (hnext := ?_)
          · dsimp only [withVmPreserved, Spec.keepsFs, parseSidCodeStackROSpec, parseSidROSpec]
            have hpure_ps : (s_ps.readReg64 .x0 = x.p ∧ (s_ps.readReg64 .x1).toNat = name.length ∧
                s_ps.readReg64 .x8 = (s0.sp - 96#64) + 12#64) = True :=
              eq_true ⟨by simp only [s_ps, arm64_norm, hx21_2],
                by simp only [s_ps, arm64_norm, hx1_name, hname_toNat],
                by simp only [s_ps, arm64_norm, hsp2']⟩
            have hsp_ps : s_ps.sp = s0.sp - 96#64 := by simp only [s_ps, arm64_norm, hsp2']
            rw [hpure_ps, pure_true, emp_sepConj, hsp_ps, stackAt_sub_parseSid (s0.sp - 96#64)]
            generalize parseSidFrameStack = pf; generalize extHookStack = hsz
            generalize addrSavedRegs s0.sp s0 = asr; exact Entails.of_eq (by sep_ac_rfl)
          · intro s_after_ps hcrl4 hpc4 hrun4 hsp4 hcsp4
            dsimp only [withVmPreserved, Spec.keepsFs, parseSidCodeStackROSpec, parseSidROSpec]
            try dsimp only [parseSidRetOff] at hpc4
            simp only [sepConj_assoc]
            refine SepWPp.pure_elim fun hvm_ps =>
              SepWPp.pure_elim fun hfs4 => SepWPp.pure_elim fun htr4 => ?_
            rw [← A.pool_of_vmPreserved hvm_ps]
            have hx19_4 : s_after_ps.readReg64 .x19 = x.out := by rw [hcsp4.1]; simp only [s_ps, arm64_norm, hx19_2]
            have hx20_4 : s_after_ps.readReg64 .x20 = BitVec.ofNat 64 name.length := by rw [hcsp4.2.1]; simp only [s_ps, arm64_norm, hx1_name]
            have hx21_4 : s_after_ps.readReg64 .x21 = x.p := by rw [hcsp4.2.2.1]; simp only [s_ps, arm64_norm, hx21_2]
            have hx22_4 : s_after_ps.readReg64 .x22 = BitVec.ofNat 64 x.bs.length := by rw [hcsp4.2.2.2.1]; simp only [s_ps, arm64_norm, hx22_2]
            have hsp_ps0 : s_ps.sp = s0.sp - 96#64 := by simp only [s_ps, arm64_norm, hsp2']
            have hsp4' : s_after_ps.sp = s0.sp - 96#64 := hsp4.trans hsp_ps0; clear hsp4
            have htr4' : s_after_ps.trace = s0.trace := by rw [htr4]; simp only [s_ps, arm64_norm, htr2']
            have hcs4 : AddrUpperSaved s0 s_after_ps := hcs_ps.trans_calleeSaved_fs hcsp4 hfs4
            clear hfs4 htr4
            have hstk_ps : ∀ R : SepProp, stackAt (s0.sp - 96#64 - 80#64) extHookStack ∗
                (stackAt (s0.sp - 96#64) parseSidFrameStack ∗ R) =
                stackAt (s0.sp - 96#64) subStackSize ∗ R := by
              intro R; rw [← sepConj_assoc, ← stackAt_sub_parseSid (s0.sp - 96#64)]
            rw [hsp_ps0, hstk_ps]
            exact hdev name dev hbs_eq hbs_lt64 hrsplit
              hal0 hcrl4 hpc4 hrun4 hsp4' htr4' hx19_4 hx20_4 hx21_4 hx22_4 hcs4

/-- `signal_session::address` (Block `580`) satisfies
`withLsCodeRoLoaded lsmpl (addressSpecRO A lim uuidTryParse resStack)` on `lsProg_580 H` under the
`withLsRet`-narrowed `memrchrSpecRO` contract. -/
theorem address_ro_blk580_ok_ls [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (withVmPreserved (memrchrSpecRO extHookStack)))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_580 H) (lsmpl.base 580)
      (withLsCodeRoLoaded lsmpl (addressSpecRO A lim uuidTryParse resStack)) := by
  apply subroutine_ok_of_sepWPp_init; intro ⟨x, st⟩ R s0 hpc0 hrun0 hpre0 hal0
  have ⟨hcrl0, hpre_spec⟩ := extract_withLsCodeRoLoaded hpre0
  dsimp only [addressSpecRO] at hpre_spec; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_spec
  rcases hpre_spec with ⟨⟨hx0, hx1, hx2, hfit⟩, hm0⟩
  have hbs_lt64 : x.bs.length < 2 ^ 64 :=
    sliceRO_lt_addr_space_32 (by simpa only [sepConj_assoc] using hm0)
  have hwp := address_ro_wp_gen_placed hFs hmemrchr hres hres64 x hfit s0 hal0 hcrl0 hpc0 hrun0 hx0 hx1 hx2 hbs_lt64
  refine ⟨_, hm0, fun Fr hm hL => ?_⟩
  obtain ⟨sf, hsteps, ⟨hpcsf, hruns, P_f, hmf, hsp_f, hcs_f, hpost_f⟩ | ⟨_, P_f, hmf, hqp⟩ | hoom⟩ := hwp Fr hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpcsf, hruns, P_f, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hpost_f) hmR, hsp_f, hcs_f⟩⟩
  · exact False.elim (hqp Fr hmf)
  · exact False.elim (not_satisfies_false_sepConj hoom.2)

/-- Lift `address_ro_blk580_ok_ls` to any caller block `prog` (`IsLsBlockProg prog i H`, `i < 619`)
with `withLsRoCl lsmpl`. -/
theorem address_ro_placed_ok_rocl_ls [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (withVmPreserved (memrchrSpecRO extHookStack)))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  ls_subroutine_ok_rocl_of_block (callerProg := prog) (i := i) (j := 580)
    (address_ro_blk580_ok_ls hFs hmemrchr hres hres64) hi (by decide) (by decide)

/-- Block-`617` (`lsProg_617 H`) `address_ro_placed_ok_ls` under `withLsRet`. -/
theorem address_ro_placed_ok_ls [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withLsRet (withVmPreserved (memrchrSpecRO extHookStack)))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_rocl_ls (prog := lsProg_617 H) (i := 617)
    hFs hmemrchr hres hres64 (by decide)

/-- Legacy corollary of `address_ro_blk580_ok_ls` over unnarrowed `memrchrSpecRO extHookStack`. -/
theorem address_ro_blk580_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_580 H) (lsmpl.base 580)
      (withLsCodeRoLoaded lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_blk580_ok_ls hFs
    (withLsRet_withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO extHookStack)) ▸
      subroutine_ok_withLsRet hmemrchr)
    hres hres64

/-- Legacy corollary of `address_ro_placed_ok_rocl_ls` over unnarrowed `memrchrSpecRO extHookStack`. -/
theorem address_ro_placed_ok_rocl [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_rocl_ls (prog := prog) (i := i) hFs
    (withLsRet_withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO extHookStack)) ▸
      subroutine_ok_withLsRet hmemrchr)
    hres hres64 hi

theorem address_ro_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hmemrchr : subroutine_ok (lsProg_580 H) (lsρ lsMemrchrSym)
      (withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_ls hFs
    (withLsRet_withLsRoCl lsmpl (withVmPreserved (memrchrSpecRO extHookStack)) ▸
      subroutine_ok_withLsRet hmemrchr)
    hres hres64

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoPlacedBudget
