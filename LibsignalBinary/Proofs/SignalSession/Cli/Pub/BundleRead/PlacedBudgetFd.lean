/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetOkFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable `read_bundle::{closure#0}` (Block `563`)

Verifies `withFdsGe3Closed (bundleReadSpecPlaced ...)` on Block `563` under `[LibsignalPlacement]`,
preserving closed file descriptors `fd ≥ 3` across `path`, `read_file`, and allocator hooks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded TraceFsSound extract_withLsCodeRoLoaded sepWPp_seq_lscro
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack sessionShimSpec withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsReadFileSym lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli
  (BundleReadGhost PathGhost ReadRule getResultAt ioVecAt subroutine_ok_withFsInv utf8
   withFsInv withFsInv_post_elim withFsInv_pre_intro)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_563 blkPC_563 blkPl_563 lsProg_563)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.BundleRead.Helpers
  (breadReadSym breadUnreadableSym err_result_intro err_slot24_pack frame_80_unpack
   path_buf_dealloc_pack rodata_read_intro_p rodata_unreadable_intro_p sret_48_unpack
   stackAt_frame_80_eq stackAt_split_sub stk_le_two_pow_64)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs RustCliAllocBudget
   rustAllocEvents rustCliAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced ReadFileRuleEnv bundleReadSpecPlaced pathSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
  (allocNoOomExtern_fs_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (hookSat_keepLr_withFds_of_withFds_keepLrAndFds lsReadFile_withLsCodeRoLoaded_of_hookSat
   ls_transfer_withFdsGe3Closed_lscro shim_keepsFs_lscro_of_fs
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed withKeepLrAndFds withLsRetAddr624AndFds
   withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
  (BundleReadAfterReadEnv BundleReadEnv BundleReadTailEnv bind_sepWP_state buf22_merge_14_8
   buf22_reassoc_14_8_rest bundleReadEnv_err_end bundleReadEnv_ok_end cs_hi_of_eq
   cs_hi_of_preserved cs_hi_trans entails_of_eq fitsEvents_22_of_afterRead_err satisfies_mono_rev
   satisfies_of_eq satisfies_vecU8_unpack sepWPp_exists_pre sepWPp_mono_pre stepEvents_append_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
  (ReadCallGuardHypPlacedFd readCall_step_p_guard_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetOkFd
  (ok_branch_step_p_fd tail_dealloc_step_p_fd)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setMem_local (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem fs_setMem_local (s : State) (m : Memory) : (s.setMem m).fs = s.fs := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem readReg64_setPState_local (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem readVReg128_setPState_local (s : State) (ps : PState) (v : BitVec 5) :
    (s.setPState ps).readVReg128 v = s.readVReg128 v := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_local (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem mem_setPState_local (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem fs_setPState_local (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem status_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem trace_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem symtab_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPState_local (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl

private theorem drop_rocl_post {α : Type} {P : Program} {e : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α} (h : subroutine_ok P e (withLsRoCl pl spec)) :
    subroutine_ok P e (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsRoCl, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2)

/-! ## `Err(())` Copy and Allocation Steps -/

set_option maxHeartbeats 800000 in
/-- `FdsGe3Closed`-preserving `Err` buffer copy block (`+128 .. +188` on Block `563`). -/
theorem err_copy_step_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H) (hstk : 0x50 + extHookStack ≤ stk) (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {st0 st_pre : M.σ} {evs_pre : List AllocEvent} {s0 s : State}
    {pathCap pathPtr buf : BitVec 64} {F : SepProp}
    (hPC : s.pc = (blkPl_563).base + 128#64) (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hAl0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfds : FdsGe3Closed s.fs)
    (hx0_s : s.readReg64 .x0 = buf) (hbuf_ne : buf ≠ 0#64)
    (hx19_s : s.readReg64 .x19 = pathPtr) (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat) (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : Except.error () = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace)
    (hst_pre : st_pre = M.stepEvents evs_pre st0)
    (hevs_end : ∀ evs_d, FreeOnlyEvs evs_d →
      BundleEnv s0.fs.files x.dir x.name (evs_pre ++ evs_d)) :
    SepWPp (lsProg_563 H) (s0.readReg64 .lr) s
      (((A.live buf 22 1 ∗ memRegion buf 22 ∗ memRegion x.ret 48 ∗
          bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ F)
      (fun sf Qp =>
        Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ F) := by
  let ptrUnr := lsρ breadUnreadableSym
  let ptrRead := lsρ breadReadSym
  have hbuf22 : memRegion buf 22 =
      (∃∗ d1 : BitVec 64, ∃∗ d0 : BitVec 64,
        (buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) := by
    have h16 : memRegion buf 16 = memRegion buf 8 ∗ memRegion (buf + 8#64) 8 :=
      memRegion_split buf 8 8 (by decide)
    rw [show (22 : Nat) = 16 + 6 from rfl, memRegion_split buf 16 6 (by decide),
        h16, ProofLib.memRegion_eight buf, ProofLib.memRegion_eight (buf + 8#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [hbuf22]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWPp_exists_pre; intro d1
  apply sepWPp_exists_pre; intro d0
  apply sepWPp_mono_pre (by
    simp only [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (sret_48_unpack x.ret))))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWPp_exists_pre; intro w5; apply sepWPp_exists_pre; intro w4
  apply sepWPp_exists_pre; intro w3; apply sepWPp_exists_pre; intro w2
  apply sepWPp_exists_pre; intro w1; apply sepWPp_exists_pre; intro w0 R hm hL
  have hm_ro := rodata_unreadable_intro_p hcrl (rodata_read_intro_p hcrl hm)
  have hm_init : s.mem ⊨
      (((ptrUnr ↦ᵣ utf8 "file could not be read") ∗ (ptrRead ↦ᵣ utf8 "read") ∗
        A.pool lim st_pre s ∗ A.live buf 22 1 ∗
        (buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6 ∗
        ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
          ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5)) ∗
        bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 24 ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F) ∗ R) := by
    refine satisfies_of_eq ?_ hm_ro; dsimp only [ptrUnr, ptrRead]
    simp only [List.length_append, List.length_cons, List.length_nil]; sep_ac_rfl
  have hbuf_be : (buf == 0#64) = false := beq_false_of_ne hbuf_ne
  have hcap_ne : pathCap ≠ 0#64 := by intro heq; subst heq; simp at hcap_pos
  have hcap_be : (pathCap == 0#64) = false := beq_false_of_ne hcap_ne
  have _ := And.intro hbuf_ne (And.intro hbuf_be (And.intro hcap_ne hcap_be))
  simp only [arm64_norm] at hx0_s hx20_s
  refine (?_ : SepWPp (lsProg_563 H) (s0.readReg64 .lr) s _ _ _) R hm_init hL
  apply sepWPp_seq_lscro hcrl (mid := (blkPl_563).base + 156#64)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_563).rebase (blkPl_563).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
    blkLib_eq_563 (mid := (blkPl_563).base + 156#64)
  intro _m_strip
  wp_steps
  have hur_len : (utf8 "file could not be read").length = 22 := by
    simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]; decide +kernel
  apply SepWP.step_ldrSimd128
    (by simp [wp_norm, arm64_norm] : _ = (blkPl_563).base + 144#64)
    (by simp [wp_norm, arm64_norm, hRun]) (by simp only [wp_norm, arm64_norm]; rfl)
    rfl (by simp [ptrUnr, wp_norm, arm64_norm] : evalAddrMode _ _ = (ptrUnr, none)) rfl
    (SepLoad64.of_pointsToBytesRO rfl (off := 0) (by omega) (by simp))
    (SepLoad64.of_pointsToBytesRO rfl (off := 8) (by omega) rfl) rfl
  apply SepWP.step_ldur64
    (by simp [wp_norm, arm64_norm] : _ = (blkPl_563).base + 148#64)
    (by simp [wp_norm, arm64_norm, hRun]) (by simp only [wp_norm, arm64_norm]; rfl)
    rfl (by simp [ptrUnr, wp_norm, arm64_norm] : evalAddrMode _ _ = (ptrUnr + 14#64, none))
    (SepLoad64.of_pointsToBytesRO rfl (off := 14) (by omega) rfl) rfl
  simp (config := { zeta := false }) only [applyWriteback, BitVec.add_assoc,
    show (144#64 : BitVec 64) + 4#64 = 148#64 from rfl,
    show (148#64 : BitVec 64) + 4#64 = 152#64 from rfl]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp [wp_norm, arm64_norm])) (hnext := ?_)
  apply bind_sepWP_state; intro s_mid1
  refine SepWP.done ?_ ?_ ?_
  · simp [s_mid1, wp_norm, arm64_norm]
  · simp [s_mid1, wp_norm, arm64_norm, hRun]
  · intro hcrl_mid1 R1 hm_mid1 hL_mid1
    have hs_mid1_sp : s_mid1.sp = s0.sp - 80#64 := by simp [s_mid1, wp_norm, arm64_norm, hsp]
    have hs_mid1_x0 : s_mid1.readReg64 .x0 = buf := by simp [s_mid1, wp_norm, arm64_norm, hx0_s]
    have hs_mid1_x9 : s_mid1.readReg64 .x9 = 9223372036854775809#64 := by
      simp [s_mid1, wp_norm, arm64_norm]
    have hs_mid1_x19 : s_mid1.readReg64 .x19 = pathPtr := by simp [s_mid1, wp_norm, arm64_norm, hx19_s]
    have hs_mid1_x20 : s_mid1.readReg64 .x20 = x.ret := by simp [s_mid1, wp_norm, arm64_norm, hx20_s]
    have hs_mid1_tr : s_mid1.trace = s.trace := by simp [s_mid1, wp_norm, arm64_norm]
    have hs_mid1_fs : s_mid1.fs = s.fs := by simp [s_mid1, wp_norm, arm64_norm]
    have hs_mid1_run : s_mid1.status = .Running := by simp [s_mid1, wp_norm, arm64_norm, hRun]
    have hs_mid1_pc : s_mid1.pc = (blkPl_563).base + 156#64 := by simp [s_mid1, wp_norm, arm64_norm]
    have hm_mid1_re : s_mid1.mem ⊨
        ((A.pool lim st_pre s_mid1 ∗ (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
          (ptrRead ↦ᵣ utf8 "read") ∗ A.live buf 22 1 ∗
          (∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ∗
          ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
            ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5)) ∗
          bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 24 ∗
          ((s0.sp - 56#64) ↦₆₄ pathCap) ∗ ((s0.sp - 48#64) ↦₆₄ pathPtr) ∗
          ((s0.sp - 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F)) ∗ R1 := by
      refine satisfies_mono_rev hm_mid1 ?_; simp only [sepConj_assoc]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (buf22_reassoc_14_8_rest buf _ _ _))))
    simp only [arm64_norm] at hs_mid1_x0 hs_mid1_x9 hs_mid1_x20
    refine (?_ : SepWPp (lsProg_563 H) (s0.readReg64 .lr) s_mid1 _ _ _) R1 hm_mid1_re hL_mid1
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWPp_exists_pre; intro d2
    apply sepWPp_seq_lscro hcrl_mid1 (mid := (blkPl_563).base + 84#64)
    wp_steps_sync_pool ((blkPl_563).base + 84#64)
    apply bind_sepWP_state; intro s_mid
    refine SepWP.done ?_ ?_ ?_
    · simp [s_mid, wp_norm, arm64_norm]
    · simp [s_mid, wp_norm, arm64_norm, hs_mid1_run]
    · intro hcrl_mid R' hm_mid hL_mid
      have herr_pack_d2 : ∀ (v2 : BitVec 64),
          (A.pool lim st_pre s_mid ∗ (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
            (ptrRead ↦ᵣ utf8 "read") ∗ A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ v2) ∗
            (x.ret ↦₆₄ speWord 1) ∗ ((x.ret + 8#64) ↦₆₄ 22#64) ∗ ((x.ret + 16#64) ↦₆₄ buf) ∗
            ((x.ret + 24#64) ↦₆₄ 22#64) ∗ ((x.ret + 32#64) ↦₆₄ ptrRead) ∗
            ((x.ret + 40#64) ↦₆₄ 4#64)) ⊢
          (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
            getResultAt A.repAlloc x.ret (.error ()) ∗ A.pool lim st_pre s_mid := by
        intro v2
        have hre :
            (A.pool lim st_pre s_mid ∗ (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
              (ptrRead ↦ᵣ utf8 "read") ∗ A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ v2) ∗
              (x.ret ↦₆₄ speWord 1) ∗ ((x.ret + 8#64) ↦₆₄ 22#64) ∗ ((x.ret + 16#64) ↦₆₄ buf) ∗
              ((x.ret + 24#64) ↦₆₄ 22#64) ∗ ((x.ret + 32#64) ↦₆₄ ptrRead) ∗
              ((x.ret + 40#64) ↦₆₄ 4#64)) =
            (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
              ((x.ret ↦₆₄ speWord 1) ∗
                (((x.ret + 8#64) ↦₆₄ 22#64) ∗ ((x.ret + 16#64) ↦₆₄ buf) ∗
                  ((x.ret + 24#64) ↦₆₄ 22#64) ∗ A.repAlloc.live buf 22 1 ∗
                  (memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ v2))) ∗
                (((x.ret + 32#64) ↦₆₄ ptrRead) ∗ ((x.ret + 40#64) ↦₆₄ 4#64) ∗
                  (ptrRead ↦ᵣ utf8 "read"))) ∗ A.pool lim st_pre s_mid := by
          dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
        rw [hre]
        exact sepConj_mono_right (sepConj_mono_left (Entails.trans
          (sepConj_mono_right (sepConj_mono_left
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (buf22_merge_14_8 buf v2)))))))
          (err_result_intro A.repAlloc x.ret buf ptrRead hbuf_ne)))
      have hm_dropped : s_mid.mem ⊨
          ((getResultAt A.repAlloc x.ret (.error ()) ∗
            bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
            A.pool lim st_pre s_mid) ∗ F) ∗ R' := by
        have hm_step : s_mid.mem ⊨ (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
            (((getResultAt A.repAlloc x.ret (.error ()) ∗ A.pool lim st_pre s_mid ∗
              bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 24 ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat) ∗ F) ∗ R') :=
          satisfies_mono_rev hm_mid (by
            dsimp only [ptrUnr, ptrRead] at *
            simpa [s_mid, wp_norm, arm64_norm, speWord, sepConj_assoc] using
              sepConj_mono_left (Q := (bytesAt x.dirRo x.dirA x.dir ∗
                bytesAt x.nameRo x.nameA x.name ∗ stackAt (s0.sp - 80#64) (stk - 80) ∗
                memRegion (s0.sp - 80#64) 24 ∗
                (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F) ∗ R')
                (herr_pack_d2 _))
        refine satisfies_of_eq ?_ (Satisfies.of_sep_right hm_step); sep_ac_rfl
      have htr_mid : s_mid.trace = s.trace :=
        (by simp [s_mid, wp_norm, arm64_norm] : s_mid.trace = s_mid1.trace).trans hs_mid1_tr
      have hfds_mid : FdsGe3Closed s_mid.fs := by
        have hfs_m : s_mid.fs = s_mid1.fs := by simp [s_mid, wp_norm, arm64_norm]
        rw [hfs_m, hs_mid1_fs]; exact hfds
      exact
        (tail_dealloc_step_p_fd hFs hstk hstk_le
          (by simp [s_mid, s_mid1, wp_norm, arm64_norm])
          (by simp [s_mid, wp_norm, arm64_norm, hs_mid1_run])
          (by simp [s_mid, wp_norm, arm64_norm, hs_mid1_sp])
          hAl0 hcrl_mid hfds_mid
          (by simp [s_mid, wp_norm, arm64_norm, hs_mid1_x19])
          (by simp [s_mid, wp_norm, arm64_norm]) hcap_pos hcap_lt
          (cs_hi_trans
            (cs_hi_of_eq
              (by simp [s_mid, s_mid1, wp_norm, arm64_norm]) (by simp [s_mid, s_mid1, wp_norm, arm64_norm])
              (by simp [s_mid, s_mid1, wp_norm, arm64_norm]) (by simp [s_mid, s_mid1, wp_norm, arm64_norm])
              (by simp [s_mid, s_mid1, wp_norm, arm64_norm]) (by simp [s_mid, s_mid1, wp_norm, arm64_norm])
              (by simp [s_mid, s_mid1, wp_norm, arm64_norm]) (by simp [s_mid, s_mid1, wp_norm, arm64_norm]))
            hcs_hi)
          ((by simp [s_mid, s_mid1, calleeSavedVRegs, wp_norm, arm64_norm] :
            calleeSavedVRegs s_mid = calleeSavedVRegs s).trans hvregs)
          ⟨hr_out.1, htr_mid.trans hr_out.2⟩ hst_pre hevs_end)
        R' hm_dropped hL_mid

/-- `FdsGe3Closed`-preserving `Err(())` branch from `+44` on Block `563`. -/
theorem err_branch_step_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H) (hstk : 0x50 + extHookStack ≤ stk) (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {st0 st2 : M.σ} {evs_pr : List AllocEvent} {s0 s : State}
    {pathCap pathPtr : BitVec 64} {F : SepProp}
    (hPC : s.pc = (blkPl_563).base + 44#64) (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hAl0 : s0.spAligned = true) (hAl : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfds : FdsGe3Closed s.fs)
    (hx19_s : s.readReg64 .x19 = pathPtr) (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat) (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : Except.error () = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace)
    (hst2 : st2 = M.stepEvents evs_pr st0)
    (hfit22 : FitsEvents M lim st2 (rustAllocEvents 22 1))
    (hevs_err : ∀ evs_d, FreeOnlyEvs evs_d →
      BundleEnv s0.fs.files x.dir x.name ((evs_pr ++ rustAllocEvents 22 1) ++ evs_d)) :
    SepWPp (lsProg_563 H) (s0.readReg64 .lr) s
      (((ioVecAt A.repAlloc (s0.sp - 80#64) (.error ()) ∗ memRegion x.ret 48 ∗
          bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st2 s) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ F)
      (fun sf Qp =>
        Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ F) := by
  have hshim := shim_keepsFs_lscro_of_fs (callerProg := lsProg_563 H) (i := 563) (stk := extHookStack) hFs
  have halloc := drop_rocl_post (allocNoOomExtern_fs_rocl (prog := lsProg_563 H) (i := 563) hFs)
  dsimp only [ioVecAt] at ⊢
  have hsplit_hk : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        stackAt (s0.sp - 80#64) extHookStack :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) extHookStack (by omega) (by omega)
  apply sepWPp_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
  wp_conv_pre => rw [← hsp]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp [s1, wp_norm, arm64_norm]
  · simp [s1, wp_norm, arm64_norm, hRun]
  · intro hcrl1 R hm1 hL1
    have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, wp_norm, arm64_norm, hsp]
    have htr1 : s1.trace = s.trace := by simp [s1, wp_norm, arm64_norm]
    have hfs1 : s1.fs = s.fs := by simp [s1, wp_norm, arm64_norm]
    let frameShim : SepProp :=
      memRegion (s0.sp - 80#64) 24 ∗ memRegion x.ret 48 ∗
        bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
        memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool lim st2 s1 ∗ F
    have hm1_shim : s1.mem ⊨ stackAt s1.sp extHookStack ∗ frameShim ∗ R := by
      rw [hsp1]
      have hpack24 := err_slot24_pack (s0.sp - 80#64)
      have hm1' : s1.mem ⊨
          (((s0.sp - 80#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion ((s0.sp - 80#64) + 8#64) 16) ∗
            (stackAt (s0.sp - 80#64) (stk - 80) ∗
              (memRegion x.ret 48 ∗ bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
                A.pool lim st2 s1 ∗ F ∗ R)) := by
        rw [hsp] at hm1; refine satisfies_of_eq ?_ hm1; dsimp only [s1]; sep_ac_rfl
      have hm1'' := Satisfies.mono (sepConj_mono_left hpack24) hm1'
      rw [hsplit_hk] at hm1''; refine satisfies_of_eq ?_ hm1''; dsimp only [frameShim]; sep_ac_rfl
    obtain ⟨s2, hsteps_shim, hout_shim, -⟩ :=
      hshim.no_fault_before_outcome () (frameShim ∗ R) s1
        (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm, hRun])
        (satisfies_lscro_pre hcrl1 (by
          dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec, sessionShimSpec]
          rw [emp_sepConj]; simpa [sepConj_assoc] using hm1_shim))
        (by simpa [State.spAligned, hsp1, ← hsp] using hAl) hL1
    rcases hout_shim with ⟨⟨hpcs2, _, hruns2⟩, ⟨hsps2, hcss2⟩, hpost_shim⟩ | ⟨_, hpost_shim⟩ |
        ⟨_, _, hpost_shim⟩ | ⟨_, hpost_shim⟩
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec,
          sessionShimSpec] at hpost_shim
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost_shim
      obtain ⟨hfs2, hvm_shim, htr2, hm2⟩ := hpost_shim
      have hsp2 : s2.sp = s0.sp - 80#64 := hsps2.trans hsp1
      have hcrl2 : LibsignalCodeRoLoaded lsmpl s2.mem := hcrl1.of_keepsFrozen hsteps_shim.keepsFrozen
      have hL2 := hsteps_shim.codeLoaded hL1
      have hpcs2' : s2.pc = (blkPl_563).base + 116#64 :=
        hpcs2.trans (by simp [s1, wp_norm, arm64_norm])
      clear hpcs2
      have hwp_alloc :
          SepWPp (lsProg_563 H) (s0.readReg64 .lr) s2
            ((stackAt (s0.sp - 80#64) extHookStack ∗ A.pool lim st2 s2) ∗
              (memRegion (s0.sp - 80#64) 24 ∗ memRegion x.ret 48 ∗
                bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
                (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F))
            (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
              Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ F)
            (fun sf Qp =>
              Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ F) := by
        apply sepWPp_seq_lscro hcrl2 (mid := lsρ lsRustAllocSymCli)
        wp_steps_sync_pool (lsρ lsRustAllocSymCli)
        apply bind_sepWP_state; intro s3
        refine SepWP.done ?_ ?_ ?_
        · simp [s3, wp_norm, arm64_norm]
        · simp [s3, wp_norm, arm64_norm, hruns2]
        · intro hcrl3 R3 hm3 hL3
          let restAlloc : SepProp :=
            memRegion (s0.sp - 80#64) 24 ∗ memRegion x.ret 48 ∗
              bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
              memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F
          have hsp3 : s3.sp = s0.sp - 80#64 := by simp [s3, wp_norm, arm64_norm, hsp2]
          have hfs3 : s3.fs = s2.fs := by simp [s3, wp_norm, arm64_norm]
          obtain ⟨s4, hsteps_al, hout_al, -⟩ :=
            halloc.no_fault_before_outcome (22, 1, st2) (restAlloc ∗ R3) s3
              (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm, hruns2])
              (satisfies_lscro_pre hcrl3 (by
                dsimp only [Spec.keepsFs, rustAllocNoOomExternSpecWithStack,
                  LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
                  rustCliAllocNoOomExternSpecWithStack,
                  LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack]
                rw [sepConj_assoc, satisfies_pure_sepConj]
                refine ⟨⟨by simp [s3, wp_norm, arm64_norm], by simp [s3, wp_norm, arm64_norm],
                   ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩, hfit22,
                   ⟨563, by decide, 128, by decide, by simp only [s3, wp_norm, arm64_norm]; rfl⟩⟩, ?_⟩
                rw [hsp3]; refine satisfies_of_eq ?_ hm3
                dsimp only [s3, restAlloc]; simp only [arm64_norm]))
              (by simpa [State.spAligned, hsp3, ← hsp] using hAl) hL3
          rcases hout_al with ⟨⟨hpcs4, _, hruns4⟩, ⟨hsps4, hcss4⟩, hpost_al⟩ | ⟨_, hpost_al⟩ |
              ⟨_, _, hpost_al⟩ | ⟨_, hpost_al⟩
          · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocNoOomExternSpecWithStack,
                LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
                rustCliAllocNoOomExternSpecWithStack] at hpost_al
            simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpost_al
            obtain ⟨hfs4, ⟨htr4_pure, hnull, _hmod⟩, hmem4⟩ := hpost_al
            have hpcs4' : s4.pc = (blkPl_563).base + 128#64 :=
              hpcs4.trans (by simp [s3, wp_norm, arm64_norm])
            have hsp4 : s4.sp = s0.sp - 80#64 := hsps4.trans hsp3
            have hcrl4 : LibsignalCodeRoLoaded lsmpl s4.mem := hcrl3.of_keepsFrozen hsteps_al.keepsFrozen
            have hL4 := hsteps_al.codeLoaded hL3
            have hfds4 : FdsGe3Closed s4.fs := by rw [hfs4, hfs3, hfs2, hfs1]; exact hfds
            have hx19_4 : s4.readReg64 .x19 = pathPtr :=
              hcss4.1.trans ((by simp [s3, wp_norm, arm64_norm] :
                s3.readReg64 .x19 = s2.readReg64 .x19).trans
                (hcss2.1.trans ((by simp [s1, wp_norm, arm64_norm] :
                  s1.readReg64 .x19 = s.readReg64 .x19).trans hx19_s)))
            have hx20_4 : s4.readReg64 .x20 = x.ret :=
              hcss4.2.1.trans ((by simp [s3, wp_norm, arm64_norm] :
                s3.readReg64 .x20 = s2.readReg64 .x20).trans
                (hcss2.2.1.trans ((by simp [s1, wp_norm, arm64_norm] :
                  s1.readReg64 .x20 = s.readReg64 .x20).trans hx20_s)))
            have hcs_hi4 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
                s4.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩) :=
              cs_hi_trans (cs_hi_of_preserved hcss4)
                (cs_hi_trans
                  (cs_hi_of_eq
                    (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm])
                    (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm])
                    (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm])
                    (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm]))
                  (cs_hi_trans (cs_hi_of_preserved hcss2)
                    (cs_hi_trans
                      (cs_hi_of_eq
                        (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                        (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                        (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                        (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm]))
                      hcs_hi)))
            have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
              unfold CalleeSavedPreserved at hcss4 hcss2
              exact hcss4.2.2.2.2.2.2.2.2.2.2.2.trans
                ((by simp [s3, wp_norm, arm64_norm] : calleeSavedVRegs s3 = calleeSavedVRegs s2).trans
                  (hcss2.2.2.2.2.2.2.2.2.2.2.2.trans
                    ((by simp [s1, wp_norm, arm64_norm] : calleeSavedVRegs s1 = calleeSavedVRegs s).trans hvregs)))
            have htr3_eq : s3.trace = s.trace :=
              (by simp [s3, wp_norm, arm64_norm] : s3.trace = s2.trace).trans (htr2.trans htr1)
            have htr4_s : s4.trace = s.trace := htr4_pure.trans htr3_eq
            let st3 := M.stepEvents (rustAllocEvents 22 1) st2
            have hst3 : st3 = M.stepEvents (evs_pr ++ rustAllocEvents 22 1) st0 := by
              dsimp only [st3]; rw [hst2]; exact stepEvents_append_eq evs_pr (rustAllocEvents 22 1) st0
            have hm4_packed : s4.mem ⊨
                (((A.live (s4.readReg64 .x0) 22 1 ∗ memRegion (s4.readReg64 .x0) 22 ∗
                  memRegion x.ret 48 ∗ bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                  stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 24 ∗
                  (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                  (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                  (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                  (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                  (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                  A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
                  A.pool lim st3 s4) ∗ F) ∗ R3) := by
              rw [hsp3] at hmem4
              have hm_stk : s4.mem ⊨
                  (((A.live (s4.readReg64 .x0) 22 1 ∗ memRegion (s4.readReg64 .x0) 22 ∗
                    memRegion x.ret 48 ∗ bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                    (memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
                      stackAt (s0.sp - 80#64) extHookStack) ∗
                    memRegion (s0.sp - 80#64) 24 ∗
                    (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                    (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                    (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                    (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                    (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                    (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                    A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
                    A.pool lim st3 s4) ∗ F) ∗ R3) := by
                refine satisfies_of_eq ?_ hmem4; dsimp only [restAlloc, st3]; sep_ac_rfl
              rwa [← hsplit_hk] at hm_stk
            obtain ⟨sf, hsteps_cp, hout_cp⟩ :=
              (err_copy_step_p_fd hFs hstk hstk_le hpcs4' hruns4 hsp4 hAl0 hcrl4 hfds4
                rfl hnull hx19_4 hx20_4 hcap_pos hcap_lt hcs_hi4 hv4
                ⟨hr_out.1, htr4_s.trans hr_out.2⟩ hst3 hevs_err)
                R3 hm4_packed hL4
            exact ⟨sf, hsteps_al.trans hsteps_cp, hout_cp⟩
          · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_al
            exact (not_satisfies_false_sepConj hpost_al).elim
          · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_al
            exact (not_satisfies_false_sepConj hpost_al).elim
          · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_al
            exact (not_satisfies_false_sepConj hpost_al).elim
      have hm2_for_alloc : s2.mem ⊨
          ((stackAt (s0.sp - 80#64) extHookStack ∗ A.pool lim st2 s2) ∗
            (memRegion (s0.sp - 80#64) 24 ∗ memRegion x.ret 48 ∗
              bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
              memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F)) ∗ R := by
        rw [hsp1] at hm2
        have hpool_eq : A.pool lim st2 s1 = A.pool lim st2 s2 :=
          (A.pool_of_vmPreserved (lim := lim) (st := st2) hvm_shim).symm
        refine satisfies_of_eq ?_ hm2; dsimp only [frameShim]; rw [hpool_eq]; sep_ac_rfl
      obtain ⟨sf, hsteps_rest, hout_rest⟩ := hwp_alloc R hm2_for_alloc hL2
      exact ⟨sf, hsteps_shim.trans hsteps_rest, hout_rest⟩
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_shim
      exact (not_satisfies_false_sepConj hpost_shim).elim
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_shim
      exact (not_satisfies_false_sepConj hpost_shim).elim
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_shim
      exact (not_satisfies_false_sepConj hpost_shim).elim

/-! ## Prologue and Top-Level Contracts -/

/-- Return-address-guarded `withFdsGe3Closed` contract for `read_bundle::{closure#0}` (Block `563`). -/
theorem bundleRead_placed_ok_of_guard_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {lrOk : BitVec 64 → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop} {pathStk readStk stk : Nat}
    (hpLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathStk)))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (withPreGuard (fun s => lrOk (s.readReg64 .lr))
          (withFdsGe3Closed (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))))
    (hlr : lrOk ((blkPl_563).base + 44#64))
    (hFs : TraceFsSound (lsProg_563 H))
    (hstk : 0x50 + max (max pathStk readStk) extHookStack ≤ stk) :
    subroutine_ok (lsProg_563 H) (lsmpl.base 563)
      (withFdsGe3Closed
        (bundleReadSpecPlaced rd pathOk A lim (BundleReadEnv rd PathEnv ReadEnv) stk)) := by
  have hPath563 := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed
    (ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_563 H) hPath
      (by decide) hjPath hjPath_unmut)
  have hRead563 : ReadCallGuardHypPlacedFd lrOk A lim H rd pathOk readStk ReadEnv :=
    ls_transfer_lscro (callerProg := lsProg_563 H) hRead (by decide) hjRead hjRead_unmut
  refine subroutine_ok.of_codeLoaded fun ⟨x, st0⟩ R s0 hpc0 hrun0 hpre0 hAl0 hL0 => ?_
  rw [show lsmpl.base 563 = (blkPl_563).base + 0#64 by rw [BitVec.add_zero]; rfl] at hpc0
  have hpath_le : pathStk ≤ stk - 80 := by omega
  have hread_le : readStk ≤ stk - 80 := by omega
  have hext_le : 0x50 + extHookStack ≤ stk := by omega
  obtain ⟨hfds0, hpre0⟩ := extract_withFdsGe3Closed hpre0
  obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre0
  dsimp only [bundleReadSpecPlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0_0, hx1_0, hx2_0, hx3_0, hx4_0, hdir_lt, hname_lt, hpOk, hfit0⟩, hm0⟩
  have hstk_le : stk ≤ 2 ^ 64 := stk_le_two_pow_64 (by
    have hre : ((bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ A.pool lim st0 s0) ∗ R) =
      memRegion x.ret 48 ∗ stackAt s0.sp stk ∗
        (bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗ A.pool lim st0 s0 ∗ R) := by
      sep_ac_rfl
    rwa [hre] at hm0)
  have hAl_frame : (s0.sp - 80#64) &&& 15#64 = 0#64 := by
    have hal : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hAl0
    bv_bits
  have hstk80 : stackAt s0.sp stk =
      stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 80 :=
    stackAt_frame_80_eq s0.sp stk (by omega) hstk_le
  have hsplit_path : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
        stackAt (s0.sp - 80#64) pathStk :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) pathStk hpath_le (by omega)
  let BundleEnv := BundleReadEnv rd PathEnv ReadEnv
  have hwp_all :
      SepWPp (lsProg_563 H) (s0.readReg64 .lr) s0
        ((bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ A.pool lim st0 s0) ∗ emp)
        (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ emp)
        (fun sf Qp =>
          Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ emp) := by
    rw [hstk80, hsplit_path]; simp only [sepConj_assoc]
    apply sepWPp_mono_pre (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (frame_80_unpack (s0.sp - 80#64))))))))
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWPp_exists_pre; intro v19; apply sepWPp_exists_pre; intro v20
    apply sepWPp_exists_pre; intro v30; apply sepWPp_exists_pre; intro v29
    have _ := And.intro hx0_0 (And.intro hx1_0 hx3_0)
    apply sepWPp_seq_lscro hcrl0 (mid := lsmpl.base 596)
    wp_steps_sync_pool (lsmpl.base 596)
    apply bind_sepWP_state; intro s1
    refine SepWP.done ?_ ?_ ?_
    · simp only [s1, wp_norm, arm64_norm]
    · simp [s1, wp_norm, arm64_norm, hrun0]
    · intro hcrl1 R1 hm1 hL1
      let gPath : PathGhost :=
        { dirA := x.dirA, dir := x.dir, dirRo := x.dirRo,
          nameA := x.nameA, name := x.name, nameRo := x.nameRo,
          ret := (s0.sp - 80#64) + 24#64 }
      let framePath : SepProp :=
        memRegion x.ret 48 ∗
          memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19)
      have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, wp_norm, arm64_norm]
      have htr1 : s1.trace = s0.trace := by simp [s1, wp_norm, arm64_norm]
      have hfds1 : FdsGe3Closed s1.fs := by simpa [s1, wp_norm, arm64_norm] using hfds0
      have hfit_path : LibsignalBinary.Heap.FitsEnv M lim st0 (PathEnv x.dir x.name) :=
        hfit0.seq_left
      have hLiftPath := subroutine_ok_withFsInv hFs hPath563 s0.fs.files s0.trace
      obtain ⟨s2, hsteps_path, hout_path, -⟩ :=
        hLiftPath.no_fault_before_outcome (gPath, st0) (framePath ∗ R1) s1
          (by simp only [s1, wp_norm, arm64_norm])
          (by simp [s1, wp_norm, arm64_norm, hrun0])
          (withFsInv_pre_intro
            ⟨[], by simp [htr1], fun _ => by simp [s1, wp_norm, arm64_norm]⟩
            (satisfies_lscro_pre hcrl1 (by
              dsimp only [withFdsGe3Closed, pathSpecPlaced]
              rw [sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨hfds1, ?_⟩
              rw [sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨⟨by simp [s1, gPath, wp_norm, arm64_norm],
                 by simp [s1, gPath, wp_norm, arm64_norm, hx1_0],
                 by simpa [s1, gPath, wp_norm, arm64_norm] using hx2_0,
                 by simp [s1, gPath, wp_norm, arm64_norm, hx3_0],
                 by simpa [s1, gPath, wp_norm, arm64_norm] using hx4_0,
                 hdir_lt, hname_lt, hfit_path⟩, ?_⟩
              rw [hsp1]
              have hm1_clean : s1.mem ⊨
                  A.pool lim st0 s1 ∗ bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                  memRegion x.ret 48 ∗
                  memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
                  stackAt (s0.sp - 80#64) pathStk ∗ memRegion (s0.sp - 80#64) 24 ∗
                  memRegion ((s0.sp - 80#64) + 24#64) 24 ∗
                  (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                  (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                  (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗ R1 := by
                simpa [s1, wp_norm, arm64_norm, sepConj_emp, sepConj_assoc] using hm1
              refine satisfies_of_eq ?_ hm1_clean; dsimp only [gPath, framePath]; sep_ac_rfl)))
          (by simpa [State.spAligned, hsp1] using hAl_frame) hL1
      rcases hout_path with ⟨⟨hpcs2, _, hruns2⟩, ⟨hsps2, hcss2⟩, hpost_path⟩ |
          ⟨_, hpost_path⟩ | ⟨_, _, hpost_path⟩ | ⟨_, hpost_path⟩
      · obtain ⟨hinv2, hpost_p⟩ := withFsInv_post_elim hpost_path
        dsimp only [withLsCodeRoLoaded, withFdsGe3Closed, pathSpecPlaced] at hpost_p
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_p
        obtain ⟨hfds2, hpost_p⟩ := hpost_p
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost_p
        obtain ⟨evs_p, hpost_p⟩ := hpost_p
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_p
        obtain ⟨⟨htr2_eq, hp_evs⟩, hm2⟩ := hpost_p
        have hp_evs' : PathEnv x.dir x.name evs_p := hp_evs
        let st1 := M.stepEvents evs_p st0
        have htr2 : s2.trace = s0.trace := htr2_eq.trans htr1
        have hsp2 : s2.sp = s0.sp - 80#64 := hsps2.trans hsp1
        have hpcs2' : s2.pc = (blkPl_563).base + 28#64 :=
          hpcs2.trans (by simp [s1, wp_norm, arm64_norm])
        clear hpcs2
        have hcrl2 : LibsignalCodeRoLoaded lsmpl s2.mem :=
          hcrl1.of_keepsFrozen hsteps_path.keepsFrozen
        have hL2 := hsteps_path.codeLoaded hL1
        let p := x.dir ++ [0x2f#8] ++ x.name
        have hp_len_pos : 0 < p.length := by simp [p]
        have hp_len_lt32 : p.length < 2 ^ 32 := hpLen p hpOk
        have hfit_tail :
            LibsignalBinary.Heap.FitsEnv M lim st1 (BundleReadTailEnv rd ReadEnv s0.fs.files p) :=
          hfit0.seq_right hp_evs'
        have hfit_read : LibsignalBinary.Heap.FitsEnv M lim st1 (ReadEnv s0.fs.files p) :=
          hfit_tail.seq_left
        obtain ⟨pathCap, pathPtr, hcap_pos, hp_le_cap, hcap_lt63, _hptr_ne, hm2_unp⟩ :=
          satisfies_vecU8_unpack (A := A.repAlloc) (p := p) hp_len_pos (by
            dsimp only [gPath, p] at hm2 ⊢; rw [sepConj_assoc] at hm2; exact hm2)
        have hsplit_read : stackAt (s0.sp - 80#64) (stk - 80) =
            memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - readStk) ∗
              stackAt (s0.sp - 80#64) readStk :=
          stackAt_split_sub (s0.sp - 80#64) (stk - 80) readStk hread_le (by omega)
        let frameRead : SepProp :=
          memRegion x.ret 48 ∗ bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
            memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - readStk) ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 p.length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗
            memRegion (pathPtr + BitVec.ofNat 64 p.length) (pathCap.toNat - p.length)
        have hm2_read : s2.mem ⊨
            (((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗
              stackAt (s0.sp - 80#64) readStk ∗ A.pool lim st1 s2) ∗ frameRead) ∗ R1 := by
          rw [hsp1] at hm2_unp
          have hm2_stk : s2.mem ⊨
              (memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
                stackAt (s0.sp - 80#64) pathStk) ∗
                ((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗ A.pool lim st1 s2 ∗
                  memRegion x.ret 48 ∗ bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                  (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                  (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 p.length) ∗
                  (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                  (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                  (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                  A.live pathPtr pathCap.toNat 1 ∗
                  memRegion (pathPtr + BitVec.ofNat 64 p.length) (pathCap.toNat - p.length) ∗ R1) := by
            dsimp only [framePath, RustCliAllocBudget.repAlloc, p, st1] at hm2_unp ⊢
            refine satisfies_of_eq ?_ hm2_unp
            rw [BitVec.add_assoc (s0.sp - 80#64) 24#64 8#64,
                BitVec.add_assoc (s0.sp - 80#64) 24#64 16#64,
                show (24#64 : BitVec 64) + 8#64 = 32#64 from rfl,
                show (24#64 : BitVec 64) + 16#64 = 40#64 from rfl]; sep_ac_rfl
          rw [← hsplit_path, hsplit_read] at hm2_stk
          refine satisfies_of_eq ?_ hm2_stk; dsimp only [frameRead]; sep_ac_rfl
        have hwp_after_path :
            SepWPp (lsProg_563 H) (s0.readReg64 .lr) s2
              ((((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗
                  stackAt (s0.sp - 80#64) readStk ∗ A.pool lim st1 s2) ∗ frameRead) ∗ emp)
              (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
                Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ emp)
              (fun sf Qp =>
                Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ emp) := by
          apply sepWPp_seq_lscro hcrl2 (mid := (blkPl_563).base + 40#64)
          wp_conv_pre => dsimp only [frameRead]; rw [← hsp2]
          wp_steps_sync_pool ((blkPl_563).base + 40#64)
          apply bind_sepWP_state; intro s3
          refine SepWP.done ?_ ?_ ?_
          · simp [s3, wp_norm, arm64_norm]
          · simp [s3, wp_norm, arm64_norm, hruns2]
          · intro hcrl3 R3 hm3 hL3
            have hsp3 : s3.sp = s0.sp - 80#64 := by simp [s3, wp_norm, arm64_norm, hsp2]
            have htr3 : s3.trace = s0.trace :=
              (by simp [s3, wp_norm, arm64_norm] : s3.trace = s2.trace).trans htr2
            have hfds3 : FdsGe3Closed s3.fs := by simpa [s3, wp_norm, arm64_norm] using hfds2
            have hx1_3 : (s3.readReg64 .x1).toNat = p.length := by
              simp [s3, wp_norm, arm64_norm]; omega
            have hm3_norm : s3.mem ⊨
                (((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗
                  stackAt s3.sp readStk ∗ A.pool lim st1 s3) ∗ (frameRead ∗ emp)) ∗ R3 := by
              rw [hsp3]; rw [hsp2] at hm3
              refine satisfies_of_eq ?_ hm3; dsimp only [s3, frameRead, p]; sep_ac_rfl
            exact
              (readCall_step_p_guard_fd hRead563 hlr hFs s0.fs.files s0.trace
                (ret := s0.readReg64 .lr) (st := st1) (F := frameRead ∗ emp)
                (Q := fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
                  Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ emp)
                (Qp := fun sf Qp =>
                  Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ emp)
                (s := s3)
                (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm, hruns2])
                (by simpa [State.spAligned, hsp3] using hAl_frame) hcrl3
                (by
                  obtain ⟨w, hw1, hw2⟩ := hinv2
                  exact ⟨w, by simpa [s3, wp_norm, arm64_norm] using hw1,
                    by simpa [s3, wp_norm, arm64_norm] using hw2⟩)
                hfds3 htr3 (by simp [s3, wp_norm, arm64_norm]) hx1_3
                (by simp [s3, wp_norm, arm64_norm]) hp_len_lt32 hpOk hfit_read
                (fun s4 hpcs4 hruns4 hsps4 hAls4 hcss4 hcrl4 _hinv4 hfds4 evs_r hr_evs r hr4 => by
                  let st2 := M.stepEvents evs_r st1
                  have hst2 : st2 = M.stepEvents (evs_p ++ evs_r) st0 :=
                    stepEvents_append_eq evs_p evs_r st0
                  have hfit_after :
                      LibsignalBinary.Heap.FitsEnv M lim st2
                        (BundleReadAfterReadEnv rd s0.fs.files p) :=
                    hfit_tail.seq_right hr_evs
                  have hsp4 : s4.sp = s0.sp - 80#64 := hsps4.trans hsp3
                  have hx19_4 : s4.readReg64 .x19 = pathPtr :=
                    hcss4.1.trans (by simp [s3, wp_norm, arm64_norm])
                  have hx20_4 : s4.readReg64 .x20 = x.ret :=
                    hcss4.2.1.trans ((by simp [s3, wp_norm, arm64_norm] :
                      s3.readReg64 .x20 = s2.readReg64 .x20).trans
                      (hcss2.2.1.trans (by simp [s1, wp_norm, arm64_norm])))
                  have hcs_hi4 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
                      s4.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩) :=
                    cs_hi_trans (cs_hi_of_preserved hcss4)
                      (cs_hi_trans
                        (cs_hi_of_eq
                          (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm])
                          (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm])
                          (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm])
                          (by simp [s3, wp_norm, arm64_norm]) (by simp [s3, wp_norm, arm64_norm]))
                        (cs_hi_trans (cs_hi_of_preserved hcss2)
                          (cs_hi_of_eq
                            (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                            (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                            (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                            (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm]))))
                  have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
                    unfold CalleeSavedPreserved at hcss4 hcss2
                    exact hcss4.2.2.2.2.2.2.2.2.2.2.2.trans
                      ((by simp [s3, wp_norm, arm64_norm] : calleeSavedVRegs s3 = calleeSavedVRegs s2).trans
                        (hcss2.2.2.2.2.2.2.2.2.2.2.2.trans
                          (by simp [s1, wp_norm, arm64_norm] : calleeSavedVRegs s1 = calleeSavedVRegs s0)))
                  have hpack_buf := path_buf_dealloc_pack pathPtr pathCap.toNat p hp_le_cap hcap_lt63
                  have hent_after_read :
                      (ioVecAt A.repAlloc (s0.sp - 80#64) r ∗ (pathPtr ↦ₛ p) ∗
                        stackAt s3.sp readStk ∗ A.pool lim st2 s4 ∗ (frameRead ∗ emp)) ⊢
                      ((ioVecAt A.repAlloc (s0.sp - 80#64) r ∗ memRegion x.ret 48 ∗
                        bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                        stackAt (s0.sp - 80#64) (stk - 80) ∗
                        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗ (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
                        A.pool lim st2 s4) ∗ emp) := by
                    rw [hsp3]
                    have hre1 :
                        (ioVecAt A.repAlloc (s0.sp - 80#64) r ∗ (pathPtr ↦ₛ p) ∗
                          stackAt (s0.sp - 80#64) readStk ∗ A.pool lim st2 s4 ∗ (frameRead ∗ emp)) =
                        ((pathPtr ↦ₛ p) ∗
                          memRegion (pathPtr + BitVec.ofNat 64 p.length) (pathCap.toNat - p.length)) ∗
                        ((memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - readStk) ∗
                          stackAt (s0.sp - 80#64) readStk) ∗
                          (ioVecAt A.repAlloc (s0.sp - 80#64) r ∗ memRegion x.ret 48 ∗
                            bytesAt x.dirRo x.dirA x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
                            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                            A.live pathPtr pathCap.toNat 1 ∗ A.pool lim st2 s4)) := by
                      dsimp only [frameRead, p]; simp only [sepConj_emp]; sep_ac_rfl
                    rw [hre1, ← hsplit_read]
                    refine Entails.trans (sepConj_mono_left hpack_buf) (entails_of_eq ?_)
                    simp only [sepConj_emp]; sep_ac_rfl
                  apply sepWPp_mono_pre hent_after_read
                  cases r with
                  | ok bs =>
                    exact ok_branch_step_p_fd hAllocFs hext_le hstk_le hpcs4 hruns4 hsp4 hAl0
                      hcrl4 hfds4 hx19_4 hx20_4 hcap_pos hcap_lt63 hcs_hi4 hv4 hr4 hst2
                      (fun evs_d hd => bundleReadEnv_ok_end hp_evs' hr_evs hr4.1 hd)
                  | error u =>
                    cases u
                    have hfit22 := fitsEvents_22_of_afterRead_err hr4.1 hfit_after
                    exact err_branch_step_p_fd hAllocFs hext_le hstk_le hpcs4 hruns4 hsp4 hAl0
                      hAls4 hcrl4 hfds4 hx19_4 hx20_4 hcap_pos hcap_lt63 hcs_hi4 hv4 hr4 hst2
                      hfit22 (fun evs_d hd => bundleReadEnv_err_end hp_evs' hr_evs hr4.1 hd)))
                R3 hm3_norm hL3
        obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
          hwp_after_path R1 (by simpa [sepConj_emp, sepConj_assoc] using hm2_read) hL2
        exact ⟨sf, hsteps_path.trans hsteps_rest, hout_rest⟩
      · dsimp only [withFsInv, withLsCodeRoLoaded, withFdsGe3Closed, pathSpecPlaced] at hpost_path
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_path
        exact (not_satisfies_false_sepConj hpost_path.2).elim
      · dsimp only [withFsInv, withLsCodeRoLoaded, withFdsGe3Closed, pathSpecPlaced] at hpost_path
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_path
        exact (not_satisfies_false_sepConj hpost_path.2).elim
      · dsimp only [withFsInv, withLsCodeRoLoaded, withFdsGe3Closed, pathSpecPlaced] at hpost_path
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_path
        exact (not_satisfies_false_sepConj hpost_path.2).elim
  obtain ⟨sf, hsteps_all, hout_all⟩ :=
    hwp_all R (by simpa [sepConj_emp, sepConj_assoc] using hm0) hL0
  rcases hout_all with ⟨hpcf, hrunf, _, hmf, hsp_f, hcs_f, rfl⟩ | ⟨hp1, _, hmf, rfl⟩ | ⟨_, hmo⟩
  · exact reaches_outcome_steps hsteps_all (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hpcf, hsp_f, hrunf⟩, ⟨hsp_f, hcs_f⟩,
        by simpa [BundleEnv, withFdsGe3Closed, withLsCodeRoLoaded, sepConj_emp, sepConj_assoc] using hmf⟩))
  · exact reaches_outcome_steps hsteps_all (reaches_outcome.of_outcome
      (Or.inr (Or.inl ⟨hp1,
        by simpa [BundleEnv, withFdsGe3Closed, withLsCodeRoLoaded, sepConj_emp, sepConj_assoc] using hmf⟩)))
  · exact (not_satisfies_false_sepConj hmo).elim

/-- `LsRetAddr624` and `FdsGe3Closed` contract for `read_bundle::{closure#0}` (Block `563`). -/
theorem bundleRead_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop} {pathStk readStk stk : Nat}
    (hpLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathStk)))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (withLsRetAddr624AndFds (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hFs : TraceFsSound (lsProg_563 H))
    (hstk : 0x50 + max (max pathStk readStk) extHookStack ≤ stk) :
    subroutine_ok (lsProg_563 H) (lsmpl.base 563)
      (withFdsGe3Closed
        (bundleReadSpecPlaced rd pathOk A lim (BundleReadEnv rd PathEnv ReadEnv) stk)) :=
  bundleRead_placed_ok_of_guard_deps_fd hpLen hAllocFs hjPath hjPath_unmut hPath
    hjRead hjRead_unmut hRead
    (lsRetAddr624_blockPlacement_base_add 563 44#64 (by decide) (by decide)) hFs hstk

/-- Cross-block `LsRetAddr624` and `FdsGe3Closed` contract for `read_bundle::{closure#0}` at any caller block `i < 619`. -/
theorem bundleRead_placed_caller_ok_of_deps_fd [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop} {pathStk readStk stk : Nat}
    (hpLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathStk)))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (withLsRetAddr624AndFds (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hFs : TraceFsSound (lsProg_563 H))
    (hstk : 0x50 + max (max pathStk readStk) extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 563)
      (withFdsGe3Closed
        (bundleReadSpecPlaced rd pathOk A lim (BundleReadEnv rd PathEnv ReadEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (calleeProg := lsProg_563 H)
    (i := i) (j := 563)
    (bundleRead_placed_ok_of_deps_fd hpLen hAllocFs hjPath hjPath_unmut hPath
      hjRead hjRead_unmut hRead hFs hstk) hi

/-- `keepSet`-guarded `HookSat` specialization of `bundleRead_placed_ok_of_guard_deps_fd`. -/
theorem bundleRead_placed_ok_of_keep_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {keepSet : BitVec 64 → Bool} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop} {pathStk readStk stk : Nat}
    (hpLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hAllocFs : AllocContractsFsPlaced A lim H)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathStk)))
    (hSat : HookSat H lsReadFileSym
      (withFdsGe3Closed
        (withKeepLrAndFds keepSet (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))))
    (hlr : keepSet ((blkPl_563).base + 44#64) = false)
    (hFs : TraceFsSound (lsProg_563 H))
    (hstk : 0x50 + max (max pathStk readStk) extHookStack ≤ stk) :
    subroutine_ok (lsProg_563 H) (lsmpl.base 563)
      (withFdsGe3Closed
        (bundleReadSpecPlaced rd pathOk A lim (BundleReadEnv rd PathEnv ReadEnv) stk)) :=
  bundleRead_placed_ok_of_guard_deps_fd (lrOk := fun lr => keepSet lr = false)
    hpLen hAllocFs hjPath hjPath_unmut hPath (jRead := 563) (by decide) (by decide)
    (lsReadFile_withLsCodeRoLoaded_of_hookSat (callerProg := lsProg_563 H) (i := 563)
      (hookSat_keepLr_withFds_of_withFds_keepLrAndFds hSat))
    hlr hFs hstk

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetFd
