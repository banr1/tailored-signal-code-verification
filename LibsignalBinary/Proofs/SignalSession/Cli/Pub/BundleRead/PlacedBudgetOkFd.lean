/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded `Ok(bs)` Branch and Epilogue for `read_bundle::{closure#0}`

File-descriptor-preserving (`FdsGe3Closed`) tail-deallocation epilogue and `Ok(bs)` branch on Block
`563`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetOkFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (BundleReadGhost ReadRule getResultAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_563 lsProg_563)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.BundleRead.Helpers
  (frame_80_pack ok_result_intro slot24_pack sret_32_unpack stackAt_frame_80_eq
   stackAt_split_sub)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced bundleReadSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (dealloc_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
  (bind_sepWP_state cs_hi_of_eq cs_hi_of_preserved cs_hi_trans rustLayoutOk_of_pos_lt63
   satisfies_mono_rev satisfies_of_eq sepWPp_exists_pre sepWPp_mono_pre stepEvents_append_eq)

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

/-- `FdsGe3Closed`-preserving epilogue (`+84 .. +108` on Block `563`), preserving `s.fs` across `__rust_dealloc` via `AllocContractsFsPlaced`. -/
theorem tail_dealloc_step_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {st0 st_pre : M.σ} {evs_pre : List AllocEvent}
    {s0 s : State}
    {pathCap pathPtr : BitVec 64} {r : Except Unit (List (BitVec 8))}
    {F : SepProp}
    (hPC : s.pc = (blkPl_563).base + 84#64)
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx1_s : s.readReg64 .x1 = pathCap)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace)
    (hst_pre : st_pre = M.stepEvents evs_pre st0)
    (hevs_end : ∀ evs_d, FreeOnlyEvs evs_d →
      BundleEnv s0.fs.files x.dir x.name (evs_pre ++ evs_d)) :
    SepWPp (lsProg_563 H) (s0.readReg64 .lr) s
      (((getResultAt A.repAlloc x.ret r ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
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
  have hAl_frame : (s0.sp - 80#64) &&& 15#64 = 0#64 := by
    have hal : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hAl0
    bv_bits
  have hsplit_hk : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        stackAt (s0.sp - 80#64) extHookStack :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) extHookStack (by omega) (by omega)
  apply sepWPp_seq_lscro hcrl (mid := lsρ lsRustDeallocSymCli)
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp [s1, wp_norm, arm64_norm]
  · simp [s1, wp_norm, arm64_norm, hRun]
  · intro hcrl1 R hm1 hL1
    have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, wp_norm, arm64_norm, hsp]
    have htr_s1 : s1.trace = s.trace := by simp [s1, wp_norm, arm64_norm]
    have hfs_s1 : s1.fs = s.fs := by simp [s1, wp_norm, arm64_norm]
    let restDealloc : SepProp :=
      getResultAt A.repAlloc x.ret r ∗
        bytesAt x.dirRo x.dirA x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        memRegion (s0.sp - 80#64) 24 ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗ F
    have hm1_d : s1.mem ⊨
        (A.pool lim st_pre s1 ∗ A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          stackAt s1.sp extHookStack) ∗ restDealloc ∗ R := by
      rw [hsp1]
      have hm1' := hm1
      simp only [List.length_append, List.length_cons, List.length_nil] at hm1' ⊢
      rw [hsplit_hk] at hm1'
      refine satisfies_of_eq ?_ hm1'
      dsimp only [restDealloc]
      simp only [List.length_append, List.length_cons, List.length_nil]
      sep_ac_rfl
    obtain ⟨sd, hsteps_d, hout_d, -⟩ :=
      (dealloc_keepsFs_lscro_of_fs (callerProg := lsProg_563 H) (i := 563) hFs).no_fault_before_outcome
        (pathPtr, pathCap.toNat, 1, st_pre) (restDealloc ∗ R) s1
        (by simp [s1, wp_norm, arm64_norm])
        (by simp [s1, wp_norm, arm64_norm, hRun])
        (satisfies_lscro_pre hcrl1 (by
          dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack]
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨by simp [s1, wp_norm, arm64_norm],
             by simp [s1, wp_norm, arm64_norm, hx1_s],
             rfl,
             rustLayoutOk_of_pos_lt63 hcap_pos hcap_lt,
             ⟨563, by decide, 96, by decide, by simp only [s1, wp_norm, arm64_norm]; rfl⟩⟩,
            by simpa [sepConj_assoc] using hm1_d⟩))
        (by simpa [State.spAligned, hsp1] using hAl_frame)
        hL1
    rcases hout_d with ⟨⟨hpcsd, hsp_d0, hrunsd⟩, ⟨hspsd, hcssd⟩, hpost_d⟩ | ⟨_, hpost_d⟩ |
        ⟨_, _, hpost_d⟩ | ⟨_, hpost_d⟩
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          rustCliDeallocBudgetExternSpecWithStack] at hpost_d
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost_d
      obtain ⟨hfs_sd, htr_sd, hmem_sd⟩ := hpost_d
      replace hpcsd : sd.pc = (blkPl_563).base + 96#64 :=
        hpcsd.trans (by simp [s1, wp_norm, arm64_norm])
      have hspd : sd.sp = s0.sp - 80#64 := hspsd.trans hsp1
      clear hsp_d0 hspsd
      have hcrl_d : LibsignalCodeRoLoaded lsmpl sd.mem :=
        hcrl1.of_keepsFrozen hsteps_d.keepsFrozen
      have hLd := hsteps_d.codeLoaded hL1
      let evs_d := rustDeallocEvents pathCap.toNat 1
      let evs_all := evs_pre ++ evs_d
      have hst_all : M.stepEvents evs_d st_pre = M.stepEvents evs_all st0 := by
        rw [hst_pre]; exact stepEvents_append_eq evs_pre evs_d st0
      have hmd_ep : sd.mem ⊨
          (((getResultAt A.repAlloc x.ret r ∗
            bytesAt x.dirRo x.dirA x.dir ∗
            bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.pool lim (M.stepEvents evs_all st0) sd) ∗ F) ∗ R) := by
        have hmem_sd' := hmem_sd
        have hst_all' : M.stepEvents (rustDeallocEvents pathCap.toNat 1) st_pre =
            M.stepEvents evs_all st0 := hst_all
        rw [hsp1, hst_all'] at hmem_sd'
        rw [hsplit_hk]
        refine satisfies_of_eq ?_ hmem_sd'
        dsimp only [restDealloc]
        simp only [List.length_append, List.length_cons, List.length_nil]
        sep_ac_rfl
      have hwp_ep :
          SepWPp (lsProg_563 H) (s0.readReg64 .lr) sd
            (((getResultAt A.repAlloc x.ret r ∗
              bytesAt x.dirRo x.dirA x.dir ∗
              bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              memRegion (s0.sp - 80#64) 24 ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.pool lim (M.stepEvents evs_all st0) sd) ∗ F))
            (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
              Q = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post (x, st0) s0 sf ∗ F)
            (fun sf Qp =>
              Qp = (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).onPanic (x, st0) s0 sf ∗ F) := by
        apply sepWPp_seq_lscro hcrl_d (mid := s0.readReg64 .lr)
        wp_conv_pre => rw [← hspd]
        wp_steps_sync_pool (s0.readReg64 .lr)
        apply bind_sepWP_state; intro sf
        refine SepWP.done ?_ ?_ ?_
        · simp [sf, wp_norm, arm64_norm]
        · simp [sf, wp_norm, arm64_norm, hrunsd]
        · intro _ R_ep hm_ep _hL_ep
          have hpack80 := frame_80_pack (s0.sp - 80#64) pathCap pathPtr
            (BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length)
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x20) (s0.readReg64 .x19)
          have hstk80 : stackAt s0.sp stk =
              stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 80 :=
            stackAt_frame_80_eq s0.sp stk (by omega) hstk_le
          have htr_sf : sf.trace = sd.trace := by simp [sf, wp_norm, arm64_norm]
          have hfs_sf : sf.fs = sd.fs := by simp [sf, wp_norm, arm64_norm]
          have hfds_sf : FdsGe3Closed sf.fs := by
            rw [hfs_sf, hfs_sd, hfs_s1]; exact hfds
          have hr_final :
              r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ sf.trace = s0.trace ∧
                BundleEnv s0.fs.files x.dir x.name evs_all :=
            ⟨hr_out.1, htr_sf.trans (htr_sd.trans (htr_s1.trans hr_out.2)),
              hevs_end evs_d (FreeOnlyEvs.singleton 1 pathCap.toNat)⟩
          refine ⟨sf, Steps.refl sf,
            Or.inl ⟨by simp [sf, wp_norm, arm64_norm], by simp [sf, wp_norm, arm64_norm, hrunsd], _, ?_,
              by simp [sf, wp_norm, arm64_norm], ?_, rfl⟩⟩
          · have hm_ep' : sf.mem ⊨
                (((getResultAt A.repAlloc x.ret r ∗
                  bytesAt x.dirRo x.dirA x.dir ∗
                  bytesAt x.nameRo x.nameA x.name ∗
                  (stackAt (s0.sp - 80#64) (stk - 80) ∗
                    (memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ∗
                  A.pool lim (M.stepEvents evs_all st0) sf) ∗ F) ∗ R_ep) := by
              refine satisfies_of_eq ?_ hm_ep
              simp only [hspd, List.length_append, List.length_cons, List.length_nil]
              sep_ac_rfl
            have h1 :
                (stackAt (s0.sp - 80#64) (stk - 80) ∗
                  (memRegion (s0.sp - 80#64) 24 ∗
                    (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                    (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                    (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                    (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                    (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                    (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                    (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ⊢
                stackAt s0.sp stk := by
              rw [hstk80]; exact sepConj_mono_right hpack80
            have hpost_ent :
                ((getResultAt A.repAlloc x.ret r ∗
                  bytesAt x.dirRo x.dirA x.dir ∗
                  bytesAt x.nameRo x.nameA x.name ∗
                  (stackAt (s0.sp - 80#64) (stk - 80) ∗
                    (memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ∗
                  A.pool lim (M.stepEvents evs_all st0) sf) ∗ F) ⊢
                (withFdsGe3Closed (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk)).post
                  (x, st0) s0 sf ∗ F := by
              dsimp only [withFdsGe3Closed, bundleReadSpecPlaced, withLsCodeRoLoaded]
              refine Entails.trans
                (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left h1))))) ?_
              have hre :
                  ((getResultAt A.repAlloc x.ret r ∗
                    bytesAt x.dirRo x.dirA x.dir ∗
                    bytesAt x.nameRo x.nameA x.name ∗
                    stackAt s0.sp stk ∗
                    A.pool lim (M.stepEvents evs_all st0) sf) ∗ F) =
                  (getResultAt A.repAlloc x.ret r ∗
                    (bytesAt x.dirRo x.dirA x.dir ∗
                      bytesAt x.nameRo x.nameA x.name ∗
                      stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs_all st0) sf)) ∗ F := by
                sep_ac_rfl
              rw [hre]
              refine sepConj_mono_left (Entails.pure_right hfds_sf ?_)
              refine Entails.sepExists_right evs_all ?_
              exact sepConj_mono_left
                (Entails.sepExists_right r (Entails.pure_right hr_final (Entails.refl _)))
            exact Satisfies.mono (sepConj_mono_left hpost_ent) hm_ep'
          · have hcs_sf_s0 :=
              cs_hi_trans
                (cs_hi_of_eq (s1 := sf) (s2 := sd)
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm])
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm])
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm])
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm]))
                (cs_hi_trans (cs_hi_of_preserved hcssd)
                  (cs_hi_trans
                    (cs_hi_of_eq (s1 := s1) (s2 := s)
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm]))
                    hcs_hi))
            unfold CalleeSavedPreserved at hcssd ⊢
            refine ⟨by simp [sf, wp_norm, arm64_norm],
              by simp [sf, wp_norm, arm64_norm],
              hcs_sf_s0 21 ⟨by omega, by omega⟩,
              hcs_sf_s0 22 ⟨by omega, by omega⟩,
              hcs_sf_s0 23 ⟨by omega, by omega⟩,
              hcs_sf_s0 24 ⟨by omega, by omega⟩,
              hcs_sf_s0 25 ⟨by omega, by omega⟩,
              hcs_sf_s0 26 ⟨by omega, by omega⟩,
              hcs_sf_s0 27 ⟨by omega, by omega⟩,
              hcs_sf_s0 28 ⟨by omega, by omega⟩,
              by simp [sf, wp_norm, arm64_norm],
              ((by simp [sf, calleeSavedVRegs, wp_norm, arm64_norm] :
                calleeSavedVRegs sf = calleeSavedVRegs sd).trans
                (hcssd.2.2.2.2.2.2.2.2.2.2.2.trans
                  ((by simp [s1, calleeSavedVRegs, wp_norm, arm64_norm] :
                    calleeSavedVRegs s1 = calleeSavedVRegs s).trans hvregs)))⟩
      obtain ⟨sf, hsteps_ep, hout_ep⟩ := hwp_ep R hmd_ep hLd
      exact ⟨sf, hsteps_d.trans hsteps_ep, hout_ep⟩
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_d
      exact (not_satisfies_false_sepConj hpost_d).elim
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_d
      exact (not_satisfies_false_sepConj hpost_d).elim
    · dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hpost_d
      exact (not_satisfies_false_sepConj hpost_d).elim

set_option maxHeartbeats 800000 in
/-- `FdsGe3Closed`-preserving `Ok(bs)` branch (`+44 .. +84` on Block `563`), entering `tail_dealloc_step_p_fd`. -/
theorem ok_branch_step_p_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {st0 st_pre : M.σ} {evs_pre : List AllocEvent}
    {s0 s : State}
    {pathCap pathPtr : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp}
    (hPC : s.pc = (blkPl_563).base + 44#64)
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : Except.ok bs = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace)
    (hst_pre : st_pre = M.stepEvents evs_pre st0)
    (hevs_end : ∀ evs_d, FreeOnlyEvs evs_d →
      BundleEnv s0.fs.files x.dir x.name (evs_pre ++ evs_d)) :
    SepWPp (lsProg_563 H) (s0.readReg64 .lr) s
      (((vecU8 A.repAlloc (s0.sp - 80#64) bs ∗
          memRegion x.ret 48 ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
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
  dsimp only [vecU8, vecU8At, vecHeader, RustCliAllocBudget.repAlloc]
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_pre; intro vecCap
  apply sepWPp_exists_pre; intro vecPtr
  apply sepWPp_mono_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (sret_32_unpack x.ret))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWPp_exists_pre; intro w3
  apply sepWPp_exists_pre; intro w2
  apply sepWPp_exists_pre; intro w1
  apply sepWPp_exists_pre; intro w0 R hm hL
  have hpure_vec :
      bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0 := by
    have hm' : s.mem ⊨ ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
        ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗ (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
          (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if vecCap = 0 then emp
           else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
             memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length)) ∗
          ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
            ((x.ret + 24#64) ↦₆₄ w3) ∗ memRegion (x.ret + 32#64) 16) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s ∗ F) ∗ R) := by
      refine satisfies_of_eq ?_ hm; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hm'; exact hm'.1
  have hnot_err : (vecCap + 1#64 == 0#64) = false := by
    apply beq_false_of_ne; intro heq
    have hnat := congrArg BitVec.toNat heq; simp [BitVec.toNat_add] at hnat; omega
  have heq_cond : ConditionHolds CondCode.EQ (AddWithCarry64 vecCap 1#64 false).2 = false := by
    have _ : vecCap.toNat < 2 ^ 63 := hpure_vec.2.1
    simp only [ConditionHolds, AddWithCarry64]; bv_bits
  have hcap_ne : pathCap ≠ 0#64 := by intro heq; subst heq; simp at hcap_pos
  have hcap_ne0 : (pathCap == 0#64) = false := beq_false_of_ne hcap_ne
  have _ := And.intro heq_cond (And.intro hnot_err (And.intro hcap_ne hcap_ne0))
  have hm_flat : s.mem ⊨
      (((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ memRegion (x.ret + 32#64) 16 ∗
        ((s0.sp - 80#64) ↦₆₄ vecCap) ∗
        (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
        (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
        (if vecCap = 0 then emp
         else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
           memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length)) ∗
        bytesAt x.dirRo x.dirA x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 80#64) (stk - 80) ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
        A.pool lim st_pre s ∗ F) ∗ R) := by
    refine satisfies_of_eq ?_ hm
    simp only [List.length_append, List.length_cons, List.length_nil]
    sep_ac_rfl
  simp only [arm64_norm] at hx20_s
  refine (?_ : SepWPp (lsProg_563 H) (s0.readReg64 .lr) s _ _ _) R hm_flat hL
  apply sepWPp_seq_lscro hcrl (mid := (blkPl_563).base + 84#64)
  wp_steps_sync_pool ((blkPl_563).base + 84#64)
  apply bind_sepWP_state; intro s_mid
  refine SepWP.done ?_ ?_ ?_
  · simp [s_mid, wp_norm, arm64_norm]
  · simp [s_mid, wp_norm, arm64_norm, hRun]
  · intro hcrl_mid R' hm_mid hL_mid
    have hs_mid_sp : s_mid.sp = s0.sp - 80#64 := by simp [s_mid, wp_norm, arm64_norm, hsp]
    have hs_mid_x1 : s_mid.readReg64 .x1 = pathCap := by simp [s_mid, wp_norm, arm64_norm]
    have hs_mid_x19 : s_mid.readReg64 .x19 = pathPtr := by simp [s_mid, wp_norm, arm64_norm, hx19_s]
    have hs_mid_tr : s_mid.trace = s.trace := by simp [s_mid, wp_norm, arm64_norm]
    have hfds_mid : FdsGe3Closed s_mid.fs := by simpa [s_mid, wp_norm, arm64_norm] using hfds
    have hpack_ok :
        ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
          (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
          (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
          (if vecCap = 0 then emp
           else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
             memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
          ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) ⊢
        (getResultAt A.repAlloc x.ret (.ok bs) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) := by
      have hre1 :
          ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
            (if vecCap = 0 then emp
             else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
               memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
            ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
              ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16)) =
          ((x.ret ↦₆₄ okTagVec) ∗
            (((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
              ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
              ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
              (if vecCap = 0 then emp
               else A.repAlloc.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
                 memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
            memRegion (x.ret + 32#64) 16) ∗
          (((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) := by
        dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
      have hboth := sepConj_mono (ok_result_intro A.repAlloc x.ret vecCap vecPtr bs)
        (slot24_pack (s0.sp - 80#64) vecCap vecPtr (BitVec.ofNat 64 bs.length))
      rw [← hre1] at hboth
      have hall := sepConj_mono_left
        (Q := bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) hboth
      have hre2 :
          (getResultAt A.repAlloc x.ret (.ok bs) ∗ memRegion (s0.sp - 80#64) 24) ∗
            (bytesAt x.dirRo x.dirA x.dir ∗
              bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
              A.pool lim st_pre s_mid) =
          getResultAt A.repAlloc x.ret (.ok bs) ∗
            bytesAt x.dirRo x.dirA x.dir ∗
            bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
            A.pool lim st_pre s_mid := by sep_ac_rfl
      rw [hre2] at hall; simpa [sepConj_assoc] using hall
    have hm_mid_orig : s_mid.mem ⊨
        ((((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
            (if vecCap = 0 then emp
             else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
               memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
          ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) ∗ F) ∗ R') := by
      refine satisfies_of_eq ?_ hm_mid
      dsimp only [s_mid, okTagVec]
      simp only [arm64_norm, List.length_append, List.length_cons]
      sep_ac_rfl
    have hm_norm : s_mid.mem ⊨
        ((getResultAt A.repAlloc x.ret (.ok bs) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) ∗ F) ∗ R' :=
      satisfies_mono_rev hm_mid_orig
        (sepConj_mono_left (Q := R') (sepConj_mono_left (Q := F) hpack_ok))
    exact
      (tail_dealloc_step_p_fd hFs hstk hstk_le
        (by simp [s_mid, wp_norm, arm64_norm])
        (by simp [s_mid, wp_norm, arm64_norm, hRun])
        hs_mid_sp hAl0 hcrl_mid hfds_mid
        hs_mid_x19 hs_mid_x1 hcap_pos hcap_lt
        (cs_hi_trans
          (cs_hi_of_eq
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm])
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm])
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm])
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm]))
          hcs_hi)
        ((by simp [s_mid, wp_norm, arm64_norm] :
          calleeSavedVRegs s_mid = calleeSavedVRegs s).trans hvregs)
        ⟨hr_out.1, hs_mid_tr.trans hr_out.2⟩
        hst_pre hevs_end)
      R' hm_norm hL_mid

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetOkFd
