/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` `signal_session::stores::path` (Block 596)

Defines the deterministic allocator event list `pathEvents` and verifies `signal_session::stores::path`
on Block 596 against `pathSpecPlaced A lim PathEnv stk` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved fitsEvents_append rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks ls_hook_ok_ultra_of_mem
   lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall extHookStack memcpyName reserveCap withStack)
open CryptoVerification.SpqrV1.Varint
  (elem_len_ult_spare_iff vecU8At_eq_header_rest vecU8At_expose_slice vecU8At_of_header_rest
   vecU8At_pack_slice vecU8RestAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (PathGhost)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_596 lsProg_596)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon.SepWPp (call_lscro)
open CryptoVerification.SignalSession.Cli.Path.Helpers
  (bv_eq_ofNat_of_toNat cells_14_eq fsp_add_112_eq memRegion_1_eq_pointsTo8 memRegion_24_cells
   ofNat_beq_zero_false ofNat_getElem_63_false ofNat_getLsbD_63_false ofNat_ne_zero
   pointsTo8_eq_singleton session2MemcpyBytesAtSpecX sp_sub_112_aligned stackAt_path_frame
   stackAt_split_ge stk_lt_two_pow_64)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced pathSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOomExtern_lscro_of_cli session_memcpy_region_lscro_of_cli shim_lscro_of_cli
   subroutine_ok_withLsCodeRoLoaded_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. Deterministic `path` Allocator Events & Envelope -/

/-- Capacity of the intermediate `Vec<u8>` right after `push(b'/')` on `dir`. -/
def pathSlashCap (dirLen : Nat) : Nat := reserveCap dirLen dirLen 1

/-- Allocator events emitted by `dir.to_owned()` in `signal_session::stores::path`. -/
def pathToOwnedEvents (dirLen : Nat) : List AllocEvent :=
  if dirLen = 0 then [] else rustAllocEvents dirLen 1

/-- Allocator events emitted by `v.push(b'/')` in `signal_session::stores::path`. -/
def pathPushSlashEvents (dirLen : Nat) : List AllocEvent :=
  if dirLen = 0 then rustAllocEvents (pathSlashCap 0) 1
  else rustReallocEvents dirLen (pathSlashCap dirLen) 1

/-- Allocator events emitted by `v.extend_from_slice(name)` in `signal_session::stores::path`. -/
def pathAppendNameEvents (dirLen nameLen : Nat) : List AllocEvent :=
  let cap1 := pathSlashCap dirLen
  if cap1 < (dirLen + 1) + nameLen then rustReallocEvents cap1 (reserveCap cap1 (dirLen + 1) nameLen) 1
  else []

/-- Exact deterministic allocator event list of `signal_session::stores::path(dir, name)`. -/
def pathEvents (dir name : List (BitVec 8)) : List AllocEvent :=
  pathToOwnedEvents dir.length ++ (pathPushSlashEvents dir.length ++ pathAppendNameEvents dir.length name.length)

/-- Exact allocator event envelope of `signal_session::stores::path`. -/
def PathEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop := evs = pathEvents dir name

theorem fitsEnv_path_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (dir name : List (BitVec 8)) :
    FitsEnv M lim st (PathEnv dir name) ↔ FitsEvents M lim st (pathEvents dir name) := FitsEnv.eq_iff

private theorem doReserveEvents_push_slash (v ptr0 : BitVec 64) (dir : List (BitVec 8))
    (hdir_lt : dir.length < 2 ^ 64) :
    doReserveEvents (DoReserveCall.mk v (BitVec.ofNat 64 dir.length) ptr0 dir 1) =
      pathPushSlashEvents dir.length := by
  have htoNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt]
  unfold doReserveEvents pathPushSlashEvents pathSlashCap; dsimp only; rw [htoNat]
  by_cases h0 : dir.length = 0
  · simp only [h0, ↓reduceIte]
  · have hne : BitVec.ofNat 64 dir.length ≠ 0#64 := ofNat_ne_zero (Nat.pos_of_ne_zero h0) hdir_lt
    simp only [h0, hne, ↓reduceIte]

private theorem doReserveEvents_append_name (v ptr1 : BitVec 64) (dir name : List (BitVec 8))
    (hlt_cap : pathSlashCap dir.length < (dir.length + 1) + name.length)
    (hcap1_lt : pathSlashCap dir.length < 2 ^ 64) :
    doReserveEvents
        (DoReserveCall.mk v (BitVec.ofNat 64 (pathSlashCap dir.length)) ptr1
          (dir ++ [0x2f#8]) name.length) =
      pathAppendNameEvents dir.length name.length := by
  have hcap1_pos : 0 < pathSlashCap dir.length := by simp only [pathSlashCap, reserveCap]; omega
  have hcap1_toNat : (BitVec.ofNat 64 (pathSlashCap dir.length)).toNat = pathSlashCap dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap1_lt]
  have hcap1_ne : BitVec.ofNat 64 (pathSlashCap dir.length) ≠ 0#64 := ofNat_ne_zero hcap1_pos hcap1_lt
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  unfold doReserveEvents pathAppendNameEvents; dsimp only; rw [hcap1_toNat, hlen1]
  simp only [hcap1_ne, hlt_cap, ↓reduceIte]

/-! ## 2. Callee-Saved Invariant & `VmPreserved` `memcpy` (`ro : Bool`) Contract -/

private def PathCalleeSavedP (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem PathCalleeSavedP.refl (s0 : State) : PathCalleeSavedP s0 s0 := ⟨rfl, rfl, rfl, rfl⟩

private theorem PathCalleeSavedP.trans {s0 s1 s2 : State}
    (h01 : PathCalleeSavedP s0 s1) (h12 : PathCalleeSavedP s1 s2) : PathCalleeSavedP s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.trans h01.2.2.2⟩

private theorem PathCalleeSavedP.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) : PathCalleeSavedP s1 s2 :=
  ⟨hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.2.2⟩

abbrev session2MemcpyBytesAtBudgetSpecX (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved (session2MemcpyBytesAtSpecX ro)

private theorem memcpy_bytesAt_placed_ok_of_ro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO596 : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) extHookStack)))
    (ro : Bool) :
    subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtBudgetSpecX ro)) := by
  cases ro
  · have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_596 H) (i := 596)
      (stk := extHookStack) hC
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply satisfies_lscro_pre hcrl0
      dsimp only [session2MemcpyBytesAtBudgetSpecX, withVmPreserved, session2MemcpyBytesAtSpecX,
        withStack, sessionMemcpyRegionBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
        ProofLib.memcpyRegionSpec] at hpre0 ⊢
      simp only [bytesAt_false, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeRoLoaded, session2MemcpyBytesAtBudgetSpecX, withVmPreserved,
        session2MemcpyBytesAtSpecX, withStack, sessionMemcpyRegionBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
        ProofLib.memcpyRegionSpec] at hpost ⊢
      simp only [bytesAt_false, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
        ProofLib.memcpyRegionSpec] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
        ProofLib.memcpyRegionSpec] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withLsCodeRoLoaded, withStack, sessionMemcpyRegionBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
        ProofLib.memcpyRegionSpec] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  · refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl
          (withStack (withVmPreserved sessionMemcpyRegionROSpec) extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply satisfies_lscro_pre hcrl0
      dsimp only [session2MemcpyBytesAtBudgetSpecX, withVmPreserved, session2MemcpyBytesAtSpecX,
        withStack, sessionMemcpyRegionROSpec] at hpre0 ⊢
      simp only [bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨hpre0.1, hpre0.2⟩
    refine hRO596.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeRoLoaded, session2MemcpyBytesAtBudgetSpecX, withVmPreserved,
        session2MemcpyBytesAtSpecX, withStack, sessionMemcpyRegionROSpec] at hpost ⊢
      simp only [bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · dsimp only [withLsCodeRoLoaded, withStack, withVmPreserved,
        sessionMemcpyRegionROSpec] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withLsCodeRoLoaded, withStack, withVmPreserved,
        sessionMemcpyRegionROSpec] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withLsCodeRoLoaded, withStack, withVmPreserved,
        sessionMemcpyRegionROSpec] at hoom
      exact (not_satisfies_false_sepConj hoom).elim

private theorem ro596_of_hookSat [LibsignalPlacement] {H : LibsignalHooks}
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)) :
    subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) extHookStack)) := by
  have hmc_ro : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withVmPreserved sessionMemcpyRegionROSpec) :=
    ls_hook_ok_ultra_of_mem (prog := lsProg_596 H) (i := 596) hRO (by decide)
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨_hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withVmPreserved sessionMemcpyRegionROSpec).pre (dst, src, bs) s0 ∗
      (stackAt s0.sp extHookStack ∗ R) := by
    dsimp only [withStack, withVmPreserved, sessionMemcpyRegionROSpec] at hpre0 ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    exact ⟨hpre0.1, hpre0.2⟩
  refine hmc_ro.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withStack, withVmPreserved,
      sessionMemcpyRegionROSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, hpost.2.2⟩
  · dsimp only [withVmPreserved, sessionMemcpyRegionROSpec] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [withVmPreserved, sessionMemcpyRegionROSpec] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [withVmPreserved, sessionMemcpyRegionROSpec] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 3. `SepWPp` Call Helpers (`onPanic = ⌜False⌝`) -/

private abbrev pathOnPanicP [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat)
    (x0 : PathGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (pathSpecPlaced A lim PathEnv stk).onPanic x0 s0 sf ∗ R)

private theorem step_shim_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat} {call_pc fsp ret_pc ret : BitVec 64} {s0 s : State}
    (hshim : subroutine_ok (lsProg_596 H) call_pc
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec extHookStack)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hcs : PathCalleeSavedP s0 s) (hP : P = stackAt fsp extHookStack ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = fsp →
      sm.trace = s0.trace → VmPreserved s sm → CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        (stackAt fsp extHookStack ∗ F) Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine call_lscro (x := ()) (F := F) hshim hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    dsimp only [withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    simp only [emp_sepConj, hsp]; convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    dsimp only [withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ hm
    dsimp only [withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hm; rw [sepConj_assoc] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    dsimp only [withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hvm hcsm
        (hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)) hcrlm)

private theorem step_alloc_no_oom_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk size : Nat} {st : M.σ} {call_pc fsp ret_pc ret : BitVec 64} {s0 s : State}
    (halloc : subroutine_ok (lsProg_596 H) call_pc
      (withLsCodeRoLoaded lsmpl (rustAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).toNat = size) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : RustLayoutOk size 1) (hfit : FitsEvents M lim st (rustAllocEvents size 1))
    (hcs : PathCalleeSavedP s0 s) (hP : P = (A.pool lim st s ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x0 ≠ 0#64 → sm.trace = s0.trace → CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        ((A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sm ∗ stackAt fsp extHookStack ∗
          A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R))
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine call_lscro (x := (size, 1, st)) (F := F) halloc hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    dsimp only [rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack]
    simp only [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlay, hfit, by rw [hlr]; exact hlr_ls⟩, ?_⟩; convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    dsimp only [rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ hm
    dsimp only [rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack] at hm; rw [sepConj_assoc] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    have hcs_s0 := hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)
    dsimp only [rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    simp only [hsp, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htrm, hptr_ne0, _⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hptr_ne0 (htrm.trans htr) hcsm hcs_s0 hcrlm)

private theorem step_memcpy_ro_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat} {ro : Bool} {call_pc dst src fsp ret_pc ret : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State}
    (hmc : subroutine_ok (lsProg_596 H) call_pc
      (withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtBudgetSpecX ro)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (memRegion dst bs.length ∗ bytesAt ro src bs ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = fsp →
      sm.trace = s0.trace → VmPreserved s sm → CalleeSavedPreserved s sm →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        (((dst ↦ₛ bs) ∗ bytesAt ro src bs ∗ stackAt fsp extHookStack) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine call_lscro (x := (dst, src, bs)) (F := F) hmc hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    dsimp only [session2MemcpyBytesAtBudgetSpecX, withVmPreserved, session2MemcpyBytesAtSpecX]
    simp only [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩; convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    dsimp only [session2MemcpyBytesAtBudgetSpecX, withVmPreserved, session2MemcpyBytesAtSpecX] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ hm
    dsimp only [session2MemcpyBytesAtBudgetSpecX, withVmPreserved, session2MemcpyBytesAtSpecX] at hm
    rw [sepConj_assoc] at hm; exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    dsimp only [session2MemcpyBytesAtBudgetSpecX, withVmPreserved, session2MemcpyBytesAtSpecX]
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hvm hcsm
        (hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)) hcrlm)

private theorem step_cli_reserve_call_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack stk additional : Nat} {st : M.σ}
    {call_pc v curCap curPtr fsp ret_pc ret : BitVec 64} {curBs : List (BitVec 8)} {s0 s : State}
    (hres : subroutine_ok (lsProg_596 H) call_pc
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs additional)))
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : PathCalleeSavedP s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim st s ∗ stackAt fsp resStack) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = fsp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional))
          newPtr curBs ∗
          A.pool lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) st)
            sm ∗
          stackAt fsp resStack) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact hfsp_align
  refine call_lscro (x := (DoReserveCall.mk v curCap curPtr curBs additional, st)) (F := F)
    hres hcrl hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    dsimp only [doReserveSpecOf] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ hm
    dsimp only [doReserveSpecOf] at hm; rw [sepConj_assoc] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hcrlm
    rw [hsp] at hspm
    dsimp only [doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (PathCalleeSavedP.of_calleeSavedPreserved hcsm)) hcrlm)
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 4. Symbolic-Execution Phases on Block `596` -/

private theorem step_to_owned_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack stk : Nat} {st : M.σ}
    {s0 s : State} {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret dirA nameA ret_lr : BitVec 64} {dir name : List (BitVec 8)} {dirRo : Bool}
    (hshim : subroutine_ok (lsProg_596 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec extHookStack)))
    (halloc : subroutine_ok (lsProg_596 H) (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hmc_dir : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtBudgetSpecX dirRo)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64) (hdir_lt : dir.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (pathToOwnedEvents dir.length))
    (hpc : s.pc = (blkPl_596).base + 64#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dirA)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 dir.length)
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (bytesAt dirRo dirA dir ∗ A.pool lim st s ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptr0 : BitVec 64), ptr0 ≠ 0#64 →
      sm.pc = (blkPl_596).base + 120#64 → sm.status = .Running → sm.sp = fsp →
      sm.trace = s0.trace → sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length → sm.readReg64 .x21 = nameA →
      sm.readReg64 .x22 = BitVec.ofNat 64 dir.length → sm.readReg64 .x23 = ptr0 →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir ∗
          bytesAt dirRo dirA dir ∗
          A.pool lim (M.stepEvents (pathToOwnedEvents dir.length) st) sm ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  subst hP
  rcases (show dir = [] ∨ 0 < dir.length by cases dir <;> simp) with rfl | hdir_pos
  · apply sepWPp_seq_lscro hcrl (mid := (blkPl_596).base + 120#64)
    wp_steps_sync_pool ((blkPl_596).base + 120#64)
    apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl1
    refine SepWPp.weaken_pre ?_
      (hnext _ 1#64 (by decide) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) hcrl1)
    simp only [vecU8RestAt, pathToOwnedEvents, List.length_nil, ↓reduceIte, M.stepEvents_nil,
      BitVec.ofNat_eq_ofNat, emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hdir_lt64 : dir.length < 2 ^ 64 := by omega
    have hdir_beq0 : (BitVec.ofNat 64 dir.length == 0#64) = false :=
      ofNat_beq_zero_false hdir_pos hdir_lt64
    have hdir_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt64]
    have hdir_ne0 : dir.length ≠ 0 := Nat.ne_of_gt hdir_pos
    have hlay : RustLayoutOk dir.length 1 := ⟨⟨hdir_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hfit_alloc : FitsEvents M lim st (rustAllocEvents dir.length 1) := by
      simpa only [pathToOwnedEvents, hdir_ne0, ↓reduceIte] using hfit
    rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt]
    apply sepWPp_seq_lscro hcrl (mid := lsρ lsRustNoAllocShimSymCli)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl1
    refine step_shim_call_p hshim hcrl1 (fsp := fsp) (ret_pc := (blkPl_596).base + 84#64)
      (F := bytesAt dirRo dirA dir ∗ A.pool lim st _ ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by sep_ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hvm1 hcs1 hcs_s1 hcrl_s1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, _⟩
    simp only [arm64_norm, wp_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx24_1
    rw [← A.pool_of_vmPreserved hvm1]
    apply sepWPp_seq_lscro hcrl_s1 (mid := lsρ lsRustAllocSymCli)
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl2
    refine step_alloc_no_oom_call_p halloc hcrl2 (size := dir.length) (st := st)
      (fsp := fsp) (ret_pc := (blkPl_596).base + 100#64)
      (F := bytesAt dirRo dirA dir ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *]; try rfl)
      hlay hfit_alloc
      (hcs_s1.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by sep_ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hptr_ne0 htr2 hcs2 hcs_s2 hcrl_s2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, _⟩
    simp only [arm64_norm, wp_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx24_2
    have hptr_beq0 : (s2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hptr_ne0
    apply sepWPp_seq_lscro hcrl_s2 (mid := lsρ memcpyName)
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl3
    refine step_memcpy_ro_call_p hmc_dir hcrl3
      (dst := s2.readReg64 Reg.x0) (src := dirA) (fsp := fsp)
      (ret_pc := (blkPl_596).base + 120#64) (bs := dir)
      (F := A.pool lim (M.stepEvents (rustAllocEvents dir.length 1) st) _ ∗
        A.live (s2.readReg64 Reg.x0) dir.length 1 ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by omega)
      (hcs_s2.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hvm3 hcs3 hcs_s3 hcrl_s3
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, _⟩
    simp only [arm64_norm, wp_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
    rw [← A.pool_of_vmPreserved hvm3]
    have hcap0_ne : BitVec.ofNat 64 dir.length ≠ 0#64 := ofNat_ne_zero hdir_pos hdir_lt64
    have hrest_eq :
        A.live (s2.readReg64 Reg.x0) dir.length 1 ∗ ((s2.readReg64 Reg.x0) ↦ₛ dir) =
          vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) (s2.readReg64 Reg.x0) dir := by
      simp only [vecU8RestAt, BitVec.ofNat_eq_ofNat, hcap0_ne, ↓reduceIte, hdir_toNat,
        Nat.sub_self, memRegion_zero, sepConj_emp]
      rfl
    refine SepWPp.weaken_pre ?_
      (hnext s3 (s2.readReg64 Reg.x0) hptr_ne0
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs_s3 hcrl_s3)
    simp only [pathToOwnedEvents, hdir_ne0, ↓reduceIte]
    rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt, ← hrest_eq]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem step_push_slash_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack stk : Nat} {st : M.σ}
    {s0 s : State} {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA ptr0 v1 v2 v3 ret_lr : BitVec 64} {dir name : List (BitVec 8)}
    (hres : subroutine_ok (lsProg_596 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64) (hdir_lt : dir.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (pathPushSlashEvents dir.length)) (hptr0 : ptr0 ≠ 0#64)
    (hpc : s.pc = (blkPl_596).base + 120#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 dir.length)
    (hx23 : s.readReg64 .x23 = ptr0) (hcs : PathCalleeSavedP s0 s)
    (hP : P = (((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
      vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir ∗ A.pool lim st s ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptr1 : BitVec 64),
      let cap1 := BitVec.ofNat 64 (pathSlashCap dir.length)
      dir.length + 1 ≤ cap1.toNat → cap1.toNat < 2 ^ 34 → cap1.toNat = pathSlashCap dir.length →
      sm.pc = (blkPl_596).base + 180#64 → sm.status = .Running → sm.sp = fsp →
      sm.trace = s0.trace → sm.readReg64 .x9 = cap1 - BitVec.ofNat 64 (dir.length + 1) →
      sm.readReg64 .x19 = ret → sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x21 = nameA → sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((vecU8At A.repAlloc (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗
          A.pool lim (M.stepEvents (pathPushSlashEvents dir.length) st) sm ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  subst hP
  have hdir_lt64 : dir.length < 2 ^ 64 := by omega
  have hdir_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt64]
  rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
  apply sepWPp_seq_lscro hcrl (mid := lsmpl.base 561)
  wp_steps_sync_pool (lsmpl.base 561)
  apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl1
  have hvec0 :
      ((fsp + 8#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        ((fsp + 16#64) ↦₆₄ ptr0) ∗
        ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A.repAlloc (BitVec.ofNat 64 dir.length) ptr0 dir =
      vecU8At A.repAlloc (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir := by
    have h0 := vecU8At_of_header_rest A.repAlloc (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir
      (by omega) (by omega) hptr0
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h0
  have hbound1 : reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1 + 1 ≤ 2 ^ 63 := by
    simp only [reserveCap, hdir_toNat]; omega
  have hevs1 := doReserveEvents_push_slash (fsp + 8#64) ptr0 dir hdir_lt64
  have hfit_res1 :
      FitsEnv M lim st
        (DoReserveEnv (DoReserveCall.mk (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir 1)) := by
    rw [fitsEnv_doReserve_iff, hevs1]
    exact hfit
  refine step_cli_reserve_call_p hres hcrl1 hbound1 hfit_res1
    (v := fsp + 8#64) (curCap := BitVec.ofNat 64 dir.length) (curPtr := ptr0)
    (fsp := fsp) (ret_pc := (blkPl_596).base + 152#64) (curBs := dir) (additional := 1)
    (F := memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
      (max resStack extHookStack - resStack) ∗ F)
    (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) hfsp_align
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]; try rfl)
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by rw [← hvec0]; sep_ac_rfl) ?_
  intro s1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1 hcrl_s1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _⟩
  simp only [arm64_norm, wp_norm, *] at hx19_1 hx20_1 hx21_1
  rw [hevs1, hdir_toNat]
  change SepWPp (lsProg_596 H) ret_lr s1
    ((vecU8At A.repAlloc (fsp + 8#64) (BitVec.ofNat 64 (pathSlashCap dir.length)) ptr1 dir ∗
      A.pool lim (M.stepEvents (pathPushSlashEvents dir.length) st) s1 ∗ stackAt fsp resStack) ∗
      (memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
        (max resStack extHookStack - resStack) ∗ F)) Q (pathOnPanicP A lim stk x0 s0 R)
  set cap1 : BitVec 64 := BitVec.ofNat 64 (pathSlashCap dir.length)
  have hlt64 : pathSlashCap dir.length < 2 ^ 64 := by simp only [pathSlashCap, reserveCap]; omega
  have hcap1_eq : cap1.toNat = pathSlashCap dir.length := by
    simp only [cap1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hcap1_lt34 : cap1.toNat < 2 ^ 34 := by rw [hcap1_eq]; simp only [pathSlashCap, reserveCap]; omega
  have hcap1_ge : dir.length + 1 ≤ cap1.toNat := by
    rw [hcap1_eq]; simp only [pathSlashCap, reserveCap]; omega
  simp only [vecU8At_eq_header_rest A.repAlloc (fsp + 8#64) cap1 ptr1 dir, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
  have hback1 :
      ((fsp + 8#64) ↦₆₄ cap1) ∗ (((fsp + 8#64) + 8#64) ↦₆₄ ptr1) ∗
        (((fsp + 8#64) + 16#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A.repAlloc cap1 ptr1 dir ∗
        A.pool lim (M.stepEvents (pathPushSlashEvents dir.length) st) s1 ∗ stackAt fsp resStack ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F =
      vecU8At A.repAlloc (fsp + 8#64) cap1 ptr1 dir ∗
        A.pool lim (M.stepEvents (pathPushSlashEvents dir.length) st) s1 ∗ stackAt fsp resStack ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F := by
    rw [← vecU8At_of_header_rest A.repAlloc (fsp + 8#64) cap1 ptr1 dir hle_v1 hlt_v1 hptr1]; sep_ac_rfl
  rw [hback1,
    vecU8At_expose_slice A.repAlloc (fsp + 8#64) cap1 ptr1 dir 1 hcap1_ge (by omega) hptr1 (by decide),
    memRegion_1_eq_pointsTo8]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => ?_
  apply sepWPp_seq_lscro hcrl_s1 (mid := (blkPl_596).base + 180#64)
  wp_steps_sync_pool ((blkPl_596).base + 180#64)
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl2
  have hadd1 : BitVec.ofNat 64 dir.length + 1#64 = BitVec.ofNat 64 (dir.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hpack1 := vecU8At_pack_slice A.repAlloc (fsp + 8#64) cap1 ptr1 dir [0x2f#8]
    (by simpa using hcap1_ge) (by omega) hptr1 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_singleton] at hpack1
  refine SepWPp.weaken_pre ?_
    (hnext _ ptr1 hcap1_ge hcap1_lt34 hcap1_eq
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hcs_s1.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) hcrl2)
  rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt,
    pointsTo8_eq_singleton, ← hpack1]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem step_copy_name_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack stk : Nat} {st : M.σ}
    {s0 s : State} {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA cap2 ptr2 ret_lr : BitVec 64} {dir name : List (BitVec 8)} {nameRo : Bool}
    (hmc_name : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtBudgetSpecX nameRo)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64) (hname_lt : name.length < 2 ^ 32)
    (hne : name ≠ []) (hle : (dir.length + 1) + name.length ≤ cap2.toNat)
    (hcap2 : cap2.toNat < 2 ^ 63) (hptr2 : ptr2 ≠ 0#64)
    (hpc : s.pc = (blkPl_596).base + 192#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1))
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (vecU8At A.repAlloc (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]) ∗
      bytesAt nameRo nameA name ∗ A.pool lim st s ∗ stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (v_len : BitVec 64),
      sm.pc = (blkPl_596).base + 212#64 → sm.status = .Running → sm.sp = fsp →
      sm.trace = s0.trace → sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
          vecU8RestAt A.repAlloc cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
          bytesAt nameRo nameA name ∗ A.pool lim st sm ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  subst hP
  have hpos : 0 < name.length := List.length_pos_of_ne_nil hne
  have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  rw [vecU8At_expose_slice A.repAlloc (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]) name.length
      (by simpa [hlen1] using hle) hcap2 hptr2 hpos,
    stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1]
  apply sepWPp_seq_lscro hcrl (mid := lsρ memcpyName)
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl1
  refine step_memcpy_ro_call_p
      (dst := ptr2 + BitVec.ofNat 64 (dir.length + 1)) (src := nameA) (fsp := fsp)
      (ret_pc := (blkPl_596).base + 212#64) (bs := name) hmc_name hcrl1
      (F := ((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗
        ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
        A.repAlloc.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
          (cap2.toNat - (dir.length + 1) - name.length) ∗ A.pool lim st _ ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by omega)
      (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hvmm hcsm hcs_s0 hcrlm
  rcases hcsm with ⟨hx19m, hx20m, _, hx22m, _⟩
  simp only [arm64_norm, wp_norm, *] at hx19m hx20m hx22m
  rw [← A.pool_of_vmPreserved hvmm]
  have hcap2_ne : cap2 ≠ 0 := by intro h0; subst h0; simp at hle
  have htot_len : (dir ++ [0x2f#8] ++ name).length = dir.length + 1 + name.length := by simp; omega
  have htot_bv :
      ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
        ptr2 + BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length := by
    rw [htot_len, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrest2 :
      A.repAlloc.live ptr2 cap2.toNat 1 ∗
        ((ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗ ((ptr2 + BitVec.ofNat 64 (dir.length + 1)) ↦ₛ name)) ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
          (cap2.toNat - (dir.length + 1) - name.length) =
      vecU8RestAt A.repAlloc cap2 ptr2 (dir ++ [0x2f#8] ++ name) := by
    have happ := pointsToBytes_append ptr2 (dir ++ [0x2f#8]) name
    rw [hlen1] at happ; rw [← happ, htot_bv]
    simp only [vecU8RestAt, hcap2_ne, ↓reduceIte, htot_len, Nat.sub_sub]
  refine SepWPp.weaken_pre ?_
    (hnext sm (BitVec.ofNat 64 (dir.length + 1)) hpcm hrunm hspm htrm hx19m hx20m hx22m hcs_s0 hcrlm)
  rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt, ← hrest2]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem step_append_name_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack stk : Nat} {st : M.σ}
    {s0 s : State} {x0 : PathGhost × M.σ} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA ptr1 ret_lr : BitVec 64} {dir name : List (BitVec 8)} {nameRo : Bool}
    (hres : subroutine_ok (lsProg_596 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hmc_name : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (session2MemcpyBytesAtBudgetSpecX nameRo)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64) (hname_lt : name.length < 2 ^ 32)
    (hcap1_ge : dir.length + 1 ≤ (BitVec.ofNat 64 (pathSlashCap dir.length)).toNat)
    (hcap1_lt : (BitVec.ofNat 64 (pathSlashCap dir.length)).toNat < 2 ^ 34)
    (hcap1_eq : (BitVec.ofNat 64 (pathSlashCap dir.length)).toNat = pathSlashCap dir.length)
    (hfit : FitsEvents M lim st (pathAppendNameEvents dir.length name.length))
    (hpc : s.pc = (blkPl_596).base + 180#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx9 : s.readReg64 .x9 =
      BitVec.ofNat 64 (pathSlashCap dir.length) - BitVec.ofNat 64 (dir.length + 1))
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1))
    (hcs : PathCalleeSavedP s0 s)
    (hP : P = (vecU8At A.repAlloc (fsp + 8#64) (BitVec.ofNat 64 (pathSlashCap dir.length))
        ptr1 (dir ++ [0x2f#8]) ∗
      bytesAt nameRo nameA name ∗ A.pool lim st s ∗ stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 v_len : BitVec 64),
      (dir ++ [0x2f#8] ++ name).length ≤ cap2.toNat → cap2.toNat < 2 ^ 63 → ptr2 ≠ 0#64 →
      sm.pc = (blkPl_596).base + 212#64 → sm.status = .Running → sm.sp = fsp →
      sm.trace = s0.trace → sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      PathCalleeSavedP s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_596 H) ret_lr sm
        ((((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
          vecU8RestAt A.repAlloc cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
          bytesAt nameRo nameA name ∗
          A.pool lim (M.stepEvents (pathAppendNameEvents dir.length name.length) st) sm ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanicP A lim stk x0 s0 R)) :
    SepWPp (lsProg_596 H) ret_lr s P Q (pathOnPanicP A lim stk x0 s0 R) := by
  subst hP
  set cap1 : BitVec 64 := BitVec.ofNat 64 (pathSlashCap dir.length)
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  have hult_iff := elem_len_ult_spare_iff (cap := cap1) (bsLen := dir.length + 1)
    (elemLen := name.length) hcap1_ge (by omega) (by omega)
  by_cases hgrow : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = true
  · have hlt_cap : cap1.toNat < (dir.length + 1) + name.length := hult_iff.mp hgrow
    have hlt_cap' : pathSlashCap dir.length < (dir.length + 1) + name.length := by
      rwa [← hcap1_eq]
    have hname_pos : 0 < name.length := by omega
    have hne : name ≠ [] := List.ne_nil_of_length_pos hname_pos
    have hlen1_toNat : (BitVec.ofNat 64 (dir.length + 1)).toNat = dir.length + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
    apply sepWPp_seq_lscro hcrl (mid := lsmpl.base 561)
    wp_steps_sync_pool (lsmpl.base 561)
    apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl1
    have hbound2 : reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length + 1 ≤ 2 ^ 63 := by
      simp only [reserveCap, hlen1]; omega
    have hevs2 := doReserveEvents_append_name (fsp + 8#64) ptr1 dir name hlt_cap'
      (by rw [← hcap1_eq]; omega)
    have hfit_res2 :
        FitsEnv M lim st
          (DoReserveEnv (DoReserveCall.mk (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) name.length)) := by
      rw [fitsEnv_doReserve_iff]
      dsimp only [cap1]
      rw [hevs2]
      exact hfit
    refine step_cli_reserve_call_p hres hcrl1 hbound2 hfit_res2
      (v := fsp + 8#64) (curCap := cap1) (curPtr := ptr1) (fsp := fsp)
      (ret_pc := (blkPl_596).base + 284#64) (curBs := dir ++ [0x2f#8]) (additional := name.length)
      (F := bytesAt nameRo nameA name ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F)
      (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by sep_ac_rfl) ?_
    intro s1 ptr2 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1 hcrl_s1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _⟩
    simp only [arm64_norm, wp_norm, *] at hx19_1 hx20_1 hx21_1
    have hevs2' :
        doReserveEvents (DoReserveCall.mk (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) name.length) =
          pathAppendNameEvents dir.length name.length := hevs2
    rw [hevs2']
    set cap2 : BitVec 64 := BitVec.ofNat 64 (reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length)
    have hcap2_lt : cap2.toNat < 2 ^ 63 := by
      simp only [cap2, reserveCap, hlen1, BitVec.toNat_ofNat]; omega
    have hcap2_ge : (dir.length + 1) + name.length ≤ cap2.toNat := by
      have hlt64 : reserveCap cap1.toNat (dir.length + 1) name.length < 2 ^ 64 := by
        simp only [reserveCap]; omega
      simp only [cap2, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, reserveCap]; omega
    simp only [vecU8At_eq_header_rest A.repAlloc (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]),
      BitVec.add_assoc, BitVec.reduceAdd, hlen1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_v2, hlt_v2, hptr2⟩ => ?_
    apply sepWPp_seq_lscro hcrl_s1 (mid := (blkPl_596).base + 192#64)
    wp_steps_sync_pool ((blkPl_596).base + 192#64)
    apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hcrl2
    refine step_copy_name_p (ret := ret) (nameA := nameA)
      (st := M.stepEvents (pathAppendNameEvents dir.length name.length) st)
      hmc_name hcrl2 hsub_lt hname_lt hne hcap2_ge hcap2_lt hptr2 (F := F)
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) hfsp_align
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hcs_s1.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]))
      (by rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
          have hhdr := vecU8At_of_header_rest A.repAlloc (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8])
            (by omega) hlt_v2 hptr2
          simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1] at hhdr
          rw [← hhdr]; sep_ac_rfl) ?_
    intro sm v_len hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm cap2 ptr2 v_len (by simp; omega) hcap2_lt hptr2
        hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm)
  · have hgrow_f : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = false :=
      Bool.eq_false_iff.mpr hgrow
    have hfit_cap : (dir.length + 1) + name.length ≤ cap1.toNat := by
      have := mt hult_iff.mpr hgrow; omega
    have hnot_lt : ¬ (pathSlashCap dir.length < (dir.length + 1) + name.length) := by
      rw [← hcap1_eq]; omega
    have hevs_nil : pathAppendNameEvents dir.length name.length = [] := by
      simp only [pathAppendNameEvents, hnot_lt, ↓reduceIte]
    simp only [vecU8At_eq_header_rest A.repAlloc (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]), sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
    have hrepack1 :
        ((fsp + 8#64) ↦₆₄ cap1) ∗ (((fsp + 8#64) + 8#64) ↦₆₄ ptr1) ∗
          (((fsp + 8#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ [0x2f#8]).length) ∗
          vecU8RestAt A.repAlloc cap1 ptr1 (dir ++ [0x2f#8]) ∗ bytesAt nameRo nameA name ∗
          A.pool lim st s ∗ stackAt fsp (max resStack extHookStack) ∗ F =
        (vecU8At A.repAlloc (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗ bytesAt nameRo nameA name ∗
          A.pool lim st s ∗ stackAt fsp (max resStack extHookStack)) ∗ F := by
      rw [← vecU8At_of_header_rest A.repAlloc (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])
        hle_v1 hlt_v1 hptr1]; sep_ac_rfl
    rw [hrepack1]
    rcases (show name = [] ∨ 0 < name.length by cases name <;> simp) with rfl | hname_pos
    · apply sepWPp_seq_lscro hcrl (mid := (blkPl_596).base + 212#64)
      wp_steps_sync_pool ((blkPl_596).base + 212#64)
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl1
      refine SepWPp.weaken_pre ?_
        (hnext _ cap1 ptr1 (BitVec.ofNat 64 (dir.length + 1)) (by simpa using hfit_cap) (by omega) hptr1
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
          (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) hcrl1)
      have hhdr1 := vecU8At_of_header_rest A.repAlloc (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])
        hle_v1 hlt_v1 hptr1
      simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1] at hhdr1
      rw [← hhdr1, List.append_nil, hevs_nil, M.stepEvents_nil]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hname_beq0 : (BitVec.ofNat 64 name.length == 0#64) = false :=
        ofNat_beq_zero_false hname_pos (by omega)
      have hne : name ≠ [] := List.ne_nil_of_length_pos hname_pos
      apply sepWPp_seq_lscro hcrl (mid := (blkPl_596).base + 192#64)
      wp_steps_sync_pool ((blkPl_596).base + 192#64)
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl1
      refine step_copy_name_p (ret := ret) (nameA := nameA) (st := st)
        hmc_name hcrl1 hsub_lt hname_lt hne hfit_cap (by omega) hptr1 (F := F)
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) hfsp_align
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (hcs.trans (by simp only [PathCalleeSavedP, arm64_norm, wp_norm])) (by sep_ac_rfl) ?_
      intro sm v_len hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm
      rw [hevs_nil, M.stepEvents_nil] at hnext
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sm cap1 ptr1 v_len (by simp; omega) (by omega) hptr1
          hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm hcrlm)

/-! ## 5. Top-Level Relocatable Budget Theorems -/

/-- Core `[LibsignalPlacement]` theorem proving `pathSpecPlaced A lim PathEnv stk` on Block `596`
from an `lsProg_596 H` read-only `memcpy` contract. -/
theorem path_placed_ok_of_ro596 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resProg : Program} {resBlk : Nat} [IsLsBlockProg resProg resBlk H]
    {resStack stk : Nat} (hC : AllocContractsXCliPlaced A lim H)
    (hRO596 : subroutine_ok (lsProg_596 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved sessionMemcpyRegionROSpec) extHookStack)))
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hstk : 0x70 + max resStack extHookStack ≤ stk) (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_596 H) (lsmpl.base 596) (pathSpecPlaced A lim PathEnv stk) := by
  have hres596 := ls_transfer_lscro (callerProg := lsProg_596 H) (i := 596) (j := resBlk) hRes
    (by decide) hresBlk hresUnmut
  have hshim := shim_lscro_of_cli (callerProg := lsProg_596 H) (i := 596) (stk := extHookStack) hC
  have halloc := allocNoOomExtern_lscro_of_cli (callerProg := lsProg_596 H) (i := 596) hC
  change subroutine_ok (lsProg_596 H) (blkPl_596).base (pathSpecPlaced A lim PathEnv stk)
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨dirA, dir, dirRo, nameA, name, nameRo, ret⟩, st⟩ R s0 hpc hrun hpre halign
  have hmc_dir := memcpy_bytesAt_placed_ok_of_ro hC hRO596 dirRo
  have hmc_name := memcpy_bytesAt_placed_ok_of_ro hC hRO596 nameRo
  obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜s0.readReg64 .x0 = ret ∧ s0.readReg64 .x1 = dirA ∧ (s0.readReg64 .x2).toNat = dir.length ∧
      s0.readReg64 .x3 = nameA ∧ (s0.readReg64 .x4).toNat = name.length ∧
      dir.length < 2 ^ 32 ∧ name.length < 2 ^ 32 ∧ FitsEnv M lim st (PathEnv dir name)⌝ ∗
      bytesAt dirRo dirA dir ∗ bytesAt nameRo nameA name ∗ memRegion ret 24 ∗
      stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hdir_lt, hname_lt, hfit_env⟩, hmem⟩
  have hfit_all : FitsEvents M lim st (pathEvents dir name) := (fitsEnv_path_iff dir name).mp hfit_env
  obtain ⟨hfit_own, hfit_rest⟩ := (fitsEvents_append M lim (pathToOwnedEvents dir.length)
    (pathPushSlashEvents dir.length ++ pathAppendNameEvents dir.length name.length) st).mp hfit_all
  obtain ⟨hfit_slash, hfit_app⟩ := (fitsEvents_append M lim (pathPushSlashEvents dir.length)
    (pathAppendNameEvents dir.length name.length)
    (M.stepEvents (pathToOwnedEvents dir.length) st)).mp hfit_rest
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 dir.length := bv_eq_ofNat_of_toNat hx2_nat
  have hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 name.length := bv_eq_ofNat_of_toNat hx4_nat
  have hmem_stk : s0.mem ⊨ memRegion ret 24 ∗ stackAt s0.sp stk ∗
      (bytesAt dirRo dirA dir ∗ bytesAt nameRo nameA name ∗ A.pool lim st s0 ∗ R) := by
    convert hmem using 1; sep_ac_rfl
  have hstk_lt : stk < 2 ^ 64 := stk_lt_two_pow_64 hmem_stk
  have hsub_lt : max resStack extHookStack ≤ 2 ^ 64 := by omega
  have halign64 : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using halign
  refine ⟨bytesAt dirRo dirA dir ∗ bytesAt nameRo nameA name ∗ memRegion ret 24 ∗
    stackAt s0.sp stk ∗ A.pool lim st s0, R, hmem, ?_⟩
  have hbit63 : (BitVec.ofNat 64 dir.length).getLsbD 63 = false := ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 dir.length)[63] = false := ofNat_getElem_63_false (by omega)
  rw [stackAt_split_ge s0.sp hstk (by omega), stackAt_path_frame s0.sp (by omega)]
  generalize hfsp : s0.sp - 112#64 = fsp
  have hfsp_align : fsp &&& 15#64 = 0#64 := by rw [← hfsp]; exact sp_sub_112_aligned halign64
  rw [memRegion_24_cells ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 => SepWPp.exists_elim fun r2 => ?_
  rw [cells_14_eq fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
    SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 =>
    SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
    SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 =>
    SepWPp.exists_elim fun v12 => SepWPp.exists_elim fun v13 => ?_
  apply sepWPp_seq_lscro hcrl0 (mid := (blkPl_596).base + 4#64)
  wp_steps_sync_pool ((blkPl_596).base + 4#64)
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl_sp
  apply sepWPp_seq_lscro hcrl_sp (mid := (blkPl_596).base + 64#64)
  wp_steps_sync_pool ((blkPl_596).base + 64#64)
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl_pro
  set savedFrame : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
    (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗ (fsp ↦₆₄ v0) ∗
    ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
    ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    with hsaved_def
  clear_value savedFrame
  refine step_to_owned_p (ret := ret) (dirA := dirA) (nameA := nameA) (name := name) (st := st)
    hshim halloc hmc_dir hcrl_pro hsub_lt hdir_lt hfit_own
    (F := ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
      bytesAt nameRo nameA name ∗ savedFrame)
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) hfsp_align
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    (by simp only [PathCalleeSavedP, arm64_norm, wp_norm]) (by rw [hsaved_def]; sep_ac_rfl) ?_
  intro s1 ptr0 hptr0 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 hcrl1
  refine step_push_slash_p hres596 hcrl1 hsub_lt hdir_lt hfit_slash hptr0
    (v1 := v1) (v2 := v2) (v3 := v3)
    (F := bytesAt dirRo dirA dir ∗ bytesAt nameRo nameA name ∗ savedFrame)
    hpc1 hrun1 hsp1 hfsp_align htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 (by sep_ac_rfl) ?_
  intro s2 ptr1 cap1 hcap1_ge hcap1_lt hcap1_eq hpc2 hrun2 hsp2 htr2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hcrl2
  refine step_append_name_p hres596 hmc_name hcrl2 hsub_lt hname_lt hcap1_ge hcap1_lt hcap1_eq hfit_app
    (F := bytesAt dirRo dirA dir ∗ savedFrame)
    hpc2 hrun2 hsp2 hfsp_align htr2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 (by sep_ac_rfl) ?_
  intro s3 cap2 ptr2 v_len hcap2_ge hcap2_lt hptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx22_3 hcs3 _hcrl3
  rcases hcs3 with ⟨hx26_3, hx27_3, hx28_3, hvregs_3⟩
  rw [hsaved_def]
  have hst_final :
      M.stepEvents (pathAppendNameEvents dir.length name.length)
        (M.stepEvents (pathPushSlashEvents dir.length)
          (M.stepEvents (pathToOwnedEvents dir.length) st)) =
      M.stepEvents (pathEvents dir name) st := by
    unfold pathEvents; rw [M.stepEvents_append, M.stepEvents_append]
  rw [hst_final]
  have hq_pre :
      (((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
        vecU8RestAt A.repAlloc cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗ bytesAt nameRo nameA name ∗
        A.pool lim (M.stepEvents (pathEvents dir name) st) s3 ∗
        stackAt fsp (max resStack extHookStack)) ∗ bytesAt dirRo dirA dir ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
          (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗ (fsp ↦₆₄ v0) ∗
          ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
      (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
        vecU8RestAt A.repAlloc cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
        bytesAt dirRo dirA dir ∗ bytesAt nameRo nameA name ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
        stackAt fsp (max resStack extHookStack) ∗
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
        ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        A.pool lim (M.stepEvents (pathEvents dir name) st) s3 := by sep_ac_rfl
  have hs3_spAligned : s3.spAligned = true := by simp [State.spAligned, hsp3, hfsp_align]
  rw [hq_pre]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWPp.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  refine ⟨?_, ?_, by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, *]⟩
  · intro hPR
    have htot_bv :
        BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
          BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length := by
      simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add]
    have hvec_out :
        (ret ↦₆₄ cap2) ∗ ((ret + 8#64) ↦₆₄ ptr2) ∗
          ((ret + 16#64) ↦₆₄ (BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)) ∗
          vecU8RestAt A.repAlloc cap2 ptr2 (dir ++ [0x2f#8] ++ name) =
        vecU8At A.repAlloc ret cap2 ptr2 (dir ++ [0x2f#8] ++ name) := by
      rw [htot_bv]
      exact vecU8At_of_header_rest A.repAlloc ret cap2 ptr2 (dir ++ [0x2f#8] ++ name)
        hcap2_ge hcap2_lt hptr2
    change _ ⊨ (∃∗ evs : List AllocEvent,
      ⌜_ = s0.trace ∧ PathEnv dir name evs⌝ ∗ vecU8 A.repAlloc ret (dir ++ [0x2f#8] ++ name) ∗
      bytesAt dirRo dirA dir ∗ bytesAt nameRo nameA name ∗ stackAt s0.sp stk ∗
      A.pool lim (M.stepEvents evs st) _) ∗ R
    simp only [vecU8, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨pathEvents dir name, cap2, ptr2, ⟨by simp only [arm64_norm, wp_norm, *], rfl⟩, ?_⟩
    rw [stackAt_split_ge s0.sp hstk (by omega), stackAt_path_frame s0.sp (by omega),
      hfsp, cells_14_eq fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc]
    refine ⟨v0, cap2, ptr2, BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 25#5), v7,
      s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
    rw [← hvec_out]; exact Eq.mp (by sep_ac_rfl) hPR
  · simp only [arm64_norm, wp_norm, ← hfsp, fsp_add_112_eq]

/-- Core `[LibsignalPlacement]` theorem proving `pathSpecPlaced A lim PathEnv stk` on Block `596`
from `HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)`. -/
theorem path_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resProg : Program} {resBlk : Nat} [IsLsBlockProg resProg resBlk H]
    {resStack stk : Nat} (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hstk : 0x70 + max resStack extHookStack ≤ stk) (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_596 H) (lsmpl.base 596) (pathSpecPlaced A lim PathEnv stk) :=
  path_placed_ok_of_ro596 hC (ro596_of_hookSat hRO) hRes hstk hresBlk hresUnmut

/-- Caller-transferable `[LibsignalPlacement]` `path` contract for any block `< 619`
from `HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec)`. -/
theorem path_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg resProg : Program} {i resBlk : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg resProg resBlk H] {resStack stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hstk : 0x70 + max resStack extHookStack ≤ stk) (hi : i < 619 := by decide)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 596) (pathSpecPlaced A lim PathEnv stk) :=
  ls_transfer_lscro (callerProg := callerProg) (i := i) (j := 596)
    (path_placed_ok_of_deps hC hRO hRes hstk hresBlk hresUnmut) hi

/-- Caller-transferable `[LibsignalPlacement]` `path` contract for any block `< 619`
discharging both `AllocContractsXCliPlaced` and read-only `memcpy` from `AllocContractsFsPlaced`. -/
theorem path_placed_caller_ok_of_allocFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg resProg : Program} {i resBlk : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg resProg resBlk H] {resStack stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hstk : 0x70 + max resStack extHookStack ≤ stk) (hi : i < 619 := by decide)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 596) (pathSpecPlaced A lim PathEnv stk) :=
  ls_transfer_lscro (callerProg := callerProg) (i := i) (j := 596)
    (path_placed_ok_of_ro596 (toAllocContractsX hFs)
      (ls_transfer_lscro (callerProg := lsProg_596 H) (i := 596) (j := 617)
        (subroutine_ok_withLsCodeRoLoaded_of_keepsFs
          (hFs.session_memcpy_region_ro extHookStack (by decide) (by decide)))
        (by decide))
      hRes hstk hresBlk hresUnmut) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
