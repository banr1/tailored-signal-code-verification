/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable Branch Helpers for `save_identity::{closure#0}`

Lifts `PublicKey::serialize` (Block 205), `SepWPp` callee combinators, and Block `565` epilogue
and branch lemmas to preserve `FdsGe3Closed` (`withFdsGe3Closed` outside `withLsCodeRoLoaded`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey djbType)
open CryptoGames.LibsignalSessionApi (IdentityChange)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_205 blkPl_205 lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr
  (okTagVec protocolAddressAt speWord utf8 vecResultAt)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (publicKeyEqSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
   withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (decodeIdentityKey)
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyResultAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGetGhost DirGhost DirPutStrGhost IdPeerAns IdPollGhost ReadRule dirAt getResultAt
   idSaveBoxAt idSaveOf idSaveOutAt idSavePeers pathOf)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_565 blkPl_565)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
  (boxU8Buf_to_vecU8_33 calleeSavedVRegs_writeVReg128_0 epilogueOut epilogueOut_err_reassemble
   epilogueOut_ok_reassemble epiloguePre fs_advancePC fs_applyWriteback fs_setMem fs_setPC
   fs_setPState fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128 ispoll_sp_eqs
   offAfterDecode offAfterDealloc offAfterEq offAfterGet offAfterPut offAfterSer offEpiLdur11
   offEpiStr44 offEpilogue offErrLdr60 offErrShuffle offErrStur11 offOkTail out_add_eqs
   overlap7View1 overlap7View2 overlap7_realign protocolAddressAt_borrow putStk_le_saveSubMax
   restore_savePollStack s48_byte7_entails_memRegion16 s48_split_byte7 saveMinStk saveSubMax
   savedCalleeSlots sepWP_conseq sepWPp_conseq sepWPp_of_sepWP_final serStk_le_saveSubMax
   slot90_split_vec24 speAt_read_invalidState_unpack sret48_epilogue_split
   stackAt_64_eq_publicKeyEq_frames stackAt_sub_split)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   NullAllowed RustCliAllocBudget RustLayoutOk SeqEnv not_nullAllowed_of_fitsAllocEvents
   rustAllocEvents rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetExternSpecWithStack
   rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
   rustCliDeallocBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents publicKeySerializeSpecWithStack
   publicKeySerializeSpecX publicKeySerializeStackX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocNoOomExternSpecWithStack rustAllocSpecWithStack rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (shim_keepsFs_lscro_of_fs subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced dirPutStrSpecPlaced idSavePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (ispoll_call_total_raw_placed)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0
  fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState
  fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128
  offAfterGet offAfterDecode offAfterDealloc offAfterEq offErrShuffle offErrLdr60 offErrStur11
  offOkTail offAfterSer offAfterPut offEpilogue offEpiLdur11 offEpiStr44

/-! ## 1. `.keepsFs` / `withFdsGe3Closed` `<PublicKey>::serialize` (Block `205`) -/

private theorem memRegion_33_cells_p (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗
        ((a + 17#64) ↦₆₄ u1) ∗ ((a + 25#64) ↦₆₄ u0)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 32) (b' := a + 1#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 1#64) (n := 8) (k := 24) (b' := a + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 9#64) (n := 8) (k := 16) (b' := a + 17#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 17#64) (n := 8) (k := 8) (b' := a + 25#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_one a,
    ProofLib.memRegion_eight (a + 1#64),
    ProofLib.memRegion_eight (a + 9#64),
    ProofLib.memRegion_eight (a + 17#64),
    ProofLib.memRegion_eight (a + 25#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

/-- Cross-block `.keepsFs` lift of `rustAllocNoOomExternSpecWithStack` from `AllocContractsFsPlaced`. -/
theorem allocNoOomExtern_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl
        (rustAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs) := by
  have halloc := ls_transfer_lscro (callerProg := callerProg) (j := 617) hFs.alloc hi
  refine subroutine_ok_outcome_intro fun ⟨size, align, st⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨hinv, hpre_rest⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [Spec.keepsFs, rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at hpre_rest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_rest
  rcases hpre_rest with ⟨⟨hx0, hx1, hlay, hfit, hlr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustAllocSpecWithStack M A lim false extHookStack).keepsFs).pre
        (size, align, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack]
    have h1 : s0.mem ⊨ ⌜(s0.readReg64 .x0).toNat = size ∧
        (s0.readReg64 .x1).toNat = align ∧ RustLayoutOk size align ∧
        LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          ((A.pool lim st s0 ∗ stackAt s0.sp extHookStack) ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hlay, hlr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv, hmem⟩
    convert h1 using 1; sep_ac_rfl
  refine halloc.mono_outcome (size, align, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack, rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hfs, hpost⟩
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte] at hpost
      have hnull_abs : sf.mem ⊨ ⌜NullAllowed size align⌝ ∗
          (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗ stackAt s0.sp extHookStack ∗ R) := by
        convert hpost using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj] at hnull_abs
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hfit hnull_abs.1)
    · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hpost ⊢
      have hpost' : sf.mem ⊨ ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp extHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ R)) := by
        convert hpost using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hpost'.1.2.1, h0, hpost'.2.1⟩, ?_⟩
      simpa only [sepConj_assoc] using hpost'.2.2
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

/-- `.keepsFs`-strengthened `<PublicKey>::serialize` (Block `205`) under `AllocContractsFsPlaced`,
transferred to any caller block `i < 619`. -/
theorem publicKeySerialize_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim).keepsFs) := by
  have h205 : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim).keepsFs) := by
    unfold withLsCodeRoLoaded Spec.keepsFs publicKeySerializeSpecX publicKeySerializeSpecWithStack
    simp only [PublicKey.serialize, boxU8Buf,
      ProofLib.stackAt_split_cells _ extHookStack 4 (by decide)]
    cells_unfold
    wp_init xs s0
    obtain ⟨⟨self, pk⟩, st⟩ := xs
    dsimp only at *
    have hshim := shim_keepsFs_lscro_of_fs (callerProg := (blkPC_205).rebase (blkPl_205).base H)
      hFs (stk := extHookStack)
    have halloc := allocNoOomExtern_keepsFs_lscro_of_fs
      (callerProg := (blkPC_205).rebase (blkPl_205).base H) hFs
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
    have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
    have hfit0 : FitsEnv M lim st PublicKeySerializeEnv := by assumption
    have hfit : FitsEvents M lim st (rustAllocEvents 33 1) := hfit0 _ rfl
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : RustLayoutOk 33 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (List.Vector.toList_length pk.bytes)
    rw [hpk_cells self]
    apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hshim hcrl1 ()
    refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
    apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    intro ⟨hcl2, hro2⟩
    wp_call halloc (33, 1, st)
    have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
    simp only [memRegion_33_cells_p, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
      SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
      SepWP.exists_elim fun b0 => ?_
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    have hfs_tot : sf_1.fs = s0.fs := by
      have hfs1 : sf.fs = s0.fs := by simpa only [wp_norm, arm64_norm] using ‹sf.fs = _›
      have hfs2 : sf_1.fs = sf.fs := by simpa only [wp_norm, arm64_norm] using ‹sf_1.fs = _›
      exact hfs2.trans hfs1
    simp only [List.length_cons, List.Vector.toList_length,
      List.cons_ne_nil, ite_false, djbType,
      pointsToBytes_cons, hpk_cells, publicKeySerializeEvents,
      BitVec.add_assoc, BitVec.reduceAdd]
    wp_done
  exact ls_transfer_lscro (callerProg := callerProg) (j := 205) h205 hi

/-- `withFdsGe3Closed`-threaded `<PublicKey>::serialize` (Block `205`) under
`AllocContractsFsPlaced`, transferred to any caller block `i < 619`. -/
theorem publicKeySerialize_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpecX M A lim))) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (spec := publicKeySerializeSpecX M A lim)
    (publicKeySerialize_keepsFs_lscro_of_fs (callerProg := callerProg) hFs hi)

/-! ## 2. `SepWPp` Callee Combinators with `FdsGe3Closed` -/

theorem ispoll_call_dirGet_placed_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (xg : DirGetGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hfit : FitsEnv M lim st (GetEnv s.fs.files xg.dir xg.name))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace ∧
        GetEnv s.fs.files xg.dir xg.name evs) →
      SepWPp prog ret sm
        ((getResultAt A.repAlloc xg.ret gr ∗ dirAt A.repAlloc xg.self xg.dir ∗
          bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hcall' := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed hcall
  refine ispoll_call_total_raw_placed hcall' (xg, st) F hpc hrun hsp_align hlr hinv ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded]
    simp only [sepConj_assoc]
    exact Entails.pure_right hfds
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk, hfit⟩ (Entails.refl _))
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfdsm => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gr =>
      SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs gr hpcm hrunm hspm hcsm hinvm hfdsm hgr)

theorem ispoll_call_decode_placed_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved (identityKeyDecodeRawSpec A)))))
    (xg : DecodeGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.bytesA)
    (hx1 : (s.readReg64 .x1).toNat = xg.bytes.length)
    (hx8 : s.readReg64 .x8 = xg.ret)
    (hpre : P ⊢ ((xg.bytesA ↦ₛ xg.bytes) ∗ memRegion xg.ret 48 ∗ lsLogOff ∗
      A.pool lim st s ∗ stackAt s.sp 0x60) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs → sm.trace = s.trace →
      SepWPp prog ret sm
        ((identityKeyResultAt A.repAlloc xg.ret (decodeIdentityKey xg.bytes) ∗
          (xg.bytesA ↦ₛ xg.bytes) ∗ lsLogOff ∗
          A.pool lim st sm ∗ stackAt s.sp 0x60) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hlog : lsLogOff = CryptoVerification.LibsignalTripleRatchet.lsLogOff := rfl
  refine ispoll_call_total_raw_placed hcall xg (A.pool lim st s ∗ F)
    hpc hrun hsp_align hlr hinv ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    rw [hlog]
    simp only [withFdsGe3Closed, withVmPreserved, identityKeyDecodeRawSpec, sepConj_assoc]
    exact Entails.pure_right hfds
      (Entails.pure_right ⟨hx0, hx1, hx8⟩ (Entails.of_eq (by sep_ac_rfl)))
  · intro sm R' hpost
    simp only [withFdsGe3Closed, withVmPreserved, identityKeyDecodeRawSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withFdsGe3Closed, withVmPreserved, identityKeyDecodeRawSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withFdsGe3Closed, withVmPreserved, identityKeyDecodeRawSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFdsGe3Closed, withVmPreserved, identityKeyDecodeRawSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hfdsm =>
      SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun htrm => ?_
    rw [← hlog, ← A.pool_transport lim st s sm hvm]
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfdsm htrm)

theorem ispoll_call_publicKeyEq_placed_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved publicKeyEqSpec))))
    (p1 : BitVec 64) (pk1 : PublicKey) (p2 : BitVec 64) (pk2 : PublicKey)
    (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = p1) (hx1 : s.readReg64 .x1 = p2)
    (hpre : P ⊢ ((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp 64) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs →
      sm.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) → sm.trace = s.trace →
      SepWPp prog ret sm
        (((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
          A.pool lim st sm ∗ stackAt s.sp 64) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_total_raw_placed hcall (p1, pk1, p2, pk2, s.sp) (A.pool lim st s ∗ F)
    hpc hrun hsp_align hlr hinv ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFdsGe3Closed, withVmPreserved, publicKeyEqSpec,
      ← stackAt_64_eq_publicKeyEq_frames s.sp, sepConj_assoc]
    exact Entails.pure_right hfds
      (Entails.pure_right ⟨hx0, hx1, trivial⟩ (Entails.of_eq (by sep_ac_rfl)))
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, withVmPreserved, publicKeyEqSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    dsimp only [withFdsGe3Closed, withVmPreserved, publicKeyEqSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, withVmPreserved, publicKeyEqSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFdsGe3Closed, withVmPreserved, publicKeyEqSpec,
      ← stackAt_64_eq_publicKeyEq_frames s.sp, sepConj_assoc]
    refine SepWPp.pure_elim fun hfdsm =>
      SepWPp.pure_elim fun hvm => SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    rw [← A.pool_transport lim st s sm hvm]
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfdsm hx0m htrm)

theorem ispoll_call_serialize_placed_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpecX M A lim))))
    (keyA : BitVec 64) (pk : PublicKey) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = keyA)
    (hfit : FitsEnv M lim st PublicKeySerializeEnv)
    (hpre : P ⊢ ((keyA ↦ₛ pk.bytes.toList) ∗ A.pool lim st s ∗
      stackAt s.sp publicKeySerializeStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs →
      sm.readReg64 .x1 = 33#64 → sm.trace = s.trace →
      SepWPp prog ret sm
        ((boxU8Buf A.repAlloc (sm.readReg64 .x0) pk.serialize ∗
          (keyA ↦ₛ pk.bytes.toList) ∗
          A.pool lim (M.stepEvents publicKeySerializeEvents st) sm ∗
          stackAt s.sp publicKeySerializeStackX) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_total_raw_placed hcall (⟨keyA, pk⟩, st) F
    hpc hrun hsp_align hlr hinv ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFdsGe3Closed, publicKeySerializeSpecX, publicKeySerializeSpecWithStack,
      sepConj_assoc]
    exact Entails.pure_right hfds (Entails.pure_right ⟨hx0, hfit⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [withFdsGe3Closed, publicKeySerializeSpecX, publicKeySerializeSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withFdsGe3Closed, publicKeySerializeSpecX, publicKeySerializeSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withFdsGe3Closed, publicKeySerializeSpecX, publicKeySerializeSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFdsGe3Closed, publicKeySerializeSpecX, publicKeySerializeSpecWithStack,
      sepConj_assoc]
    refine SepWPp.pure_elim fun hfdsm => SepWPp.pure_elim fun ⟨hx1m, htrm⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfdsm hx1m htrm)

theorem ispoll_call_dirPutStr_placed_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {putStk : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (xg : DirPutStrGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameA)
    (hx2 : (s.readReg64 .x2).toNat = xg.name.length) (hx3 : s.readReg64 .x3 = xg.bytesV)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.changed.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PutStrEnv xg.dir xg.name xg.bytes))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ bytesAt xg.nameRo xg.nameA xg.name ∗
      vecU8 A.repAlloc xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs →
      sm.trace = s.trace → PutStrEnv xg.dir xg.name xg.bytes evs →
      SepWPp prog ret sm
        ((dirAt A.repAlloc xg.self (xg.dir.put xg.name xg.bytes) ∗
          bytesAt xg.nameRo xg.nameA xg.name ∗
          memRegion xg.bytesV 24 ∗ stackAt s.sp putStk ∗
          A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | simp (config := { decide := true }) only [offAfterPut, Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp prog ret s P Q Qp := by
  have hcall' := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed hcall
  refine ispoll_call_total_raw_placed hcall' (xg, st) F hpc hrun hsp_align hlr hinv ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced, withLsCodeRoLoaded]
    simp only [sepConj_assoc]
    exact Entails.pure_right hfds
      (Entails.pure_right
        ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hfit, (show s.readReg64 Reg.x30 = ret_pc from hlr) ▸ hlr_ls⟩
        (Entails.refl _))
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    dsimp only [withFdsGe3Closed, dirPutStrSpecPlaced, withLsCodeRoLoaded]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfdsm => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hinvm hfdsm htrm hevs)

theorem ispoll_call_dealloc_placed_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (rustDeallocExternSpecWithStack M A lim extHookStack))))
    (ptr : BitVec 64) (size : Nat) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = 1) (hlay : RustLayoutOk size 1)
    (hpre : P ⊢ (A.pool lim st s ∗ A.live ptr size 1 ∗ memRegion ptr size ∗
      stackAt s.sp extHookStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FdsGe3Closed sm.fs → sm.trace = s.trace →
      SepWPp prog ret sm
        ((A.pool lim (M.stepEvents (rustDeallocEvents size 1) st) sm ∗
          stackAt s.sp extHookStack) ∗ F) Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | simp (config := { decide := true }) only [offAfterDealloc, Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_total_raw_placed hcall (ptr, size, 1, st) F
    hpc hrun hsp_align hlr hinv ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFdsGe3Closed, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetSpecWithStack]
    simp only [sepConj_assoc]
    exact Entails.pure_right hfds
      (Entails.pure_right ⟨hx0, hx1, hx2, hlay, hlr ▸ hlr_ls⟩ (Entails.of_eq (by sep_ac_rfl)))
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    dsimp only [withFdsGe3Closed, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    dsimp only [withFdsGe3Closed, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    dsimp only [withFdsGe3Closed, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetSpecWithStack]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfdsm => SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfdsm htrm)

/-! ## 3. Epilogue & Branch Helpers on Block `565` with `FdsGe3Closed` -/

theorem ispoll_epilogue_1bc_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s0 s : State} (x : IdPollGhost) (st : M.σ)
    (c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8)
    (Rest : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_565).base + offEpilogue)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hq : ∀ sf : State,
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s.trace → sf.fs = s.fs →
      Q sf (epilogueOut s0 x (s.readReg64 .x25)
        ((s.readReg64 .x26).truncate 32) ((s.readReg64 .x8).truncate 32)
        (s.readReg64 .x21) (s.readReg64 .x22)
        c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ A.pool lim st sf ∗ Rest)) :
    SepWP ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ A.pool lim st s ∗ Rest) Q := by
  dsimp only [offEpilogue] at hpc
  conv =>
    arg 4
    unfold epiloguePre overlap7View1 idSaveBoxAt savedCalleeSlots
    rw [sret48_epilogue_split x.call.out]
    unfold overlap7View1
    simp only [wp_norm, arm64_norm, ispoll_sp_eqs, out_add_eqs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun o0 => SepWP.exists_elim fun o8 =>
    SepWP.exists_elim fun o12 => SepWP.exists_elim fun o16 =>
    SepWP.exists_elim fun o24 => SepWP.exists_elim fun o32 =>
    SepWP.exists_elim fun o40 => SepWP.exists_elim fun b1 =>
    SepWP.exists_elim fun b2 => SepWP.exists_elim fun b3 =>
    SepWP.exists_elim fun b4 => SepWP.exists_elim fun b5 =>
    SepWP.exists_elim fun b6 => SepWP.exists_elim fun b7 => ?_
  wp_steps_sync_pool ((blkPl_565).base + offEpiLdur11)
  have h7_sp :
      ((s0.sp - 200#64) ↦₃₂ (c4 ++ c3 ++ c2 ++ c1)) ∗
        ((s0.sp - 196#64) ↦₈ c5) ∗ ((s0.sp - 195#64) ↦₁₆ (c7 ++ c6)) =
      ((s0.sp - 200#64) ↦₁₆ (c2 ++ c1)) ∗
        ((s0.sp - 198#64) ↦₈ c3) ∗ ((s0.sp - 197#64) ↦₃₂ (c7 ++ c6 ++ c5 ++ c4)) := by
    have h7 := overlap7_realign (s0.sp - 200#64) c1 c2 c3 c4 c5 c6 c7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_sp
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_565).base + offEpiStr44)
  have h7_out :
      ((x.call.out + 41#64) ↦₃₂ (c4 ++ c3 ++ c2 ++ c1)) ∗
        ((x.call.out + 45#64) ↦₈ b5) ∗ ((x.call.out + 46#64) ↦₁₆ (b7 ++ b6)) =
      ((x.call.out + 41#64) ↦₁₆ (c2 ++ c1)) ∗
        ((x.call.out + 43#64) ↦₈ c3) ∗ ((x.call.out + 44#64) ↦₃₂ (b7 ++ b6 ++ b5 ++ c4)) := by
    have h7 := overlap7_realign (x.call.out + 41#64) c1 c2 c3 c4 b5 b6 b7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [out_add_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_out
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  refine Eq.mpr (congrArg (Q _) ?_)
    (hq _ (by wp_norm_goal)
      (by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs])
      (by wp_norm_goal)
      (by wp_norm_goal))
  unfold epilogueOut overlap7View2 idSaveBoxAt savedCalleeSlots
  simp only [wp_norm, arm64_norm, ispoll_sp_eqs]
  sep_ac_rfl

theorem ispoll_ok_tail_190_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpecX M A lim))))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (gr : Except Unit (List (BitVec 8))) (o : Option IdentityKey) (c : IdentityChange)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (hpc : s.pc = (blkPl_565).base + offOkTail)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx26 : (s.readReg64 .x26).truncate 32 = (if c == .replacedExisting then 1#32 else 0#32))
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hc : idSaveOf (.ok o) x.call.call.key = .ok c)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hans : IdPeerAns gr (.ok o))
    (hFitSer : FitsEnv M lim (M.stepEvents evsPre st0) PublicKeySerializeEnv)
    (hFitPut : FitsEnv M lim (M.stepEvents (evsPre ++ publicKeySerializeEvents) st0)
      (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveEvs : ∀ evsPut,
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv s0.fs.files x (evsPre ++ publicKeySerializeEvents ++ evsPut)) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (dirAt A.repAlloc (x.self + 40#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evsPre st0) s ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 208#64) 8 ∗
        overlap7View1 (s0.sp - 200#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 193#64) ↦₈ c15) ∗
        ((s0.sp - 192#64) ↦₆₄ s16) ∗
        ((s0.sp - 184#64) ↦₈ s24) ∗
        memRegion (s0.sp - 183#64) 7 ∗
        ((s0.sp - 176#64) ↦₆₄ s32) ∗
        ((s0.sp - 168#64) ↦₈ s40) ∗
        memRegion (s0.sp - 167#64) 7 ∗
        memRegion (s0.sp - 160#64) 16 ∗
        memRegion (s0.sp - 144#64) 48 ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk)).post
          (x, st0) s0 sf))
      (fun sf P_f =>
        P_f ⊢ (withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk)).onPanic
          (x, st0) s0 sf) := by
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hlog : lsLogOff = lsLogOff := rfl
  dsimp only [offOkTail] at hpc
  conv =>
    arg 4
    rw [protocolAddressAt_borrow A.repAlloc x.call.call.addr x.call.call.addrA]
    unfold idSaveBoxAt
    simp only [sepConj_assoc]
  apply sepWPp_seq_lscro (mid := lsmpl.base 205) hinv
  wp_steps_sync_pool (lsmpl.base 205)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hinv_ser
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 208#64) (serStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_serialize_placed_fd (ret_pc := (blkPl_565).base + offAfterSer) hSer
    x.call.call.keyA x.call.call.key.publicKey (M.stepEvents evsPre st0) ?ispollF1
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    hinv_ser (by simpa only [wp_norm, arm64_norm] using hfds)
    (by wp_norm_goal) hFitSer ?ispollPre1 ?_
  case ispollPre1 => ispoll_close_frame
  intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 hfds1 hx1_1 htr1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hx1_1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, _, hx26_1, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp1, ← hsp]
  rw [← M.stepEvents_append]
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 208#64) (serStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_rw_pre (slot90_split_vec24 s0.sp)
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply sepWPp_seq_lscro (mid := lsmpl.base 543) hinv1
  wp_steps_sync_pool (lsmpl.base 543)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hinv_put
  ispoll_fold_pre (boxU8Buf_to_vecU8_33 A.repAlloc s0.sp (sm1.readReg64 .x0) x.call.call.key)
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 208#64) (putStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  have hx2_len : (BitVec.ofNat 64 x.call.call.addr.name.bytes.length).toNat =
      x.call.call.addr.name.bytes.length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ispoll_call_dirPutStr_placed_fd (ret_pc := (blkPl_565).base + offAfterPut) hPut
    { self := x.self + 40#64
      dir := x.peers
      nameRo := false
      nameA := x.call.call.addr.name.ptr
      name := x.call.call.addr.name.bytes
      bytesV := s0.sp - 144#64
      bytes := x.call.call.key.serialize }
    (M.stepEvents (evsPre ++ publicKeySerializeEvents) st0) ?ispollF2
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    hinv_put (by simpa only [wp_norm, arm64_norm] using hfds1)
    (by simp only [wp_norm, arm64_norm])
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, hx2_len])
    (by wp_norm_goal) hnlen hclen hFitPut
    ?ispollPre2 ?_
  case ispollPre2 => ispoll_close_frame
  intro sm2 evsPut hpc2 hrun2 hsp2 hcs2 _hinv2 hfds2 htr2 hevsPut
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx29_1, hvregs_1] at hpc2 hsp2 htr2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, _, _, hx26_2, _, _, _, hvregs_2⟩
  have hsp_al2 : sm2.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp2, ← hsp]
  rw [← M.stepEvents_append]
  let evsTot := evsPre ++ publicKeySerializeEvents ++ evsPut
  have hSaveTot : SaveEnv s0.fs.files x evsTot := hSaveEvs evsPut hevsPut
  have hmerge48 :
      (memRegion (s0.sp - 144#64) 24 ∗ memRegion (s0.sp - 120#64) 24) =
        memRegion (s0.sp - 144#64) 48 :=
    (ProofLib.memRegion_split' (b := s0.sp - 144#64) (n := 24) (k := 24)
      (b' := s0.sp - 120#64) rfl (by bv_omega) (by decide)).symm
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1, hsp2]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 208#64) (putStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_rw_pre hmerge48
  let restPut : SepProp :=
    dirAt A.repAlloc (x.self + 40#64)
      (x.peers.put x.call.call.addr.name.bytes x.call.call.key.serialize) ∗
    protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
    (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
    lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
    stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗
    memRegion (s0.sp - 208#64) 8 ∗
    ((s0.sp - 193#64) ↦₈ c15) ∗
    memRegion (s0.sp - 183#64) 7 ∗
    ((s0.sp - 176#64) ↦₆₄ s32) ∗
    ((s0.sp - 168#64) ↦₈ s40) ∗
    memRegion (s0.sp - 167#64) 7 ∗
    memRegion (s0.sp - 160#64) 16 ∗
    memRegion (s0.sp - 144#64) 48
  refine sepWPp_conseq
    (P' := epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗
      A.pool lim (M.stepEvents evsTot st0) sm2 ∗ restPut)
    (Entails.of_eq ?_) ?_
  · dsimp only [restPut, evsTot]
    rw [protocolAddressAt_borrow A.repAlloc x.call.call.addr x.call.call.addrA]
    unfold epiloguePre idSaveBoxAt
    sep_ac_rfl
  apply sepWPp_of_sepWP_final
  wp_steps_sync_pool ((blkPl_565).base + offEpilogue)
  refine sepWP_conseq
    (P' := epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗
      A.pool lim (M.stepEvents evsTot st0) _ ∗ restPut)
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine ispoll_epilogue_1bc_placed_fd (A := A) (lim := lim) (H := H) x
    (M.stepEvents evsTot st0) c1 c2 c3 c4 c5 c6 c7 s16 s24 restPut
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, hvregs_2])
    (by wp_norm_goal) (by wp_norm_goal) ?_
  intro sf hspf hcsf htrf hfsf
  refine ⟨hspf, hcsf, ?_⟩
  have htr_eq : sf.trace = s0.trace := by
    simp only [wp_norm, arm64_norm, htr2] at htrf; exact htrf
  have hfds_f : FdsGe3Closed sf.fs := by
    simp only [wp_norm, arm64_norm] at hfsf
    rwa [hfsf]
  simp only [wp_norm, arm64_norm] at hx26
  conv =>
    lhs; arg 1
    simp only [wp_norm, arm64_norm, hx26_2, hx26_1, hx26]
  unfold epilogueOut
  have hokTag : okTagVec = -2#64 := rfl
  refine Entails.trans (Entails.of_eq (by dsimp only [restPut, okTagVec]; sep_ac_rfl :
    _ = ((x.call.out ↦₆₄ okTagVec) ∗
          ((x.call.out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          ((x.call.out + 12#64) ↦₃₂ (_ : BitVec 32)) ∗
          ((x.call.out + 16#64) ↦₆₄ (_ : BitVec 64)) ∗
          ((x.call.out + 24#64) ↦₆₄ (_ : BitVec 64)) ∗
          ((x.call.out + 32#64) ↦₆₄ s16) ∗
          ((x.call.out + 40#64) ↦₈ s24) ∗
          overlap7View2 (x.call.out + 41#64) c1 c2 c3 c4 c5 c6 c7) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 208#64) 8 ∗
          overlap7View2 (s0.sp - 200#64) c1 c2 c3 c4 c5 c6 c7 ∗
          ((s0.sp - 193#64) ↦₈ c15) ∗
          ((s0.sp - 192#64) ↦₆₄ s16) ∗
          ((s0.sp - 184#64) ↦₈ s24) ∗
          memRegion (s0.sp - 183#64) 7 ∗
          ((s0.sp - 176#64) ↦₆₄ s32) ∗
          ((s0.sp - 168#64) ↦₈ s40) ∗
          memRegion (s0.sp - 167#64) 7 ∗
          memRegion (s0.sp - 160#64) 16 ∗
          memRegion (s0.sp - 144#64) 48 ∗
          savedCalleeSlots s0) ∗
        (dirAt A.repAlloc (x.self + 40#64)
          (x.peers.put x.call.call.addr.name.bytes x.call.call.key.serialize) ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evsTot st0) sf))) ?_
  refine Entails.trans
    (sepConj_mono (epilogueOut_ok_reassemble A.repAlloc x.call.out c _ _ _ s16 s24 c1 c2 c3 c4 c5 c6 c7)
      (sepConj_mono_left (restore_savePollStack s0 hstk hhi c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40))) ?_
  dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded]
  refine Entails.pure_right hfds_f ?_
  rw [hlog]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_right evsTot
    (Entails.sepExists_right gr (Entails.sepExists_right (.ok o) ?_))
  have hprop_ok :
      (gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
      IdPeerAns gr (.ok o) ∧ SaveEnv s0.fs.files x evsTot :=
    ⟨⟨hgr, htr_eq⟩, hans, hSaveTot⟩
  simp only [hc, idSavePeers, sepConj_assoc]
  exact Entails.pure_right hprop_ok (Entails.of_eq (by sep_ac_rfl))

private theorem sepWP_let_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let _s_cur := s; SepWP prog ret s P Q) : SepWP prog ret s P Q := h

theorem ispoll_branch_err_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (blkPl_565).base + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hfds : FdsGe3Closed s.fs)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (herr_case : x.peers.get rd s0.fs.files x.call.call.addr.val.name = .error () ∧ s.trace = s0.trace)
    (hSaveEvs : SaveEnv s0.fs.files x evsPre) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (getResultAt A.repAlloc (s0.sp - 144#64) (.error ()) ∗
        dirAt A.repAlloc (x.self + 40#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evsPre st0) s ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 208#64) 8 ∗
        overlap7View1 (s0.sp - 200#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 193#64) ↦₈ c15) ∗
        ((s0.sp - 192#64) ↦₆₄ s16) ∗
        ((s0.sp - 184#64) ↦₈ s24) ∗
        memRegion (s0.sp - 183#64) 7 ∗
        ((s0.sp - 176#64) ↦₆₄ s32) ∗
        ((s0.sp - 168#64) ↦₈ s40) ∗
        memRegion (s0.sp - 167#64) 7 ∗
        ((s0.sp - 160#64) ↦₆₄ s48) ∗
        ((s0.sp - 152#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk)).post
          (x, st0) s0 sf))
      (fun sf P_f =>
        P_f ⊢ (withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk)).onPanic
          (x, st0) s0 sf) := by
  have hlog : lsLogOff = lsLogOff := rfl
  dsimp only [offAfterGet] at hpc
  dsimp only [getResultAt, vecResultAt]
  conv =>
    arg 4
    rw [speAt_read_invalidState_unpack A.repAlloc s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bs => SepWPp.exists_elim fun cap =>
    SepWPp.exists_elim fun ptr => SepWPp.exists_elim fun fnPtr => ?_
  apply sepWPp_of_sepWP_final
  let w5 : BitVec 64 := BitVec.ofNat 64 (utf8 "read").length
  wp_steps_sync_pool ((blkPl_565).base + offErrShuffle)
  ispoll_rw_pre (s48_split_byte7 s0.sp fnPtr w5)
  conv => arg 4; unfold overlap7View1; simp only [ispoll_sp_eqs, sepConj_assoc]
  wp_steps_sync_pool ((blkPl_565).base + offErrLdr60)
  have h7_97 :
      ((s0.sp - 151#64) ↦₃₂ (w5.extractLsb' 32 8 ++ w5.extractLsb' 24 8 ++ w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 147#64) ↦₈ w5.extractLsb' 40 8) ∗
        ((s0.sp - 146#64) ↦₁₆ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8)) =
      ((s0.sp - 151#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 149#64) ↦₈ w5.extractLsb' 24 8) ∗
        ((s0.sp - 148#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8)) := by
    have h7 := overlap7_realign (s0.sp - 151#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_97
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_565).base + offErrStur11)
  have h7_c8 :
      ((s0.sp - 200#64) ↦₃₂ (w5.extractLsb' 32 8 ++ w5.extractLsb' 24 8 ++ w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 196#64) ↦₈ c5) ∗ ((s0.sp - 195#64) ↦₁₆ (c7 ++ c6)) =
      ((s0.sp - 200#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 198#64) ↦₈ w5.extractLsb' 24 8) ∗
        ((s0.sp - 197#64) ↦₃₂ (c7 ++ c6 ++ c5 ++ w5.extractLsb' 32 8)) := by
    have h7 := overlap7_realign (s0.sp - 200#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) c5 c6 c7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_c8
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_565).base + offEpilogue)
  let restErr : SepProp :=
    ((s0.sp - 144#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 136#64) ↦₆₄ cap) ∗
    ((s0.sp - 128#64) ↦₆₄ ptr) ∗ ((s0.sp - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((s0.sp - 112#64) ↦₆₄ fnPtr) ∗ ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
    (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    (fnPtr ↦ᵣ utf8 "read") ∗ dirAt A.repAlloc (x.self + 40#64) x.peers ∗
    protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
    (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
    stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗ memRegion (s0.sp - 208#64) 8 ∗
    ((s0.sp - 193#64) ↦₈ c15) ∗ memRegion (s0.sp - 183#64) 7 ∗
    ((s0.sp - 176#64) ↦₆₄ fnPtr) ∗ ((s0.sp - 168#64) ↦₈ w5.extractLsb' 0 8) ∗
    memRegion (s0.sp - 167#64) 7
  apply sepWP_let_state; intro s_epi
  refine sepWP_conseq (P' :=
      memRegion (s0.sp - 160#64) 16 ∗
      (epiloguePre s0 x
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        fnPtr (w5.extractLsb' 0 8) ∗ A.pool lim (M.stepEvents evsPre st0) s_epi ∗ restErr)) ?_ ?_
  · have hback_c8 := (overlap7_realign (s0.sp - 200#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)).symm
    have hback_97 := (overlap7_realign (s0.sp - 151#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)).symm
    unfold overlap7View2 at hback_c8 hback_97
    simp only [ispoll_sp_eqs] at hback_c8 hback_97
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_left (s48_byte7_entails_memRegion16 s0.sp fnPtr (w5.extractLsb' 0 8)
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)))
    · refine Eq.trans (by dsimp only [restErr, s_epi]; rw [← A.repAlloc_live_norm]; sep_ac_rfl :
        _ = (((s0.sp - 151#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
              ((s0.sp - 149#64) ↦₈ w5.extractLsb' 24 8) ∗
              ((s0.sp - 148#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8))) ∗
            (((s0.sp - 200#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
              ((s0.sp - 198#64) ↦₈ w5.extractLsb' 24 8) ∗
              ((s0.sp - 197#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8))) ∗
            (((s0.sp - 160#64) ↦₆₄ fnPtr) ∗
              ((s0.sp - 152#64) ↦₈ w5.extractLsb' 0 8) ∗
              (((s0.sp - 192#64) ↦₆₄ fnPtr) ∗
                ((s0.sp - 184#64) ↦₈ w5.extractLsb' 0 8) ∗
                memRegion x.call.out 48 ∗
                idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
                savedCalleeSlots s0 ∗ A.pool lim (M.stepEvents evsPre st0) s_epi ∗ restErr))) ?_
      rw [hback_97, hback_c8]
      unfold epiloguePre
      sep_ac_rfl
  refine sepWP_conseq (P' :=
      epiloguePre s0 x
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        fnPtr (w5.extractLsb' 0 8) ∗ A.pool lim (M.stepEvents evsPre st0) s_epi ∗
        (memRegion (s0.sp - 160#64) 16 ∗ restErr))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine ispoll_epilogue_1bc_placed_fd (A := A) (lim := lim) (H := H) x
    (M.stepEvents evsPre st0)
    (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
    (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
    fnPtr (w5.extractLsb' 0 8) (memRegion (s0.sp - 160#64) 16 ∗ restErr)
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, hvregs])
    (by wp_norm_goal) (by wp_norm_goal) ?_
  intro sf hspf hcsf htrf hfsf
  refine ⟨hspf, hcsf, ?_⟩
  have htr_s : sf.trace = s.trace := by simp only [wp_norm, arm64_norm] at htrf; exact htrf
  have hfds_f : FdsGe3Closed sf.fs := by
    simp only [wp_norm, arm64_norm] at hfsf
    rwa [hfsf]
  have hcap_lo :
      BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 cap) &&& 0xFFFFFFFF000000FF#64 |||
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (cap >>> 8)) &&& 16777215#64) <<< 8) =
      cap.extractLsb' 0 32 := by
    ext i hi; interval_cases i <;> simp
  have hcap_hi : BitVec.truncate 32 (cap >>> 32) = cap.extractLsb' 32 32 := by
    ext i hi; interval_cases i <;> simp
  unfold epilogueOut
  conv =>
    lhs; arg 1
    simp only [wp_norm, arm64_norm, hcap_lo, hcap_hi]
  refine Entails.trans (Entails.of_eq (by dsimp only [restErr]; rw [← A.repAlloc_live_norm]; sep_ac_rfl :
    _ = ((x.call.out ↦₆₄ speWord 1) ∗
          ((x.call.out + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((x.call.out + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((x.call.out + 16#64) ↦₆₄ ptr) ∗
          ((x.call.out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((x.call.out + 32#64) ↦₆₄ fnPtr) ∗
          ((x.call.out + 40#64) ↦₈ w5.extractLsb' 0 8) ∗
          overlap7View2 (x.call.out + 41#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
            if cap = 0#64 then emp
            else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗
          ((s0.sp - 144#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 136#64) ↦₆₄ cap) ∗ ((s0.sp - 128#64) ↦₆₄ ptr) ∗
          ((s0.sp - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((s0.sp - 112#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length)) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 208#64) 8 ∗
          overlap7View2 (s0.sp - 200#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          ((s0.sp - 193#64) ↦₈ c15) ∗
          ((s0.sp - 192#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 184#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 183#64) 7 ∗
          ((s0.sp - 176#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 168#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 167#64) 7 ∗
          memRegion (s0.sp - 160#64) 16 ∗
          savedCalleeSlots s0) ∗
        (dirAt A.repAlloc (x.self + 40#64) x.peers ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evsPre st0) sf))) ?_
  refine Entails.trans
    (sepConj_mono_left (epilogueOut_err_reassemble A.repAlloc s0.sp x.call.out bs cap ptr fnPtr)) ?_
  refine Entails.trans
    (Entails.of_eq (by sep_ac_rfl :
      (idSaveOutAt A.repAlloc x.call.out (.error ()) ∗ memRegion (s0.sp - 144#64) 48) ∗ _ =
      idSaveOutAt A.repAlloc x.call.out (.error ()) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 208#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 208#64) 8 ∗
          overlap7View2 (s0.sp - 200#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          ((s0.sp - 193#64) ↦₈ c15) ∗
          ((s0.sp - 192#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 184#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 183#64) 7 ∗
          ((s0.sp - 176#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 168#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 167#64) 7 ∗
          memRegion (s0.sp - 160#64) 16 ∗
          memRegion (s0.sp - 144#64) 48 ∗
          savedCalleeSlots s0) ∗
        (dirAt A.repAlloc (x.self + 40#64) x.peers ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evsPre st0) sf))) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (restore_savePollStack s0 hstk hhi
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        c15 fnPtr (w5.extractLsb' 0 8) fnPtr (w5.extractLsb' 0 8)))) ?_
  dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded]
  refine Entails.pure_right hfds_f ?_
  rw [hlog]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_right evsPre
    (Entails.sepExists_right (Except.error () : Except Unit (List (BitVec 8)))
      (Entails.sepExists_right (Except.error () : Except Unit (Option IdentityKey)) ?_))
  simp only [idSaveOf, idSavePeers, sepConj_assoc]
  refine Entails.pure_right ?_ (Entails.of_eq (by sep_ac_rfl))
  exact ⟨⟨herr_case.1.symm, htr_s.trans herr_case.2⟩, rfl, hSaveEvs⟩

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd
