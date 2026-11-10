/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat`-backed `black_box` Sibling of `IdTrustPollPlacedBudgetFd` (`IdTrustPollPlacedBudgetFdSat`)

Replaces `h_bb : H lsBlackBoxU8Sym = some blackBoxHook` with
`h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` in `<PublicKey as PartialEq>::eq` (Block `212`)
and `<IdentityFiles as IdentityKeyStore>::is_trusted_identity::{closure#0}` (Block `566`):
1. `VmPreserved.fdsHiFrame` preserves `FdsGe3Closed` directly across `withVmPreserved` specs.
2. `pkEq_cells_placed_ok_16_fd` splits `80` B (`64` B frames + `16` B `black_box` stack) out of
   `calleeStk = max (max getStk 96) (max 64 extHookStack)` (`≥ 16384` B), keeping the outer
   `idTrustPoll_placed_ok_of_get_bb_fd_sat` conclusion token-identical to
   `IdTrustPollPlacedBudgetFd.idTrustPoll_placed_ok_of_get_bb_fd`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFdSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_212 blkPC_213 blkPl_212 blkPl_213
   libsignalMutatedBlocks lsBlackBoxU8Sym lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (ctEqSliceSpecExt publicKeyEqSpecExt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speWord)
open CryptoVerification.RecordCodecs (decodeIdentityKey decodeIdentityKey_serialize)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdFileWf IdPeerAns IdPollGhost ReadRule dirAt getResultAt idTrustOf idTrustOutAt
   pathOf utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_566 blkPC_566 blkPl_566 lsProg_566)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
  (cap_ne_zero_of_cons cells_24_split cons_len_bv_ne_zero exists_pollKeyChunks_of_length_32
   getResultAt_err_sp_144 getResultAt_ok_sp_144 memRegion_8_sp_72_hi memRegion_8_sp_72_lo
   out_48_pre_split out_err_fold out_ok_fold pointsTo64_sp_152_split pollKeyChunks
   pollKeyChunks_sp_136 pollKeyChunks_sp_144_of_eq post_ok_disj publicKey_beq_eq_decide
   sevenHi_sp_72' sevenLo_out_41' sevenLo_sp_151' sevenLo_sp_72' sp_144_cells4_fold_48
   sp_144_cells6_fold_48 sp_144_ikDec_fold_48 sp_144_key_fold_48 sp_151_sevenHi_fold_7
   sp_152_fold_64 sret_48_sp_144_rebuild_split stackAt_sub_split vecU8BufRest)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers.CliIdTrustPollNorm
  (extractLsb_append_hi extractLsb_append_lo extractLsb_pack32_0 extractLsb_pack32_0_16
   extractLsb_pack32_16 extractLsb_pack32_16_16 extractLsb_pack32_24 extractLsb_pack32_8
   fs_setMem_pre fs_setPC_pre fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre
   fs_writeReg_pre fs_writeVReg128_pre okTagVec_eq_neg2 readReg32_setMem_setPC_pre
   readReg32_setPC_pre readReg32_writeVReg128_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg64_writeVReg128_pre readReg_setMem_setPC_pre
   readReg_setPC_pre readReg_writeVReg128_pre readVReg128_setMem_pre
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre readVReg128_writeReg_pre
   sp_setMem_setPC_pre sp_setPC_pre sp_writeVReg128_pre speWord_one_eq
   trace_writeReg32_pre trace_writeReg_pre trace_writeVReg128_pre)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat ct_eq_placed_vm_ok_ext_sat publicKeyEqMemSpec16 publicKeyEqSpec16
   publicKey_eq_mem_placed_vm_ok_16_sat publicKey_eq_placed_vm_ok_16_sat
   publicKey_eq_placed_vm_ok_ext_sat)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed subroutine_ok_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced idTrustPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudget
  (CliIdTrustPollEnv cliIdTrustPollInnerSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudgetFd
  (cliIdTrustPollInnerSpecPlaced_fd deallocVecBufSpec_fd deallocVecBuf_placed_ok_fd
   dirGetCellsPlacedSpec_fd dirGet_cells_placed_ok_fd idTrustPoll_placed_of_inner_fd
   ikDecodeCellsSpecPlaced_fd ikDecode_cells_placed_ok_fd pkEqCellsSpecPlaced_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (identityKeyDecodePlacedBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
  (identityKey_decode_placed_ok_fd ls_transfer_withFdsGe3Closed_cl_to_lscro)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre fs_writeVReg128_pre
  trace_writeVReg128_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre
  extractLsb_append_lo extractLsb_append_hi
  extractLsb_pack32_0 extractLsb_pack32_8 extractLsb_pack32_16 extractLsb_pack32_24
  extractLsb_pack32_0_16 extractLsb_pack32_16_16
  speWord_one_eq okTagVec_eq_neg2
  trace_writeReg32_pre trace_writeReg_pre

/-! ## 1. `FdsGe3Closed` Lifts from `VmPreserved` & `HookSat`-backed Block `213` / `212` -/

/-- `VmPreserved` (`FdsHiFrame`) preserves `FdsGe3Closed` on `fd ∈ [3, 2 ^ 31)`. -/
theorem fdsGe3Closed_of_vmPreserved {s0 sf : State}
    (hvm : VmPreserved s0 sf) (h0 : FdsGe3Closed s0.fs) :
    FdsGe3Closed sf.fs :=
  fun fd hlo hhi => (hvm.fdsHiFrame fd hlo hhi).trans (h0 fd hlo hhi)

/-- Any `subroutine_ok` for `withVmPreserved spec` lifts directly to `withFdsGe3Closed`. -/
theorem subroutine_ok_withFdsGe3Closed_of_vmPreserved {α : Type} {P : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok P entry (withVmPreserved spec)) :
    subroutine_ok P entry (withFdsGe3Closed (withVmPreserved spec)) := by
  refine subroutine_ok_withFdsGe3Closed h fun _ _ s0 sf h0 hpost => ?_
  dsimp only [withVmPreserved] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact fdsGe3Closed_of_vmPreserved hpost.1 h0

/-- Any `subroutine_ok` for `withLsCodeLoaded lsmpl (withVmPreserved spec)` lifts directly to
`withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved spec))`. -/
theorem subroutine_ok_withFdsGe3Closed_of_lscl_vmPreserved [LibsignalPlacement] {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCodeLoaded lsmpl (withVmPreserved spec))) :
    subroutine_ok P entry (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved spec))) := by
  refine subroutine_ok_withFdsGe3Closed h fun _ _ s0 sf h0 hpost => ?_
  dsimp only [withLsCodeLoaded, withVmPreserved] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact fdsGe3Closed_of_vmPreserved hpost.1 h0

/-- `withFdsGe3Closed`-threaded `ct_eq` (Block `213`) on `ctEqSliceSpecExt` (`48 + 16384` B) under
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem ct_eq_placed_ok_ext_fd_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      (withFdsGe3Closed (withVmPreserved ctEqSliceSpecExt)) :=
  subroutine_ok_withFdsGe3Closed_of_vmPreserved (ct_eq_placed_vm_ok_ext_sat h_bb)

/-- `withFdsGe3Closed`-threaded `<PublicKey as PartialEq>::eq` (Block `212`) on
`publicKeyEqSpecExt` (`64 + 16384` B) under `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem publicKeyEq_placed_ok_of_bb_ext_fd_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpecExt))) :=
  subroutine_ok_withFdsGe3Closed_of_lscl_vmPreserved (publicKey_eq_placed_vm_ok_ext_sat h_bb)

/-- `withFdsGe3Closed`-threaded `<PublicKey as PartialEq>::eq` (Block `212`) on
`publicKeyEqSpec16` (`80 = 64 + 16` B) under `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem publicKeyEq_placed_ok_of_bb_16_fd_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec16))) :=
  subroutine_ok_withFdsGe3Closed_of_lscl_vmPreserved (publicKey_eq_placed_vm_ok_16_sat h_bb)

/-- `withFdsGe3Closed`-threaded `<PublicKey as PartialEq>::eq` (Block `212`) on
`publicKeyEqMemSpec16` (`80 = 64 + 16` B) under `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem publicKeyEq_mem_placed_ok_of_bb_16_fd_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16))) :=
  subroutine_ok_withFdsGe3Closed_of_lscl_vmPreserved (publicKey_eq_mem_placed_vm_ok_16_sat h_bb)

/-! ## 2. `80`-Byte Stack Cell Wrapper for `<PublicKey as PartialEq>::eq` -/

/-- `80`-byte (`64` B frames + `16` B `black_box` stack) counterpart of `pkEq_cells_placed_ok_fd`. -/
theorem pkEq_cells_placed_ok_16_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hEq : subroutine_ok prog (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved publicKeyEqMemSpec16))))
    (hle : 80 ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (pkEqCellsSpecPlaced_fd A lim calleeStk)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨⟨p1, ik1, p2, ik2, fsp⟩, st⟩ R s0 hpc hrun hpre hsp hcl
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [pkEqCellsSpecPlaced_fd, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hClosed0, hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - 80)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved publicKeyEqMemSpec16))).pre
        (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) s0 ∗ (A.pool lim st s0 ∗ stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [withFdsGe3Closed, withVmPreserved, publicKeyEqMemSpec16]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosed0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, rfl⟩, ?_⟩
    dsimp only [stackAt, stkRem] at hmem ⊢
    convert hmem using 1; sep_ac_rfl
  rcases hEq.no_fault_before_outcome (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp)
      (A.pool lim st s0 ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩, -⟩
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, ?_⟩))
    dsimp only [withLsCodeRoLoaded, withFdsGe3Closed, withVmPreserved, publicKeyEqMemSpec16,
      pkEqCellsSpecPlaced_fd] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hClosedF, hvm, ⟨hr0, htr⟩, hq⟩
    rw [publicKey_beq_eq_decide] at hr0
    rw [← A.pool_transport lim st s0 sf hvm] at hq
    refine ⟨⟨hClosedF, hr0, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stackAt, stkRem] at hq ⊢
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, withFdsGe3Closed, withVmPreserved, publicKeyEqMemSpec16] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, withFdsGe3Closed, withVmPreserved, publicKeyEqMemSpec16] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, withFdsGe3Closed, withVmPreserved, publicKeyEqMemSpec16] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 3. Block `566` (`is_trusted_identity::{closure#0}`) Symbolic Execution (`80`-Byte `eq`) -/

private theorem utf8_read_len_eq_p : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]
  decide +kernel

private theorem close_noPanic_subgoal_p {sf : State} {F R P_out : SepProp}
    (hm : sf.mem ⊨ ((⌜False⌝ ∗ F) ∗ R)) :
    sf.mem ⊨ P_out := by
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

private def idTrustPostAnsPool_p_fd {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ)
    (TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (x : IdPollGhost) (dget : Except Unit (List (BitVec 8)))
    (s0 sf : State) : SepProp :=
  ⌜FdsGe3Closed sf.fs⌝ ∗
    ∃∗ evs : List AllocEvent,
      (∃∗ gr : Except Unit (List (BitVec 8)),
        ∃∗ p : Except Unit (Option IdentityKey),
        ⌜(gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p ∧ TrustEnv s0.fs.files x evs⌝ ∗
        idTrustOutAt A.repAlloc x.call.out (idTrustOf p x.call.call.key)) ∗
      A.pool lim (M.stepEvents evs st) sf

private theorem idTrustPostAnsPool_intro_p_fd {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ)
    (TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (x : IdPollGhost) (dget : Except Unit (List (BitVec 8)))
    (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8)))
    (p : Except Unit (Option IdentityKey)) (s0 sf : State)
    (hClosed : FdsGe3Closed sf.fs)
    (hpure : (gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p ∧ TrustEnv s0.fs.files x evs) :
    idTrustOutAt A.repAlloc x.call.out (idTrustOf p x.call.call.key) ∗
      A.pool lim (M.stepEvents evs st) sf ⊢
      idTrustPostAnsPool_p_fd A lim st TrustEnv x dget s0 sf := by
  have htrue :
      (((gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p ∧ TrustEnv s0.fs.files x evs) : Prop) =
        True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  unfold idTrustPostAnsPool_p_fd
  refine Entails.pure_right hClosed ?_
  refine Entails.sepExists_right evs (sepConj_mono_left ?_)
  refine Entails.sepExists_right gr (Entails.sepExists_right p ?_)
  rw [htrue]
  exact Entails.of_eq (by simp)

private theorem focus_postAnsPool_p_fd {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ)
    (TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (x : IdPollGhost) (dget : Except Unit (List (BitVec 8)))
    (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8)))
    (p : Except Unit (Option IdentityKey)) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hf : P = (idTrustOutAt A.repAlloc x.call.out (idTrustOf p x.call.call.key) ∗
        A.pool lim (M.stepEvents evs st) s_ret) ∗ R)
    (hClosed : FdsGe3Closed s_ret.fs)
    (hpure : (gr = dget ∧ s_ret.trace = s0.trace) ∧ IdPeerAns gr p ∧
      TrustEnv s0.fs.files x evs)
    (hnext : SepWP prog ret_pc s_ret
      (idTrustPostAnsPool_p_fd A lim st TrustEnv x dget s0 s_ret ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken
    (idTrustPostAnsPool_intro_p_fd A lim st TrustEnv x dget evs gr p s0 s_ret hClosed hpure)
    (hf := hf) hnext

private theorem focus_out_err_fold_p (A : CryptoVerification.RustHeap.RustAlloc) (out : BitVec 64)
    (sCap sPtr : BitVec 64) (sBs : List (BitVec 8)) (fnPtr : BitVec 64)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    {b8 : BitVec 8} {w9 : BitVec 32} {h13 : BitVec 16} {b15 : BitVec 8}
    {b40 b41 b42 b43 : BitVec 8} {w44 : BitVec 32}
    (hf : P = ((out ↦₆₄ speWord 1) ∗
        (((out + 8#64) ↦₈ b8) ∗ ((out + 9#64) ↦₃₂ w9) ∗
          ((out + 13#64) ↦₁₆ h13) ∗ ((out + 15#64) ↦₈ b15)) ∗
        ((out + 16#64) ↦₆₄ sPtr) ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        vecU8Buf A sCap sPtr sBs ∗
        ((out + 32#64) ↦₆₄ fnPtr) ∗
        (((out + 40#64) ↦₈ b40) ∗ ((out + 41#64) ↦₈ b41) ∗
          ((out + 42#64) ↦₈ b42) ∗ ((out + 43#64) ↦₈ b43) ∗ ((out + 44#64) ↦₃₂ w44)) ∗
        (fnPtr ↦ᵣ utf8 "read")) ∗ R)
    (hsCap : b15 ++ h13 ++ w9 ++ b8 = sCap)
    (hfnLen : w44 ++ b43 ++ b42 ++ b41 ++ b40 = 4#64)
    (hnext : SepWP prog ret_pc s_ret (idTrustOutAt A out (.error ()) ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken
    (out_err_fold A out sCap sPtr sBs fnPtr b8 w9 h13 b15 b40 b41 b42 b43 w44
      hsCap (hfnLen.trans utf8_read_len_eq_p.symm))
    (hf := hf) hnext

private theorem focus_pollKeyChunks_sp_144_p (sp : BitVec 64) {bs : List (BitVec 8)}
    {kw0 : BitVec 32} {kw4 : BitVec 16} {kb6 : BitVec 8}
    {kv7 kv15 kv23 : BitVec 64} {kb31 : BitVec 8}
    (hchunks : ∀ a : BitVec 64, (a ↦ₛ bs) = pollKeyChunks a kw0 kw4 kb6 kv7 kv15 kv23 kb31)
    {prog : Program} {target : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    {w0' : BitVec 32} {w4' : BitVec 16} {b6' : BitVec 8}
    (hf : P = (((sp - 144#64) ↦₃₂ w0') ∗ ((sp - 140#64) ↦₁₆ w4') ∗
        ((sp - 138#64) ↦₈ b6') ∗ ((sp - 137#64) ↦₆₄ kv7) ∗
        ((sp - 129#64) ↦₆₄ kv15) ∗ ((sp - 121#64) ↦₆₄ kv23) ∗
        ((sp - 113#64) ↦₈ kb31)) ∗ R)
    (hw0 : w0' = kw0) (hw4 : w4' = kw4) (hb6 : b6' = kb6)
    (hnext : SepWP prog target s (((sp - 144#64) ↦ₛ bs) ∗ R) post) :
    SepWP prog target s P post := by
  rw [hf, pollKeyChunks_sp_144_of_eq sp hchunks hw0 hw4 hb6]
  exact hnext

private theorem unpack_getResultAt_err_p {prog : Program} {ret : BitVec 64} {sf : State}
    {A : CryptoVerification.RustHeap.RustAlloc} {sp : BitVec 64} {rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ (fnPtr : BitVec 64) (sBs : List (BitVec 8)) (sCap sPtr : BitVec 64),
      SepWPp prog ret sf
        (((sp - 144#64) ↦₆₄ speWord 1) ∗
          ((sp - 136#64) ↦₆₄ sCap) ∗ ((sp - 128#64) ↦₆₄ sPtr) ∗
          ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
          vecU8Buf A sCap sPtr sBs ∗
          ((sp - 112#64) ↦₆₄ fnPtr) ∗
          ((sp - 104#64) ↦₆₄ 4#64) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗ rest) Q Qp) :
    SepWPp prog ret sf (getResultAt A (sp - 144#64) (.error ()) ∗ rest) Q Qp := by
  rw [getResultAt_err_sp_144 A sp, utf8_read_len_eq_p]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWPp.exists_elim; intro fnPtr
  apply ProofLib.SepWPp.exists_elim; intro sBs
  apply ProofLib.SepWPp.exists_elim; intro sCap
  apply ProofLib.SepWPp.exists_elim; intro sPtr
  exact h fnPtr sBs sCap sPtr

private theorem unpack_getResultAt_ok_p {prog : Program} {ret : BitVec 64} {sf : State}
    {A : CryptoVerification.RustHeap.RustAlloc} {sp : BitVec 64} {bs : List (BitVec 8)}
    {rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ (bCap bPtr : BitVec 64),
      bs.length ≤ bCap.toNat → bCap.toNat < 2 ^ 63 → bPtr ≠ 0#64 →
      SepWPp prog ret sf
        (((sp - 144#64) ↦₆₄ okTagVec) ∗ ((sp - 136#64) ↦₆₄ bCap) ∗
          ((sp - 128#64) ↦₆₄ bPtr) ∗ ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗
          memRegion (sp - 112#64) 16 ∗ rest) Q Qp) :
    SepWPp prog ret sf (getResultAt A (sp - 144#64) (.ok bs) ∗ rest) Q Qp := by
  rw [getResultAt_ok_sp_144 A sp bs]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWPp.exists_elim; intro bCap
  apply ProofLib.SepWPp.exists_elim; intro bPtr
  apply ProofLib.SepWPp.pure_elim; rintro ⟨h1, h2, h3⟩
  exact h bCap bPtr h1 h2 h3

private abbrev cells24Frame (sp : BitVec 64) (slot72 : SepProp) : SepProp :=
  (∃∗ v0 : BitVec 64, (sp - 192#64) ↦₆₄ v0) ∗
  ((∃∗ b1 : BitVec 8, (sp - 184#64) ↦₈ b1) ∗ memRegion (sp - 183#64) 7) ∗
  (∃∗ v2 : BitVec 64, (sp - 176#64) ↦₆₄ v2) ∗
  ((∃∗ b3 : BitVec 8, (sp - 168#64) ↦₈ b3) ∗ memRegion (sp - 167#64) 7) ∗
  (∃∗ v4 : BitVec 64, (sp - 160#64) ↦₆₄ v4) ∗
  ((∃∗ b5 : BitVec 8, (sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7) ∗
  memRegion (sp - 144#64) 48 ∗
  (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗ (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
  (∃∗ s27 : BitVec 64, (sp - 80#64) ↦₆₄ s27) ∗ slot72 ∗
  (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗ (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
  (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗ (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
  (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗ (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
  (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗ (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19)

private abbrev slot72Lo (sp : BitVec 64) : SepProp :=
  (∃∗ w0 : BitVec 32, (sp - 72#64) ↦₃₂ w0) ∗ (∃∗ b4 : BitVec 8, (sp - 68#64) ↦₈ b4) ∗
  (∃∗ b5 : BitVec 8, (sp - 67#64) ↦₈ b5) ∗ (∃∗ b6 : BitVec 8, (sp - 66#64) ↦₈ b6) ∗
  (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7)

private abbrev slot72Hi (sp : BitVec 64) : SepProp :=
  (∃∗ b0 : BitVec 8, (sp - 72#64) ↦₈ b0) ∗ (∃∗ b1 : BitVec 8, (sp - 71#64) ↦₈ b1) ∗
  (∃∗ b2 : BitVec 8, (sp - 70#64) ↦₈ b2) ∗ (∃∗ w3 : BitVec 32, (sp - 69#64) ↦₃₂ w3) ∗
  (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7)

private theorem cells_24_lo_p (sp : BitVec 64) :
    cells (sp - 192#64) 24 = cells24Frame sp (slot72Lo sp) := by
  rw [cells_24_split sp, memRegion_8_sp_72_lo sp]

private theorem cells_24_hi_p (sp : BitVec 64) :
    cells (sp - 192#64) 24 = cells24Frame sp (slot72Hi sp) := by
  rw [cells_24_split sp, memRegion_8_sp_72_hi sp]

private def cliIdTrustPollExpandedSpecPlaced_fd [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (IdPollGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FdsGe3Closed s.fs⌝ ∗
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.peers.path x.call.call.addr.name.bytes) ∧
      (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.name.bytes = .ok bs → IdFileWf bs) ∧
      FitsEnv M lim st (TrustEnv s.fs.files x) ∧
      x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
      x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc (x.self + 40#64) x.peers ∗
      memRegion x.call.out 48 ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
      A.pool lim st s ∗ stackAt (s.sp - 192#64) calleeStk ∗ cells24Frame s.sp (slot72Lo s.sp)
  post := fun (x, st) s0 sf =>
    idTrustPostAnsPool_p_fd A lim st TrustEnv x
      (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes) s0 sf ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A.repAlloc (x.self + 40#64) x.peers ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
      stackAt (s0.sp - 192#64) calleeStk ∗ cells24Frame s0.sp (slot72Hi s0.sp)

private theorem cliIdTrustPollExpandedSpecPlaced_fd_eq [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop)
    (calleeStk : Nat) :
    cliIdTrustPollExpandedSpecPlaced_fd rd pathOk A lim TrustEnv calleeStk =
      cliIdTrustPollInnerSpecPlaced_fd rd pathOk A lim TrustEnv calleeStk := by
  unfold cliIdTrustPollExpandedSpecPlaced_fd cliIdTrustPollInnerSpecPlaced_fd withFdsGe3Closed
    cliIdTrustPollInnerSpecPlaced idTrustPostAnsPool_p_fd
  congr 1
  · funext ⟨x, st⟩ s
    dsimp only
    rw [cells_24_lo_p s.sp]
  · funext ⟨x, st⟩ s0 sf
    dsimp only
    rw [cells_24_hi_p s0.sp, sepConj_assoc]
    congr 1
    rw [sepExists_sepConj_left]
    congr 1; funext evs; sep_ac_rfl

set_option pp.deepTerms false in
set_option pp.maxSteps 1000000 in
set_option maxHeartbeats 3200000 in
/-- `80`-byte `publicKeyEqMemSpec16` counterpart of `idTrustPollInner_placed_ok_fd`. -/
theorem idTrustPollInner_placed_ok_16_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 18)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved (identityKeyDecodeRawSpec A)))))
    (hEq : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved publicKeyEqMemSpec16))))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hhi : max (max getStk 96) (max 64 extHookStack) ≤ 2 ^ 64) :
    subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (blkPl_566).base
      (withLsCodeRoLoaded lsmpl
        (cliIdTrustPollInnerSpecPlaced_fd rd pathOk A lim TrustEnv
          (max (max getStk 96) (max 64 extHookStack)))) := by
  let calleeStk := max (max getStk 96) (max 64 extHookStack)
  rw [← cliIdTrustPollExpandedSpecPlaced_fd_eq]
  unfold withLsCodeRoLoaded
  simp (config := { maxSteps := 2000000 }) only [cliIdTrustPollExpandedSpecPlaced_fd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hGetCells := dirGet_cells_placed_ok_fd (calleeStk := calleeStk) hGet (by omega) hhi
  have hDecCells := ikDecode_cells_placed_ok_fd (A := A) (lim := lim) (calleeStk := calleeStk)
    hDec (by omega) hhi
  have hDeallocCells := deallocVecBuf_placed_ok_fd (prog := (blkPC_566).rebase (blkPl_566).base H)
    (i := 566) (calleeStk := calleeStk) hFs (by omega) hhi
  have hEqCells := pkEq_cells_placed_ok_16_fd (A := A) (lim := lim) (calleeStk := calleeStk)
    hEq (by simp only [calleeStk, extHookStack]; omega) hhi
  clear hGet hDec hEq hFs
  wpp_init xs s0
  obtain ⟨x, st⟩ := xs
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit_get : FitsEnv M lim st (GetEnv s0.fs.files x.peers x.call.call.addr.name.bytes) :=
    hFitGet s0.fs.files x st (by assumption)
  apply sepWPp_seq_lscro (mid := lsmpl.base 589) hcrl0
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  wp_call_spec_lscro hGetCells (dirGetCellsPlacedSpec_fd rd pathOk A lim GetEnv calleeStk) hcrl1
    ((s0.sp - 144#64, x.self + 40#64, x.peers,
      x.call.call.addr.name.ptr, x.call.call.addr.name.bytes, s0.sp - 192#64), st)
  case panic =>
    intro _ _ hm
    exact close_noPanic_subgoal_p hm
  have hget_evs : GetEnv s0.fs.files x.peers x.call.call.addr.name.bytes w := by
    simpa only [wp_norm, arm64_norm] using ‹GetEnv _ x.peers x.call.call.addr.name.bytes w›
  cases w_1 with
  | error u =>
    cases u
    apply unpack_getResultAt_err_p
    intro fnPtr sBs sCap sPtr
    apply SepWPp.of_sepWP_ret
    apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
      blkLib_eq_566 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip
    apply SepWP.focus_rw (out_48_pre_split x.call.out)
    wp_pull_exists
    apply SepWP.focus_weaken (sp_152_fold_64 s0.sp _)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_rw (pointsTo64_sp_152_split s0.sp _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_151' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenHi_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
    wp_steps
    apply SepWP.focus_weaken (sp_151_sevenHi_fold_7 s0.sp _ _ _ _)
    apply SepWP.focus_weaken (sp_144_cells6_fold_48 s0.sp _ _ _ _ _ _)
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    refine focus_out_err_fold_p A.repAlloc x.call.out sCap sPtr sBs fnPtr (by sep_focus) ?_ ?_ ?_
    · bv_bits
    · bv_bits
    refine focus_postAnsPool_p_fd A lim st TrustEnv x
      (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
      w (.error ()) (.error ()) s0 (by sep_focus) ?_ ?_ ?_
    · simp only [wp_norm, arm64_norm, *]
    · exact ⟨⟨by simpa only [wp_norm, arm64_norm] using
          ‹(.error () : Except Unit (List (BitVec 8))) = _›,
        by simp only [wp_norm, arm64_norm, *]⟩, rfl,
        hTrustGet s0.fs.files x w hget_evs⟩
    wp_done
  | ok bs =>
    have ⟨hget, _htr_get⟩ :=
      post_ok_disj (bs := bs)
        (dget := x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
        (s0 := s0) (sf1 := sf)
        ⟨by simpa only [wp_norm, arm64_norm] using ‹(.ok bs : Except Unit (List (BitVec 8))) = _›,
          by simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›⟩
    have hfile : IdFileWf bs := by
      have hwf : ∀ bs, x.peers.get rd s0.fs.files x.call.call.addr.name.bytes = .ok bs →
          IdFileWf bs := by assumption
      exact hwf bs hget.symm
    cases bs with
    | nil =>
      apply unpack_getResultAt_ok_p
      intro bCap bPtr hbCap_le hbCap_lt _hbPtr_ne
      by_cases hc0 : bCap = 0#64
      · subst hc0
        apply SepWPp.of_sepWP_ret
        apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
          blkLib_eq_566 (mid := s0.readReg64 (Reg.gpr 30#5))
        intro _m_strip
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗ vecU8BufRest A.repAlloc 0#64 bPtr 0) = emp := by
          simp [vecU8BufRest]
        apply SepWP.focus_rw hemp
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.focus_weaken
          (out_ok_fold A.repAlloc x.call.out true _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        refine focus_postAnsPool_p_fd A lim st TrustEnv x
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          w (.ok []) (.ok none) s0 (by sep_focus) ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm, *]
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, rfl,
            hTrustGet s0.fs.files x w hget_evs⟩
        wp_done
      · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
        apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) (by assumption)
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_d0
        wp_call_spec_lscro hDeallocCells (deallocVecBufSpec_fd A lim calleeStk) hcrl_d0
          ((bPtr, bCap, [], s0.sp - 192#64), M.stepEvents w st)
        case panic =>
          intro _ _ hm
          exact close_noPanic_subgoal_p hm
        conv => arg 4; rw [← M.stepEvents_append w (rustDeallocEvents bCap.toNat 1) st]
        apply SepWPp.of_sepWP_ret
        apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
          blkLib_eq_566 (mid := s0.readReg64 (Reg.gpr 30#5))
        intro _m_strip
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.focus_weaken
          (out_ok_fold A.repAlloc x.call.out true _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        refine focus_postAnsPool_p_fd A lim st TrustEnv x
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (w ++ rustDeallocEvents bCap.toNat 1) (.ok []) (.ok none) s0 (by sep_focus) ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm, *]
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, rfl,
            hTrustGetFree s0.fs.files x w (rustDeallocEvents bCap.toNat 1)
              hget_evs (FreeOnlyEvs.singleton 1 bCap.toNat)⟩
        wp_done

    | cons b bs' =>
      rcases hfile with hnil | ⟨ik, hser⟩
      · nomatch hnil
      · have hdec : decodeIdentityKey (b :: bs') = .ok ik :=
          hser ▸ decodeIdentityKey_serialize ik
        apply unpack_getResultAt_ok_p
        intro bCap bPtr hbCap_le hbCap_lt _hbPtr_ne
        have hlen_lt : (b :: bs').length < 2 ^ 63 := Nat.lt_of_le_of_lt hbCap_le hbCap_lt
        have hlen_ne : BitVec.ofNat 64 (b :: bs').length ≠ 0#64 := cons_len_bv_ne_zero hlen_lt
        have hlen_beq : (BitVec.ofNat 64 (b :: bs').length == 0#64) = false :=
          beq_false_of_ne hlen_ne
        have hbCap_ne : bCap ≠ 0#64 := cap_ne_zero_of_cons hbCap_le
        have hbCap_beq : (bCap == 0#64) = false := beq_false_of_ne hbCap_ne
        apply sepWPp_seq_lscro (mid := lsmpl.base 18) (by assumption)
        apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
          blkLib_eq_566 (mid := lsmpl.base 18)
        intro _m_strip_dec
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_dec _hnsp_dec => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp_dec.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_dec
        wp_call_spec_lscro hDecCells (ikDecodeCellsSpecPlaced_fd A lim calleeStk) hcrl_dec
          ((bPtr, b :: bs', s0.sp - 144#64, ik, s0.sp - 192#64), M.stepEvents w st)
        case panic =>
          intro _ _ hm
          exact close_noPanic_subgoal_p hm
        rcases exists_pollKeyChunks_of_length_32 ik.publicKey.bytes.toList_length with
          ⟨kw0, kw4, kb6, kv7, kv15, kv23, kb31, hchunks⟩
        have hkey_sp136 :
            ((s0.sp - 144#64 + 8#64) ↦ₛ ik.publicKey.bytes.toList) =
              ((s0.sp - 136#64) ↦₃₂ kw0) ∗ ((s0.sp - 132#64) ↦₁₆ kw4) ∗
              ((s0.sp - 130#64) ↦₈ kb6) ∗ ((s0.sp - 129#64) ↦₆₄ kv7) ∗
              ((s0.sp - 121#64) ↦₆₄ kv15) ∗ ((s0.sp - 113#64) ↦₆₄ kv23) ∗
              ((s0.sp - 105#64) ↦₈ kb31) := by
          have ha : s0.sp - 144#64 + 8#64 = s0.sp - 136#64 := by bv_omega
          rw [ha, hchunks (s0.sp - 136#64), pollKeyChunks_sp_136]
        have hm8 : memRegion (s0.sp - 144#64 + 40#64) 8 = memRegion (s0.sp - 104#64) 8 := by
          congr 1; bv_omega
        apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) (by assumption)
        apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
          blkLib_eq_566 (mid := lsρ lsRustDeallocSymCli)
        intro _m_strip_d1
        apply SepWP.focus_rw hkey_sp136
        apply SepWP.focus_rw hm8
        wp_steps
        apply SepWP.focus_weaken (sp_144_ikDec_fold_48 s0.sp _ _ _ _ _ _ _ _)
        refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_d1 _hnsp_d1 => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp_d1.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_d1
        wp_call_spec_lscro hDeallocCells (deallocVecBufSpec_fd A lim calleeStk) hcrl_d1
          ((bPtr, bCap, b :: bs', s0.sp - 192#64), M.stepEvents w st)
        case panic =>
          intro _ _ hm
          exact close_noPanic_subgoal_p hm
        conv => arg 4; rw [← M.stepEvents_append w (rustDeallocEvents bCap.toNat 1) st]
        apply sepWPp_seq_lscro (mid := lsmpl.base 212) (by assumption)
        apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
          blkLib_eq_566 (mid := lsmpl.base 212)
        intro _m_strip_eq
        apply SepWP.focus_rw (sret_48_sp_144_rebuild_split s0.sp)
        wp_pull_exists
        wp_steps
        refine focus_pollKeyChunks_sp_144_p s0.sp hchunks (by sep_focus) ?_ ?_ ?_ ?_
        · bv_bits
        · bv_bits
        · bv_bits
        refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_eq _hnsp_eq => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp_eq.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_eq
        wp_call_spec_lscro hEqCells (pkEqCellsSpecPlaced_fd A lim calleeStk) hcrl_eq
          ((s0.sp - 144#64, ik, x.call.call.keyA, x.call.call.key, s0.sp - 192#64),
            M.stepEvents (w ++ rustDeallocEvents bCap.toNat 1) st)
        case panic =>
          intro _ _ hm
          dsimp only [pkEqCellsSpecPlaced_fd] at hm
          simp only [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim
        apply SepWPp.of_sepWP_ret
        apply sepWP_seg_ls_vm (Q := (blkPC_566).rebase (blkPl_566).base (hooksException H))
          blkLib_eq_566 (mid := s0.readReg64 (Reg.gpr 30#5))
        intro _m_strip_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_key_fold_48 s0.sp ik.publicKey.bytes.toList_length)
        apply SepWP.focus_weaken
          (out_ok_fold A.repAlloc x.call.out (decide (ik = x.call.call.key))
            _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_ret _hnsp_ret => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp_ret.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        refine focus_postAnsPool_p_fd A lim st TrustEnv x
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (w ++ rustDeallocEvents bCap.toNat 1) (.ok (b :: bs')) (.ok (some ik)) s0
          (by sep_focus) ?_ ?_ ?_
        · simp only [wp_norm, arm64_norm, *]
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, ⟨ik, rfl, hser⟩,
            hTrustGetFree s0.fs.files x w (rustDeallocEvents bCap.toNat 1)
              hget_evs (FreeOnlyEvs.singleton 1 bCap.toNat)⟩
        wp_done

/-- Specialization of `idTrustPollInner_placed_ok_16_fd` to `CliIdTrustPollEnv GetEnv`. -/
theorem idTrustPollInner_env_placed_ok_16_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 18)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved (identityKeyDecodeRawSpec A)))))
    (hEq : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (withVmPreserved publicKeyEqMemSpec16))))
    (hhi : max (max getStk 96) (max 64 extHookStack) ≤ 2 ^ 64) :
    subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (blkPl_566).base
      (withLsCodeRoLoaded lsmpl
        (cliIdTrustPollInnerSpecPlaced_fd rd pathOk A lim (CliIdTrustPollEnv GetEnv)
          (max (max getStk 96) (max 64 extHookStack)))) :=
  idTrustPollInner_placed_ok_16_fd hFs hGet hDec hEq
    (fun _ _ _ => CliIdTrustPollEnv.fits_get)
    (fun _ _ _ => CliIdTrustPollEnv.of_get)
    (fun _ _ _ _ => CliIdTrustPollEnv.of_get_freeOnly)
    hhi

/-! ## 4. Block `566` Entry Theorems under `HookSat H lsBlackBoxU8Sym blackBoxSpecSat` -/

/-- Generic-envelope `80`-byte `eq` form of `idTrustPoll_placed_ok_of_deps_gen_fd` (Block `566`). -/
theorem idTrustPoll_placed_ok_of_deps_gen_16_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16))))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim TrustEnv stk)) := by
  have hGet' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_566 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idTrustPoll_placed_of_inner_fd
    (fun hhi => idTrustPollInner_placed_ok_16_fd hFs hGet' hDec' hEq'
      hFitGet hTrustGet hTrustGetFree hhi) hstk

/-- `CliIdTrustPollEnv` `80`-byte `eq` form of `idTrustPoll_placed_ok_of_deps_fd` (Block `566`). -/
theorem idTrustPoll_placed_ok_of_deps_16_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16))))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) := by
  have hGet' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_566 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idTrustPoll_placed_of_inner_fd
    (fun hhi => idTrustPollInner_env_placed_ok_16_fd hFs hGet' hDec' hEq' hhi) hstk

/-- `HookSat`-backed counterpart of `idTrustPoll_placed_ok_of_get_bb_fd` (conclusion is
token-identical; `h_bb` weakened from `= some blackBoxHook` to
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat`). -/
theorem idTrustPoll_placed_ok_of_get_bb_fd_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {getProg : Program} {getBlk : Nat} [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) :=
  idTrustPoll_placed_ok_of_deps_16_fd hFs hGet
    (identityKey_decode_placed_ok_fd H)
    (publicKeyEq_mem_placed_ok_of_bb_16_fd_sat h_bb) hstk hGetBlk hGetUnmut

/-- Caller-block-polymorphic form of `idTrustPoll_placed_ok_of_deps_gen_16_fd`. -/
theorem idTrustPoll_placed_caller_ok_of_deps_gen_16_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {callerProg getProg decProg eqProg : Program}
    {callerBlk getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16))))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim TrustEnv stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps_gen_16_fd hFs hGet hDec hEq
      hFitGet hTrustGet hTrustGetFree hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

/-- Caller-block-polymorphic form of `idTrustPoll_placed_ok_of_deps_16_fd`. -/
theorem idTrustPoll_placed_caller_ok_of_deps_16_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg decProg eqProg : Program}
    {callerBlk getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16))))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps_16_fd hFs hGet hDec hEq hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

/-- Caller-block-polymorphic form of `idTrustPoll_placed_ok_of_get_bb_fd_sat`. -/
theorem idTrustPoll_placed_caller_ok_of_get_bb_fd_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg : Program} {callerBlk getBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_get_bb_fd_sat hFs hGet h_bb hstk hGetBlk hGetUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFdSat
