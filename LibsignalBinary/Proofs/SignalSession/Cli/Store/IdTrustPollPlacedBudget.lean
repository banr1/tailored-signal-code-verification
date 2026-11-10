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
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudget
import ProofLib.SepLogic.WP.Apply
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `<IdentityFiles as IdentityKeyStore>::is_trusted_identity::{closure#0}`

Lifts `<PublicKey as PartialEq>::eq` (Block 212) and `IdentityKey::decode` (Block 18) to
`withVmPreserved`, and proves budget-threaded `idTrustPollSpecPlaced` on Block `566`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_212 blkPl_212 libsignalMutatedBlocks lsBlackBoxU8Sym
   ls_subroutine_ok_cl_of_plain lsmpl sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (extHookStack pkTryFromPlacedSpec pkTryFromSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (blkPC_211 blkPl_211 publicKeyEqSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.RecordCodecs.Placed (blkLib_eq_18 blkPC_18 blkPl_18 lsProg_18)
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyResultAt)
open CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers
  (exists_ikKeyChunks_of_length_32 ikKeyChunks_ret_8 ikKeyChunks_sp_87 mask_split_64
   memRegion_48_err_split memRegion_48_ok_split memRegion_sp_88_badLen_post
   memRegion_sp_88_badType_post memRegion_sp_88_nil_post memRegion_sp_88_ok_post
   pkTryFrom_sp_88_badLen pkTryFrom_sp_88_badType pkTryFrom_sp_88_nil pkTryFrom_sp_88_ok
   pointsTo64_zext8_split publicKey_deserialize_cases sevenLo_ret_8 sevenLo_sp_87 sp_88_repack
   spe_badKeyType_post spe_noKeyType_post stackAt_ikDec_split truncate16_zeroExtend32
   truncate8_zeroExtend32 zero_orr_zext8_mask)
open CryptoVerification.SignalSession.Cli (DirGhost IdPollGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_566)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
  (publicKeyEqBudgetSpec publicKey_eq_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
  (pkTryFromPlacedBudgetSpec pkTryFrom_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirGetSpecPlaced idTrustPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudget
  (CliIdTrustPollEnv idTrustPollInner_env_placed_ok idTrustPollInner_placed_ok
   idTrustPoll_placed_of_inner)

export LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudget
  (CliIdTrustPollEnv)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved

/-! ## 1. `<PublicKey as PartialEq>::eq` (Block `212`) and `IdentityKey::decode` (Block `18`)
  with `withVmPreserved` -/

/-- Bridge from `LoopBudget.publicKey_eq_placed_ok` (Block `212`) to
`withVmPreserved Getters.publicKeyEqSpec`. -/
theorem publicKeyEq_placed_ok_of_bb [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H)
      (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)) := by
  have h := publicKey_eq_placed_ok (H := H) h_bb
  have hspec : publicKeyEqBudgetSpec = withVmPreserved publicKeyEqSpec := rfl
  rwa [hspec] at h

/-- Relocatable `[LibsignalPlacement]` `VmPreserved`-strengthened specification of
`IdentityKey::decode` (Block `18`) over `A : RustCliAllocBudget M`. -/
abbrev identityKeyDecodePlacedBudgetSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) : Spec DecodeGhost :=
  withLsCodeLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A))

set_option maxHeartbeats 1200000 in
/-- Relocatable `IdentityKey::decode` (Block `18`) meets `identityKeyDecodePlacedBudgetSpec A`,
given the `VmPreserved`-strengthened `PublicKey::try_from` contract (Block `211`). -/
theorem identityKey_decode_placed_ok_of_pkTryFrom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hpk : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedBudgetSpec) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedBudgetSpec A) := by
  have hcall : subroutine_ok (lsProg_18 H) (lsmpl.base 211)
      (withLsCl lsmpl pkTryFromPlacedBudgetSpec) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_18 H) hpk
  clear hpk
  simp only [withLsCl, pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec,
    pkTryFromSpec, sepConj_assoc] at hcall
  simp only [identityKeyDecodePlacedBudgetSpec, withLsCodeLoaded, withVmPreserved,
    identityKeyDecodeRawSpec, sepConj_assoc]
  wp_init x s0
  obtain ⟨bytesA, bytes, ret⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = bytesA := by assumption
  have hx8 : s0.readReg64 (Reg.gpr 8#5) = ret := by assumption
  subst hx0 hx8
  rcases publicKey_deserialize_cases bytes with
    ⟨pk, hdes, hdec⟩ | ⟨hdes, hdec⟩ | ⟨t, hdes, hdec⟩ | ⟨n, hdes, hdec⟩
  · have hbs32 : pk.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_ikKeyChunks_of_length_32 hbs32
    rw [hdec, memRegion_48_ok_split (s0.readReg64 (Reg.gpr 8#5)),
        identityKeyResultAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
        ikKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_ok_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_ok s0.sp pk, hchunks (s0.sp - 87#64), ikKeyChunks_sp_87 s0.sp]
    simp only [sepConj_assoc]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    rw [sevenLo_sp_87 s0.sp]
    wp_steps
    rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_steps
    rw [sp_88_repack s0.sp]
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    try simp only [sepConj_assoc, hvm_tot]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_noKeyType_post A.repAlloc (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_nil_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_nil s0.sp]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    try simp only [sepConj_assoc, hvm_tot]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_badKeyType_post A.repAlloc (s0.readReg64 (Reg.gpr 8#5)) t]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badType_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badType s0.sp t]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    try rw [zero_orr_zext8_mask]
    rw [pointsTo64_zext8_split (s0.readReg64 (Reg.gpr 8#5)) t]
    try simp only [sepConj_assoc, hvm_tot]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badLen_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badLen s0.sp n]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    try rw [mask_split_64] at hvm2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    dsimp only [identityKeyResultAt, speAt]
    try simp only [sepConj_assoc, hvm_tot]
    wp_done

/-- Relocatable `IdentityKey::decode` (Block `18`) meets `identityKeyDecodePlacedBudgetSpec A`
for any hooks `H`. -/
theorem identityKey_decode_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedBudgetSpec A) :=
  identityKey_decode_placed_ok_of_pkTryFrom (pkTryFrom_placed_ok H)

/-! ## 2. Block `566` (`is_trusted_identity::{closure#0}`) Entry Theorems -/

theorem idTrustPoll_placed_ok_of_deps_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim TrustEnv stk) := by
  have hGet' := ls_transfer_lscro (callerProg := lsProg_566 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := lsProg_566 H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_cl_to_lscro (callerProg := lsProg_566 H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idTrustPoll_placed_of_inner
    (fun hhi => idTrustPollInner_placed_ok hC hGet' hDec' hEq'
      hFitGet hTrustGet hTrustGetFree hhi) hstk

/-- Block `566` (`is_trusted_identity::{closure#0}`) meets
`idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk`
given `AllocContractsXCliPlaced`, `Dir::get` (block `589`), `IdentityKey::decode` (block `18`),
and `<PublicKey as PartialEq>::eq` (block `212`). -/
theorem idTrustPoll_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk) := by
  have hGet' := ls_transfer_lscro (callerProg := lsProg_566 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := lsProg_566 H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_cl_to_lscro (callerProg := lsProg_566 H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idTrustPoll_placed_of_inner
    (fun hhi => idTrustPollInner_env_placed_ok hC hGet' hDec' hEq' hhi) hstk

/-- Convenience specialization discharging `IdentityKey::decode` via
`identityKey_decode_placed_ok` and `<PublicKey as PartialEq>::eq` via
`publicKeyEq_placed_ok_of_bb`. -/
theorem idTrustPoll_placed_ok_of_get_bb [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {getProg : Program} {getBlk : Nat} [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk) :=
  idTrustPoll_placed_ok_of_deps hC hGet
    (identityKey_decode_placed_ok H)
    (publicKeyEq_placed_ok_of_bb h_bb) hstk hGetBlk hGetUnmut

theorem idTrustPoll_placed_caller_ok_of_deps_gen [LibsignalPlacement] {M : AllocCostModel}
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
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim TrustEnv stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps_gen hC hGet hDec hEq
      hFitGet hTrustGet hTrustGetFree hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

theorem idTrustPoll_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg decProg eqProg : Program}
    {callerBlk getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps hC hGet hDec hEq hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
